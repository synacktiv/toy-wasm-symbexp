{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Main (main) where

import Arch.WASM.Instructions
import Control.Monad
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Identity
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import Data.Char (chr)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as M
import Data.SBV hiding (Symbolic)
import Data.SBV.Control
import Domain.Symbolic (Symbolic (..), simplify, vsimplify)
import Language.Wasm (decode)
import Language.Wasm.Structure
  ( Function (Function),
    Module (functions),
  )
import Options.Applicative
import Symb.Expression

-- | SMT means Z3, and Symbolic our own symbolic representation
data RunningMode = SMT | Symbolic
  deriving (Show, Read)

-- | command line options
data Options = Options
  { _runningMode :: RunningMode,
    _path :: FilePath,
    _username :: String,
    _password :: String,
    _expected :: Word32
  }

-- | command line parser
-- yes, optparse-applicative is awesome
arguments :: Parser Options
arguments =
  Options
    <$> option auto (long "mode" <> help "Accepted values: SMT, Symbolic" <> showDefault <> value SMT)
    <*> strArgument (metavar "PATH" <> help "Path to keygenme.wasm")
    <*> strArgument (metavar "USERNAME" <> help "Challenge username")
    <*> strArgument (metavar "PASSWORD" <> help "Challenge password")
    <*> option auto (long "expected" <> help "Expected value" <> showDefault <> value 2)

opts :: ParserInfo Options
opts = info (arguments <**> helper) (fullDesc <> progDesc "Solve the ForumCracks challenge")

-- | Break "and" clauses
breakup :: Show a => Symbolic a -> [Symbolic a]
breakup s =
  case s of
    And a b -> breakup a ++ breakup b
    Eq (Or a@(Oneif _) b) (Raw 0) -> [Eq a (Raw 0), Eq b (Raw 0)]
    _ -> [s]

-- | parses a list of constraints, and recognizes some patterns:
-- * if the constraint is false, the whole expression can't be satisfied
-- * if there is a variable equality constraint, assign the value to the variable
--   (note that we do not have to check for conflicting assignments, as we use vsimplify that will resolve to False in that case)
checkConstraint :: M.Map String Word8 -> Symbolic Bool -> Maybe (M.Map String Word8)
checkConstraint vars sb =
  case vsimplify vars sb of
    Raw False -> Nothing
    Eq (Sym x) (Raw v) -> Just (M.insert x v vars)
    _ -> Just vars

-- | a simple utility function that checks if a Symbolic is a given raw value
isRaw :: Eq a => a -> Symbolic a -> Bool
isRaw x s =
  case s of
    Raw x' -> x == x'
    _ -> False

-- | store a string in memory, making it symbolic when the character is '?'
-- returns a symbolic string for solution printing
storeString ::
  (Symb f, Monad m) =>
  (String -> m (f Word8)) ->
  Int ->
  BS.ByteString ->
  IntMap.IntMap (f Word8) ->
  m ([f Word8], IntMap.IntMap (f Word8))
storeString sym8 addr bs stt = foldM setbyte ([], stt) (zip [addr ..] (BS.unpack bs))
  where
    setbyte (curstring, curmem) (a, b) = do
      val <-
        if b == 0x3f
          then sym8 ('a' : show a)
          else pure (inject b)
      pure (curstring ++ [val], IntMap.insert a val curmem)

main :: IO ()
main = do
  -- command line parsing
  Options runningMode modulepath username password expected <- execParser opts
  md <- either error id . decode <$> BS.readFile modulepath
  -- prepare the environment
  let Function _ _ instrs = functions md !! 4
      busername = BS8.pack username
      bpassword = BS8.pack password
      ausername = 0
      apassword = BS8.length busername + 2
  let mkistate :: Symb f => IntMap.IntMap (f Word8) -> WState f
      mkistate stt = WState stt [] (Frame [VI32 (inject $ fromIntegral a) | a <- [ausername, apassword]] instrs)
  case runningMode of
    Symbolic -> do
      -- run our own symbolic computation
      let (susername, memory_temp) = runIdentity $ storeString (pure . Sym) ausername busername mempty
          (spassword, memory) = runIdentity $ storeString (pure . Sym) apassword bpassword memory_temp
          stt = mkistate memory
      let allBranches = mpEvaluate md stt
      -- traverse all execution path, and print them using showCase
      forM_ allBranches $ \(cstrs, res) ->
        case res of
          Left rr -> error rr
          Right (_, [VI32 result]) -> showCase expected cstrs result susername spassword
          Right _ -> error "malformed program output"
    SMT -> do
      runSMTWith (z3 {verbose = False}) $ do
        (susername, memory_temp) <- storeString sWord8 ausername busername mempty
        (spassword, memory) <- storeString sWord8 apassword bpassword memory_temp
        -- constrain all bytes of the username and password strings to be ascii, so as to cut running time
        mapM_ (\v -> constrain (v .>= literal 0x20 .&& v .<= literal 0x7f)) memory
        let sbcstate = mkistate memory
        -- run all paths
        let allBranches = mpEvaluate md sbcstate
        -- for all paths, "and" all the constraints together, including that the result is equal to the expected value
        constraints <- forM allBranches $ \(cstrs, res) ->
          case res of
            Left rr -> error rr
            Right (_, [VI32 result]) -> pure (sAnd ((result .== fromIntegral expected) : cstrs))
            Right _ -> error "malformed program output"
        -- and "or" all paths constraintes
        constrain (sOr constraints)
        query $ do
          -- run z3
          cs <- checkSat
          -- and display results
          case cs of
            Sat -> do
              vusername <- mapM (fmap (chr . fromIntegral) . getValue) susername
              vpassword <- mapM (fmap (chr . fromIntegral) . getValue) spassword
              liftIO $ do
                putStrLn ("username: " ++ vusername)
                putStrLn ("password: " ++ vpassword)
            Unsat -> liftIO (putStrLn "no sat")
            _ -> error (show cs)

-- | display a single execution path result
showCase :: Word32 -> [Domain.Symbolic.Symbolic Bool] -> Domain.Symbolic.Symbolic Word32 -> [Domain.Symbolic.Symbolic Word8] -> [Domain.Symbolic.Symbolic Word8] -> IO ()
showCase expected cstrs res susername spassword = do
  -- simplify and breakup all constraints
  let allcstrs = concatMap (breakup . simplify) (Eq res (Raw expected) : cstrs)
  -- look for contradictions in the constraints, and update the variable map
  let simplResult = do
        -- create the variable map
        vars <- foldM checkConstraint M.empty allcstrs
        -- simplify everything now that we know some variable values
        let ncstrs = map (vsimplify vars) allcstrs
        -- ensure there are no "False" constraints
        guard (not (any (isRaw False) ncstrs))
        -- ensure all characters are printable
        guard (0 `notElem` vars)
        -- yay!
        pure (vars, filter (not . isRaw True) ncstrs)
  forM_ simplResult $ \(vars, scstrs) -> do
    putStrLn "# Solution:"
    unless (null scstrs) $ do
      putStrLn "Constraints:"
      mapM_ (putStrLn . (" * " ++) . show) scstrs
    let toChar e =
          case e of
            Raw x -> [chr (fromIntegral x)]
            Sym v -> maybe "?" (pure . chr . fromIntegral) (M.lookup v vars)
            _ -> show e
    putStrLn ("username: " ++ concatMap toChar susername)
    putStrLn ("password: " ++ concatMap toChar spassword)
