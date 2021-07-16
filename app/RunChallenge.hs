{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Main (main) where

import Arch.WASM.Instructions
import Control.Monad
import Control.Monad.IO.Class (liftIO)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import qualified Data.IntMap.Strict as IntMap
import Data.SBV
import Data.SBV.Control
import Language.Wasm (decode)
import Language.Wasm.Structure
  ( Function (Function),
    Module (functions),
  )
import Symb.Expression
import System.Environment (getArgs)
import Data.Char (chr)

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
  [modulepath, username, password] <- getArgs
  md <- either error id . decode <$> BS.readFile modulepath
  let Function _ _ instrs = functions md !! 4
      busername = BS8.pack username
      bpassword = BS8.pack password
      ausername = 0
      apassword = BS8.length busername + 2
      mkistate stt = WState stt [] (Frame [VI32 (inject $ fromIntegral a) | a <- [ausername, apassword]] instrs)
  runSMTWith (z3 {verbose = False}) $ do
    (susername, memory_temp) <- storeString sWord8 ausername busername mempty
    (spassword, memory) <- storeString sWord8 apassword bpassword memory_temp
    mapM_ (\v -> constrain (v .>= literal 0x20 .&& v .<= literal 0x7f)) memory
    let sbcstate = mkistate memory
    let allBranches = mpEvaluate md sbcstate
    constraints <- forM allBranches $ \(cstrs, res) ->
      case res of
        Left rr -> error rr
        Right (_, [VI32 result]) -> pure (sAnd ((result .== 2) : cstrs))
        Right _ -> error "malformed program output"
    constrain (sOr constraints)
    query $ do
      cs <- checkSat
      case cs of
        Sat -> do
          vusername <- mapM (fmap (chr . fromIntegral) . getValue) susername
          vpassword <- mapM (fmap (chr . fromIntegral) . getValue) spassword
          liftIO $ do
            putStrLn ("username: " ++ vusername)
            putStrLn ("password: " ++ vpassword)
        Unsat -> liftIO (putStrLn "no sat")
        _ -> error (show cs)

