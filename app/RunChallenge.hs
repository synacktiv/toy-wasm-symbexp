{-# LANGUAGE OverloadedStrings #-}

module Main where

import Arch.WASM.Instructions
import Control.Monad
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import qualified Data.IntMap.Strict as IntMap
import Data.List (foldl')
import qualified Data.Set as S
import Data.Word (Word8)
import Domain.Symbolic
import Domain.Taint
import Language.Wasm (decode)
import Language.Wasm.Structure
  ( Function (Function),
    Module (functions),
  )
import Symb.Expression
import System.Environment (getArgs)

storeString :: Symb f => Int -> BS.ByteString -> IntMap.IntMap (f Word8) -> IntMap.IntMap (f Word8)
storeString addr bs stt = foldl' setbyte stt (zip [addr ..] (BS.unpack bs))
  where
    setbyte curmem (a, b) = IntMap.insert a (if b == 0x3f then sym8 ('a' : show a) else inject b) curmem

storeStringTainted :: String -> Int -> BS.ByteString -> IntMap.IntMap (Tainted Word8) -> IntMap.IntMap (Tainted Word8)
storeStringTainted tag addr bs stt = foldl' setbyte stt (zip [addr ..] (BS.unpack bs))
  where
    setbyte curmem (a, b) = IntMap.insert a (Tainted (Just b) (S.singleton tag)) curmem

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
  let taintedstate = mkistate (storeStringTainted "username" ausername busername $ storeStringTainted "password" apassword bpassword mempty)
      taintedres = trivialEvaluate md taintedstate :: Either String [VNum Tainted]
  let symbstate = mkistate (storeString ausername busername $ storeString apassword bpassword mempty) :: WState Symbolic
      symbres = mpEvaluate md symbstate
  print taintedres
  forM_ symbres $ \(cstrs, res) ->
    case res of
      Left rr -> error rr
      Right (_, vars) -> do
        putStrLn "----"
        putStrLn "constraints"
        mapM_ (print . simplify) cstrs
        putStrLn "result"
        let showVar (VI32 x) = print (simplify x)
            showVar _ = error "unexpected"
        mapM_ showVar vars
