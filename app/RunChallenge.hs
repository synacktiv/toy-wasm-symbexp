module Main where

import Arch.WASM.Instructions
import Symb.Expression
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import qualified Data.IntMap.Strict as IntMap
import Data.List (foldl')
import Data.Word (Word8)
import Language.Wasm (decode)
import Language.Wasm.Structure
  ( Function (Function),
    Module (functions),
  )
import System.Environment (getArgs)

storeString :: Symb f => Int -> BS.ByteString -> IntMap.IntMap (f Word8) -> IntMap.IntMap (f Word8)
storeString addr bs stt = foldl' setbyte stt (zip [addr ..] (BS.unpack bs))
  where
    setbyte curmem (a, b) = IntMap.insert a (inject b) curmem

main :: IO ()
main = do
  [modulepath, username, password] <- getArgs
  md <- either error id . decode <$> BS.readFile modulepath
  let Function _ _ instrs = functions md !! 4
      busername = BS8.pack username
      bpassword = BS8.pack password
      ausername = 0
      apassword = BS8.length busername + 2
      istate =
        WState
          (storeString ausername busername $ storeString apassword bpassword mempty)
          []
          (Frame [VI32 (fromIntegral a) | a <- [ausername, apassword]] instrs)
  print $ trivialEvaluate md istate
