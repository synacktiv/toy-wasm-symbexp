{-# LANGUAGE FlexibleContexts #-}

module Main where

import Arch.WASM.Instructions
import Control.Monad.Identity
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import Data.Functor.Classes
import qualified Data.IntMap.Strict as IntMap
import Data.List (foldl')
import qualified Data.Set as S
import Data.Word (Word32, Word8)
import Domain.Taint
import GHC.Natural (Natural)
import Language.Wasm.Structure
import Symb.Expression
import Test.Hspec

-- | expects:
--  local0: pointer to the expected password
--  local1: pointer to the actual password
--  local2: a local variable (i pointer)
--  local3: a local variable (temporary storage)
--  local4: return value
-- does a strcmp
challengePassword :: [Instruction Natural]
challengePassword =
  [ I32Const 0,
    SetLocal 2,
    I32Const 1,
    SetLocal 4,
    Block
      (Inline Nothing)
      [ Loop
          (Inline Nothing)
          [ -- load the byte from the expected password
            GetLocal 2,
            GetLocal 0,
            IBinOp BS32 IAdd,
            I32Load8U (MemArg 0 0),
            -- store it to local3
            SetLocal 3,
            -- and pop it to the stack
            GetLocal 3,
            -- load the byte from the actual password
            GetLocal 2,
            GetLocal 1,
            IBinOp BS32 IAdd,
            I32Load8U (MemArg 0 0),
            -- compare the bytes
            IRelOp BS32 IEq,
            If (Inline Nothing) [] [I32Const 0, SetLocal 4, Br 2],
            -- check if this was the last byte
            GetLocal 3,
            I32Const 0,
            IRelOp BS32 IEq,
            BrIf 1,
            -- increment counter
            GetLocal 2,
            I32Const 1,
            IBinOp BS32 IAdd,
            SetLocal 2
          ]
      ],
    GetLocal 4
  ]

storeMemory :: Symb f => Int -> BS8.ByteString -> IntMap.IntMap (f Word8) -> IntMap.IntMap (f Word8)
storeMemory addr bs stt = foldl' setbyte stt (zip [addr ..] (BS.unpack bs))
  where
    setbyte curmem (a, b) = IntMap.insert a (inject b) curmem

-- | specialized version of storeMemory that adds a custom taint to bytes
storeTainted :: String -> Int -> BS.ByteString -> IntMap.IntMap (Tainted Word8) -> IntMap.IntMap (Tainted Word8)
storeTainted tag addr bs stt = foldl' setbyte stt (zip [addr ..] (BS.unpack bs))
  where
    setbyte curmem (a, b) = IntMap.insert a (Tainted (Just b) (S.singleton tag)) curmem

runChallengePassword :: [Char] -> [Char] -> Either String [VNum Tainted]
runChallengePassword expected password = trivialEvaluate md stt
  where
    bexpected = BS8.pack expected
    bpassword = BS8.pack password
    aexpected = 0
    apassword = BS8.length bexpected + 2
    md = emptyModule
    mem = storeTainted "expected" aexpected bexpected $ storeTainted "password" apassword bpassword mempty
    stt = WState mem [] (Frame [VI32 (Tainted (Just x) mempty) | x <- [0, fromIntegral apassword, 0, 0, 0]] challengePassword)

testProgram :: (Show1 f, Eq1 f, Symb f, RMonad f Identity) => [Instruction Natural] -> [f Word32] -> [f Word32] -> Expectation
testProgram instrs istack estack = trivialEvaluate md stt `shouldBe` Right (map VI32 estack)
  where
    md = emptyModule
    stt = WState mempty [] (Frame (map VI32 istack) instrs)

interpreterTests :: Spec
interpreterTests = do
  it "simple add" $ testProgram [GetLocal 0, GetLocal 1, IBinOp BS32 IAdd] [Identity 4, 8] [12]
  it "simple loop" $
    testProgram
      [ Block
          (Inline Nothing)
          [ Loop
              (Inline Nothing)
              [ GetLocal 0,
                I32Const 0,
                IRelOp BS32 IEq,
                BrIf 1,
                GetLocal 0,
                GetLocal 1,
                IBinOp BS32 IAdd,
                SetLocal 1,
                GetLocal 0,
                I32Const 1,
                IBinOp BS32 ISub,
                SetLocal 0
              ]
          ],
        GetLocal 1
      ]
      [Identity 50, 0]
      [sum [0 .. 50]]

taintTests :: Spec
taintTests = do
  it "untainted add" $
    testProgram
      [GetLocal 0, GetLocal 1, IBinOp BS32 IAdd]
      [Tainted (Just 4) mempty, Tainted (Just 8) mempty]
      [Tainted (Just 12) mempty]
  it "tainted add" $
    testProgram
      [GetLocal 0, GetLocal 1, IBinOp BS32 IAdd]
      [Tainted (Just 4) (S.singleton "left"), Tainted (Just 8) (S.singleton "right")]
      [Tainted (Just 12) (S.fromList ["left", "right"])]

main :: IO ()
main = hspec $ do
  describe "concrete intepreter test" interpreterTests
  describe "tainting intepreter test" taintTests
  describe "strcmp" $ do
    -- note that the taint does not work here :)
    it "aba == aba" $ runChallengePassword "aba" "aba" `shouldBe` Right [VI32 (Tainted (Just 1) mempty)]
    it "aba != abk" $ runChallengePassword "aba" "abk" `shouldBe` Right [VI32 (Tainted (Just 0) mempty)]
    it "aba != ab" $ runChallengePassword "aba" "ab" `shouldBe` Right [VI32 (Tainted (Just 0) mempty)]
