module Main where

import Arch.WASM.Instructions
import Control.Monad.Identity
import Data.Word (Word32)
import GHC.Natural (Natural)
import Language.Wasm.Structure
import Test.Hspec

testProgram :: [Instruction Natural] -> [Word32] -> [Word32] -> Expectation
testProgram instrs istack estack = trivialEvaluate md stt `shouldBe` Right (map show estack)
  where
    md = emptyModule
    stt = WState mempty [] (Frame (map (VI32 . Identity) istack) instrs)

insterpreterTests :: SpecWith ()
insterpreterTests = do
  it "simple add" $ testProgram [GetLocal 0, GetLocal 1, IBinOp BS32 IAdd] [4, 8] [12]
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
      [50, 0]
      [sum [0 .. 50]]

main :: IO ()
main = hspec $ do
  describe "intepreter test" insterpreterTests
