{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Arch.WASM.Instructions where

import Control.Lens
import Control.Monad (forM_, when)
import Control.Monad.Except
  ( MonadError (throwError),
    runExceptT,
  )
import Control.Monad.Reader (runReaderT)
import Control.Monad.Reader.Class (MonadReader (ask))
import Control.Monad.State.Strict
  ( MonadState,
    evalState,
  )
import Data.Bits
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe (fromMaybe)
import Data.Word
import GHC.Natural (Natural)
import Language.Wasm.Structure

data WASM

data WState = WState
  { _wmemory :: IntMap.IntMap Word8,
    _wstack :: [StackElement],
    _wframe :: Frame
  }
  deriving (Show)

data Frame = Frame
  { _fvals :: [VNum],
    _finstrs :: [Instruction Natural]
  }
  deriving (Show)

data StackElement
  = Value VNum
  | Cont [Instruction Natural]
  | Activation ResultType Frame
  deriving (Show)

data VNum
  = VI32 Word32
  | VI64 Word64
  | VF32 Float
  | VF64 Double
  deriving (Show, Eq)

makeLenses ''WState
makeLenses ''Frame

getValueType :: VNum -> ValueType
getValueType v =
  case v of
    VI32 _ -> I32
    VI64 _ -> I64
    VF32 _ -> F32
    VF64 _ -> F64

push :: MonadState WState m => StackElement -> m ()
push x = wstack %= (x :)

pushV :: MonadState WState m => VNum -> m ()
pushV = push . Value

popM :: MonadState WState m => m (Maybe StackElement)
popM =
  use wstack >>= \case
    [] -> pure Nothing
    x : xs -> Just x <$ (wstack .= xs)

pop :: (MonadState WState m, MonadError String m) => m StackElement
pop = popM >>= maybe (throwError "Pop failed, empty stack") pure

popV :: (MonadState WState m, MonadError String m) => m VNum
popV =
  pop >>= \case
    Value x -> pure x
    _ -> throwError "Did not pop a value"

pop32 :: (MonadState WState m, MonadError String m) => m Word32
pop32 =
  popV >>= \case
    VI32 x -> pure x
    v -> throwError ("Expected I32, got " ++ show (getValueType v))

cast :: MonadError String m => ValueType -> VNum -> m VNum
cast vt v
  | rt == vt = pure v
  | otherwise = throwError ("mismatched types, expected " ++ show vt ++ " got " ++ show rt)
  where
    rt = getValueType v

getFunction :: (MonadError String m) => Natural -> Module -> m Function
getFunction fid md =
  case functions md ^? ix (fromIntegral fid) of
    Nothing -> throwError "Unknown function called"
    Just f -> pure f

getFuncType :: (MonadError String m) => Natural -> Module -> m FuncType
getFuncType fid md =
  case types md ^? ix (fromIntegral fid) of
    Nothing -> throwError "Unknown type"
    Just f -> pure f

makeDefault :: ValueType -> VNum
makeDefault vt =
  case vt of
    I32 -> VI32 0
    I64 -> VI64 0
    F32 -> VF32 0
    F64 -> VF64 0

storeByte :: (MonadState WState m, MonadError String m) => Word32 -> MemArg -> Word8 -> m ()
storeByte addr (MemArg off 0) b = wmemory . at (fromIntegral addr + fromIntegral off) ?= b
storeByte _ _ _ = throwError "Alignement unsupported for storing bytes"

loadByte :: (MonadState WState m, MonadError String m) => Word32 -> MemArg -> m Word8
loadByte addr (MemArg off 0) = fromMaybe 0 <$> preuse (wmemory . ix (fromIntegral addr + fromIntegral off))
loadByte _ _ = throwError "Alignement unsupported for loading bytes"

toBool :: VNum -> Bool
toBool v =
  case v of
    VI32 x -> x /= 0
    VI64 x -> x /= 0
    VF32 x -> x /= 0
    VF64 x -> x /= 0

runBreak :: (MonadState WState m, Num t, Eq t, MonadError String m) => t -> m ()
runBreak n = do
  let popCont cur = do
        v <- pop
        case v of
          Cont ninstr -> if cur == 0 then pure ninstr else popCont (cur - 1)
          Value _ -> popCont cur
          Activation _ _ -> error "popped an activation"
  rv <- popCont n
  wframe . finstrs .= rv

decodeInstr :: (MonadError String m, MonadState WState m, MonadReader Module m) => Instruction Natural -> m ()
decodeInstr i =
  case i of
    GetLocal n -> do
      vals <- use (wframe . fvals)
      case vals ^? ix (fromIntegral n) of
        Nothing -> throwError "Out of range GetLocal"
        Just v -> wstack %= (Value v :)
    SetLocal n -> do
      v <- popV
      wframe . fvals . ix (fromIntegral n) .= v
    Call fid -> do
      md <- ask
      -- get function type, body, and create new frame
      Function ftype flocals fcontent <- getFunction fid md
      FuncType prms rt <- getFuncType ftype md
      newlocals <- (++ map makeDefault flocals) . reverse <$> mapM (\t -> popV >>= cast t) prms
      let nframe = Frame newlocals fcontent
      -- store previous frame, and replace with the new frame
      use wframe >>= push . Activation rt
      wframe .= nframe
    I32Const n -> pushV (VI32 (fromIntegral n))
    Block (Inline Nothing) blockbody -> do
      use (wframe . finstrs) >>= push . Cont
      wframe . finstrs .= blockbody
    Loop (Inline Nothing) loopbody -> do
      use (wframe . finstrs) >>= push . Cont . (i :)
      wframe . finstrs .= loopbody
    I32Store8 ma -> do
      vtoStore <- pop32
      addr <- pop32
      let toStore = fromIntegral vtoStore
      storeByte addr ma toStore
    I32Load8U ma -> do
      addr <- pop32
      loadByte addr ma >>= pushV . VI32 . fromIntegral
    IRelOp BS32 opr -> do
      b <- pop32
      a <- pop32
      res <- case opr of
        IEq -> pure $ a == b
        INe -> pure $ a /= b
        ILeU -> pure $ a <= b
        _ -> throwError "Unsupported comparison"
      push $ Value $ VI32 $ if res then 1 else 0
    If (Inline Nothing) tb fb -> do
      res <- toBool <$> popV
      use (wframe . finstrs) >>= push . Cont
      wframe . finstrs
        .= if res
          then tb
          else fb
    IBinOp BS32 bop -> do
      b <- pop32
      a <- pop32
      topush <- case bop of
        IMul -> pure $ a * b
        IAdd -> pure $ a + b
        IXor -> pure $ a `xor` b
        IAnd -> pure $ a .&. b
        IOr -> pure $ a .|. b
        ISub -> pure $ a - b
        IShrU -> pure $ a `shiftR` fromIntegral b
        IRotl -> pure $ a `rotateL` fromIntegral b
        _ -> throwError ("unsupported binop " ++ show bop)
      pushV (VI32 topush)
    BrIf n -> do
      brnch <- toBool <$> popV
      when brnch (runBreak n)
    Br n -> runBreak n
    _ -> throwError ("unknown instruction " ++ show i)

interpret :: (MonadError String m, MonadState WState m, MonadReader Module m) => m [VNum]
interpret = do
  instructions <- use (wframe . finstrs)
  case instructions of
    (x : xs) -> do
      wframe . finstrs .= xs
      decodeInstr x
      interpret
    [] -> do
      e <- pop
      case e of
        Value v -> findActivation [v]
        Activation [] newframe -> do
          (wframe .= newframe) *> interpret
        Cont is -> (wframe . finstrs .= is) *> interpret
        _ -> throwError "unhandled stack element"
  where
    findActivation stackr = do
      e <- popM
      case e of
        Nothing -> pure stackr
        Just (Value v) -> findActivation (v : stackr)
        Just (Activation rtps newframe) ->
          if length rtps /= length stackr
            then throwError "mismatched stack"
            else do
              forM_ (zip stackr rtps) $ \(s, r) -> do
                cast r s >>= push . Value
              wframe .= newframe
              interpret
        _ -> throwError "Error in findActivation"

trivialEvaluate :: Module -> WState -> Either String [VNum]
trivialEvaluate md = evalState (runExceptT (runReaderT interpret md))