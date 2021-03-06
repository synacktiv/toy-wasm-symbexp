{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Arch.WASM.Instructions where

import Control.Lens
import Control.Monad.Except
  ( MonadError (throwError),
    runExceptT,
  )
import Control.Monad.Reader (runReaderT)
import Control.Monad.Reader.Class (MonadReader (ask))
import Control.Monad.State.Strict
import Data.Functor.Classes
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe (fromMaybe)
import Data.Word
import Domain.Multipath
import GHC.Natural (Natural)
import Language.Wasm.Structure
  ( BitSize (BS32),
    BlockType (Inline),
    FuncType (FuncType),
    Function (Function),
    IBinOp (IAdd, IAnd, IMul, IOr, IRotl, IShrU, ISub, IXor),
    IRelOp (IEq, ILeU, INe),
    Instruction
      ( Block,
        Br,
        BrIf,
        Call,
        GetLocal,
        I32Const,
        I32Load8U,
        I32Store8,
        IBinOp,
        IRelOp,
        If,
        Loop,
        SetLocal
      ),
    MemArg (MemArg),
    Module (functions, types),
    ResultType,
    ValueType (..),
  )
import Symb.Expression

data WASM

data WState (f :: * -> *) = WState
  { _wmemory :: IntMap.IntMap (f Word8),
    _wstack :: [StackElement f],
    _wframe :: Frame f
  }

data Frame (f :: * -> *) = Frame
  { _fvals :: [VNum f],
    _finstrs :: [Instruction Natural]
  }

data StackElement (f :: * -> *)
  = Value (VNum f)
  | Cont [Instruction Natural]
  | Activation ResultType (Frame f)

data VNum (f :: * -> *)
  = VI32 (f Word32)
  | VI64 (f Word64)
  | VF32 (f Float)
  | VF64 (f Double)

makeLenses ''WState
makeLenses ''Frame

instance Show1 f => Show (VNum f) where
  showsPrec n v = case v of
    VI32 x -> liftShowsPrec showsPrec showList n x
    VI64 x -> liftShowsPrec showsPrec showList n x
    VF32 x -> liftShowsPrec showsPrec showList n x
    VF64 x -> liftShowsPrec showsPrec showList n x

instance Eq1 f => Eq (VNum f) where
  a == b = case (a, b) of
    (VI32 x, VI32 y) -> liftEq (==) x y
    (VF32 x, VF32 y) -> liftEq (==) x y
    (VI64 x, VI64 y) -> liftEq (==) x y
    (VF64 x, VF64 y) -> liftEq (==) x y
    _ -> False

getValueType :: VNum f -> ValueType
getValueType v =
  case v of
    VI32 _ -> I32
    VI64 _ -> I64
    VF32 _ -> F32
    VF64 _ -> F64

push :: MonadState (WState f) m => StackElement f -> m ()
push x = wstack %= (x :)

pushV :: MonadState (WState f) m => VNum f -> m ()
pushV = push . Value

popM :: MonadState (WState f) m => m (Maybe (StackElement f))
popM =
  use wstack >>= \case
    [] -> pure Nothing
    x : xs -> Just x <$ (wstack .= xs)

pop :: (MonadState (WState f) m, MonadError String m) => m (StackElement f)
pop = popM >>= maybe (throwError "Pop failed, empty stack") pure

popV :: (MonadState (WState f) m, MonadError String m) => m (VNum f)
popV =
  pop >>= \case
    Value x -> pure x
    _ -> throwError "Did not pop a value"

pop32 :: (MonadState (WState f) m, MonadError String m) => m (f Word32)
pop32 =
  popV >>= \case
    VI32 x -> pure x
    v -> throwError ("Expected I32, got " ++ show (getValueType v))

cast :: MonadError String m => ValueType -> VNum f -> m (VNum f)
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

makeDefault :: Symb f => ValueType -> VNum f
makeDefault vt =
  case vt of
    I32 -> VI32 (inject 0)
    I64 -> VI64 (inject 0)
    F32 -> VF32 (inject 0)
    F64 -> VF64 (inject 0)

storeByte :: (MonadState (WState f) m, MonadError String m) => Word32 -> MemArg -> f Word8 -> m ()
storeByte addr (MemArg off 0) b = wmemory . at (fromIntegral addr + fromIntegral off) ?= b
storeByte _ _ _ = throwError "Alignement unsupported for storing bytes"

loadByte :: (Symb f, MonadState (WState f) m, MonadError String m) => Word32 -> MemArg -> m (f Word8)
loadByte addr (MemArg off 0) = fromMaybe (inject 0) <$> preuse (wmemory . ix (fromIntegral addr + fromIntegral off))
loadByte _ _ = throwError "Alignement unsupported for loading bytes"

toBool :: Symb f => VNum f -> f Bool
toBool v =
  case v of
    VI32 x -> x ./=: inject 0
    VI64 x -> x ./=: inject 0
    VF32 x -> x ./=: inject 0
    VF64 x -> x ./=: inject 0

runBreak :: (MonadState (WState f) m, Num t, Eq t, MonadError String m) => t -> m ()
runBreak n = do
  let popCont cur = do
        v <- pop
        case v of
          Cont ninstr -> if cur == 0 then pure ninstr else popCont (cur - 1)
          Value _ -> popCont cur
          Activation _ _ -> error "popped an activation"
  rv <- popCont n
  wframe . finstrs .= rv

force :: (RMonad f m, MonadError String m) => f Word32 -> m Word32
force x = resolve x >>= maybe (throwError "forcing failed") pure

decodeInstr :: (MonadError String m, MonadState (WState f) m, MonadReader Module m, Symb f, RMonad f m) => Instruction Natural -> m ()
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
    I32Const n -> pushV (VI32 (inject n))
    Block (Inline Nothing) blockbody -> do
      use (wframe . finstrs) >>= push . Cont
      wframe . finstrs .= blockbody
    Loop (Inline Nothing) loopbody -> do
      use (wframe . finstrs) >>= push . Cont . (i :)
      wframe . finstrs .= loopbody
    I32Store8 ma -> do
      vtoStore <- pop32
      addr <- pop32 >>= force
      let toStore = u32tou8 vtoStore
      storeByte addr ma toStore
    I32Load8U ma -> do
      addr <- pop32 >>= force
      loadByte addr ma >>= pushV . VI32 . u8tou32
    IRelOp BS32 opr -> do
      b <- pop32
      a <- pop32
      res <- case opr of
        IEq -> pure $ a .==: b
        INe -> pure $ a ./=: b
        ILeU -> pure $ a .<=: b
        _ -> throwError "Unsupported comparison"
      push $ Value $ VI32 $ oneif res
    If (Inline Nothing) tb fb -> do
      fres <- toBool <$> popV
      res <- resolveBool fres
      use (wframe . finstrs) >>= push . Cont
      wframe . finstrs
        .= if res
          then tb
          else fb
    IBinOp BS32 bop -> do
      b <- pop32
      a <- pop32
      topush <- case bop of
        IMul -> pure $ a .*: b
        IAdd -> pure $ a .+: b
        IXor -> pure $ a .^: b
        IAnd -> pure $ a .&: b
        IOr -> pure $ a .|: b
        ISub -> pure $ a .-: b
        IShrU -> pure $ a .>>: u32tou8 b
        IRotl -> pure $ a `rotl` u32tou8 b
        _ -> throwError ("unsupported binop " ++ show bop)
      pushV (VI32 topush)
    BrIf n -> do
      fbrnch <- toBool <$> popV
      brnch <- resolveBool fbrnch
      when brnch (runBreak n)
    Br n -> runBreak n
    _ -> throwError ("unknown instruction " ++ show i)

interpret :: (MonadError String m, MonadState (WState f) m, MonadReader Module m, Symb f, RMonad f m) => m [VNum f]
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

trivialEvaluate :: (Symb f, RMonad f Identity) => Module -> WState f -> Either String [VNum f]
trivialEvaluate md = evalState (runExceptT (runReaderT interpret md))

mpEvaluate :: (Evaluable f, Symb f, RMonad f (MP f Module (WState f))) => Module -> WState f -> [([f Bool], Either String (WState f, [VNum f]))]
mpEvaluate md ws = evalMP md ws [] interpret