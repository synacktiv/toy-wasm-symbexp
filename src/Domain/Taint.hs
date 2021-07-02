{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Domain.Taint where

import Control.Monad.Identity (Identity)
import Data.Bits
import Data.Functor.Classes (Eq1 (..), Show1 (liftShowsPrec))
import Data.Maybe (fromMaybe)
import qualified Data.Set as S
import Symb.Expression (RMonad (..), Symb (..))

data Tainted a = Tainted
  { _content :: Maybe a, -- actual value
    _taint :: S.Set String -- set of taints that are applied to this value
  }
  deriving (Show, Eq, Functor)

liftTaint2 :: (a -> b -> c) -> Tainted a -> Tainted b -> Tainted c
liftTaint2 f (Tainted a ta) (Tainted b tb) = Tainted (f <$> a <*> b) (ta <> tb)

instance Symb Tainted where
  inject x = Tainted (Just x) mempty
  (.+:) = liftTaint2 (+)
  (.-:) = liftTaint2 (-)
  (.*:) = liftTaint2 (*)
  (.^:) = liftTaint2 xor
  (.&:) = liftTaint2 (.&.)
  (.|:) = liftTaint2 (.|.)
  (.>>:) = liftTaint2 (\l r -> shiftR l (fromIntegral r))
  (.<<:) = liftTaint2 (\l r -> shiftL l (fromIntegral r))
  rotl = liftTaint2 (\l r -> rotateL l (fromIntegral r))
  rotr = liftTaint2 (\l r -> rotateR l (fromIntegral r))
  (.==:) = liftTaint2 (==)
  (./=:) = liftTaint2 (/=)
  (.<=:) = liftTaint2 (<=)
  u32tou8 = fmap fromIntegral
  u8tou32 = fmap fromIntegral
  i32tou32 = fmap fromIntegral
  u32toi32 = fmap fromIntegral
  oneif = fmap (\b -> if b then 1 else 0)
  sym8 nm = Tainted Nothing (S.singleton nm)

instance RMonad Tainted Identity where
  resolveBool = pure . fromMaybe (error "could not resolve boolean") . _content
  resolve = pure . _content

instance Show1 Tainted where
  liftShowsPrec sp _ n (Tainted cnt tnt) = maybe ("?" ++) (sp n) cnt . if null tnt then id else showList (S.toList tnt)

instance Eq1 Tainted where
  liftEq subeq (Tainted c1 t1) (Tainted c2 t2) = mc && t1 == t2
    where
      mc = case (c1, c2) of
        (Nothing, Nothing) -> True
        (Just s1, Just s2) -> subeq s1 s2
        _ -> False