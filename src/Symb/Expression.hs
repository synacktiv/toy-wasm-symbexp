{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Symb.Expression where

import Control.Lens (Identity (runIdentity))
import Control.Monad.List
import Data.Bits
import Data.Int
import Data.Word

class Symb f where
  inject :: a -> f a
  (.+:) :: (Ord a, Num a) => f a -> f a -> f a
  (.-:) :: (Ord a, Num a) => f a -> f a -> f a
  (.*:) :: (Ord a, Num a) => f a -> f a -> f a
  (.^:) :: (Ord a, Num a, Bits a) => f a -> f a -> f a
  (.&:) :: (Ord a, Num a, Bits a) => f a -> f a -> f a
  (.|:) :: (Ord a, Num a, Bits a) => f a -> f a -> f a
  (.>>:) :: Bits a => f a -> f Word8 -> f a
  (.<<:) :: Bits a => f a -> f Word8 -> f a
  rotl :: Bits a => f a -> f Word8 -> f a
  rotr :: Bits a => f a -> f Word8 -> f a
  (.==:) :: Eq a => f a -> f a -> f Bool
  (./=:) :: Eq a => f a -> f a -> f Bool
  (.<=:) :: Ord a => f a -> f a -> f Bool
  u32tou8 :: f Word32 -> f Word8
  u8tou32 :: f Word8 -> f Word32
  i32tou32 :: f Int32 -> f Word32
  u32toi32 :: f Word32 -> f Int32
  oneif :: (Ord a, Num a) => f Bool -> f a

instance Symb Identity where
  inject = pure
  (.+:) = liftM2 (+)
  (.-:) = liftM2 (-)
  (.*:) = liftM2 (*)
  (.^:) = liftM2 xor
  (.&:) = liftM2 (.&.)
  (.|:) = liftM2 (.|.)
  a .>>: b = shiftR <$> a <*> (fromIntegral <$> b)
  a .<<: b = shiftL <$> a <*> (fromIntegral <$> b)
  (.==:) = liftM2 (==)
  (./=:) = liftM2 (/=)
  (.<=:) = liftM2 (<=)
  u32tou8 = fmap fromIntegral
  u8tou32 = fmap fromIntegral
  i32tou32 = fmap fromIntegral
  u32toi32 = fmap fromIntegral
  oneif = fmap (\x -> if x then 1 else 0)
  rotl = liftM2 (\a b -> a `rotateL` fromIntegral b)
  rotr = liftM2 (\a b -> a `rotateR` fromIntegral b)

class RMonad f m where
  -- | resolve a boolean value
  resolveBool :: f Bool -> m Bool

  -- | tentatively resolve an arbitrary value
  resolve :: f a -> m (Maybe a)

instance RMonad Identity Identity where
  resolveBool = pure . runIdentity
  resolve = pure . pure . runIdentity

instance (MonadTrans t, RMonad f m, Monad (t m), Monad m) => RMonad f (t m) where
  resolveBool = lift . resolveBool
  resolve = lift . resolve