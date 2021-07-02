{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module Domain.Symbolic where

import Data.Bits
import Data.Functor.Classes (Show1 (liftShowsPrec))
import Data.Int (Int32)
import Data.Word (Word32, Word8)
import Symb.Expression (Evaluable (..), Symb (..))

data Dir = L | R
  deriving (Eq)

data Symbolic a where
  Add :: (Eq a, Num a) => Symbolic a -> Symbolic a -> Symbolic a
  Sub :: (Eq a, Num a) => Symbolic a -> Symbolic a -> Symbolic a
  Mul :: (Eq a, Num a) => Symbolic a -> Symbolic a -> Symbolic a
  Xor :: Bits a => Symbolic a -> Symbolic a -> Symbolic a
  And :: Bits a => Symbolic a -> Symbolic a -> Symbolic a
  Or :: Bits a => Symbolic a -> Symbolic a -> Symbolic a
  Shift :: Bits a => Dir -> Symbolic a -> Symbolic Word8 -> Symbolic a
  Rot :: Bits a => Dir -> Symbolic a -> Symbolic Word8 -> Symbolic a
  Eq :: (Eq a, Show a) => Symbolic a -> Symbolic a -> Symbolic Bool
  Ne :: (Eq a, Show a) => Symbolic a -> Symbolic a -> Symbolic Bool
  Lte :: (Ord a, Show a) => Symbolic a -> Symbolic a -> Symbolic Bool
  U32tou8 :: Symbolic Word32 -> Symbolic Word8
  U8tou32 :: Symbolic Word8 -> Symbolic Word32
  I32tou32 :: Symbolic Int32 -> Symbolic Word32
  U32toi32 :: Symbolic Word32 -> Symbolic Int32
  Oneif :: Num a => Symbolic Bool -> Symbolic a
  Raw :: a -> Symbolic a
  Sym :: String -> Symbolic Word8

instance Show a => Show (Symbolic a) where
  showsPrec n a = liftShowsPrec showsPrec showList n a

instance Show1 Symbolic where
  liftShowsPrec sp sl p alg =
    case alg of
      Or x y -> showParen (p > 10) $ liftShowsPrec sp sl 10 x . (" | " ++) . liftShowsPrec sp sl 11 y
      Xor x y -> showParen (p > 9) $ liftShowsPrec sp sl 9 x . (" ^ " ++) . liftShowsPrec sp sl 10 y
      And x y -> showParen (p > 8) $ liftShowsPrec sp sl 8 x . (" & " ++) . liftShowsPrec sp sl 9 y
      Eq x y -> showParen (p > 7) $ liftShowsPrec showsPrec showList 7 x . (" == " ++) . liftShowsPrec showsPrec showList 8 y
      Ne x y -> showParen (p > 7) $ liftShowsPrec showsPrec showList 7 x . (" != " ++) . liftShowsPrec showsPrec showList 8 y
      Lte x y -> showParen (p > 6) $ liftShowsPrec showsPrec showList 6 x . (" <= " ++) . liftShowsPrec showsPrec showList 7 y
      Shift L x y -> showParen (p > 5) $ liftShowsPrec sp sl 5 x . (" << " ++) . liftShowsPrec showsPrec showList 6 y
      Shift R x y -> showParen (p > 5) $ liftShowsPrec sp sl 5 x . (" >> " ++) . liftShowsPrec showsPrec showList 6 y
      Rot L x y -> showParen (p > 5) $ liftShowsPrec sp sl 5 x . (" rotl " ++) . liftShowsPrec showsPrec showList 6 y
      Rot R x y -> showParen (p > 5) $ liftShowsPrec sp sl 5 x . (" rotr " ++) . liftShowsPrec showsPrec showList 6 y
      Add x y -> showParen (p > 4) $ liftShowsPrec sp sl 4 x . (" + " ++) . liftShowsPrec sp sl 5 y
      Sub x y -> showParen (p > 4) $ liftShowsPrec sp sl 4 x . (" - " ++) . liftShowsPrec sp sl 5 y
      Mul x y -> showParen (p > 3) $ liftShowsPrec sp sl 3 x . (" * " ++) . liftShowsPrec sp sl 4 y
      U32tou8 v -> ("u8(" ++) . liftShowsPrec showsPrec showList 0 v . (")" ++)
      U8tou32 v -> ("u32(" ++) . liftShowsPrec showsPrec showList 0 v . (")" ++)
      I32tou32 v -> ("unsigned(" ++) . liftShowsPrec showsPrec showList 0 v . (")" ++)
      U32toi32 v -> ("signed(" ++) . liftShowsPrec showsPrec showList 0 v . (")" ++)
      Oneif v -> ("oneif(" ++) . liftShowsPrec showsPrec showList 0 v . (")" ++)
      Raw v -> sp p v
      Sym v -> (v ++)

instance Symb Symbolic where
  inject = Raw
  (.+:) = Add
  (.-:) = Sub
  (.*:) = Mul
  (.^:) = Xor
  (.&:) = And
  (.|:) = Or
  (.>>:) = Shift R
  (.<<:) = Shift L
  rotl = Rot L
  rotr = Rot R
  (.==:) = Eq
  (./=:) = Ne
  (.<=:) = Lte
  u32tou8 = U32tou8
  u8tou32 = U8tou32
  i32tou32 = I32tou32
  u32toi32 = U32toi32
  oneif = Oneif
  sym8 = Sym

instance (Num a, Ord a, Show a) => Num (Symbolic a) where
  (+) = Add
  (*) = Mul
  negate = Mul (-1)
  fromInteger = Raw . fromInteger
  signum x = Oneif (Lte x 0) * 2 - 1
  abs x = signum x * x

instance Evaluable Symbolic where
  seval a = case a of
    Raw x -> Just x
    Add x y -> (+) <$> seval x <*> seval y
    Sub x y -> (-) <$> seval x <*> seval y
    Mul x y -> (*) <$> seval x <*> seval y
    Xor x y -> xor <$> seval x <*> seval y
    And x y -> (.&.) <$> seval x <*> seval y
    Or x y -> (.|.) <$> seval x <*> seval y
    Shift R x y -> shiftR <$> seval x <*> (fromIntegral <$> seval y)
    Shift L x y -> shiftL <$> seval x <*> (fromIntegral <$> seval y)
    Rot R x y -> rotateR <$> seval x <*> (fromIntegral <$> seval y)
    Rot L x y -> rotateL <$> seval x <*> (fromIntegral <$> seval y)
    Eq x y -> (==) <$> seval x <*> seval y
    Ne x y -> (/=) <$> seval x <*> seval y
    Lte x y -> (<=) <$> seval x <*> seval y
    U32tou8 x -> fmap fromIntegral (seval x)
    U8tou32 x -> fmap fromIntegral (seval x)
    I32tou32 x -> fmap fromIntegral (seval x)
    U32toi32 x -> fmap fromIntegral (seval x)
    Oneif y -> fmap (\x -> if x then 1 else 0) (seval y)
    Sym _ -> Nothing

simplify :: Symbolic a -> Symbolic a
simplify e =
  case e of
    Raw x -> Raw x
    Add x y ->
      let x' = simplify x
          y' = simplify y
          r = Add x' y'
       in case (x', y') of
            (Raw 0, _) -> y'
            (_, Raw 0) -> x'
            _ -> maybe r Raw (seval r)
    Sub x y ->
      let r = Sub (simplify x) (simplify y)
       in maybe r Raw (seval r)
    Mul x y ->
      let r = Mul (simplify x) (simplify y)
       in maybe r Raw (seval r)
    Xor x y ->
      let r = Xor (simplify x) (simplify y)
       in maybe r Raw (seval r)
    And x y ->
      let x' = simplify x
          y' = simplify y
          r = And x' y'
       in case (x', y') of
            (Raw v, _) | v == zeroBits -> x'
            _ -> maybe r Raw (seval r)
    Or x y ->
      let r = Or (simplify x) (simplify y)
       in maybe r Raw (seval r)
    Shift d x y ->
      let r = Shift d (simplify x) (simplify y)
       in maybe r Raw (seval r)
    Rot d x y ->
      let r = Rot d (simplify x) (simplify y)
       in maybe r Raw (seval r)
    Eq x y ->
      let x' = simplify x
          y' = simplify y
          r = Eq x' y'
       in case (x', y') of
            (Ne _ _, Raw True) -> x'
            (Ne c1 c2, Raw False) -> simplify (Eq c1 c2)
            (Eq _ _, Raw True) -> x'
            (Eq c1 c2, Raw False) -> simplify (Ne c1 c2)
            _ -> maybe r Raw (seval r)
    Ne x y ->
      let x' = simplify x
          y' = simplify y
          r = Ne x' y'
       in case (x', y') of
            (Oneif cnd, Raw 0) -> simplify (Eq cnd (Raw True))
            _ -> maybe r Raw (seval r)
    Lte x y ->
      let r = Lte (simplify x) (simplify y)
       in maybe r Raw (seval r)
    U32tou8 x ->
      let r = U32tou8 (simplify x)
       in maybe r Raw (seval r)
    U8tou32 x ->
      let r = U8tou32 (simplify x)
       in maybe r Raw (seval r)
    I32tou32 x ->
      let r = I32tou32 (simplify x)
       in maybe r Raw (seval r)
    U32toi32 x ->
      let r = U32toi32 (simplify x)
       in maybe r Raw (seval r)
    Oneif x ->
      let r = Oneif (simplify x)
       in maybe r Raw (seval r)
    Sym _ -> e
