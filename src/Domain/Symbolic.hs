{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Domain.Symbolic where

import Data.Bits
import Data.Functor.Classes (Show1 (liftShowsPrec))
import Data.Int (Int32)
import qualified Data.Map.Strict as M
import Data.SBV (SymVal)
import Data.Word (Word32, Word8)
import Hedgehog (MonadGen)
import Hedgehog.Gen (bool_, choice, element, enumBounded, recursive, subterm2, word32, word8)
import Hedgehog.Range (constantBounded)
import Symb.Expression (Evaluable (..), Symb (..))

data Dir = L | R
  deriving (Eq, Enum, Bounded)

-- | this is a direct encoding of the Symb typeclass, it does not contain
-- anything interesting, really
data Symbolic a where
  Add :: (Eq a, Num a, SymVal a) => Symbolic a -> Symbolic a -> Symbolic a
  Sub :: (Eq a, Num a, SymVal a) => Symbolic a -> Symbolic a -> Symbolic a
  Mul :: (Eq a, Num a, SymVal a) => Symbolic a -> Symbolic a -> Symbolic a
  Xor :: (Bits a, SymVal a) => Symbolic a -> Symbolic a -> Symbolic a
  And :: (Bits a, SymVal a) => Symbolic a -> Symbolic a -> Symbolic a
  Or :: (Bits a, SymVal a) => Symbolic a -> Symbolic a -> Symbolic a
  Shift :: (Bits a, SymVal a) => Dir -> Symbolic a -> Symbolic Word8 -> Symbolic a
  Rot :: (Bits a, SymVal a) => Dir -> Symbolic a -> Symbolic Word8 -> Symbolic a
  Eq :: (Eq a, Show a, SymVal a) => Symbolic a -> Symbolic a -> Symbolic Bool
  Ne :: (Eq a, Show a, SymVal a) => Symbolic a -> Symbolic a -> Symbolic Bool
  Lte :: (Ord a, Show a, SymVal a) => Symbolic a -> Symbolic a -> Symbolic Bool
  U32tou8 :: Symbolic Word32 -> Symbolic Word8
  U8tou32 :: Symbolic Word8 -> Symbolic Word32
  I32tou32 :: Symbolic Int32 -> Symbolic Word32
  U32toi32 :: Symbolic Word32 -> Symbolic Int32
  Oneif :: (Num a, SymVal a) => Symbolic Bool -> Symbolic a
  Raw :: a -> Symbolic a
  Sym :: String -> Symbolic Word8

-- | debug show, useful when something goes wrong and you want to copy paste
-- an expression in the REPL
--
-- completing is left as an exercise to the reader :)
dshow :: Show a => Symbolic a -> String
dshow s =
  case s of
    Or a b -> "Or (" ++ dshow a ++ ") (" ++ dshow b ++ ")"
    Eq a b -> "Eq (" ++ dshow a ++ ") (" ++ dshow b ++ ")"
    Ne a b -> "Ne (" ++ dshow a ++ ") (" ++ dshow b ++ ")"
    Sub a b -> "Sub (" ++ dshow a ++ ") (" ++ dshow b ++ ")"
    Oneif x -> "Oneif (" ++ dshow x ++ ")"
    Raw x -> "Raw " ++ show x
    U8tou32 x -> "U8tou32 (" ++ dshow x ++ ")"
    Sym v -> "Sym " ++ show v
    Shift L a b -> "Shift L (" ++ dshow a ++ ") (" ++ dshow b ++ ")"
    _ -> show s

instance Show a => Show (Symbolic a) where
  showsPrec n a = liftShowsPrec showsPrec showList n a

-- | A pretty printer that understands operator precedence
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

-- | as Symbolic is a direct encoding of Symb, writing the instance is trivial ...
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

-- | A Num instance makes things useful in the repl :)
instance (Num a, Ord a, Show a, SymVal a) => Num (Symbolic a) where
  (+) = Add
  (*) = Mul
  negate = Mul (-1)
  fromInteger = Raw . fromInteger
  signum x = Oneif (Lte x 0) * 2 - 1
  abs x = signum x * x

instance Evaluable Symbolic where
  seval = veval mempty

-- | evaluate with a map containing the variable values
veval :: M.Map String Word8 -> Symbolic a -> Maybe a
veval vars = go
  where
    go :: Symbolic a -> Maybe a
    go a = case a of
      Raw x -> Just x
      Add x y -> (+) <$> go x <*> go y
      Sub x y -> (-) <$> go x <*> go y
      Mul x y -> (*) <$> go x <*> go y
      Xor x y -> xor <$> go x <*> go y
      And x y -> (.&.) <$> go x <*> go y
      Or x y -> (.|.) <$> go x <*> go y
      Shift R x y -> shiftR <$> go x <*> (fromIntegral <$> go y)
      Shift L x y -> shiftL <$> go x <*> (fromIntegral <$> go y)
      Rot R x y -> rotateR <$> go x <*> (fromIntegral <$> go y)
      Rot L x y -> rotateL <$> go x <*> (fromIntegral <$> go y)
      Eq x y -> (==) <$> go x <*> go y
      Ne x y -> (/=) <$> go x <*> go y
      Lte x y -> (<=) <$> go x <*> go y
      U32tou8 x -> fmap fromIntegral (go x)
      U8tou32 x -> fmap fromIntegral (go x)
      I32tou32 x -> fmap fromIntegral (go x)
      U32toi32 x -> fmap fromIntegral (go x)
      Oneif y -> fmap (\x -> if x then 1 else 0) (go y)
      Sym varname -> M.lookup varname vars

-- | simplify an expression, not knowing any variable values
simplify :: Show a => Symbolic a -> Symbolic a
simplify = vsimplify mempty

-- | simplify an expression, knowing some variable values
vsimplify :: Show a => M.Map String Word8 -> Symbolic a -> Symbolic a
vsimplify vars = go
  where
    go :: Show a => Symbolic a -> Symbolic a
    go e = case e of
      Raw x -> Raw x
      Add x y ->
        let x' = go x
            y' = go y
            r = Add x' y'
         in case (x', y') of
              (Raw 0, _) -> y'
              (_, Raw 0) -> x'
              _ -> maybe r Raw (veval vars r)
      Sub x y ->
        let r = Sub (go x) (go y)
         in maybe r Raw (veval vars r)
      Mul x y ->
        let r = Mul (go x) (go y)
         in maybe r Raw (veval vars r)
      Xor x y ->
        let r = Xor (go x) (go y)
         in maybe r Raw (veval vars r)
      And x y ->
        let x' = go x
            y' = go y
            r = And x' y'
         in case (x', y') of
              (Raw v, _) | v == zeroBits -> x'
              _ -> maybe r Raw (veval vars r)
      Or x y ->
        let r = Or (go x) (go y)
         in maybe r Raw (veval vars r)
      Shift d x y ->
        let r = Shift d (go x) (go y)
         in maybe r Raw (veval vars r)
      Rot d x y ->
        let r = Rot d (go x) (go y)
         in maybe r Raw (veval vars r)
      Eq x y ->
        let x' = go x
            y' = go y
            r = Eq x' y'
         in case (x', y') of
              (Mul v (Raw 2), Raw 2) -> go (Eq v (Raw 1))
              (U8tou32 v, Raw k) -> go (Eq v (Raw (fromIntegral k)))
              (Ne _ _, Raw True) -> x'
              (Ne c1 c2, Raw False) -> go (Eq c1 c2)
              (Eq _ _, Raw True) -> x'
              (Eq c1 c2, Raw False) -> go (Ne c1 c2)
              (Oneif (Eq a b), Raw 0) -> go (Ne a b)
              (Oneif (Eq a b), Raw 1) -> go (Eq a b)
              (Oneif (Ne a b), Raw 0) -> go (Eq a b)
              (Oneif (Ne a b), Raw 1) -> go (Ne a b)
              (Sub a b, c) -> go (Eq a (Add b c))
              (Or (Oneif c1) (Oneif c2), Raw 1) -> Or c1 c2
              (Oneif _, Raw z) | z /= 0 && z /= 1 -> Raw False
              (Or a@(Eq _ _) b, Raw False) -> go (And (Eq a (Raw False)) (Eq b (Raw False)))
              _ -> maybe r Raw (veval vars r)
      Ne x y ->
        let x' = go x
            y' = go y
            r = Ne x' y'
         in case (x', y') of
              (Oneif cnd, Raw 0) -> go (Eq cnd (Raw True))
              (Or (Oneif c1) (Oneif c2), Raw 0) -> go (Or c1 c2)
              _ -> maybe r Raw (veval vars r)
      Lte x y ->
        let r = Lte (go x) (go y)
         in maybe r Raw (veval vars r)
      U32tou8 x ->
        let r = U32tou8 (go x)
         in maybe r Raw (veval vars r)
      U8tou32 x ->
        let r = U8tou32 (go x)
         in maybe r Raw (veval vars r)
      I32tou32 x ->
        let r = I32tou32 (go x)
         in maybe r Raw (veval vars r)
      U32toi32 x ->
        let r = U32toi32 (go x)
         in maybe r Raw (veval vars r)
      Oneif x ->
        let r = Oneif (go x)
         in maybe r Raw (veval vars r)
      Sym n -> maybe e Raw (M.lookup n vars)

-- for testing purpose

genvarnames :: [String]
genvarnames = map pure ['a' .. 'f']

genvars :: MonadGen m => m (M.Map String Word8)
genvars = M.fromList <$> traverse (\vn -> (vn,) <$> word8 constantBounded) genvarnames

genword8 :: MonadGen m => m (Symbolic Word8)
genword8 = choice [Raw <$> word8 constantBounded, Sym <$> element genvarnames]

genword32 :: MonadGen m => m (Symbolic Word32)
genword32 =
  recursive
    choice
    [Raw <$> word32 constantBounded]
    [ subterm2 genword32 genword32 Add,
      subterm2 genword32 genword32 Sub,
      subterm2 genword32 genword32 Mul,
      subterm2 genword32 genword32 Xor,
      subterm2 genword32 genword32 And,
      subterm2 genword32 genword32 Or,
      Shift <$> enumBounded <*> genword32 <*> genword8,
      Rot <$> enumBounded <*> genword32 <*> genword8,
      Oneif <$> genbool
    ]

genbool :: MonadGen m => m (Symbolic Bool)
genbool =
  recursive
    choice
    [Raw <$> bool_]
    [ Eq <$> genword32 <*> genword32,
      Ne <$> genword32 <*> genword32,
      Lte <$> genword32 <*> genword32,
      subterm2 genbool genbool Eq,
      subterm2 genbool genbool Ne,
      subterm2 genbool genbool Or,
      subterm2 genbool genbool And
    ]