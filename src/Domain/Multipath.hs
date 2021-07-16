{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Domain.Multipath where

import Control.Monad.Error.Class
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import Symb.Expression
import Data.SBV

data MP (f :: * -> *) r s a where
  -- Functor interface
  Fmap :: (a -> b) -> MP f r s a -> MP f r s b
  -- Applicative interface
  Pure :: a -> MP f r s a
  -- Monad interface
  Bind :: MP f r s a -> (a -> MP f r s b) -> MP f r s b
  -- MonadError String
  Throw :: String -> MP f r s a
  Catch :: MP f r s a -> (String -> MP f r s a) -> MP f r s a
  -- Reader interface
  Ask :: MP f r s r
  Local :: (r -> r) -> MP f r s a -> MP f r s a
  -- State interface
  Get :: MP f r s s
  Put :: s -> MP f r s ()
  -- Multipath interface
  Multi :: (Enum a, Bounded a, Eq a, Show a, SymVal a) => f a -> MP f r s a

instance Functor (MP f r s) where
  fmap = Fmap

instance Applicative (MP f r s) where
  pure = Pure
  f <*> x = do
    vf <- f
    vf <$> x

instance Monad (MP f r s) where
  (>>=) = Bind

instance MonadReader r (MP f r s) where
  ask = Ask
  local = Local

instance MonadError [Char] (MP f r s) where
  throwError = Throw
  catchError = Catch

instance MonadState s (MP f r s) where
  get = Get
  put = Put

instance Evaluable f => RMonad f (MP f r s) where
  resolveBool a =
    case seval a of
      Nothing -> Multi a
      Just x -> pure x
  resolve = pure . seval

evalMP ::
  (RMonad f (MP f r s), Evaluable f, Symb f) =>
  r ->
  s ->
  [f Bool] ->
  MP f r s a ->
  [([f Bool], Either String (s, a))]
evalMP r s constraints o =
  case o of
    Fmap f sub -> fmap (fmap (fmap f)) <$> evalMP r s constraints sub
    Pure x -> [(constraints, Right (s, x))]
    Bind a f -> do
      (curconstraints, rs) <- evalMP r s constraints a
      case rs of
        Left rr -> pure (curconstraints, Left rr)
        Right (s', a') -> evalMP r s' curconstraints (f a')
    Throw rr -> [(constraints, Left rr)]
    Catch sub handler -> do
      res <- evalMP r s constraints sub
      case res of
        (_, Left rr) -> evalMP r s constraints (handler rr)
        _ -> pure res
    Ask -> [(constraints, Right (s, r))]
    Local f sub -> evalMP (f r) s constraints sub
    Get -> [(constraints, Right (s, s))]
    Put s' -> [(constraints, Right (s', ()))]
    Multi var -> [((var .==: inject a) : constraints, Right (s, a)) | a <- [minBound .. maxBound]]