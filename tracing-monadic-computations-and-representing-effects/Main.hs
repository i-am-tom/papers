{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Control.Applicative (WrappedMonad (..))
import Control.Monad ((>=>), ap, liftM, join, replicateM, when)
import Control.Monad.Writer (MonadWriter (..), Writer)
import Data.Functor.Identity (Identity (Identity))
import Data.Kind (Type)
import Prelude hiding (drop, round)
import Test.QuickCheck

----------------------------------------------------------------------
-- 2 Simple Tracing with Free Monads

prop_naturality :: (Monad m, Eq (m y)) => (x -> y) -> m (m x) -> Bool
prop_naturality f x = fmap f (join x) == join (fmap (fmap f) x)

prop_bind_to_join_fmap :: (Monad m, Eq (m z)) => (x -> m y) -> (y -> m z) -> m x -> Bool
prop_bind_to_join_fmap f g x = (x >>= f >>= g) == (join . fmap g . join . fmap f) x

prop_join_fmap_reassociate :: (Monad m, Eq (m z)) => (x -> m y) -> (y -> m z) -> m x -> Bool
prop_join_fmap_reassociate f g x = (join . fmap g . join . fmap f) x
  == (join . join . fmap (fmap g) . fmap f) x

----------------------------------------------------------------------
-- 2.1 Free Monads

type Free :: (Type -> Type) -> Type -> Type
data Free f x = Wrap (f (Free f x)) | Pure x
  deriving stock Functor

deriving stock instance (forall e. Show e => Show (f e), Show x)
  => Show (Free f x)

instance Functor f => Applicative (Free f) where
  (<*>) = ap
  pure = Pure

instance Functor f => Monad (Free f) where
  Pure x >>= f = f x
  Wrap f >>= k = Wrap (fmap (>>= k) f)

class (Monad m, Monad t) => MonadTrans m t | t -> m where
  lift :: m a -> t a
  drop :: t a -> m a

instance (m ~ n, Functor m, Monad m) => MonadTrans m (Free n) where
  lift = Wrap . fmap Pure
  drop = \case
    Pure x -> pure x
    Wrap m -> m >>= drop

-- $> test_maybe
--
-- $> drop test_maybe
test_maybe :: Free Maybe x
test_maybe = do
  lift (Just 2)
  lift (Just 4)

  lift Nothing

-- $> test_writer
--
-- $> drop test_writer
test_writer :: Free (Writer String) String
test_writer = do
  lift (tell "wo")
  lift (tell "rl")
  lift (tell "d!")

  pure "hello"

----------------------------------------------------------------------
-- 3 More Advanced Tracing with Free Structures

-- 3.1 The @MonadTrace@ Class

class Monad m => MonadTrace m where
  mark :: m ()

mind :: (MonadTrans m v, MonadTrace v) => m a -> v a
mind m = lift m >>= \x -> x <$ mark

----------------------------------------------------------------------
-- 3.2 The @Nest@ Monad

type Nest :: (Type -> Type) -> Type -> Type
newtype Nest m x = Nest { unnest :: m (Free m x) }
  deriving stock (Functor)

deriving stock instance (forall e. Show e => Show (f e), Show x)
  => Show (Nest f x)

instance (Monad m) => Applicative (Nest m) where
  (<*>) = ap
  pure = Nest . return . pure

instance Monad m => Monad (Nest m) where
  Nest f >>= k = Nest (f >>= prod . fmap k)
    where
      prod :: Monad m => Free m (Nest m x) -> m (Free m x)
      prod (Pure (Nest m)) = m
      prod (Wrap m) = (pure . Wrap . (>>= prod)) m

instance (m ~ n, Monad m) => MonadTrans m (Nest n) where
  lift = Nest . fmap pure
  drop = unnest >=> revert
    where
      revert = \case
        Pure x -> pure x
        Wrap x -> x >>= revert

instance Monad m => MonadTrace (Nest m) where
  mark = (Nest . pure . Wrap . pure . Pure) ()

-- $> test_trace
test_trace :: Nest [] Int
test_trace = do
  x <- lift [1, 2]
  mark
  
  lift [0 .. x]

----------------------------------------------------------------------
-- 4 Interpreting Traces

----------------------------------------------------------------------
-- 4.1 The Partiality Monad

type Partial :: Type -> Type
data Partial x = Later (Partial x) | Now x

collatz :: Integer -> Bool
collatz 1 = True
collatz x
  | odd x     = collatz (3 * x + 1)
  | otherwise = collatz (x `div` 2)

oneOf :: Integer -> Integer -> Bool
oneOf x y = collatz x || collatz y

collatzN :: Integer -> Nest Identity Bool
collatzN 1 = pure True
collatzN x
  | odd x     = mark *> collatzN (3 * x + 1)
  | otherwise = mark *> collatzN (x `div` 2)

-- $> collatzN 120 \/ collatzN 130
--
-- $> collatzN 0   \/ collatzN 130
--
-- $> collatzN 130 \/ collatzN 0
(\/) :: Nest Identity Bool -> Nest Identity Bool -> Bool
(\/) (Nest (Identity (Pure False))) (Nest (Identity (Pure False))) = False
(\/) (Nest (Identity (Pure True )))  _                             = True
(\/)  _                             (Nest (Identity (Pure True ))) = True
(\/) (Nest (Identity (Wrap m)))      x                             = x \/ Nest m

----------------------------------------------------------------------
-- 4.2 Approximating Computations

type Distr :: Type -> Type
newtype Distr x = Distr { runDistr :: [(x, Double)] }
  deriving stock (Functor, Show)

instance Applicative Distr where
  (<*>) = ap
  pure x = Distr [(x, 1)]

instance Monad Distr where
  xs >>= k = Distr do
    (x, p) <- runDistr xs
    (y, q) <- runDistr (k x)

    pure (y, p * q)

coin :: Distr Int
coin = Distr [(0, 0.5), (1, 0.5)]

third :: Distr Int
third = do
  x <- coin
  y <- coin

  case (x, y) of
    (1, 1) -> pure 0
    (1, 0) -> pure 1
    (0, 1) -> pure 2
    (0, 0) -> third

thirdN :: Nest Distr Int
thirdN = do
  x <- lift coin
  y <- lift coin

  case (x, y) of
    (1, 1) -> pure 0
    (1, 0) -> pure 1
    (0, 1) -> pure 2
    (0, 0) -> mark *> thirdN

-- $> approx 0 thirdN
--
-- $> import qualified Data.Map.Strict as Map
--
-- $> let simplify = Distr . Map.toList . Map.fromListWith (+) . runDistr
--
-- $> simplify (approx 1 thirdN)
--
-- $> simplify (approx 2 thirdN)
approx :: (Functor m, Monad m) => Int -> Nest m x -> m (Maybe x)
approx k = drop . takeN k

takeN :: (Functor m, Monad m) => Int -> Nest m x -> Nest m (Maybe x)
takeN k (Nest x) = Nest (fmap (aux k) x)
  where
    aux 0 (Wrap _) = pure Nothing
    aux k (Wrap m) = Wrap (fmap (aux (k - 1)) m)
    aux _ (Pure x) = pure (Just x)

----------------------------------------------------------------------
-- 4.3 The Prolog @cut@ Operator

call :: Nest [] x -> [x]
call (Nest xs) = aux xs
  where
    aux [] = []
    aux (Pure x : xss) = x : aux xss
    aux (Wrap ys : _) = aux ys

brace :: Nest [] x -> Nest [] x
brace = lift . call

cut :: Nest [] ()
cut = mark

-- $> cut_list
cut_list :: [Int]
cut_list = call do
  x <- lift [4, 7, 13, 9]

  brace do
    y <- lift [2, 8, 1]

    when (x + y >= 15) cut
    pure (x + y)

----------------------------------------------------------------------
-- 4.4 Poor Man's Concurrency Transformer, Revisited

type Action :: (Type -> Type) -> Type -> Type
data Action m x
  = Par (Action m x) (Action m x) | Act (m (Action m x)) | Done x | Kill
  deriving stock Functor

instance Functor m => Applicative (Action m) where
  (<*>) = ap
  pure = Done

instance Functor m => Monad (Action m) where
  Par a b >>= f = Par (a >>= f) (b >>= f)
  Act m   >>= f = Act (fmap (>>= f) m)
  Done x  >>= f = f x
  Kill    >>= _ = Kill

type Concurrent :: (Type -> Type) -> Type -> Type
type Concurrent m = Nest (Action m)

instance (s ~ t, Monoid s) => MonadWriter s (Concurrent (Writer t)) where
  tell = act . tell
  listen = error "write better code"
  pass = error "write better code"

done :: Monad m => x -> Concurrent m x
done = lift . Done

kill :: Monad m => Concurrent m x
kill = lift Kill

act :: Monad m => m x -> Concurrent m x
act = lift . Act . fmap Done

par :: Monad m => Concurrent m x -> Concurrent m x -> Concurrent m x
par (Nest x) (Nest y) = Nest (Par (Done (Wrap x)) (Done (Wrap y)))

fork :: Monad m => Concurrent m x -> Concurrent m ()
fork m = par (m *> kill) (act (pure ()))

round :: Monad m => [Nest (Action m) x] -> m [x]
round = \case
  [] -> pure []
  Nest z : zs -> case z of
    Kill          -> round zs
    Done (Pure x) -> round zs >>= \xs -> pure (x : xs)
    Done (Wrap m) -> round (zs ++ [Nest m])
    Act m         -> m >>= \x -> round (Nest x : zs)
    Par x y       -> round ([Nest y] ++ zs ++ [Nest x])

cat :: Concurrent (Writer String) Int
cat = replicateM 5 (tell "cat" *> mark) *> return 1

fish :: Concurrent (Writer String) Int
fish = replicateM 7 (tell "fish" *> mark) *> return 2

-- $> test_parallel
test_parallel :: Writer String [()]
test_parallel = round [par fish cat *> tell "dog"]

-- $> test_parallel_2
test_parallel_2 :: Writer String [Int]
test_parallel_2 = round [fork fish *> cat >>= \x -> x <$ tell "dog"]

-- $> test_parallel_3
test_parallel_3 :: Writer String [Int]
test_parallel_3 = round [fork (replicateM 7 (tell "fish") *> return 2) *> cat >>= \x -> x <$ tell "dog"]

----------------------------------------------------------------------
-- 6 Future Work

type Trace :: Type -> Type -> Type
data Trace s x = TCons s (Trace s x) | Nil x
  deriving stock Functor

instance Applicative (Trace s) where
  pure = Nil
  (<*>) = ap

instance Monad (Trace s) where
  Nil x >>= f = f x
  TCons s xs >>= f = TCons s (xs >>= f)

type States :: Type -> Type -> Type
newtype States s x = States { runStates :: s -> Trace s x }

main :: IO ()
main = pure ()
