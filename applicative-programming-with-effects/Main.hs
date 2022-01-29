{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Main where

import Control.Monad (ap)
import Data.Bifunctor (bimap)
import Data.Coerce (coerce)
import Data.Function (fix)
import Data.Functor.Foldable (cata)
import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Exts (IsList)
import Prelude hiding ((<$>), (*), Applicative (..), repeat, Monoid, Traversable (..), zipWith)
import Test.QuickCheck ((===), Property)

----------------------------------------------------------------------
-- 1 Introduction

sequenceIO :: [IO x] -> IO [x]
sequenceIO = \case
  [    ] -> return []
  c : cs -> return (:) `ap` c `ap` sequenceIO cs

transpose :: [[x]] -> [[x]]
transpose [        ] = repeat []
transpose (xs : xss) = zipWith (:) xs (transpose xss)

repeat :: x -> [x]
repeat x = x : repeat x

zapp :: [x -> y] -> [x] -> [y]
zapp (f : fs) (x : xs) = f x : zapp fs xs
zapp  _        _       = []

-- https://github.com/i-am-tom/learn-me-a-haskell/blob/master/src/Utils/Lift.hs
zipWith :: ZipWith i k => i -> k
zipWith = zipWith' . repeat

class ZipWith i k | i -> k, k -> i where
  zipWith' :: [i] -> k

instance (k ~ ([x] -> ks), ZipWith xs ks) => ZipWith (x -> xs) k where
  zipWith' fs xs = zipWith' (fs `zapp` xs)

instance {-# INCOHERENT #-} [x] ~ k => ZipWith x k where
  zipWith' = id

type Exp :: Type -> Type
data Exp v = Var v | Val Int | Add (Exp v) (Exp v)

makeBaseFunctor ''Exp

eval :: Ord v => Exp v -> Env v -> Int
eval = flip \γ ->
  cata \case
    VarF   x -> fetch x γ
    ValF   i -> i
    AddF p q -> p + q

eval' :: Ord v => Exp v -> Env v -> Int
eval' = cata \case
  VarF   x -> fetch x
  ValF   i -> k i
  AddF p q -> k (+) `s` p `s` q

----------------------------------------------------------------------
-- 2 The Applicative class

infixl 4 ⊛

class Applicative f where
  pure :: x -> f x
  (⊛) :: f (x -> y) -> f x -> f y

law_identity :: (Applicative f, Eq (f x), Show (f x)) => f x -> Property
law_identity u = (pure id ⊛ u) === u

law_composition :: (Applicative f, Eq (f z), Show (f z)) => f (y -> z) -> f (x -> y) -> f x -> Property
law_composition u v w = (pure (.) ⊛ u ⊛ v ⊛ w) === (u ⊛ (v ⊛ w))

law_homomorphism :: forall f x y. (Applicative f, Eq (f y), Show (f y)) => (x -> y) -> x -> Property
law_homomorphism f x = (pure f ⊛ pure x) === pure @f (f x)

law_interchange :: (Applicative f, Eq (f y), Show (f y)) => f (x -> y) -> x -> Property
law_interchange u x = (u ⊛ pure x) === (pure ($ x) ⊛ u)

(<$>) :: Applicative f => (a -> b) -> f a -> f b
f <$> u = pure f ⊛ u

-- ... and again
applicative :: Lift f i k => i -> k
applicative = lift' . pure

class Applicative f => Lift f i k | i f -> k, k -> f where
  lift' :: f i -> k

instance (k ~ (f i -> ks), Lift f is ks) => Lift f (i -> is) k where
  lift' fs xs = lift' (fs ⊛ xs)

instance {-# INCOHERENT #-} (Applicative f, f i ~ k) => Lift f i k where
  lift' = id

instance Applicative ((->) env) where
  pure x  = \_ -> x             -- K
  ef ⊛ ex = \γ -> (ef γ) (ex γ) -- S

instance Applicative IO where
  pure x  = return x
  fs ⊛ xs = fs >>= \f -> xs >>= \x -> return (f x)

sequenceIO' :: [IO x] -> IO [x]
sequenceIO' = \case
  [    ] -> pure []
  c : cs -> pure (:) ⊛ c ⊛ sequenceIO' cs

eval'' :: Ord v => Exp v -> Env v -> Int
eval'' = cata \case
  VarF x   -> fetch x
  ValF i   -> pure i
  AddF p q -> pure (+) ⊛ p ⊛ q

newtype Ziply x = Ziply { runZiply :: [x] }
  deriving newtype (Eq, Functor, IsList, Ord, Show)

instance Applicative Ziply where
  Ziply fs ⊛ Ziply xs = Ziply (zapp fs xs)
  pure = Ziply . repeat

transpose' :: [[x]] -> [[x]]
transpose' = runZiply . fix go . coerce
  where
    go f = \case
      [      ] -> pure []
      xs : xss -> pure (:) ⊛ xs ⊛ f xss

----------------------------------------------------------------------
-- 3 Traversing data structures

-- dist :: Applicative f => [f x] -> f [x]
-- dist = \case
--   [    ] -> pure []
--   v : vs -> pure (:) ⊛ v ⊛ dist vs

instance Applicative Maybe where
  pure = Just

  Just f ⊛ Just x = Just (f x)
  _      ⊛ _      = Nothing

flakyMap :: (x -> Maybe y) -> [x] -> Maybe [y]
flakyMap f = dist . fmap f

class Traversable t where
  traverse :: Applicative f => (x -> f y) -> t x -> f (t y)

  dist :: Applicative f => t (f x) -> f (t x)
  dist = traverse id

instance Traversable [] where
  traverse f = \case
    [    ] -> pure []
    x : xs -> pure (:) ⊛ f x ⊛ traverse f xs

newtype Id a = An { an :: a }

instance Applicative Id where
  pure        = An
  An f ⊛ An x = An (f x)

fmap' :: Traversable t => (a -> b) -> t a -> t b
fmap' f = an . traverse (An . f)

data Tree a = Leaf | Node (Tree a) a (Tree a)

instance Traversable Tree where
  traverse f = \case
    Leaf       -> pure Leaf
    Node l x r -> pure Node ⊛ traverse f l ⊛ f x ⊛ traverse f r

----------------------------------------------------------------------
-- 4 Monoids are phantom Applicative functors

class Monoid o where
  ø   :: o
  (⊕) :: o -> o -> o

instance Monoid [x] where
  ø = []
  (⊕) = (++)

newtype Accy o a = Acc { acc :: o }

instance Monoid o => Applicative (Accy o) where
  pure _          = Acc ø
  Acc o1 ⊛ Acc o2 = Acc (o1 ⊕ o2)

accumulate :: (Traversable t, Monoid o) => (a -> o) -> t a -> o
accumulate f = acc . traverse (Acc . f)

reduce :: (Traversable t, Monoid o) => t o -> o
reduce = accumulate id

flatten :: Tree a -> [a]
flatten = accumulate (: [])

concat :: [[x]] -> [x]
concat = reduce

newtype Mighty = Might { might :: Bool }

instance Monoid Mighty where
  ø = Might False
  Might x ⊕ Might y = Might (x || y)

any :: Traversable t => (x -> Bool) -> t x -> Bool
any p = might . accumulate (Might . p)

----------------------------------------------------------------------
-- 5 Applicative versus Monad

miffy :: Monad m => m Bool -> m x -> m x -> m x
miffy mb mt me = mb >>= \b -> if b then mt else me

iffy :: Applicative f => f Bool -> f x -> f x -> f x
iffy fb ft fe = pure cond ⊛ fb ⊛ ft ⊛ fe
  where cond b t e = if b then t else e

newtype (f ∘ g) x = Comp { comp :: f (g x) }

instance (Applicative f, Applicative g) => Applicative (f ∘ g) where
  pure x = Comp (pure (pure x))
  Comp fs ⊛ Comp xs = Comp (pure (⊛) ⊛ fs ⊛ xs)

data Except e x = OK x | Failed e

instance Monoid e => Applicative (Except e) where
  pure = OK

  OK f     ⊛ OK x     = OK (f x)
  Failed x ⊛ Failed y = Failed (x ⊕ y)
  _        ⊛ Failed y = Failed      y
  Failed x ⊛ _        = Failed  x

----------------------------------------------------------------------
-- 6 Applicative functors and Arrows

class Arrow p where
  arr :: (a -> b) -> p a b
  (>>>) :: p a b -> p b c -> p a c
  first :: p a b -> p (a, c) (b, c)

instance Arrow (->) where
  arr = id
  f >>> g = g . f
  first f = \(a, c) -> (f a, c)

newtype Kleisli f a b = Kleisli (a -> f b)

instance Monad f => Arrow (Kleisli f) where
  arr f = Kleisli (return . f)
  Kleisli f >>> Kleisli g = Kleisli \x -> f x >>= g
  first (Kleisli f) = Kleisli \(a, c) -> f a >>= \b -> return (b, c)

newtype EnvArrow p env a = Env (p env a)

instance Arrow p => Applicative (EnvArrow p env) where
  pure x = Env $ arr \_ -> x
  Env u ⊛ Env v = Env (u ∆ v >>> arr \(f, x) -> f x)
    where
      x ∆ y = arr dup >>> first x >>> arr swap >>> first y >>> arr swap
      dup a = (a, a)
      swap (a, b) = (b, a)

newtype StaticArrow f p a b = Static (f (p a b))

instance (Applicative f, Arrow p) => Arrow (StaticArrow f p) where
  arr f = Static (pure (arr f))
  Static f >>> Static g = Static (pure (>>>) ⊛ f ⊛ g)
  first (Static f) = Static (pure first ⊛ f)

----------------------------------------------------------------------
-- 7 Applicative functors, categorically

class Functor f => Monoidal f where
  unit :: f ()
  (*) :: f x -> f y -> f (x, y)

  default unit :: Applicative f => f ()
  unit = pure ()

  default (*) :: Applicative f => f x -> f y -> f (x, y)
  fa * fb = pure (,) ⊛ fa ⊛ fb

law_naturality :: (Eq (f (x, y)), Show (f (x, y)), Monoidal f) => (a -> x) -> (b -> y) -> f a -> f b -> Property
law_naturality f g u v = fmap (bimap f g) (u * v) === fmap f u * fmap g v

law_left_identity :: (Eq (f x), Show (f x), Monoidal f) => f x -> Property
law_left_identity v = fmap snd (unit * v) === v

law_right_identity :: (Eq (f y), Show (f y), Monoidal f) => f y -> Property
law_right_identity u = fmap fst (u * unit) === u

law_associativity :: (Eq (f ((x, y), z)), Show (f ((x, y), z)), Monoidal f) => f x -> f y -> f z -> Property
law_associativity u v w = fmap assoc (u * (v * w)) === (u * v) * w
  where assoc (a, (b, c)) = ((a, b), c)

----------------------------------------------------------------------
-- Appendix

type Env :: Type -> Type
type Env v = Map v Int

fetch :: Ord v => v -> Env v -> Int
fetch v xs = xs Map.! v

k :: x -> env -> x
k x _ = x

s :: (env -> x -> y) -> (env -> x) -> (env -> y)
s ef es γ = (ef γ) (es γ)
