{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Main where

import Control.Applicative (WrappedMonad (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Constraint, Type)
import Data.Void (Void, absurd)
import Prelude hiding (Maybe (..))
import GHC.Exts (unsafeCoerce#)

----------------------------------------------------------------------
-- 1. Introduction

data Expr' = Val' Int | Add' Expr' Expr'

type Stack' :: Type
type Stack' = [Either Expr' Int]

eval' :: Expr' -> Int
eval' e = load' e []

load' :: Expr' -> Stack' -> Int
load' (Val'   i) s = unload' i s
load' (Add' x y) s = load' x (Left y : s)

unload' :: Int -> Stack' -> Int
unload' x = \case
  [         ] -> x
  Left  e : s -> load' e (Right x : s)
  Right v : s -> unload' (x + v) s

-- eval (1 + (2 + 3))
--   = load  (1 + (2 + 3)) []
--   = load   1            [L (2 + 3)]
--   = unload 1            [L (2 + 3)]
--   = load  (2 + 3)       [R 1]
--   = load   2            [L 3, R 1]
--   = unload 2            [L 3, R 1]
--   = load   3            [R 2, R 1]
--   = unload 3            [R 2, R 1]
--   = unload 5            [R 1]
--   = unload 6            []

----------------------------------------------------------------------
-- 2. Polynomial Functor and Bifunctors

newtype I x = I x
  deriving stock (Eq, Functor)
  deriving newtype (Show)

newtype instance K a x = K₁ a
  deriving stock (Eq, Functor)
  deriving newtype (Show)

data instance (p + q) x = L₁ (p x) | R₁ (q x)
  deriving stock (Eq, Functor, Show)

data instance (p × q) x = T₁ (p x) (q x)
  deriving stock (Eq, Functor, Show)

infixl 6 +
infixl 7 ×

type Maybe :: Type -> Type
type Maybe = U + I

instance Applicative Maybe where
  pure = Just

  Just f <*> Just x = Just (f x)
  _      <*> _      = Nothing

instance Monad Maybe where
  Nothing >>= _ = Nothing
  Just xs >>= f = f xs

pattern Nothing :: Maybe x
pattern Nothing = L₁ (K₁ ())

pattern Just :: x -> Maybe x
pattern Just x = R₁ (I x)
{-# COMPLETE Nothing, Just #-}

type ExprP :: Type -> Type
type ExprP = K Int + I × I

pattern ValP :: Int -> ExprP x
pattern ValP x = L₁ (K₁ x)

pattern AddP :: x -> x -> ExprP x
pattern AddP x y = R₁ (T₁ (I x) (I y))
{-# COMPLETE ValP, AddP #-}

type Μ :: (Type -> Type) -> Type
data Μ f = In (f (Μ f))

instance (forall x. Show x => Show (f x)) => Show (Μ f) where
  show (In xs) = show xs

type Expr :: Type
type Expr = Μ ExprP

pattern Val :: Int -> Expr
pattern Val x = In (ValP x)

pattern Add :: Expr -> Expr -> Expr
pattern Add x y = In (AddP x y)
{-# COMPLETE Val, Add #-}

-- Hey, they're back!
cata :: Functor f => (f x -> x) -> Μ f -> x
cata φ (In p) = φ (fmap (cata φ) p)

eval'' :: Expr -> Int
eval'' = cata \case
  ValP i   -> i
  AddP x y -> x + y

data instance K a x y = K₂ a  deriving stock (Eq, Functor, Show)
data          Fst x y = Fst x deriving stock (Eq, Functor, Show)
data          Snd x y = Snd y deriving stock (Eq, Functor, Show)

data instance (p + q) x y = L₂ (p x y) | R₂ (q x y) deriving stock (Eq, Functor, Show)
data instance (p × q) x y = T₂ (p x y)      (q x y) deriving stock (Eq, Functor, Show)

instance Bifunctor (K x) where
  bimap _ _ (K₂ x) = K₂ x

instance Bifunctor Fst where
  bimap f _ (Fst x) = Fst (f x)

instance Bifunctor Snd where
  bimap _ g (Snd y) = Snd (g y)

instance (Bifunctor p, Bifunctor q) => Bifunctor (p + q) where
  bimap f g (L₂ p) = L₂ (bimap f g p)
  bimap f g (R₂ p) = R₂ (bimap f g p)

instance (Bifunctor p, Bifunctor q) => Bifunctor (p × q) where
  bimap f g (T₂ x y) = T₂ (bimap f g x) (bimap f g y)

inflate :: Functor f => f Z -> f x
inflate = unsafeCoerce# -- Forgive me, Padre
-- inflate = fmap absurd

----------------------------------------------------------------------
-- 3. Clowns, Jokers and Dissection

type Clown :: (Type -> Type) -> Type -> Type -> Type
data Clown f c j = Clown (f c)
  deriving stock (Eq, Functor, Show)

instance Functor f => Bifunctor (Clown f) where
  bimap f _ (Clown fc) = Clown (fmap f fc)

type Joker :: (Type -> Type) -> Type -> Type -> Type
data Joker f c j = Joker (f j)
  deriving stock (Eq, Functor, Show)

instance Functor f => Bifunctor (Joker f) where
  bimap _ g (Joker fj) = Joker (fmap g fj)

class (Functor f, Bifunctor (Δ f)) => Dissection f where
  type Δ f :: Type -> Type -> Type

  left  :: f c + (Δ f c j, j) -> (c, Δ f c j) + f j
  right :: f j + (Δ f c j, c) -> (j, Δ f c j) + f c
  plug  :: x -> Δ f x x -> f x

instance Dissection (K x) where
  type instance Δ (K x) = Z

  left :: K x c + (Z c j, j) -> (c, Z c j) + K x j
  left = \case
    L₀ (K₁    x) -> R₀ (K₁ x)
    R₀ (K₂ v, _) -> absurd v

  right :: K x j + (Z c j, c) -> (j, Z c j) + K x c
  right = \case
    L₀ (K₁    x) -> R₀ (K₁ x)
    R₀ (K₂ v, _) -> absurd v

  plug :: y -> Z y y -> K x y
  plug _ (K₂ void) = absurd void

instance Dissection I where
  type instance Δ I = U

  left :: I c + (U c j, j) -> (c, U c j) + I j
  left = \case
    L₀ (I  x) -> L₀ (x, K₂ ())
    R₀ (_, y) -> R₀ (I y)

  right :: I j + (U c j, c) -> (j, U c j) + I c
  right = \case
    L₀ (I  x) -> L₀ (x, K₂ ())
    R₀ (_, y) -> R₀ (I y)

  plug :: x -> U x x -> I x
  plug x _ = I x

instance (Dissection p, Dissection q) => Dissection (p + q) where
  type instance Δ (p + q) = Δ p + Δ q

  left :: (p + q) c + ((Δ p + Δ q) c j, j) -> (c, (Δ p + Δ q) c j) + (p + q) j
  left = \case
      L₀ (L₁ pc)    -> mindp (left (L₀  pc))
      L₀ (R₁ qc)    -> mindq (left (L₀  qc))
      R₀ (L₂ pd, j) -> mindp (left (R₀ (pd, j)))
      R₀ (R₂ qd, j) -> mindq (left (R₀ (qd, j)))
    where
      mindp :: (c, Δ p c j) + p j -> (c, (Δ p + Δ q) c j) + (p + q) j
      mindp = \case
        L₀ (j, pd) -> L₀ (j, L₂ pd)
        R₀     pc  -> R₀    (L₁ pc)

      mindq :: (c, Δ q c j) + q j -> (c, (Δ p + Δ q) c j) + (p + q) j
      mindq = \case
        L₀ (j, qd) -> L₀ (j, R₂ qd)
        R₀     qc  -> R₀    (R₁ qc)

  right :: (p + q) j + (Δ (p + q) c j, c) -> (j, Δ (p + q) c j) + (p + q) c
  right = \case
      L₀ (L₁ pj)    -> mindp (right (L₀  pj))
      L₀ (R₁ qj)    -> mindq (right (L₀  qj))
      R₀ (L₂ pd, c) -> mindp (right (R₀ (pd, c)))
      R₀ (R₂ qd, c) -> mindq (right (R₀ (qd, c)))
    where
      mindp :: (j, Δ p c j) + p c -> (j, Δ (p + q) c j) + (p + q) c
      mindp = \case
        L₀ (j, pd) -> L₀ (j, L₂ pd)
        R₀     pc  -> R₀    (L₁ pc)

      mindq :: (j, Δ q c j) + q c -> (j, Δ (p + q) c j) + (p + q) c
      mindq = \case
        L₀ (j, qd) -> L₀ (j, R₂ qd)
        R₀     qc  -> R₀    (R₁ qc)

  plug :: x -> (Δ p + Δ q) x x -> (p + q) x
  plug x = \case
    L₂ pd -> L₁ (plug x pd)
    R₂ qd -> R₁ (plug x qd)

instance (Dissection p, Dissection q) => Dissection (p × q) where
  type instance Δ (p × q) = Δ p × Joker q + Clown p × Δ q

  left = \case
      L₀ (T₁ pc qc) -> mindq pc (left (L₀ qc))
      R₀ (L₂ (T₂ pd (Joker qj)), j) -> mindp qj (left (R₀ (pd, j)))
      R₀ (R₂ (T₂ (Clown pc) qd), j) -> mindq pc (left (R₀ (qd, j)))
    where
      mindp :: q j -> (c, Δ p c j) + p j -> (c, Δ (p × q) c j) + (p × q) j
      mindp qj = \case
        L₀ (c, pd) -> L₀ (c, L₂ (T₂ pd (Joker qj)))
        R₀     pj  -> R₀ (T₁ pj qj)

      mindq :: p c -> (c, Δ q c j) + q j -> (c, Δ (p × q) c j) + (p × q) j
      mindq pc = \case
        L₀ (c, qd) -> L₀ (c, R₂ (T₂ (Clown pc) qd))
        R₀     qj  -> mindp qj (left (L₀ pc))

  right = \case
      L₀ (T₁ pj qj) -> mindp qj (right (L₀ pj))
      R₀ (L₂ (T₂ pd (Joker qj)), c) -> mindp qj (right (R₀ (pd, c)))
      R₀ (R₂ (T₂ (Clown pc) qd), c) -> mindq pc (right (R₀ (qd, c)))
    where
      mindp :: q j -> (j, Δ p c j) + p c -> (j, Δ (p × q) c j) + (p × q) c
      mindp qj = \case
        L₀ (j, pd) -> L₀ (j, L₂ (T₂ pd (Joker qj)))
        R₀     pc  -> mindq pc (right (L₀ qj))

      mindq :: p c -> (j, Δ q c j) + q c -> (j, Δ (p × q) c j) + (p × q) c
      mindq pc = \case
        L₀ (j, qd) -> L₀ (j, R₂ (T₂ (Clown pc) qd))
        R₀     qc  -> R₀ (T₁ pc qc)

  plug x = \case
    L₂ (T₂ pd (Joker qx)) -> T₁ (plug x pd) qx
    R₂ (T₂ (Clown px) qd) -> T₁ px (plug x qd)

-- Δ (K Int + I × I) Int Expr
--   = (Δ (K Int) + Δ (I × I)) Int Expr
--   = (Δ (K Int) + Δ I × Joker I + Clown I × Δ I) Int Expr
--   = (Z + Δ I × Joker I + Clown I × Δ I) Int Expr
--   = (Z + U × Joker I + Clown I × U) Int Expr
--   = (Z + Joker I + Clown I × U) Int Expr
--   = (Z + Joker I + Clown I) Int Expr
--   = (Joker I + Clown I) Int Expr
--   = (Joker I Int + Clown I Int) Expr
--   = Joker I Int Expr + Clown I Int Expr
--   = I Expr + I Int
--   = Expr + Int

-- $> tmap (+ 1) (Just 2)
tmap :: Dissection f => (x -> y) -> f x -> f y
tmap f xs = go (right (L₀ xs))
  where
    go = \case
      L₀ (x, xss) -> go (right (R₀ (xss, f x)))
      R₀     ys   -> ys

----------------------------------------------------------------------
-- 4. How to Creep Gradually to the Right

type Stack :: (Type -> Type) -> Type -> Type
type Stack f x = [Δ f x (Μ f)]

tcata :: Dissection f => (f x -> x) -> Μ f -> x
tcata φ expr = load φ expr []

load :: Dissection f => (f x -> x) -> Μ f -> [Δ f x (Μ f)] -> x
load φ (In xs) stack = next φ stack (right (L₀ xs))

next :: Dissection f => (f x -> x) -> [Δ f x (Μ f)] -> (Μ f, Δ f x (Μ f)) + f x -> x
next φ stack = \case
  L₀ (x, more) -> load φ x (more : stack)
  R₀     done  -> unload φ (φ done) stack

unload :: Dissection f => (f x -> x) -> x -> [Δ f x (Μ f)] -> x
unload φ x = \case
  piece : stack -> next φ stack (right (R₀ (piece, x)))
  [           ] -> x

eval :: Expr -> Int
eval = tcata \case
  ValP i   -> i
  AddP x y -> x + y

----------------------------------------------------------------------
-- 5. Derivative Derived by Diagonal Dissection

type Undo :: (Type -> Type) -> Type -> Type
type Undo f x = Δ f x x

zUp :: Dissection f => (Μ f, [Δ f (Μ f) (Μ f)]) -> Maybe (Μ f, [Δ f (Μ f) (Μ f)])
zUp = \case
  (   _, [      ]) -> Nothing
  (tree, fd : fds) -> Just (In (plug tree fd), fds)

zDown :: Dissection f => (Μ f, [Δ f (Μ f) (Μ f)]) -> Maybe (Μ f, [Δ f (Μ f) (Μ f)])
zDown (In tree, rests) = case right (L₀ tree) of
  L₀ (subtree, rest) -> Just (subtree, rest : rests)
  R₀  _              -> Nothing

zLeft :: Dissection f => (Μ f, [Δ f (Μ f) (Μ f)]) -> Maybe (Μ f, [Δ f (Μ f) (Μ f)])
zLeft = \case
  (          _, [      ]) -> Nothing
  (tree :: Μ f, fd : fds) -> case left (R₀ (fd, tree)) of
    L₀ (t', fd')      -> Just (t', fd' : fds)
    R₀ (_ :: f (Μ f)) -> Nothing

zRight :: Dissection f => (Μ f, [Δ f (Μ f) (Μ f)]) -> Maybe (Μ f, [Δ f (Μ f) (Μ f)])
zRight = \case
  (          _, [      ]) -> Nothing
  (tree :: Μ f, fd : fds) -> case right (R₀ (fd, tree)) of
    L₀ (t', fd')      -> Just (t', fd' : fds)
    R₀ (_ :: f (Μ f)) -> Nothing

----------------------------------------------------------------------
-- 6. Division: No Clowns!

divide :: Dissection f => f x -> (x, Δ f Z x) + f Z
divide px = right (L₀ px)

inflateFst :: Bifunctor b => b Z y -> b x y
inflateFst = unsafeCoerce# -- bimap (coerce absurd) id

divide¹ :: Dissection f => (x, Δ f Z x) + f Z -> f x
divide¹ = \case
  L₀ (x, fl) -> plug x (inflateFst fl)
  R₀     fz  -> inflate fz

----------------------------------------------------------------------
-- 7. A Generic Abstractor

type Free :: (Type -> Type) -> Type -> Type
data Free f x = Pure x | Free (f (Free f x))
  deriving Applicative via (WrappedMonad (Free f))
  deriving stock Functor

type Pres :: (Type -> Constraint) -> (Type -> Type) -> Constraint
type Pres c f = forall x. c x => c (f x)

deriving instance (Pres Eq f, Eq x) => Eq (Free f x)
deriving instance (Pres Show f, Show x) => Show (Free f x)

instance Functor f => Monad (Free f) where
  Pure x >>= f = f x
  Free k >>= f = Free (fmap (>>= f) k)

type S :: Type -> Type
type S = Maybe

substitute :: Functor f => Free f (S x) -> Free f x -> Free f x
substitute t s = t >>= \case
  Nothing -> s
  Just x  -> Pure x

substitute¹ :: (Pres Eq f, Functor f, Eq x) => Free f x -> Free f x -> Free f (S x)
substitute¹  t       s | t == s = Pure $ Nothing
substitute¹ (Pure x) _          = Pure $ Just x
substitute¹ (Free k) s          = Free $ fmap (substitute¹ s) k

-- Here's where GHC stops playing nicely...

----------------------------------------------------------------------
-- Appendix

data family K x :: k

type U :: k
type U = K ()

type Z :: k
type Z = K Void

data family (+) :: k -> k -> k
data family (×) :: k -> k -> k

data instance x + y = L₀ x | R₀ y deriving stock (Eq, Functor, Show)
data instance x × y = T₀ x      y deriving stock (Eq, Functor, Show)
