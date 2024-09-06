{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Data.Bool (bool)
import Data.Kind (Constraint, Type)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Monoid (Sum)
import Data.Set (Set)
import Numeric.Natural (Natural)

----------------------------------------------------------------------
-- 1 Introduction

nonIncrementalSum :: Set Int -> Int
nonIncrementalSum s = foldr (+) 0 s

eg0 :: Int
eg0 = nonIncrementalSum [ 1 .. 10 ]

eg1 :: Int
eg1 = nonIncrementalSum [ 2 .. 11 ]

type SetInputChange :: Type
data SetInputChange = Minus Int | Plus Int

type SetOutputChange :: Type
type SetOutputChange = Int

sumDerivative :: Set Int -> [ SetInputChange ] -> SetOutputChange
sumDerivative _ = sum . map \case Plus x -> x; Minus x -> negate x

sumUpdate :: Int -> SetOutputChange -> Int
sumUpdate = (+)

eg2 :: SetOutputChange
eg2 = sumDerivative [ 1 .. 10 ] [ Minus 1, Plus 11 ]

eg3 :: Int
eg3 = sumUpdate eg0 eg2

-- >>> f (a ⊕ da) ~= f a ⊕ (derive f a) da.
--
-- Applying f to the updated a value should yield the same result as applying f
-- to the original a value, then applying the change in f given the change in
-- a.
--
-- f a = original result
-- f (a ⊕ da) = updated result
-- f' a da = the difference between the two

----------------------------------------------------------------------
-- 2 A theory of changes

----------------------------------------------------------------------
-- 2.1 Change sturctures

type Change :: Type -> Constraint
class {- Monoid (Δ x) => -} Change x where
  type Δ x :: Type

  (<~) :: x -> Δ x -> x
  (\\) :: x -> x -> Δ x

prop_complement :: (Change x, Eq x) => x -> x -> Bool
prop_complement x y = x <~ (y \\ x) == y

class Monoid m => Group m where
  inverse :: m -> m
  -- x <> inverse x === mempty

class Group m => Abelian m where
  -- x <> y === y <> x

----------------------------------------------------------------------

type Bag :: Type -> Type
newtype Bag x = Bag (Map x Int)

instance Ord x => Semigroup (Bag x) where
  Bag xs <> Bag ys = Bag do
    Map.unionWith (+) xs ys

instance Ord x => Monoid (Bag x) where
  mempty = Bag Map.empty

instance Ord x => Group (Bag x) where
  inverse (Bag xs) = Bag (fmap negate xs)

instance Ord x => Abelian (Bag x)

----------------------------------------------------------------------

instance Group (Sum Int) where
  inverse = negate

instance Num x => Change (Sum x) where
  type Δ (Sum x) = Sum x

  (<~) = (+)
  (\\) = (-)

----------------------------------------------------------------------

instance Change Bool where
  type Δ Bool = Bool

  (<~) x = bool x (not x)
  (\\) = (/=)

----------------------------------------------------------------------
-- 2.2 Function changes

instance (Change x, Change y) => Change (x -> y) where
  -- The derivative of an @x -> y@ function is a function that, given a
  -- previous @x@ value, maps input changes to output changes.
  type Δ (x -> y) = x -> Δ x -> Δ y

  -- To update a function with a change, we produce a new function that updates
  -- the output with the nil change. ???
  (<~) :: (x -> y) -> (x -> Δ x -> Δ y) -> (x -> y)
  (<~) f df = \x -> f x <~ df x (x \\ x)

  (\\) :: (x -> y) -> (x -> y) -> x -> Δ x -> Δ y
  (\\) f g = \x dx -> f (x <~ dx) \\ g x

----------------------------------------------------------------------
-- 3 Incrementalizing λ-calculi

type Literal :: Type -> Type
data Literal x where
  Int :: Sum Int -> Literal (Sum Int)

type Expr :: Type -> Type
data Expr x where
  App :: Expr (x -> y) -> Expr x -> Expr y
  Lambda :: Variable x -> (Expr x -> Expr y) -> Expr (x -> y)
  Literal :: Literal x -> Expr x
  Variable :: Variable x -> Expr x

type Variable :: Type -> Type
data Variable x where
  Named :: Natural -> Variable x
  Derived :: Variable x -> Variable (Δ x)

----------------------------------------------------------------------

derive :: Expr x -> Expr (Δ x)
derive = \case
  App f x -> App (App (derive f) x) (derive x)
  Lambda t f -> Lambda t \x -> Lambda (Derived t) \_dx -> derive (f x)
  Literal (Int _) -> Literal (Int 0)
  Variable x -> Variable (Derived x)

main :: IO ()
main = pure ()
