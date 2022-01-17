{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Data.Functor.Foldable (ana)
import Data.Functor.Foldable.TH (makeBaseFunctor)
import Control.Applicative (Alternative (..))
import Control.Monad (ap)
import Data.Bool (bool)
import Data.Kind (Type)
import Test.QuickCheck ((===), Arbitrary (..), Fun (..), Property, elements)

-- $> import Test.QuickCheck

----------------------------------------------------------------------
-- 1 Introduction

-- Promise ~ Maybe to isomorphism
data Promise x = Unknown | Known x
  deriving stock (Functor, Eq, Ord, Show)

instance Applicative Promise where
  pure = Known
  (<*>) = ap

instance Alternative Promise where
  empty = Unknown

  -- amb = (<|>)
  Known x <|> _ = Known x
  Unknown <|> y = y

instance Monad Promise where
  Known x >>= f = f x
  Unknown >>= _ = Unknown

pand :: Promise Bool -> Promise Bool -> Promise Bool
pand  _            (Known False) = Known False
pand (Known False)  _            = Known False
pand (Known  True) (Known  True) = Known True
pand  _             _            = Unknown

pand' :: Promise Bool -> Promise Bool -> Promise Bool
pand' a b = let f x y = x >>= bool (pure False) y in f a b <|> f b a

----------------------------------------------------------------------
-- 3 Non-deterministic primitives

data Decision = One | Two
  deriving stock (Eq, Show)

instance Arbitrary Decision where
  arbitrary = elements [ One, Two ]

data Tree
  = Tree
      { left     :: Tree
      , contents :: Decision
      , right    :: Tree
      }

makeBaseFunctor ''Tree

choice' :: Decision -> x -> x -> x
choice' One a _ = a
choice' Two _ b = b

----------------------------------------------------------------------
-- 5 Implementation

type Unfold :: (Type -> Type -> Type) -> Type -> Type
type Unfold p x = p x (x, Decision, x)

tree :: x -> Unfold (->) x -> Tree
tree x f = let g (l, c, r) = TreeF l c r in ana (g . f) x

choice :: Tree -> x -> x -> x
choice o = choice' (contents o)

-- Example from section (2)
simpleCorrectButUseless :: Tree
simpleCorrectButUseless = tree () \_ -> ((), One, ())

alternating :: Tree
alternating = tree True \t -> (not t, if t then One else Two, not t)

-- $> quickCheck prop_theorem1
prop_theorem1 :: String -> String -> Int -> Unfold Fun Int -> Property
prop_theorem1 a b x (Fun _ f) = choice o a b === bool b a (choice o True False)
  where o = tree x f

----------------------------------------------------------------------
-- 6 Examples

-- $> quickCheck prop_referential_transparency
prop_referential_transparency :: String -> String -> Int -> Unfold Fun Int -> Property
prop_referential_transparency a b x (Fun _ f) = choice o a b === choice o a b
  where o = tree x f

-- $> interleave simpleCorrectButUseless [1 .. 5] [6 .. 10]
--
-- $> interleave alternating [1 .. 5] [6 .. 10]
interleave :: Tree -> [x] -> [x] -> [x]
interleave t xs ys = choice' (contents t)
  case xs of
    [     ] -> ys
    x : xss -> x : interleave (right t) xss ys

  case ys of
    [     ] -> xs
    y : yss -> y : interleave (right t) xs yss
