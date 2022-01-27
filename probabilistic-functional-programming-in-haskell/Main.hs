{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
module Main where

import Control.Applicative qualified as A
import Data.Functor ((<&>))
import Data.Kind (Constraint, Type)
import Data.List (delete, transpose)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Numeric.Natural (Natural)
import Prelude hiding (Functor (..), Applicative (..), Monad (..))
import Prelude qualified as P
import System.Random (Random)
import System.Random qualified as Random
import Text.Printf (PrintfArg, printf)

----------------------------------------------------------------------
-- 0 Haskell2030

class Trivial x
instance Trivial x

type Functor :: (Type -> Constraint) -> (Type -> Type) -> Constraint
class Functor c f | f -> c where
  fmap :: c y => (x -> y) -> (f x -> f y)

instance {-# OVERLAPPABLE #-} (P.Functor f, t ~ Trivial)
    => Functor t f where
  fmap = P.fmap

type Applicative :: (Type -> Constraint) -> (Type -> Type) -> Constraint
class Functor c f => Applicative c f | f -> c where
  liftA2 :: c z => (x -> y -> z) -> (f x -> f y -> f z)
  pure   :: c x => x -> f x

instance {-# OVERLAPPABLE #-} (P.Applicative f, t ~ Trivial)
    => Applicative t f where
  liftA2 = A.liftA2
  pure   = P.pure

type Alternative :: (Type -> Constraint) -> (Type -> Type) -> Constraint
class Applicative c f => Alternative c f | f -> c where
  (<|>) :: c x => f x -> f x -> f x
  empty :: f x

instance {-# OVERLAPPABLE #-} (A.Alternative f, t ~ Trivial)
    => Alternative t f where
  (<|>) = (A.<|>)
  empty = A.empty

type Monad :: (Type -> Constraint) -> (Type -> Type) -> Constraint
class Applicative c m => Monad c m | m -> c where
  (>>=) :: c y => m x -> (x -> m y) -> m y

infixl 5 >>=

instance {-# OVERLAPPABLE #-} (P.Monad f, t ~ Trivial)
    => Monad t f where
  (>>=) = (P.>>=)

(>=>) :: (Monad t f, t x, t z) => (x -> f y) -> (y -> f z) -> x -> f z
(f >=> g) x = f x >>= g

infixl 3 >=>

----------------------------------------------------------------------
-- 1 Introduction

type Probability :: Type
newtype Probability = Probability { toFloat :: Float }
  deriving newtype (Eq, Floating, Fractional, Num, Ord, Show)
  deriving newtype (PrintfArg, Random)

type Dist :: Type -> Type
newtype Dist x = Dist { unDist :: Map x Probability }
  deriving stock (Eq, Ord)

instance Show x => Show (Dist x) where
  show (Dist xs) = unlines do
    (x, p) <- Map.toList xs

    pure $ printf "%10s: % 5.1f%%" (show x) (p * 100)

instance Functor Ord Dist where
  fmap f (Dist xs) = Dist (Map.mapKeysWith (+) f xs)

instance Applicative Ord Dist where
  liftA2 f xs ys = Dist do
    Map.fromListWith (+) do
      (x, p) <- Map.toList (unDist xs)
      (y, q) <- Map.toList (unDist ys)

      pure (f x y, p * q)

  pure x = Dist (Map.singleton x 1)

instance Alternative Ord Dist where
  Dist xs <|> Dist ys = Dist do
    Map.fromListWith (+) do
      (x, p) <- Map.toList xs ++ Map.toList ys
      pure (x, p / 2)

  empty = Dist Map.empty

instance Monad Ord Dist where
  Dist xs >>= f = Dist do
    Map.fromListWith (+) do
      (x, p) <- Map.toList $ xs
      (y, q) <- Map.toList $ unDist (f x)

      pure (y, p * q)

type Spread :: Type -> Type
type Spread x = [x] -> Dist x

uniform :: Ord x => Spread x
uniform xs = Dist $ Map.fromListWith (+) (map (, p) xs)
  where p = recip . fromIntegral $ length xs

die :: Dist Int
die = uniform [ 1 .. 6 ]

normal :: Ord x => Spread x
normal xs = Dist do
  let samples :: [Probability]
      samples = [0 .. length xs - 1] <&> \i ->
        fromIntegral i / fromIntegral (length xs - 1)

      -- google.com/search?q=normal+distribution+formula
      curve :: Probability -> Probability
      curve x = recip (sqrt (2 * pi) * exp (2 * (x - 0.5) ** 2))

      unscaled :: [Probability]
      unscaled = map curve samples

      scaled :: [Probability]
      scaled = map (/ sum unscaled) unscaled

  Map.fromList (zip xs scaled)

type Event :: Type -> Type
type Event x = x -> Bool

(??) :: Event x -> Dist x -> Probability
(??) p (Dist xs) = sum [ c | (x, c) <- Map.toList xs, p x ]

dice :: Natural -> Dist [Int]
dice = \case
  0 -> pure []
  n -> liftA2 (:) die (dice (n - 1))

enum :: Ord x => [(Trans x, Probability)] -> Trans x
enum xs x = Dist $ Map.fromList do
  (t, p) <- xs
  (y, q) <- Map.toList $ unDist (t x)

  pure (y, p * q)

selectOne :: Ord x => [x] -> Dist (x, [x])
selectOne xs = uniform [(x, delete x xs) | x <- xs]

selectMany :: Ord x => Natural -> [x] -> Dist ([x], [x])
selectMany m xs = case m of
  0 -> pure ([], xs)
  n -> do
    (x,  xss) <- selectOne xs
    (ys, yss) <- selectMany (n - 1) xss

    pure (x : ys, yss)

select :: Ord x => Natural -> [x] -> Dist [x]
select n = fmap (reverse . fst) . selectMany n

type Trans :: Type -> Type
type Trans x = x -> Dist x

----------------------------------------------------------------------
-- 2 The Monty Hall Problem

data Outcome = Win | Lose
  deriving stock (Eq, Ord, Show)

firstChoice :: Dist Outcome
firstChoice = uniform [ Win, Lose, Lose ]

switch :: Trans Outcome
switch = pure . \case
  Win  -> Lose
  Lose -> Win

data Door = A | B | C
  deriving stock (Bounded, Enum, Eq, Ord, Show)

doors :: [Door]
doors = [ minBound .. maxBound ]

data State
  = Doors
      { prize  :: Maybe Door
      , chosen :: Maybe Door
      , opened :: Maybe Door
      }
  deriving stock (Eq, Ord, Show)

start :: State
start = Doors Nothing Nothing Nothing

hide :: Trans State
hide s = uniform [ s { prize = Just d } | d <- doors ]

choose :: Trans State
choose s = uniform [ s { chosen = Just d } | d <- doors ]

open :: Trans State
open s = uniform
  [ s { opened = Just d }
  | d <- doors

  , Just d /= prize s
  , Just d /= chosen s
  ]

type Strategy = Trans State

switch' :: Strategy
switch' s = uniform
  [ s { chosen = Just d }
  | d <- doors

  , Just d /= chosen s
  , Just d /= opened s
  ]

stay' :: Strategy
stay' = pure

game :: Strategy -> Trans State
game s = hide >=> choose >=> open >=> s

result :: State -> Outcome
result s
  | chosen s == prize s = Win
  | otherwise           = Lose

eval :: Strategy -> Dist Outcome
eval s = fmap result (game s start)

----------------------------------------------------------------------
-- 3 An Example from Biology: Tree Growth

type Height = Natural

data Tree = Alive Height | Hit Height | Fallen
  deriving stock (Eq, Ord, Show)

grow :: Trans Tree
grow (Alive h) = normal [ Alive k | k <- [ h + 1 .. h + 5 ] ]
grow  _        = empty

hit :: Trans Tree
hit (Alive h) = pure (Hit h)
hit  _        = empty

fall :: Trans Tree
fall _ = pure Fallen

evolve :: Trans Tree
evolve t@(Alive _) = enum [(grow, 0.9), (hit, 0.04), (fall, 0.06)] t
evolve t           = pure t

type Iterate :: (Type -> Constraint) -> (Type -> Type) -> Constraint
class Iterate c f | f -> c where
  (*.) :: c x => Natural -> (x -> f x) -> (x -> f x)

  while :: c x => (x -> Bool) -> (x -> f x) -> (x -> f x)
  until :: c x => (x -> Bool) -> (x -> f x) -> (x -> f x)

  until p = while (not . p)

instance Iterate Ord Dist where
  0 *. _ = pure
  n *. f = f >=> (n - 1) *. f

  while p xs x
    | p x       = xs x >>= while p xs
    | otherwise = pure x

infixl 4 *.

tree :: Natural -> Tree -> Dist Tree
tree n = n *. evolve

----------------------------------------------------------------------
-- 4 Randomisation

type R :: Type -> Type
type R = IO

type RChange :: Type -> Type
type RChange x = x -> IO x

selectP :: (Alternative c f, c x) => Dist x -> Probability -> f x
selectP (Dist xs') s' = go s' (Map.toList xs')
  where
    go s = \case
      (x, p) : xs
        | p >= s    -> pure x
        | otherwise -> go (s - p) xs
      [] -> empty

pick :: Dist x -> R x
pick d = Random.randomRIO (0, 1) >>= selectP d

random :: Trans x -> RChange x
random t = pick . t

type RDist :: Type -> Type
type RDist x = R (Dist x)

type RTrans :: Type -> Type
type RTrans x = x -> RDist x

rDist :: Ord x => [R x] -> RDist x
rDist = fmap uniform . sequenceA

type Sim :: (Type -> Type) -> Constraint
class Sim f where (~.) :: Ord x => Natural -> (x -> f x) -> RTrans x

instance Sim IO   where n ~. t = rDist . replicate (fromIntegral n) . t
instance Sim Dist where n ~. t = n ~. random t

simTree :: Natural -> Natural -> Tree -> RDist Tree
simTree k n = k ~. tree n

simEval :: Natural -> Strategy -> RDist Outcome
simEval k s = fmap (fmap result) $ (k ~. game s) start

----------------------------------------------------------------------
-- 5 Tracing

type Trace :: Type -> Type
type Trace = []

type Space :: Type -> Type
type Space x = Trace (Dist x)

type Walk :: Type -> Type
type Walk x = x -> Trace x

type Expand :: Type -> Type
type Expand x = x -> Space x

type Change :: Type -> Type
type Change x = x -> x

walk :: Natural -> Change x -> Walk x
walk n f = take (fromIntegral n) . iterate f

(*..) :: Ord x => Natural -> Trans x -> Expand x
0 *.. _ = pure . pure
1 *.. t = pure . t
n *.. t = t >>: (n - 1) *.. t

(>>:) :: Ord x => Trans x -> Expand x -> Expand x
(f >>: g) x = (d >>= f) : ds where ds@(d : _) = g x


infixl 4 >>:

type RTrace :: Type -> Type
type RTrace x = R (Trace x)

type RSpace :: Type -> Type
type RSpace x = R (Space x)

type RWalk :: Type -> Type
type RWalk x = x -> RTrace x

type RExpand :: Type -> Type
type RExpand x = x -> RSpace x

rWalk :: Natural -> RChange x -> RWalk x
rWalk 0 _ = pure . pure
rWalk 1 t = fmap pure . t
rWalk n t = t >>:= rWalk (n - 1) t

(>>:=) :: RChange x -> RWalk x -> RWalk x
(f >>:= g) x = g x >>= \ds@(d : _) -> fmap (: ds) (f d)

type Sim' :: (Type -> Type) -> Constraint
class Sim' f where
  (~..) :: Ord x => (Natural,Natural) -> (x -> f x) -> RExpand x

mergeTraces :: Ord x => [RTrace x] -> RSpace x
mergeTraces = fmap (map uniform . transpose) . sequence

instance Sim' IO where
  (k, n) ~.. t
    = mergeTraces
    . replicate (fromIntegral k)
    . rWalk n t

instance Sim' Dist where
  x ~.. t = x ~.. random t

hist :: Natural -> Tree -> Space Tree
hist n = n *.. evolve

simHist :: Natural -> Natural -> Tree -> RSpace Tree
simHist k n = (k, n) ~.. evolve
