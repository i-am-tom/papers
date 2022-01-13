{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Main where

import Data.Kind (Type)
import Numeric.Natural (Natural)
import Prelude hiding ((||))
import Prelude qualified as P

------------------------------------------------------------
-- 2 The data type of lists

data List a = Nil | Cons (a || List a)
  deriving stock (Eq)

--------------------------------------------------
-- Catamorphisms

cataList :: b -> (a -> b -> b) -> List a -> b
cataList b (⊕) = h
  where
    h  Nil           = b
    h (Cons (a, as)) = a ⊕ h as

length :: Num num => List a -> num
length = cataList 0 \_ n -> 1 + n

filter :: (a -> Bool) -> List a -> List a
filter p = cataList Nil (⊕)
  where
    a ⊕ as
      | p a       = Cons (a, as)
      | otherwise = as

-- f . (| b, ⊕ |) = (| c, ⊗ |) ⇐  f b = c ∧ f (a ⊕ as) = a ⊗ f as

--------------------------------------------------
-- Anamorphisms

anaList :: (b -> (a, b)) -> (b -> Bool) -> b -> List a
anaList g p = h
  where
    h b | p b       = Nil
        | otherwise = let (a, b') = g b in Cons (a, h b')

zip :: (Eq a, Eq b) => (List a, List b) -> List (a, b)
zip = anaList g p
  where
    p (         as,           bs ) = as == Nil ∨ bs == Nil
    g (Cons (a, as), Cons (b, bs)) = ((a, b), (as, bs))

iterate :: (a -> a) -> a -> List a
iterate f = anaList g p
  where
    p _ = False
    g a = (a, f a)

map :: Eq a => (a -> b) -> List a -> List b
-- map f = cata Nil \a bs -> Cons (f a, bs)
map f = anaList g p
  where
    p        a       = a == Nil
    g (Cons (a, as)) = (f a, as)

--------------------------------------------------
-- Hylomorphisms

hyloList :: c -> (b -> c -> c) -> (a -> (b, a)) -> (a -> Bool) -> a -> c
hyloList c (⊕) g p = h
  where
    h a | p a       = c
        | otherwise = let (b, a') = g a in b ⊕ h a'

fac :: Natural -> Natural
fac = hyloList 1 (*) g p
  where
    p n = n == 0
    g n = (n, n - 1)

--------------------------------------------------
-- Paramorphisms

paraNat :: b -> (Natural -> b -> b) -> Natural -> b
paraNat b (⊕) = h
  where
    h 0 = b
    h n = n ⊕ h (n - 1)

paraList :: b -> (a -> (List a, b) -> b) -> List a -> b
paraList b (⊕) = h
  where
    h  Nil           = b
    h (Cons (a, as)) = a ⊕ (as, h as)

fac' :: Natural -> Natural
fac' = paraNat 1 (⊕)
  where n ⊕ m = (1 + n) * m

tails :: List a -> List (List a)
tails = paraList (Cons (Nil, Nil)) (⊕)
  where a ⊕ (as, tls) = Cons (Cons (a, as), tls)

------------------------------------------------------------
-- 3 Algebraic data types

--------------------------------------------------
-- Functors

class Bifunctor f where
  (†) :: (a -> b) -> (c -> d) -> f a c -> f b d

class Monofunctor f where
  f :: (a -> b) -> f a -> f b

-- Product

type (||) = (,)

(||) :: (a -> b) || (c -> d) -> (a, c) -> (b, d)
(f, g) || (x, x') = (f x, g x')

-- Just going to use fst to mean grave pi and snd to mean acute pi; whose
-- coding font has a glyph for these?

(△) :: (a -> b) -> (a -> c) -> a -> (b, c)
(f △ g) x = (f x, g x)

(▲) :: a -> (a, a)
(▲) x = (x, x)

-- Sum

type (¦) = Either -- We don't need the ⊥
infixl 4 ¦

(¦) :: (a -> b) -> (c -> d) -> a ¦ c -> b ¦ d
f ¦ g = either (Left . f) (Right . g)

ì :: a -> a ¦ b
ì = Left

í :: b -> a ¦ b
í = Right

(▽) :: (a -> c) -> (b -> c) -> a ¦ b -> c
(▽) = either

infix 2 ▽

(▼) :: a ¦ a -> a
(▼) = either id id

-- Arrow

type (→) = (->)

(→) :: (a -> b) -> (c -> d) -> (b -> c) -> a -> d
(f → g) h = g . h . f

(←) :: (c -> d) -> (a -> b) -> (b -> c) -> a -> d
(←) = flip (→)

-- Again, I can't write any cool F-arrows, so I'm going to use fat arrows to
-- refer to the second arrow type at the bottom of page 7.

(⇐) :: Functor f => (f c -> d) -> (a -> f b) -> (b -> c) -> a -> d
(f ⇐ g) h = f . fmap h . g

eval :: (a -> b, a) -> b
eval = uncurry ($)

type One = ()

void :: One
void = ()

(?) :: (a -> Bool) -> a -> a ¦ a
p? a = if p a then ì a else í a

ifte :: (a -> Bool) -> (a -> b) -> (a -> b) -> (a -> b)
ifte p f g = (f ▽ g) . (p?)

_VOID :: x -> One
_VOID x = ()

μ :: (a -> a) -> a
μ f = x where x = f x

type Φ f g = forall x. f x -> g x 

-- Recursive types

-- One day, when we have anonymous types that I can generate with generics,
-- I'll be able to do some real wizardry here.

class Functor (L x) => Mu x where
  data L x :: Type -> Type

  inF :: L x x -> x
  outF :: x -> L x x

id' :: Mu x => x -> x
id' = μ (inF ⇐ outF)

instance Mu (List a) where
  newtype L (List a) x
    = ListL { unListL :: One ¦ a || x }
    deriving stock (Functor)

  inF = (const Nil ▽ Cons) . unListL
  outF = ListL . \case
    Nil     -> ì void
    Cons as -> í as

instance Mu Natural where
  newtype L Natural x
    = NatL { unNatL :: One ¦ x }
    deriving stock (Functor)

  inF = (const 0 ▽ succ) . unNatL
  outF = NatL . \case
    0 -> ì  void
    n -> í (pred n)

------------------------------------------------------------
-- 4 Recursion schemes

cata :: Mu a => (L a b -> b) -> a -> b
cata φ = μ(φ ⇐ outF)

ana :: Mu a => (b -> L a b) -> b -> a
ana ψ = μ(inF ⇐ ψ)

hylo :: Functor f => (f b -> b, a -> f a) -> a -> b
hylo (φ, ψ) = μ(φ ⇐ ψ)

para :: Mu a => (L a (a, b) -> b) -> a -> b
para ξ = μ \f -> ξ . fmap (id △ f) . outF

--------------------------------------------------
-- Relating cata- and anamorphisms

-- Weird formulation?
data Tree a = Empty | Leaf a | Branch (Tree a || Tree a)

instance Mu (Tree a) where
  data L (Tree a) x
    = TreeL { unTreeL :: One ¦ a ¦ x || x }
    deriving stock (Functor)

  inF = ((const Empty ▽ Leaf) ▽ Branch) . unTreeL
  outF = TreeL . \case
    Empty    -> ì (ì void)
    Leaf x   -> ì (í x)
    Branch x -> í x

swap :: Tree a -> Tree a
swap = inF . TreeL . (id ¦ id ¦ snd △ fst) . unTreeL . outF

----------------------------------------------------------------------
-- Appendix

apo :: Mu a => (b -> L a (Either a b)) -> b -> a
apo λ = μ \f -> inF . fmap (id ▽ f) . λ

(∨) :: Bool -> Bool -> Bool
(∨) = (P.||)

infix 3 ∨
