{-# OPTIONS_GHC -Wall -Wextra -Wno-orphans #-}

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Main where

import Control.Alternative.Free (Alt (..), AltF (..), liftAlt, runAlt)
import Control.Applicative (Alternative (..), liftA2)
import Data.Functor.Compose (Compose (Compose, getCompose))
import Data.Functor.Const (Const (Const))
import Data.Functor.Identity (Identity (runIdentity))
import Data.Kind (Type)
import Data.Monoid (All (All))
import Data.Set (Set)
import Data.Set qualified as Set

----------------------------------------------------------------------
-- 1. Introduction

-- Free alternative over the single constructor 'Token'.
type RuleF₁ :: Type -> Type
data RuleF₁ x where TokenF₁ :: Char -> RuleF₁ Char

token₁ :: Char -> Rule₁ Char
token₁ = liftAlt . TokenF₁

type Rule₁ :: Type -> Type
type Rule₁ = Alt RuleF₁

bs₁ :: Rule₁ String
bs₁ = liftA2 (:) (token₁ 'b') bs₁ <|> pure ""

bs₁' :: Rule₁ String -- left-recursive version of 'bs'.
bs₁' = liftA2 (flip (:)) bs₁' (token₁ 'b') <|> pure ""

-- @nullable bs₁'@ runs forever.
nullable :: Rule₁ x -> Bool
nullable = getBoolean . runAlt \case
  TokenF₁ _ -> empty

----------------------------------------------------------------------
-- 2. Background, examples and machinery

firstSet₁ :: Rule₁ x -> Set Char
firstSet₁ = foldMap go . alternatives
  where
    go :: AltF RuleF₁ x -> Set Char
    go = \case
      Pure  _            -> Set.empty
      Ap   (TokenF₁ c) _ -> Set.singleton c

type (∘) :: (Type -> Type) -> (Type -> Type) -> (Type -> Type)
type (∘) = Compose

liftInner :: Applicative p => q x -> (p ∘ q) x
liftInner = Compose . pure

liftOuter :: (Functor p, Applicative q) => p x -> (p ∘ q) x
liftOuter = Compose . fmap pure

withInner :: Functor p => (q x -> f x) -> (p ∘ q) x -> (p ∘ f) x
withInner f = Compose . fmap f . getCompose

----------------------------------------------------------------------
-- 3. A recursion primitive

type RuleF₂ :: Type -> Type
data RuleF₂ x where
  TokenF₂ :: Char -> RuleF₂ Char
  FixF₂ :: (Rule₂ x -> Rule₂ x) -> RuleF₂ x

type Rule₂ :: Type -> Type
type Rule₂ = Alt RuleF₂

fix₂ :: (Rule₂ x -> Rule₂ x) -> Rule₂ x
fix₂ = liftAlt . FixF₂

token₂ :: Char -> Rule₂ Char
token₂ = liftAlt . TokenF₂

bs₂ :: Rule₂ String
bs₂ = fix₂ \rest -> liftA2 (:) (token₂ 'b') rest <|> pure ""

bs₂' :: Rule₂ String
bs₂' = fix₂ \rest -> liftA2 (flip (:)) rest (token₂ 'b') <|> pure ""

badBind :: Rule₂ ()
badBind = fix₂ (Alt . map go . alternatives)
  where
    go :: AltF RuleF₂ () -> AltF f ()
    go = \case
      Pure x -> Pure x
      _      -> pure ()

class Alternative p => CharParser p where
  token :: Char -> p Char

type FinalRule₂ :: Type -> Type
type FinalRule₂ x = forall p. CharParser p => p x

finalBs₂ :: FinalRule₂ String
finalBs₂ = liftA2 (:) (token 'b') finalBs₂ <|> pure ""

finalBs₂' :: FinalRule₂ String
finalBs₂' = liftA2 (flip (:)) finalBs₂' (token 'b') <|> pure ""

instance CharParser Boolean where
  token _ = empty

-- Wasn't a million miles of guessing where we were going!
nullableF :: FinalRule₂ x -> Bool
nullableF = getBoolean

class Applicative p => ApplicativeFix₂ p where
  afix₂ :: (p x -> p x) -> p x

bsFix :: (Alternative p, ApplicativeFix₂ p, CharParser p) => p String
bsFix = afix₂ \rest -> liftA2 (:) (token 'b') rest <|> pure ""

bsFix₁ :: (Alternative p, ApplicativeFix₂ p, CharParser p) => p String
bsFix₁ = afix₂ \rest -> liftA2 (flip (:)) rest (token 'b') <|> pure ""

instance ApplicativeFix₂ Boolean where
  afix₂ f = f empty

class Applicative p => ApplicativeFix p where
  afix :: (forall q. Applicative q => (p ∘ q) x -> (p ∘ q) x) -> p x

  default afix :: Alternative p => (forall q. Applicative q => (p ∘ q) x -> (p ∘ q) x) -> p x
  afix f = fmap runIdentity $ getCompose (f empty)

instance (CharParser p, Applicative q) => CharParser (p ∘ q) where
  token = liftOuter . token

type FinalRule :: Type -> Type
type FinalRule x = forall p. (Alternative p, ApplicativeFix p, CharParser p) => p x

bs :: FinalRule String
bs = afix \s -> liftA2 (:) (token 'b') s <|> pure ""

bs' :: FinalRule String
bs' = afix \s -> liftA2 (flip (:)) s (token 'b') <|> pure ""

instance CharParser Rule₂ where
  token = token₂

deriving anyclass instance ApplicativeFix Rule₂

-- Both @bs@ and @bs'@ work now!
nullable₂ :: Rule₂ x -> Bool
nullable₂ = getBoolean . runAlt do
  Boolean . \case
    TokenF₂ _ -> False
    FixF₂   f -> nullable₂ (f empty)

----------------------------------------------------------------------
-- 5. Making @afix@ practical

manyAF :: (Alternative p, ApplicativeFix p) => p x -> p [x]
manyAF xs = afix \s -> liftA2 (:) (liftOuter xs) s <|> pure []

someAF :: (Alternative p, ApplicativeFix p) => p x -> p [x]
someAF xs = liftA2 (:) xs (manyAF xs)

assocComp₁ :: Functor p => ((p ∘ q) ∘ r) x -> (p ∘ (q ∘ r)) x
assocComp₁ = Compose . fmap Compose . getCompose . getCompose

assocComp₂ :: Functor p => ((p ∘ q) ∘ r) x -> (p ∘ (q ∘ r)) x
assocComp₂ = Compose . fmap Compose . getCompose . getCompose

liftComposed :: (Functor p, Applicative q) => (p ∘ r) x -> (p ∘ (q ∘ r)) x
liftComposed = Compose . fmap (Compose . pure) . getCompose

----------------------------------------------------------------------
-- Appendix

newtype Boolean x = Boolean { getBoolean :: Bool }
  deriving (Functor, Applicative) via (Const All)
  deriving anyclass (ApplicativeFix)

instance Alternative Boolean where
  Boolean x <|> Boolean y = Boolean (x || y)
  empty = Boolean False
