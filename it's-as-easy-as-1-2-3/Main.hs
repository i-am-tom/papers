{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
module Main where

import Control.Applicative (Alternative (..), liftA2)
import Data.Function (fix)
import Data.Tree (Tree (..))
import GHC.Generics (Generic)
import Test.QuickCheck (Arbitrary (..), genericShrink, sized)

----------------------------------------------------------------------
-- 2 Arithmetic Expressions

data Expr = Val Integer | Add Expr Expr
  deriving stock (Eq, Generic, Show)

instance Arbitrary Expr where
  arbitrary = sized $ fix \f m ->
    case m of
      0 -> Val <$> arbitrary
      n -> Add <$> f (n `div` 2) <*> f (n `div` 2)

  shrink = genericShrink

eg0 :: Expr
eg0 = Add (Val 1) (Val 2)

----------------------------------------------------------------------
-- 3 Denotational Semantics

eval :: Expr -> Integer
eval = \case
  Val n   -> n
  Add x y -> eval x + eval y

eg1 :: Integer
eg1 = eval $ Add (Val 1) (Add (Val 2) (Val 3))

----------------------------------------------------------------------
-- 4 Operational Semantics

trans :: Expr -> [Expr]
trans = \case
  Val  _              -> []
  Add (Val x) (Val y) -> [Val (x + y)]
  Add (    x) (    y) -> fmap (`Add` y) (trans x) ++ fmap (x `Add`) (trans y)

exec :: Expr -> Tree Expr
exec = unfold id trans

unfold :: (a -> b) -> (a -> [a]) -> a -> Tree b
unfold f g x = Node (f x) [unfold f g x' | x' <- g x]

----------------------------------------------------------------------
-- 5 Contextual Semantics

data Con
  = Hole
  | AddL Con Expr
  | AddR Expr Con

subst :: Con -> Expr -> Expr
subst x e = case x of
  Hole     -> e
  AddL c r -> Add (subst c e) r
  AddR l c -> Add l (subst c e)

split :: Expr -> [(Con, Expr)]
split e = (Hole, e) : case e of
  Val _   -> []
  Add x y -> mconcat
    [ [(AddL c y, e') | (c, e') <- split x]
    , [(AddR x c, e') | (c, e') <- split y]
    ]

trans' :: Expr -> [Expr]
trans' = \case
  Add (Val n) (Val m) -> [Val (n + m)]
  e -> do
    (c, x) <- tail (split e)
    fmap (subst c) (trans x)

----------------------------------------------------------------------
-- 6 Big-Step Semantics

eval_ :: Expr -> [Integer]
eval_ = \case
  Val n   -> pure n
  Add x y -> liftA2 (+) (eval_ x) (eval_ y)

----------------------------------------------------------------------
-- 7 Rule Induction

prop :: Expr -> Bool
prop x = and [ eval x == eval x' | x' <- trans x ]

----------------------------------------------------------------------
-- 8 Abstract Machines

data Cont
  = ADD Integer Cont
  | EVAL Expr Cont
  | HALT

eval' :: Expr -> Integer
eval' = go HALT
  where
    go :: Cont -> Expr -> Integer
    go c = \case
      Val n   -> exec' n c
      Add x y -> go (EVAL y c) x

    exec' :: Integer -> Cont -> Integer
    exec' m = \case
      HALT     -> m
      EVAL y c -> go (ADD m c) y
      ADD  n k -> exec' (m + n) k

----------------------------------------------------------------------
-- 9 Adding Exceptions

data Expr'
  = Val' Integer
  | Add' Expr' Expr'
  | Throw'
  | Catch' Expr' Expr'
  deriving stock Show

eval'' :: Expr' -> Maybe Integer
eval'' = \case
  Add'  x y  -> liftA2 (+) (eval'' x) (eval'' y)
  Catch' x h -> eval'' x <|> eval'' h
  Throw'     -> Nothing
  Val'  n    -> Just n

type Code = [Op]
type Stack = [Item]

data Op
  = PUSH' Integer
  | ADD'
  | THROW'
  | MARK' Code
  | UNMARK'
  deriving stock Show

data Item
  = VAL Integer
  | HAN Code
  deriving stock Show

exec'' :: Code -> Stack -> Stack
exec'' [           ]                  s  = s
exec'' (PUSH' n : c)                  s  = exec'' c $ VAL n : s
exec'' (ADD'    : c) (VAL m : VAL n : s) = exec'' c $ VAL (n + m) : s
exec'' (THROW'  : _)                  s  = unwind s
exec'' (MARK' h : c)                  s  = exec'' c $ HAN h : s
exec'' (UNMARK' : c) (x : HAN _ :     s) = exec'' c $ x : s

unwind :: Stack -> Stack
unwind = \case
  [       ] -> []
  VAL _ : s -> unwind s
  HAN h : s -> exec'' h s

compile :: Expr' -> Code
compile e = comp e []
  where
    comp :: Expr' -> Code -> Code
    comp (Val'   n  ) c = PUSH' n : c
    comp (Add'   x y) c = comp x (comp y (ADD' : c))
    comp  Throw'      c = THROW' : c
    comp (Catch' x h) c = MARK' (comp h c) : comp x (UNMARK' : c)
