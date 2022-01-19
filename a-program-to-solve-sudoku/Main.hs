{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Control.Monad (replicateM)
import Data.List ((\\))
import Test.QuickCheck

----------------------------------------------------------------------
-- 1 Introduction

boardsize :: Int
boardsize = 9

boxsize :: Int
boxsize = 3

cellvals :: Choices
cellvals = "123456789"

blank :: Char -> Bool
blank = (== '.')

newtype M a = M [[a]]
  deriving newtype (Eq, Show)

instance Arbitrary a => Arbitrary (M a) where
  arbitrary = fmap M
    . replicateM boardsize
    . replicateM boardsize
    $ arbitrary

----------------------------------------------------------------------
-- 2 Specification

type Matrix a = [[a]]
type Board    = Matrix Char

correct :: Board -> Bool
correct b
   = all nodups (rows b)
  && all nodups (cols b)
  && all nodups (boxs b)

nodups :: Eq a => [a] -> Bool
nodups [      ] = True
nodups (x : xs) = notElem x xs && nodups xs

----------------------------------------------------------------------
-- 2.1 Rows, columns and boxes

rows :: Matrix a -> Matrix a
rows = id

prop_rows_inverse :: (Eq a, Show a) => M a -> Property
prop_rows_inverse (M x) = rows (rows x) === x

cols :: Matrix a -> Matrix a
cols [xs]       = [[x] | x <- xs]
cols (xs : xss) = zipWith (:) xs (cols xss)
cols __________ = error "empty matrix??"

prop_cols_inverse :: (Eq a, Show a) => (M a) -> Property
prop_cols_inverse (M x) = cols (cols x) === x

boxs :: Matrix a -> Matrix a
boxs = map ungroup . ungroup . map cols . group . map group

prop_boxs_inverse :: (Eq a, Show a) => M a -> Property
prop_boxs_inverse (M x) = boxs (boxs x) === x

group :: [a] -> [[a]]
group xs
  | null xs   = []
  | otherwise = take boxsize xs : group (drop boxsize xs)

ungroup :: [[a]] -> [a]
ungroup = mconcat

prop_group_inverse :: (Eq a, Show a) => [a] -> Property
prop_group_inverse x = ungroup (group x) === x

prop_ungroup_inverse :: (Eq a, Show a) => [a] -> Property
prop_ungroup_inverse x = group (ungroup (group x)) === group x

----------------------------------------------------------------------
-- 2.2 Generating choices and matrix cartesian product

type Choices = [Char]

choices :: Board -> Matrix Choices
choices = map $ map \e -> if blank e then cellvals else [e]

mcp :: Matrix [a] -> [Matrix a]
mcp = cp . map cp

cp :: [[a]] -> [[a]]
cp [        ] = [[]]
cp (xs : xss) = [ x : ys | x <- xs, ys <- cp xss ]

----------------------------------------------------------------------
-- 2.3 Specification

sudoku_2 :: Board -> [Board]
sudoku_2 = filter correct . mcp . choices

----------------------------------------------------------------------
-- 3 Pruning the choices

fixed :: [Choices] -> Choices
fixed = mconcat . filter single

single :: Choices -> Bool
single = \case
  [_] -> True
  ___ -> False

reduce :: [Choices] -> [Choices]
reduce css = map (remove (fixed css)) css
  where
    remove fs cs
      | single cs = cs
      | otherwise = cs \\ fs

prop_filter_product :: Fun Char Bool -> Board -> Property
prop_filter_product (Fun _ p) x = filter (all p) (cp x) === cp (map (filter p) x)

-- prop_mcp_rows :: (Eq a, Show a) => M [a] -> Property
-- prop_mcp_rows (M x) = map rows (mcp x) === mcp (rows x)
-- 
-- prop_mcp_cols :: (Eq a, Show a) => M [a] -> Property
-- prop_mcp_cols (M x) = map cols (mcp x) === mcp (cols x)
-- 
-- prop_mcp_boxs :: (Eq a, Show a) => M [a] -> Property
-- prop_mcp_boxs (M x) = map boxs (mcp x) === mcp (boxs x)

prop_reduce_nodups :: M Char -> Property
prop_reduce_nodups (M x) = filter nodups (cp x) === filter nodups (cp (reduce x))

pruneBy :: (Matrix Choices -> Matrix Choices) -> (Matrix Choices -> Matrix Choices)
pruneBy f = f . map reduce . f

prune :: Matrix Choices -> Matrix Choices
prune = pruneBy boxs . pruneBy cols . pruneBy rows

prop_prune_correctness :: M Choices -> Property
prop_prune_correctness (M x) = filter correct (mcp x) === filter correct (mcp (prune x))

sudoku_3 :: Board -> [Board]
sudoku_3 = filter correct . mcp . prune . choices 

----------------------------------------------------------------------
-- 4 One choice at a time

----------------------------------------------------------------------
-- 4.1 Blocked matrices

blocked :: Matrix Choices -> Bool
blocked cm = void cm || not (safe cm)

void :: Matrix Choices -> Bool
void = any (any null)

safe :: Matrix Choices -> Bool
safe cm
   = all (nodups . fixed) (rows cm)
  && all (nodups . fixed) (cols cm)
  && all (nodups . fixed) (boxs cm)

----------------------------------------------------------------------
-- 4.2 Smallest number of choices

expand :: Matrix Choices -> [Matrix Choices]
expand cm = [rows1 ++ [row1 ++ [c] : row2] ++ rows2 | c <- cs]
  where
    (rows1, row : rows2) = break (any best) cm
    (row1,  cs  : row2)  = break best row
    best cs'             = length cs' == minchoice cm

minchoice :: Matrix Choices -> Int
minchoice = minimum . filter (> 1) . concat . map (map length)

search :: Matrix Choices -> [Matrix Choices]
search cm
  | blocked cm          = [  ]
  | all (all single) cm = [cm]
  | otherwise           = mconcat (map (search . prune) (expand cm))

----------------------------------------------------------------------
-- 4.3 Final version

sudoku_4 :: Board -> [Board]
sudoku_4 = head . search . prune . choices

-- $> sudoku_4 example
example :: Board
example
  = [ "9..83.157"
    , "5.31.628."
    , "1..74..9."
    , "....5.83."
    , "3.1..4672"
    , "2...13..9"
    , "..2.7..1."
    , ".......6."
    , ".34.6.92."
    ]
