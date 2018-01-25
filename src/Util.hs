module Util where

import           Control.Monad

import           Data.List
import qualified Data.Set as Set

-- iterate f on x until we reach a fixed point
iter :: (Eq a) => (a -> a) -> a -> a
iter f x = if x == x' then x else iter f x' where
  x' = f x

stripInfix :: (Eq a) => [a] -> [a] -> [a]
stripInfix s xs | Just xs <- stripPrefix s xs = stripInfix s xs
stripInfix s (x:xs) = x : stripInfix s xs
stripInfix s [] = []

-- | Apply a function to corresponding elements of parallel lists
zipWithN :: ([a] -> b) -> [[a]] -> [b]
zipWithN f = map f . transpose

-- Convert a list into a diagonal matrix
diagonalize :: MonadPlus m => [a] -> [[m a]]
diagonalize = diagonalize' return mzero

diagonalize' :: (a -> b) -> b -> [a] -> [[b]]
diagonalize' return mzero xs = go 0 xs where
  n  = length xs
--  go :: Arity -> [a] -> [[m a]]
  go _i [] = []
  go i (y : ys) = r : go (i + 1) ys where
    --r :: [m a]
    r = replicate i mzero ++ [return y] ++ replicate (n-i-1) mzero

splitOffFirstGroup :: (a -> a -> Bool) -> [a] -> ([a],[a])
splitOffFirstGroup equal xs@(x:_) = partition (equal x) xs
splitOffFirstGroup _     []       = ([],[])

equivalenceClasses :: (a -> a -> Bool) -> [a] -> [[a]]
equivalenceClasses _     [] = []
equivalenceClasses equal xs = let (fg,rst) = splitOffFirstGroup equal xs
                              in fg : equivalenceClasses equal rst

equivalenceClasses' :: (Ord a) => (a -> a -> Bool) -> Set.Set a -> [Set.Set a]
equivalenceClasses' f = map Set.fromList . equivalenceClasses f . Set.toList
