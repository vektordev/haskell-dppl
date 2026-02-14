{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Utils where

import Control.Monad.State
import Data.Graph
import Data.List (isPrefixOf)
import Data.Functor ((<&>))

splitByString :: String -> String -> (String, String)
splitByString split orig | split `isPrefixOf` orig = ("", orig)
splitByString split (c:orig) = let (x, y) = splitByString split orig in (c:x, y)
splitByString split [] = ("", "")

concatMap2 :: (a -> ([b], [c])) -> [a] -> ([b], [c])
concatMap2 f xs = (concat as, concat bs)
  where (as, bs) = unzip (map f xs)

mapTup3 :: (a -> b) -> (a, a, a) -> (b, b, b)
mapTup3 f (a, b, c) = (f a, f b, f c)

mapToTup :: (a -> b) -> [a] -> [(a, b)]
mapToTup f = map (\x -> (x, f x))

mapAppendTup :: [(a, b)] -> [c] -> [(a, b, c)]
mapAppendTup = zipWith (curry (\((x, y), z) -> (x, y, z)))

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f l = mapM f l <&> concat

replaceAt :: [a] -> Int -> a -> [a]
replaceAt _ n _ | n < 0 = error "No negative indices allowed"
replaceAt (_:lst) 0 x = x:lst
replaceAt (l:lst) n x = l:replaceAt lst (n-1) x

fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f x = if fx == x then x else fixpoint f fx
  where fx = f x

-- ======== SUPPLY MONAD ========

type Supply = State Int
type MonadSupply a = MonadState Int a

demandUniqueNumber :: MonadSupply m => m Int
demandUniqueNumber = do
  old <- get
  put (old + 1)
  return old

evalSupply :: Supply a -> a
evalSupply f = evalState f 0

-- ======== DAG SORTING ========

class DAGEdge a where
  edge :: a -> a -> Bool

topSortDAG :: DAGEdge a => [a] -> [a]
topSortDAG lst = sortedLst
  where
    zippedIndices = zip [0..] lst
    edges = [(i,j) | (i,x) <- zippedIndices, (j,y) <- zippedIndices, edge x y]
    graph = buildG (0, length lst - 1) edges
    sorted = topSort graph
    sortedLst = map (lst !!) sorted