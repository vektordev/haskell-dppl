{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Utils
  ( splitByString
  , mapTup3
  , mapToTup
  , mapAppendTup
  , mapAppendTup3
  , uncurry4
  , concatMapM
  , replaceAt
  , fixpoint
  , Supply
  , MonadSupply
  , demandUniqueNumber
  , evalSupply
  , DAGEdge(..)
  , topSortDAG
  ) where

import Control.Monad.State
import Data.Graph
import Data.List (isPrefixOf)
import Data.Functor ((<&>))

-- | Split at the __first__ occurrence of the delimiter, which is kept at the
-- head of the second half: @splitByString "|" "a|b|c" == ("a", "|b|c")@.
--
-- Nothing is ever dropped -- the two halves always concatenate back to the
-- input. In particular, when the delimiter does not occur the whole input
-- comes back in the first half and the second is empty
-- (@splitByString "|" "abc" == ("abc", "")@). The @("", "")@ produced by the
-- @[]@ clause below is only the recursion's base case, reached with an empty
-- remainder; the prefix consumed on the way down is rebuilt on the way out by
-- @(c:x, y)@. (Reading that clause as the no-match result is what prompted
-- task @utils-splitbystring-drops-input-without-delimiter@; the contract is
-- pinned by @Utils.splitByString@ in test/TestInternals.hs.)
splitByString :: String -> String -> (String, String)
splitByString split orig | split `isPrefixOf` orig = ("", orig)
splitByString split (c:orig) = let (x, y) = splitByString split orig in (c:x, y)
splitByString _ [] = ("", "")

mapTup3 :: (a -> b) -> (a, a, a) -> (b, b, b)
mapTup3 f (a, b, c) = (f a, f b, f c)

mapToTup :: (a -> b) -> [a] -> [(a, b)]
mapToTup f = map (\x -> (x, f x))

mapAppendTup :: [(a, b)] -> [c] -> [(a, b, c)]
mapAppendTup = zipWith (curry (\((x, y), z) -> (x, y, z)))

mapAppendTup3 :: [(a, b, c)] -> [d] -> [(a, b, c, d)]
mapAppendTup3 = zipWith (curry (\((x, y, z), a) -> (x, y, z, a)))

uncurry4 :: (a -> b -> c -> d -> e) -> (a, b, c, d) -> e
uncurry4 f (a, b, c, d) = f a b c d

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f l = mapM f l <&> concat

replaceAt :: [a] -> Int -> a -> [a]
replaceAt _ n _ | n < 0 = error "No negative indices allowed"
replaceAt (_:lst) 0 x = x:lst
replaceAt (l:lst) n x = l:replaceAt lst (n-1) x
replaceAt [] n _ = error ("replaceAt: index " ++ show n ++ " is past the end of the list")

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
    edgeList = [(i,j) | (i,x) <- zippedIndices, (j,y) <- zippedIndices, edge x y]
    graph = buildG (0, length lst - 1) edgeList
    sorted = topSort graph
    sortedLst = map (lst !!) sorted