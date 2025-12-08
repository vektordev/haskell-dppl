{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Utils where

import Control.Monad.State
import Data.Graph


concatMap2 :: (a -> ([b], [c])) -> [a] -> ([b], [c])
concatMap2 f xs = (concat as, concat bs)
  where (as, bs) = unzip (map f xs)

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