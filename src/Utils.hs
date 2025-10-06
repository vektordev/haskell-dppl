{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Utils where

import Control.Monad.State

type Supply = State Int
type MonadSupply a = MonadState Int a

demandUniqueNumber :: MonadSupply m => m Int
demandUniqueNumber = do
  old <- get
  put (old + 1)
  return old

evalSupply :: Supply a -> a
evalSupply f = evalState f 0
