module Typing where

import Lang
import RType
import PType

import Control.Monad.Except (ExceptT)

import Control.Monad.Reader

-- Because Env will be polluted by local symbols as we evaluate, we need to reset when calling functions.
-- Therefore, we define that all functions must exist in the global namespace.
-- That way, it is sufficient to carry only the global namespace as reset point.
-- local functions are in principle possible, but they need to carry their own environment with them,
-- e.g. by expanding Env to be of [(String, Env x a, Expr x a)], where [] indicates a shorthand for the global scope.
type Env x a = [(String, Expr x a)]

type Check a = ExceptT TypeError (Reader (Env () a))

data TypeError = Mismatch RType RType
               deriving (Show, Eq)