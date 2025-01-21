module SPLL.IRCompiler where
import SPLL.Lang.Types (Program(..))
import SPLL.Lang.Lang (Expr(..), getSubExprs)
import Control.Monad
import Data.Maybe (isJust)
import PredefinedFunctions (globalFenv)

-- This function returns nothing if the program is valid and an error else
validateProgram :: Program -> Either String ()
-- We sequence the either monads so we either have a list of errors(Lefts) or discard the Rights
validateProgram p@Program{functions=fn, neurals=nurals} = sequence_ contextFreeValidations
  where
    -- Validates an expression without its context. Can use subexpressions
    contextFreeValidations = concatMap (\(_, expr) -> validateAllSubexpressions p expr expr) fn
    -- All Results from all subexpressions
    validateAllSubexpressions :: Program -> Expr -> Expr -> [Either String ()]
    validateAllSubexpressions p topLevel expr = validateExpressionContextFree p topLevel expr : concatMap (validateAllSubexpressions p topLevel) (getSubExprs expr)

validateExpressionContextFree :: Program -> Expr -> Expr -> Either String ()
validateExpressionContextFree _ _ (InjF _ name _) = if isJust (lookup name globalFenv) then Right () else Left ("Cannot find InjF: " ++ name)
validateExpressionContextFree _ _ (LetIn _ name val body) | declarationsCount name val == 0 || declarationsCount name body == 0 = Left ("Duplicate declaration of identifier (Shawdowing is not allowed): " ++ name)
validateExpressionContextFree _ _ (LetIn _ name _ _) | isJust (lookup name globalFenv) = Left ("Identifier name is already used by an InjF: " ++ show name)
-- Not declared
-- In use by another top level function
validateExpressionContextFree _ _ (Lambda _ name body) = if declarationsCount name body == 0 then Left ("Duplicate declaration of identifier (Shawdowing is not allowed): " ++ name) else Right ()
validateExpressionContextFree _ _ _ = Right ()

declarationsCount :: String -> Expr -> Int
declarationsCount name (LetIn _ decl _ _) | name == decl = 1
declarationsCount name (Lambda _ lmd _) | name == lmd = 1
declarationsCount name expr = sum $ map (declarationsCount name) (getSubExprs expr)