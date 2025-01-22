module SPLL.Validator (
  validateProgram
) where
import SPLL.Lang.Types (Program(..))
import SPLL.Lang.Lang (Expr(..), getSubExprs, getFunctionNames)
import Control.Monad
import Data.Maybe (isJust, isNothing)
import PredefinedFunctions (globalFenv, parameterCount)

-- This function returns nothing if the program is valid and an error else
validateProgram :: Program -> Either String ()
-- We sequence the either monads so we either have a list of errors(Lefts) or discard the Rights
validateProgram p@Program{functions=fn, neurals=nurals} = sequence_ exprValidations
  where
    -- Validate all expressions potentially unsing the context of their top level declaration and their program
    exprValidations = concatMap (\(_, expr) -> validateAllSubexpressions p expr expr) fn
    -- All Results from all subexpressions
    validateAllSubexpressions :: Program -> Expr -> Expr -> [Either String ()]
    validateAllSubexpressions p topLevel expr = validateExpression p topLevel expr : concatMap (validateAllSubexpressions p topLevel) (getSubExprs expr)

validateExpression :: Program -> Expr -> Expr -> Either String ()
validateExpression _ _ (InjF _ name _) | isNothing (lookup name globalFenv) = Left ("Cannot find InjF: " ++ name)
validateExpression _ _ (InjF _ name params) | parameterCount name /= length params = Left("Wrong number of arguments for InjF " ++ name ++ "expected: " ++ show (parameterCount name) ++ " got: " ++ show (length params))
validateExpression _ _ (LetIn _ name val _) | declarationsCount name val > 0 = Left ("Duplicate declaration of identifier (Shawdowing is not allowed): " ++ name)
validateExpression _ _ (LetIn _ name _ body) | declarationsCount name body > 0 = Left ("Duplicate declaration of identifier (Shawdowing is not allowed): " ++ name)
validateExpression _ _ (LetIn _ name _ _) | isJust (lookup name globalFenv) = Left ("Identifier name is already used by an InjF: " ++ name)
validateExpression p _ (LetIn _ name _ _) | name `elem` getFunctionNames p = Left ("Identifier is already a function name: " ++ name)
validateExpression p topLevel (Var _ name) | usedBeforeDeclaration name topLevel && not (name `elem` getFunctionNames p) = Left ("Identifier is used without declaration: " ++ name)
validateExpression _ _ (Lambda _ name body) | declarationsCount name body > 0 = Left ("Duplicate declaration of identifier (Shawdowing is not allowed): " ++ name)
validateExpression _ _ (Lambda _ name body) | isJust (lookup name globalFenv) = Left ("Identifier name is already used by an InjF: " ++ name)
validateExpression p _ (Lambda _ name body) | name `elem` getFunctionNames p = Left ("Identifier is already a function name: " ++ name)
validateExpression _ _ _ = Right ()

declarationsCount :: String -> Expr -> Int
declarationsCount name (LetIn _ decl val body) | name == decl = 1 + declarationsCount name val + declarationsCount name body
declarationsCount name (Lambda _ lmd body) | name == lmd = 1 + declarationsCount name body
declarationsCount name expr = sum $ map (declarationsCount name) (getSubExprs expr)

-- Recursive descend, stops on declaration of the identifier. Returns true if usage is detected -> Must be undeclared, because stopping on declaration
usedBeforeDeclaration :: String -> Expr -> Bool
usedBeforeDeclaration name (LetIn _ decl _ _) | name == decl = False
usedBeforeDeclaration name (Lambda _ lmd _) | name == lmd = False
usedBeforeDeclaration name (Var _ v) | name == v = True
usedBeforeDeclaration name expr = any (usedBeforeDeclaration name) (getSubExprs expr)
