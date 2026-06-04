module SPLL.Validator (
  validateProgram
) where
import SPLL.Lang.Types (Program(..), GenericValue(..))
import SPLL.Lang.Lang (Expr(..), getSubExprs, getFunctionNames, InjFName(..))
import Control.Monad
import Data.Maybe (isJust, isNothing)
import PredefinedFunctions (globalFEnv, parameterCount)
import Data.List (intersect)

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
validateExpression Program {adts=adts} _ (InjF _ (Named name) _) | isNothing (lookup name (globalFEnv adts)) = Left ("Cannot find InjF: " ++ name)
validateExpression Program {adts=adts} _ (InjF _ (Named name) params) | parameterCount adts name /= length params = Left("Wrong number of arguments for InjF " ++ name ++ "expected: " ++ show (parameterCount adts name) ++ " got: " ++ show (length params))
validateExpression p topLevel (Var _ name) | usedBeforeDeclaration name topLevel && notElem name (getFunctionNames p) = Left ("Identifier is used without declaration: " ++ name)
validateExpression _ _ (Lambda _ name body) | declarationsCount name body > 0 = Left ("Duplicate declaration of identifier (Shawdowing is not allowed): " ++ name)
validateExpression Program {adts=adts} _ (Lambda _ name body) | isJust (lookup name (globalFEnv adts)) = Left ("Identifier name is already used by an InjF: " ++ name)
validateExpression p _ (Lambda _ name body) | name `elem` getFunctionNames p = Left ("Identifier is already a function name: " ++ name)
validateExpression p _ (Apply _ l v) | not (null (declaredVariables l `intersect` declaredVariables v)) = Left ("Identifiers " ++ show (declaredVariables l `intersect` declaredVariables v) ++ " are possibly declared multiple times")
validateExpression _ _ (Constant _ VAny) = Left "ANY may not be used in program declaration"
validateExpression _ _ _ = Right ()

declarationsCount :: String -> Expr -> Int
declarationsCount name (Lambda _ lmd body) | name == lmd = 1 + declarationsCount name body
declarationsCount name expr = sum $ map (declarationsCount name) (getSubExprs expr)

-- Recursive descend, stops on declaration of the identifier. Returns true if usage is detected -> Must be undeclared, because stopping on declaration
usedBeforeDeclaration :: String -> Expr -> Bool
usedBeforeDeclaration name (Lambda _ lmd _) | name == lmd = False
usedBeforeDeclaration name (Var _ v) | name == v = True
usedBeforeDeclaration name expr = any (usedBeforeDeclaration name) (getSubExprs expr)

declaredVariables :: Expr -> [String]
declaredVariables (Lambda _ name body) = name:declaredVariables body
declaredVariables x = concatMap declaredVariables (getSubExprs x)
