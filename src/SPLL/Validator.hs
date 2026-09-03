module SPLL.Validator (
  validateProgram
) where
import SPLL.Lang.Types (Program(..), GenericValue(..), FnDecl, NeuralDecl, MultiValue)
import SPLL.Lang.Lang (Expr(..), ExprF(..), getSubExprs, getFunctionNames, InjFName(..))
import SPLL.Typing.RType (RType(..))
import Data.Maybe (isJust, isNothing)
import PredefinedFunctions (globalFEnv, parameterCount)
import Data.List (intersect, groupBy, sortOn, nub)
import Data.Function (on)

-- Reserved Var names bound to prelude-primitive distributions; not user declarations.
distributionPrimitiveNames :: [String]
distributionPrimitiveNames = ["Uniform", "Normal"]

-- This function returns nothing if the program is valid and an error else
validateProgram :: Program -> Either String ()
-- We sequence the either monads so we either have a list of errors(Lefts) or discard the Rights
validateProgram p@Program{functions=fn, neurals=nrls, writeLogitsDecls=enc} = sequence_ (validateMainExists fn : validateWriteLogitsDecls enc : map validateNeuralShape nrls ++ exprValidations)
  where
    -- Validate all expressions potentially unsing the context of their top level declaration and their program
    exprValidations = concatMap (\(_, expr) -> validateAllSubexpressions p expr expr) fn
    -- All Results from all subexpressions
    validateAllSubexpressions :: Program -> Expr -> Expr -> [Either String ()]
    validateAllSubexpressions prog topLevel expr = validateExpression prog topLevel expr : concatMap (validateAllSubexpressions prog topLevel) (getSubExprs expr)

-- | The PartitionPlan annotation registry (explicit "neural writeLogits :: T of M"
-- declarations, plus sugar from every NeuralDecl's "of" clause) may register a given
-- RType at most once: two differing MultiValue annotations for the same type is a
-- loud, hard error. Identical re-registrations (e.g. a read-logits network's own "of" clause
-- agreeing with an explicit "neural writeLogits" entry for the same type) are not a conflict.
validateWriteLogitsDecls :: [(RType, MultiValue)] -> Either String ()
validateWriteLogitsDecls decls = mapM_ checkGroup grouped
  where
    grouped = groupBy ((==) `on` fst) (sortOn fst decls)
    checkGroup g = case nub (map snd g) of
      (_:_:_) -> Left ("Compiler Error: conflicting PartitionPlan annotations for type "
                        ++ show (fst (head g)) ++ ": " ++ show (map snd g))
      _ -> Right ()

-- | A neural declaration forward-declares the read-logits network (Symbol -> target): NN1,
-- whose logits SPLL reads. The reverse (source -> Symbol) shape used to name a second,
-- external network (NN2) with no SPLL call site; that role has been removed, and the
-- logit-vector bridge it tried to host now lives on the value-producing SPLL function
-- instead. Reject the reverse shape with a pointer at the registry syntax that covers the
-- only job it still had (registering a type's logit layout).
validateNeuralShape :: NeuralDecl -> Either String ()
validateNeuralShape (_, TArrow TSymbol _, _) = Right ()
validateNeuralShape (name, TArrow _ TSymbol, _) =
  Left ("Compiler Error: neural declaration '" ++ name ++ "' has the form (source -> Symbol), "
        ++ "which is no longer supported. To register a logit layout "
        ++ "for a type, write `neural writeLogits :: <type> of <multivalue>`; the logit vector for a "
        ++ "value is generated on the SPLL function that produces it.")
validateNeuralShape (name, ty, _) =
  Left ("Compiler Error: neural declaration '" ++ name ++ "' has type " ++ show ty
        ++ ", but neural declarations must have the form (Symbol -> target).")

-- A program must declare a "main" function, as it is the entry point compiled
-- to the generate/probability/integrate functions invoked by runGen/runProb/runInteg.
validateMainExists :: [FnDecl] -> Either String ()
validateMainExists fn
  | "main" `elem` map fst fn = Right ()
  | otherwise = Left "Compiler Error: Program has no 'main' function defined."

validateExpression :: Program -> Expr -> Expr -> Either String ()
validateExpression Program {adts=adtsDecl} _ (Expr _ (InjF (Named name) _)) | isNothing (lookup name (globalFEnv adtsDecl)) = Left ("Cannot find InjF: " ++ name)
validateExpression Program {adts=adtsDecl} _ (Expr _ (InjF (Named name) params)) | parameterCount adtsDecl name /= length params = Left("Wrong number of arguments for InjF " ++ name ++ "expected: " ++ show (parameterCount adtsDecl name) ++ " got: " ++ show (length params))
validateExpression _ _ (Expr _ (Var name)) | name `elem` distributionPrimitiveNames = Right ()
validateExpression p topLevel (Expr _ (Var name)) | usedBeforeDeclaration name topLevel && notElem name (getFunctionNames p) = Left ("Identifier is used without declaration: " ++ name)
validateExpression _ _ (Expr _ (Lambda name body)) | declarationsCount name body > 0 = Left ("Duplicate declaration of identifier (Shawdowing is not allowed): " ++ name)
validateExpression Program {adts=adtsDecl} _ (Expr _ (Lambda name _)) | isJust (lookup name (globalFEnv adtsDecl)) = Left ("Identifier name is already used by an InjF: " ++ name)
validateExpression p _ (Expr _ (Lambda name _)) | name `elem` getFunctionNames p = Left ("Identifier is already a function name: " ++ name)
validateExpression _ _ (Expr _ (Apply l v)) | not (null (declaredVariables l `intersect` declaredVariables v)) = Left ("Identifiers " ++ show (declaredVariables l `intersect` declaredVariables v) ++ " are possibly declared multiple times")
validateExpression _ _ (Expr _ (Constant VAny)) = Left "ANY may not be used in program declaration"
validateExpression _ _ _ = Right ()

declarationsCount :: String -> Expr -> Int
declarationsCount name (Expr _ (Lambda lmd body)) | name == lmd = 1 + declarationsCount name body
declarationsCount name expr = sum $ map (declarationsCount name) (getSubExprs expr)

-- Recursive descend, stops on declaration of the identifier. Returns true if usage is detected -> Must be undeclared, because stopping on declaration
usedBeforeDeclaration :: String -> Expr -> Bool
usedBeforeDeclaration name (Expr _ (Lambda lmd _)) | name == lmd = False
usedBeforeDeclaration name (Expr _ (Var v)) | name == v = True
usedBeforeDeclaration name expr = any (usedBeforeDeclaration name) (getSubExprs expr)

declaredVariables :: Expr -> [String]
declaredVariables (Expr _ (Lambda name body)) = name:declaredVariables body
declaredVariables x = concatMap declaredVariables (getSubExprs x)
