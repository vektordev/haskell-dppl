module SPLL.Typing.Witnessing (
  addWitnessesProg
, addWitnesses
) where

import SPLL.Lang.Lang
import SPLL.Typing.Typing
import SPLL.Typing.PType
import Data.List
import qualified Data.Set as Set
import Debug.Trace
-- TODO What about multiple let ins
addWitnessesProg :: Program -> Program
addWitnessesProg (Program funcs nns adts) = Program (zip (map fst funcs) (map (addWitnesses Set.empty. snd) funcs)) nns adts

addWitnesses :: Set.Set String -> Expr ->  Expr
addWitnesses _ (Var ti name) = Var (addWitnessTypeInfo name ti) name
addWitnesses _ (ThetaI ti a x) = ThetaI ti a x  -- TODO definately wrong. but sufficent as long as you dont do crazy things with thetas
addWitnesses _ (Subtree ti a x) = Subtree ti a x  -- TODO definately wrong. but sufficent as long as you dont do crazy things with thetas
addWitnesses _ (Normal ti) = Normal ti
addWitnesses _ (Uniform ti) = Uniform ti
addWitnesses _ (Constant ti x) = Constant ti x
addWitnesses witVars (InjF ti f_name params) = InjF ti f_name paramExprs
  where paramExprs = map (addWitnesses witVars) params  -- TODO In some cases some variables can be witnessed
addWitnesses witVars (LetIn ti var_name decl expr)
  | ptDecl == Deterministic = LetIn tiWitNoVar var_name witDecl witExpr
  | var_name `elem` witnessedVars (getTypeInfo witExpr) = LetIn tiWitNoVar var_name witDecl (addWitnesses (Set.insert var_name witVars) expr)
  | otherwise = LetIn tiWitNoVarBottom var_name witDecl witExpr
  where
        tiWit = getTypeInfo witExpr
        wit_vars = witnessedVars $ getTypeInfo witExpr
        ptDecl = pType $ getTypeInfo decl
        witDecl = addWitnesses witVars decl
        witExpr = addWitnesses witVars expr
        tiWitNoVar = setWitnessedVars tiWit (Set.delete var_name wit_vars)
        tiWitNoVarBottom = setPType (setWitnessedVars tiWit (Set.delete var_name wit_vars)) Bottom
addWitnesses witVars (IfThenElse ti cond tr fl) =
  IfThenElse (setWitnessedVars ti wits) condW trW flW
  -- TODO What if we dont witness a variable in a branch but its also not used? let x = normal in if flip then x else normal
  where (condW, trW, flW) = (addWitnesses witVars cond, addWitnesses witVars tr, addWitnesses witVars fl)
        wits = Set.difference (Set.intersection (witnessedVars $ getTypeInfo trW)(witnessedVars $ getTypeInfo flW)) (containedVars varsOfExpr cond)
addWitnesses witVars (GreaterThan ti e1 e2) =
  GreaterThan ti (addWitnesses witVars e1) (addWitnesses witVars e2)
addWitnesses _ (Null ti) = Null ti
addWitnesses witVars (Cons t fst rst) = Cons (setWitnessedVars t comp) witFst witRst
  where witFst = addWitnesses witVars fst
        witRst = addWitnesses witVars rst
        comp = composeWitnessed (getTypeInfo witFst) (getTypeInfo witRst)

addWitnesses witVars (TCons t fst rst) = TCons (setWitnessedVars t comp) witFst witRst
  where witFst = addWitnesses witVars fst
        witRst = addWitnesses witVars rst
        comp = composeWitnessed (getTypeInfo witFst) (getTypeInfo witRst)

addWitnessTypeInfo :: String -> TypeInfo -> TypeInfo
addWitnessTypeInfo a t = setWitnessedVars t (Set.insert a (witnessedVars t))

composeWitnessed :: TypeInfo -> TypeInfo -> WitnessedVars
composeWitnessed t1 t2 = Set.union (witnessedVars t1) (witnessedVars t2)