module SPLL.Typing.Witnessing (
  addWitnessesProg
, addWitnesses
) where

import SPLL.Lang
import SPLL.Typing.Typing
import SPLL.Typing.PType
import Data.List
import qualified Data.Set as Set
import Debug.Trace
-- TODO What about multiple let ins
addWitnessesProg :: (Show a) => Program TypeInfo a -> Program TypeInfoWit a
addWitnessesProg (Program [] expr) = Program [] (addWitnesses Set.empty expr)
addWitnessesProg (Program funcs expr) = Program (zip (map fst funcs) (map (addWitnesses Set.empty. snd) funcs))
 (addWitnesses Set.empty expr)

addWitnesses :: (Show a) => Set.Set String -> Expr TypeInfo a ->  Expr TypeInfoWit a
addWitnesses _ (Var ti name) = Var (addWitnessTypeInfo name (createWTypeInfo ti)) name
addWitnesses _ (ThetaI ti x) = ThetaI (createWTypeInfo ti) x
addWitnesses _ (Normal ti) = Normal (createWTypeInfo ti)
addWitnesses _ (Uniform ti) = Uniform (createWTypeInfo ti)
addWitnesses _ (Constant ti x) = Constant (createWTypeInfo ti) x
addWitnesses witVars (InjF ti f_name params) = InjF (createWTypeInfo ti) f_name paramExprs
  where paramExprs = map (addWitnesses witVars) params  -- TODO In some cases some variables can be witnessed
addWitnesses witVars (PlusF ti expr1 expr2)
  | pt1 == Deterministic && null wit1 = PlusF (getTypeInfo witExpr2) witExpr1 witExpr2
  | pt2 == Deterministic && null wit2 = PlusF (getTypeInfo witExpr1) witExpr1 witExpr2
  | otherwise = PlusF (createWTypeInfo ti) witExpr1 witExpr2
  where
      (TypeInfoWit _ pt1 wit1) = getTypeInfo witExpr1
      (TypeInfoWit _ pt2 wit2) = getTypeInfo witExpr2
      witExpr1 = addWitnesses witVars expr1 
      witExpr2 = addWitnesses witVars expr2
addWitnesses witVars (PlusI ti expr1 expr2)
  | pt1 == Deterministic && null wit1 = PlusI (getTypeInfo witExpr2) witExpr1 witExpr2
  | pt2 == Deterministic && null wit2 = PlusI (getTypeInfo witExpr1) witExpr1 witExpr2
  | otherwise = PlusI (createWTypeInfo ti) witExpr1 witExpr2
  where
      (TypeInfoWit _ pt1 wit1) = getTypeInfo witExpr1
      (TypeInfoWit _ pt2 wit2) = getTypeInfo witExpr2
      witExpr1 = addWitnesses witVars expr1
      witExpr2 = addWitnesses witVars expr2
addWitnesses witVars (MultF ti expr1 expr2)
  | pt1 == Deterministic && null wit1 = MultF (getTypeInfo witExpr2) witExpr1 witExpr2
  | pt2 == Deterministic && null wit2 = MultF (getTypeInfo witExpr1) witExpr1 witExpr2
  | otherwise = MultF (createWTypeInfo ti) witExpr1 witExpr2
  where
      (TypeInfoWit _ pt1 wit1) = getTypeInfo witExpr1
      (TypeInfoWit _ pt2 wit2) = getTypeInfo witExpr2
      witExpr1 = addWitnesses witVars expr1
      witExpr2 = addWitnesses witVars expr2
addWitnesses witVars (MultI ti expr1 expr2)
  | pt1 == Deterministic && null wit1 = MultI (getTypeInfo witExpr2) witExpr1 witExpr2
  | pt2 == Deterministic && null wit2 = MultI (getTypeInfo witExpr1) witExpr1 witExpr2
  | otherwise = MultI (createWTypeInfo ti) witExpr1 witExpr2
  where
      (TypeInfoWit _ pt1 wit1) = getTypeInfo witExpr1
      (TypeInfoWit _ pt2 wit2) = getTypeInfo witExpr2
      witExpr1 = addWitnesses witVars expr1
      witExpr2 = addWitnesses witVars expr2
addWitnesses witVars (ExpF (TypeInfo rt pt) f) = ExpF (TypeInfoWit rt pt fVars) witF
  where witF = addWitnesses witVars f
        (TypeInfoWit _ _ fVars) = getTypeInfo witF
addWitnesses witVars (NegF (TypeInfo rt pt) f) = NegF (TypeInfoWit rt pt fVars) witF
  where witF = addWitnesses witVars f
        (TypeInfoWit _ _ fVars) = getTypeInfo witF
addWitnesses witVars (LetIn ti@(TypeInfo _ pt) var_name decl expr) 
  | ptDecl == Deterministic = LetIn tiWitNoVar var_name witDecl witExpr
  | var_name `elem` getWitsW witExpr = LetIn tiWitNoVar var_name witDecl (addWitnesses (Set.insert var_name witVars) expr)
  | otherwise = LetIn tiWitNoVarBottom var_name witDecl witExpr
  where
        (TypeInfoWit rt ptE wit_vars) = getTypeInfo witExpr
        (TypeInfo rtDecl ptDecl) = getTypeInfo decl
        witDecl = addWitnesses witVars decl
        witExpr = addWitnesses witVars expr
        tiWitNoVar = TypeInfoWit rt ptE (Set.delete var_name wit_vars)
        tiWitNoVarBottom = TypeInfoWit rt Bottom (Set.delete var_name wit_vars)
addWitnesses witVars (IfThenElse ti cond tr fl) =
  IfThenElse (setWits (createWTypeInfo ti) wits) condW trW flW
  -- TODO What if we dont witness a variable in a branch but its also not used? let x = normal in if flip then x else normal
  where (condW, trW, flW) = (addWitnesses witVars cond, addWitnesses witVars tr, addWitnesses witVars fl)
        wits = Set.difference (Set.intersection (getWitsW trW)(getWitsW flW)) (containedVars varsOfExpr cond)
addWitnesses witVars (GreaterThan ti e1 e2) =
  GreaterThan (createWTypeInfo ti) (addWitnesses witVars e1) (addWitnesses witVars e2)
addWitnesses _ (Call ti f) =
  Call (createWTypeInfo ti) f
addWitnesses _ (Null ti) = Null (createWTypeInfo ti)
addWitnesses witVars (Cons (TypeInfo rt pt) fst rst) = Cons (TypeInfoWit rt pt comp) witFst witRst
  where witFst = addWitnesses witVars fst
        witRst = addWitnesses witVars rst
        comp = composeWitnessed (getTypeInfo witFst) (getTypeInfo witRst)

addWitnesses witVars (TCons (TypeInfo rt pt) fst rst) = TCons (TypeInfoWit rt pt comp) witFst witRst
  where witFst = addWitnesses witVars fst
        witRst = addWitnesses witVars rst
        comp = composeWitnessed (getTypeInfo witFst) (getTypeInfo witRst)

createWTypeInfo :: TypeInfo -> TypeInfoWit
createWTypeInfo (TypeInfo rt pt) = TypeInfoWit rt pt Set.empty

addWitnessTypeInfo :: String -> TypeInfoWit ->  TypeInfoWit
addWitnessTypeInfo a (TypeInfoWit rt pt wits) = TypeInfoWit rt pt (Set.insert a wits)

composeWitnessed :: TypeInfoWit -> TypeInfoWit -> WitnessedVars
composeWitnessed (TypeInfoWit rt1 pt1 wits1)(TypeInfoWit rt2 pt2 wits2) = Set.union wits1 wits2