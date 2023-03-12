module Witnessing where

import SPLL.Lang
import SPLL.Typing.Typing
import SPLL.Typing.PType
import Data.List
import qualified Data.Set as Set
-- TODO What about multiple let ins
addWitnessesProg :: Program TypeInfo a -> Program TypeInfoWit a
addWitnessesProg (Program [] expr) = Program [] (addWitnesses expr)
addWitnessesProg (Program funcs expr) = Program (zip (map fst funcs) (map (addWitnesses . snd) funcs))
 (addWitnesses expr)
addWitnesses :: Expr TypeInfo a -> Expr TypeInfoWit a
addWitnesses (Var ti name) = Var (addWitnessTypeInfo name (createWTypeInfo ti)) name
addWitnesses (ThetaI ti x) = ThetaI (createWTypeInfo ti) x
addWitnesses (Normal ti) = Normal (createWTypeInfo ti)
addWitnesses (Uniform ti) = Uniform (createWTypeInfo ti)
addWitnesses (Constant ti x) = Constant (createWTypeInfo ti) x
addWitnesses (InjF ti f_name params expr) = InjF (setWits (createWTypeInfo ti) wits) f_name paramExprs witExpr
  where witExpr = addWitnesses expr
        paramExprs = map addWitnesses params
        wits = getWitsW witExpr
addWitnesses (Plus ti expr1 expr2)
  | pt1 == Deterministic && null wit1 = Plus (getTypeInfo witExpr2) witExpr1 witExpr2
  | pt2 == Deterministic && null wit2 = Plus (getTypeInfo witExpr1) witExpr1 witExpr2
  | otherwise = Plus (createWTypeInfo ti) witExpr1 witExpr2
  where
      (TypeInfoWit _ pt1 wit1) = getTypeInfo witExpr1
      (TypeInfoWit _ pt2 wit2) = getTypeInfo witExpr2
      witExpr1 = addWitnesses expr1
      witExpr2 = addWitnesses expr2
addWitnesses (Mult ti expr1 expr2)
  | pt1 == Deterministic && null wit1 = Mult (getTypeInfo witExpr2) witExpr1 witExpr2
  | pt2 == Deterministic && null wit2 = Mult (getTypeInfo witExpr1) witExpr1 witExpr2
  | otherwise = Mult (createWTypeInfo ti) witExpr1 witExpr2
  where
      (TypeInfoWit _ pt1 wit1) = getTypeInfo witExpr1
      (TypeInfoWit _ pt2 wit2) = getTypeInfo witExpr2
      witExpr1 = addWitnesses expr1
      witExpr2 = addWitnesses expr2

addWitnesses (LetIn ti@(TypeInfo _ pt) var_name decl expr) 
  | ptDecl == Deterministic = LetIn tiWitNoVar var_name witDecl witExpr
  | var_name `elem` getWitsW witExpr = LetIn tiWitNoVar var_name witDecl witExpr
  | otherwise = LetIn tiWitNoVarBottom var_name witDecl witExpr
  where
        (TypeInfoWit rt ptE wit_vars) = getTypeInfo witExpr
        (TypeInfo rtDecl ptDecl) = getTypeInfo decl
        witDecl = addWitnesses decl
        witExpr = addWitnesses expr
        tiWitNoVar = TypeInfoWit rt ptE (Set.delete var_name wit_vars)
        tiWitNoVarBottom = TypeInfoWit rt Bottom (Set.delete var_name wit_vars)
addWitnesses (IfThenElse ti cond tr fl) =
  IfThenElse (setWits (createWTypeInfo ti) wits) condW trW flW
  -- TODO What if we dont witness a variable in a branch but its also not used? let x = normal in if flip then x else normal
  where (condW, trW, flW) = (addWitnesses cond, addWitnesses tr, addWitnesses fl)
        wits = Set.difference (Set.intersection (getWitsW trW)(getWitsW flW)) (containedVars varsOfExpr cond)
addWitnesses (GreaterThan ti e1 e2) =
  GreaterThan (createWTypeInfo ti) (addWitnesses e1) (addWitnesses e2)
addWitnesses (Call ti f) =
  Call (createWTypeInfo ti) f
addWitnesses (Null ti) = Null (createWTypeInfo ti)
addWitnesses (TNull ti) = TNull (createWTypeInfo ti)
addWitnesses (Cons (TypeInfo rt pt) fst rst) = Cons (TypeInfoWit rt pt comp) witFst witRst
  where witFst = addWitnesses fst
        witRst = addWitnesses rst
        comp = composeWitnessed (getTypeInfo witFst) (getTypeInfo witRst)

addWitnesses (TCons (TypeInfo rt pt) fst rst) = TCons (TypeInfoWit rt pt comp) witFst witRst
  where witFst = addWitnesses fst
        witRst = addWitnesses rst
        comp = composeWitnessed (getTypeInfo witFst) (getTypeInfo witRst)

createWTypeInfo :: TypeInfo -> TypeInfoWit
createWTypeInfo (TypeInfo rt pt) = TypeInfoWit rt pt Set.empty

addWitnessTypeInfo :: String -> TypeInfoWit ->  TypeInfoWit
addWitnessTypeInfo a (TypeInfoWit rt pt wits) = TypeInfoWit rt pt (Set.insert a wits)

composeWitnessed :: TypeInfoWit -> TypeInfoWit -> WitnessedVars
composeWitnessed (TypeInfoWit rt1 pt1 wits1)(TypeInfoWit rt2 pt2 wits2) = Set.union wits1 wits2