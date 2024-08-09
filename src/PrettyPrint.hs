module PrettyPrint where

import SPLL.Lang
import Data.List (intercalate)

pPrintProg :: (Show a) => Program t a -> String
pPrintProg (Program decls main) = intercalate "\n\n" (map (\f -> wrapInFunctionDeclaration (snd f) (fst f) []) env)
  where env = ("main", main):decls

wrapInFunctionDeclaration :: (Show a) => Expr t a -> String -> [String] -> String
wrapInFunctionDeclaration (Lambda _ n b) fName params = wrapInFunctionDeclaration b fName (n:params)
wrapInFunctionDeclaration e fName params = "def " ++ fName ++ "(" ++ intercalate ", " params ++ "):\n" ++ indent 1 ++ pPrintExpr e 1 ++"\n"

pPrintExpr :: (Show a) => Expr t a -> Int -> String
pPrintExpr (LetIn _ n v b) i = "let " ++ n ++ " = " ++ pPrintExpr v (i+1) ++ " in\n" ++ indent (i+1) ++ pPrintExpr b (i+1)
pPrintExpr (PlusF _ a b) i = "(" ++ pPrintExpr a i ++ " + " ++ pPrintExpr b i ++ ")"
pPrintExpr (PlusI _ a b) i = "(" ++ pPrintExpr a i ++ " + " ++ pPrintExpr b i ++ ")"
pPrintExpr (MultF _ a b) i = "(" ++ pPrintExpr a i ++ " * " ++ pPrintExpr b i ++ ")"
pPrintExpr (MultI _ a b) i = "(" ++ pPrintExpr a i ++ " * " ++ pPrintExpr b i ++ ")"
pPrintExpr (Constant _ a) _ = pPrintValue a
pPrintExpr (Var _ a) _ = a
pPrintExpr (Uniform _) _ = "Uniform"
pPrintExpr (Normal _) _ = "Normal"
pPrintExpr (IfThenElse _ c t e) i = "if " ++ pPrintExpr c i ++ " then\n" ++ indent (i+1) ++ pPrintExpr t (i+1) ++"\n" ++ indent i ++ "else\n" ++ indent (i+1) ++ pPrintExpr e (i+1)
pPrintExpr (Call _ f) _ = f ++ "()"
pPrintExpr (CallArg _ f args) i = f ++ "(" ++ intercalate ", " (map (`pPrintExpr` i) args) ++ ")"
pPrintExpr (InjF _ f args) i = f ++ "(" ++ intercalate ", " (map (`pPrintExpr` i) args) ++ ")"
pPrintExpr (ExpF _ e) i = "exp(" ++ pPrintExpr e i ++ ")"
pPrintExpr (NegF _ e) i =  "-(" ++ pPrintExpr e i ++ ")"
pPrintExpr (Lambda _ n e) i = "\\" ++ n ++ " -> " ++ pPrintExpr e (i+1)
pPrintExpr (Apply _ f v) i = pPrintExpr f i ++ "(" ++ pPrintExpr v i ++ ")"
pPrintExpr (ThetaI _ e n) i = "Theta_" ++ show n ++ "(" ++ pPrintExpr e i ++ ")"
pPrintExpr (Subtree _ e n) i = "Subtree_" ++ show n ++ "(" ++ pPrintExpr e i ++ ")"
pPrintExpr (Cons _ h t) i = pPrintExpr h i ++ " : " ++ pPrintExpr t i
pPrintExpr (TCons _ h t) i = "(" ++ pPrintExpr h i ++ ", " ++ pPrintExpr t i ++ ")"
pPrintExpr (Null _) _ = "null"
pPrintExpr (GreaterThan _ a b) i = "(" ++ pPrintExpr a i ++ " > " ++ pPrintExpr b i ++ ")"
pPrintExpr (LessThan _ a b) i = "(" ++ pPrintExpr a i ++ " < " ++ pPrintExpr b i ++ ")"
pPrintExpr (And _ a b) i = "(" ++ pPrintExpr a i ++ " && " ++ pPrintExpr b i ++ ")"
pPrintExpr (Or _ a b) i = "(" ++ pPrintExpr a i ++ " || " ++ pPrintExpr b i ++ ")"
pPrintExpr (Not _ e) i = "!(" ++ pPrintExpr e i ++ ")"
pPrintExpr (Arg _ n t e) i = n ++ ": " ++ show t ++ " = " ++ pPrintExpr e i
pPrintExpr (ReadNN _ n e) i = "readNN(" ++ n ++ ", " ++ pPrintExpr e i ++ ")"
pPrintExpr (Fix _ e) i = "fix(" ++ pPrintExpr e i ++ ")"


pPrintValue :: (Show a) => Value a -> String
pPrintValue (VBool a) = show a
pPrintValue (VFloat a) = show a
pPrintValue (VList xs) = "[" ++ intercalate "," (map pPrintValue xs) ++ "]"
pPrintValue (VTuple a b) = "(" ++ pPrintValue a ++ ", " ++ pPrintValue b ++ ")"
pPrintValue (VInt a) = show a
pPrintValue (VSymbol a) = a

indent :: Int -> String
indent n = replicate (2 * n) ' '