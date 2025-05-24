module PrettyPrint where

import SPLL.Lang.Lang
import Data.List (intercalate)
import SPLL.IntermediateRepresentation
import SPLL.Lang.Types
import Data.Foldable
import Data.Functor ((<&>))
import Data.Maybe (catMaybes)

pPrintProg :: Program -> String
pPrintProg (Program decls neurals adts) = intercalate "\n\n" (map (\f -> wrapInFunctionDeclaration (snd f) (fst f) []) decls)

pPrintIREnv :: IREnv -> String
pPrintIREnv env = intercalate "\n\n" (concatMap (\(IRFunGroup name gen prob integ doc) -> catMaybes [Just (wrapDecl name "_gen" gen), prob <&> wrapDecl name "_prob", integ <&> wrapDecl name "_integ"]) env)
    where wrapDecl name suffix (expr, doc) = wrapInFunctionDeclarationIR expr (name ++ suffix) doc []

wrapInFunctionDeclaration :: Expr -> String -> [String] -> String
wrapInFunctionDeclaration (Lambda _ n b) fName params = wrapInFunctionDeclaration b fName (n:params)
wrapInFunctionDeclaration e fName params = "def " ++ fName ++ "(" ++ intercalate ", " (reverse params) ++ "):\n" ++ indent 1 ++ pPrintExpr e 1 ++"\n"

wrapInFunctionDeclarationIR :: IRExpr -> String -> String -> [String] -> String
wrapInFunctionDeclarationIR (IRLambda n b) fName doc params = wrapInFunctionDeclarationIR b fName doc (n:params)
wrapInFunctionDeclarationIR e fName doc params = "-- " ++ doc ++ "\ndef " ++ fName ++ "(" ++ intercalate ", " params ++ "):\n" ++ indent 1 ++ pPrintIRExpr e 1 ++"\n"

pPrintExpr :: Expr -> Int -> String
pPrintExpr (LetIn _ n v b) i = "let " ++ n ++ " = " ++ pPrintExpr v (i+1) ++ " in\n" ++ indent (i+1) ++ pPrintExpr b (i+1)
pPrintExpr (Constant _ a) _ = pPrintValue a
pPrintExpr (Var _ a) _ = a
pPrintExpr (Uniform _) _ = "Uniform"
pPrintExpr (Normal _) _ = "Normal"
pPrintExpr (IfThenElse _ c t e) i = "if " ++ pPrintExpr c i ++ " then\n" ++ indent (i+1) ++ pPrintExpr t (i+1) ++"\n" ++ indent i ++ "else\n" ++ indent (i+1) ++ pPrintExpr e (i+1)
pPrintExpr (InjF _ f args) i = f ++ "(" ++ intercalate ", " (map (`pPrintExpr` i) args) ++ ")"
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
pPrintExpr (ReadNN _ n e) i = "readNN(" ++ n ++ ", " ++ pPrintExpr e i ++ ")"

pPrintIRExpr :: IRExpr -> Int -> String
pPrintIRExpr (IRIf cond thenExpr elseExpr) n =
    "\n" ++ indent n ++ "if " ++ pPrintIRExpr cond (n + 1) ++ " then\n" ++
    indent (n + 1) ++ pPrintIRExpr thenExpr (n + 1) ++ "\n" ++
    indent n ++ "else\n" ++
     indent (n + 1) ++ pPrintIRExpr elseExpr (n + 1)
pPrintIRExpr (IROp OpPlus e1 e2) n = "(" ++ pPrintIRExpr e1 (n + 1) ++ " + " ++ pPrintIRExpr e2 (n + 1) ++ ")"
pPrintIRExpr (IROp OpSub e1 e2) n = "(" ++ pPrintIRExpr e1 (n + 1) ++ " - " ++ pPrintIRExpr e2 (n + 1) ++ ")"
pPrintIRExpr (IROp OpMult e1 e2) n = "(" ++ pPrintIRExpr e1 (n + 1) ++ " * " ++ pPrintIRExpr e2 (n + 1) ++ ")"
pPrintIRExpr (IROp OpDiv e1 e2) n = "(" ++ pPrintIRExpr e1 (n + 1) ++ " / " ++ pPrintIRExpr e2 (n + 1) ++ ")"
pPrintIRExpr (IROp OpGreaterThan e1 e2) n = "(" ++ pPrintIRExpr e1 (n + 1) ++ " > " ++ pPrintIRExpr e2 (n + 1) ++ ")"
pPrintIRExpr (IROp OpLessThan e1 e2) n = "(" ++ pPrintIRExpr e1 (n + 1) ++ " < " ++ pPrintIRExpr e2 (n + 1) ++ ")"
pPrintIRExpr (IROp OpEq e1 e2) n = "(" ++ pPrintIRExpr e1 (n + 1) ++ " == " ++ pPrintIRExpr e2 (n + 1) ++ ")"
pPrintIRExpr (IROp OpOr e1 e2) n = "(" ++ pPrintIRExpr e1 (n + 1) ++ " || " ++ pPrintIRExpr e2 (n + 1) ++ ")"
pPrintIRExpr (IROp OpAnd e1 e2) n = "(" ++ pPrintIRExpr e1 (n + 1) ++ " && " ++ pPrintIRExpr e2 (n + 1) ++ ")"
pPrintIRExpr (IRUnaryOp OpNeg e) n = "-(" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRUnaryOp OpAbs e) n = "abs(" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRUnaryOp OpNot e) n = "!(" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRUnaryOp OpExp e) n = "(e^(" ++ pPrintIRExpr e (n + 1) ++ "))"
pPrintIRExpr (IRUnaryOp OpLog e) n = "log(" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRUnaryOp OpSign e) n = "sign(" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRUnaryOp OpIsAny e) n = "isAny(" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRTheta e i) n = "theta (" ++ pPrintIRExpr e (n + 1) ++ ")@" ++ show i
pPrintIRExpr (IRSubtree e i) n = "subtree (" ++ pPrintIRExpr e (n + 1) ++ ")@" ++ show i
pPrintIRExpr (IRConst val) n = "const " ++ show val
pPrintIRExpr (IRCons e1 e2) n = pPrintIRExpr e1 (n + 1) ++ ":" ++ pPrintIRExpr e2 (n + 1)
pPrintIRExpr (IRTCons e1 e2) n = "(" ++ pPrintIRExpr e1 (n + 1) ++ ", " ++ pPrintIRExpr e2 (n + 1) ++ ")"
pPrintIRExpr (IRHead e) n = "head (" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRTail e) n = "tail (" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRElementOf e lst) n = "(" ++ pPrintIRExpr e (n + 1) ++ ") in (" ++ pPrintIRExpr lst (n + 1) ++ ")"
pPrintIRExpr (IRTFst e) n = "fst (" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRTSnd e) n = "snd (" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRLeft e) n = "left (" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRRight e) n = "right (" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRFromLeft e) n = "fromLeft (" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRFromRight e) n = "fromRight (" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRIsLeft e) n = "isLeft (" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRIsRight e) n = "isRight (" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRDensity dist e) n = "density " ++ show dist ++ " (" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRCumulative dist e) n = "cumulative " ++ show dist ++ " (" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRSample dist) n = "sample " ++ show dist
pPrintIRExpr (IRLetIn varname e1 e2) n = "let " ++ varname ++ " = (" ++ pPrintIRExpr e1 (n + 1) ++ ") in \n" ++ indent (n + 1) ++ pPrintIRExpr e2 (n + 2) ++ ""
pPrintIRExpr (IRVar varname) n = varname
pPrintIRExpr (IRLambda varname body) n = "\\" ++ varname ++ " -> (" ++ pPrintIRExpr body (n + 1) ++ ")"
pPrintIRExpr (IRApply e1 e2) n = pPrintIRExpr e1 (n + 1) ++ "(" ++ pPrintIRExpr e2 (n + 1) ++ ")"
pPrintIRExpr (IRInvoke expr) n = pPrintIRExpr expr (n + 1) ++ "()"
pPrintIRExpr (IREnumSum varname val e) n = "enumSum " ++ varname ++ " = " ++ show val ++ " in (\n" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IREvalNN netName e) n = "evalNN " ++ netName ++ " (" ++ pPrintIRExpr e (n + 1) ++ ")"
pPrintIRExpr (IRIndex e1 e2) n = "(" ++ pPrintIRExpr e1 (n + 1) ++ ")[" ++ pPrintIRExpr e2 (n + 1) ++ "]"


pPrintValue :: Value -> String
pPrintValue (VBool a) = show a
pPrintValue (VFloat a) = show a
pPrintValue (VList xs) = "[" ++ intercalate "," (map pPrintValue (toList xs)) ++ "]"
pPrintValue (VTuple a b) = "(" ++ pPrintValue a ++ ", " ++ pPrintValue b ++ ")"
pPrintValue (VInt a) = show a
pPrintValue (VSymbol a) = a

indent :: Int -> String
indent n = replicate (2 * n) ' '