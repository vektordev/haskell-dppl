{-# LANGUAGE TemplateHaskell #-}

module TestParser (
  test_parser
, programToString
, exprToString
, showExamples
)where

import SPLL.Typing.RType
import SPLL.Typing.Typing
import SPLL.Lang.Types
import SPLL.Lang.Lang
import Test.QuickCheck
import SPLL.Examples
import SPLL.Parser
import ArbitrarySPLL
import Text.Megaparsec (parse, errorBundlePretty)
import PrettyPrint
import Debug.Trace (trace)
import Data.List (sortBy)
import Data.Ord (comparing)


rTypeToString :: RType -> String
rTypeToString TFloat = "Float"
rTypeToString TSymbol = "Symbol"
rTypeToString TInt = "Int"
rTypeToString TBool = "Bool"
rTypeToString (TArrow rt1 rt2) = rTypeToString rt1 ++ " -> " ++ rTypeToString rt2

tagToString :: Tag -> String
tagToString (EnumRange (start, end)) = "[" ++ show start ++ ".." ++ show end ++ "]"
tagToString (EnumList values) = "[" ++ unwords (map show values) ++ "]"
tagToString _ = undefined

valToString :: Value -> String
valToString (VBool x) = show x
valToString (VInt x) = show x
valToString (VSymbol str) = str
valToString (VFloat x) = show x

bracket :: Expr -> String
bracket e = "(" ++ exprToString e ++ ")"

exprToString :: Expr -> String
exprToString (IfThenElse _ cond tBranch fBranch) =
    "if " ++ bracket cond ++ " then " ++ bracket tBranch ++ " else " ++ bracket fBranch
exprToString (Call _ name) = name
exprToString (CallArg _ name args) = name ++ " " ++ unwords (map bracket args)
exprToString (InjF _ name args) = name ++ " " ++ unwords (map bracket args)
exprToString (MultF _ e1 e2) = "multF " ++ bracket e1 ++ " " ++ bracket e2
exprToString (MultI _ e1 e2) = "multI " ++ bracket e1 ++ " " ++ bracket e2
exprToString (PlusF _ e1 e2) = "" ++ bracket e1 ++ " + " ++ bracket e2
exprToString (PlusI _ e1 e2) = "plusI " ++ bracket e1 ++ " " ++ bracket e2
exprToString (NegF _ e) = "negate " ++ bracket e
exprToString (LetIn _ name val body) = "let " ++ name ++ " = " ++ bracket val ++ " in " ++ bracket body
exprToString (Var _ name) = name
exprToString (Constant _ value) = valToString value
exprToString (Lambda _ arg body) = "\\" ++ arg ++ " -> " ++ bracket body
exprToString (Apply _ f arg) = bracket f ++ " " ++ bracket arg
exprToString (Uniform _) = "Uniform"
exprToString (Normal _) = "Normal"
exprToString (ThetaI _ expr i) = bracket expr ++ "[" ++ show i ++ "]"
exprToString (Subtree _ expr i) = bracket expr ++ ".subtree(" ++ show i ++ ")"
exprToString (Cons _ e1 e2) = bracket e1 ++ " : " ++ bracket e2
exprToString (TCons _ e1 e2) = "(" ++ bracket e1 ++ ", " ++ bracket e2 ++ ")"
exprToString (Null _) = "[]"
exprToString (GreaterThan _ e1 e2) = bracket e1 ++ " > " ++ bracket e2
exprToString (LessThan _ e1 e2) = bracket e1 ++ " < " ++ bracket e2
exprToString (And _ e1 e2) = bracket e1 ++ " && " ++ bracket e2
exprToString (Or _ e1 e2) = bracket e1 ++ " || " ++ bracket e2
exprToString (Not _ e) = "not " ++ bracket e
exprToString (Arg _ name rtype body) = name ++ " :: " ++ rTypeToString rtype ++ " -> " ++ bracket body
exprToString (ReadNN _ name expr) = "readNN " ++ name ++ " " ++ bracket expr
exprToString (Fix _ expr) = "fix " ++ bracket expr

fnDeclToString :: FnDecl -> String
fnDeclToString (name, expr) = name ++ " = " ++ exprToString expr

neuralDeclToString :: NeuralDecl -> String
neuralDeclToString (name, rType, tag) =
    "neural " ++ name ++ " :: " ++ rTypeToString rType ++ " of " ++ tagToString tag

programToString :: Program -> String
programToString (Program fnDecls neuralDecls) =
    unlines (map fnDeclToString fnDecls ++ map neuralDeclToString neuralDecls)

testExpressions :: [(String, Expr)]
testExpressions = [
    ("simple lambda",
     Lambda makeTypeInfo "x" (Var makeTypeInfo "x")),

    ("lambda with application",
     Lambda makeTypeInfo "x"
       (Apply makeTypeInfo (Var makeTypeInfo "f") (Var makeTypeInfo "x"))),

    ("lambda with parens",
     Lambda makeTypeInfo "x"
       (Apply makeTypeInfo (Var makeTypeInfo "f") (Var makeTypeInfo "x"))),

    ("nested lambda",
     Lambda makeTypeInfo "x"
       (Lambda makeTypeInfo "y" (Var makeTypeInfo "x"))),

    ("lambda with nested application",
     Lambda makeTypeInfo "o"
       (Apply makeTypeInfo
         (Apply makeTypeInfo (Var makeTypeInfo "h2")
           (Constant makeTypeInfo (VInt 1)))
         (Constant makeTypeInfo (VInt 1)))),

    -- Adding some additional useful test cases
    ("if-then-else",
     IfThenElse makeTypeInfo
       (Var makeTypeInfo "condition")
       (Constant makeTypeInfo (VInt 1))
       (Constant makeTypeInfo (VInt 2))),

    ("let binding",
     LetIn makeTypeInfo "x"
       (Constant makeTypeInfo (VInt 1))
       (Var makeTypeInfo "x")),

    ("nested applications",
     Apply makeTypeInfo
       (Apply makeTypeInfo
         (Var makeTypeInfo "f")
         (Var makeTypeInfo "x"))
       (Var makeTypeInfo "y")),

    ("function with multiple args",
     Apply makeTypeInfo
       (Apply makeTypeInfo
         (Apply makeTypeInfo
           (Var makeTypeInfo "f")
           (Constant makeTypeInfo (VInt 1)))
         (Constant makeTypeInfo (VFloat 2.0)))
       (Var makeTypeInfo "x")),

    ("mixed operators and applications",
     Apply makeTypeInfo
       (Var makeTypeInfo "f")
       (GreaterThan makeTypeInfo
         (Var makeTypeInfo "x")
         (Constant makeTypeInfo (VInt 42))))
    ]

examples :: [Program]
examples = [
  simpleAdd,
  simpleList,
  uniformProg,
  normalProg,
  uniformProgMult,
  normalProgMult,
  uniformProgPlus,
  uniformNegPlus,
  uniformIfProg,
  testList,
  simpleTuple,
  constantProg,
  simpleCall]

showExamples :: IO ()
showExamples = do
  mapM_ (\example -> putStrLn (programToString example)) examples

-- Properties to test


-- Basic roundtrip property: parse . show = id
-- observed to hang for a bit sometimes, needs additional testing.
prop_parseShowRoundtrip :: Expr -> Property
prop_parseShowRoundtrip expr = --trace ("\n === \n" ++ show expr ++ "\n\n") $
  within 10000000 $ counterexample ("\nOriginal expression:\n" ++ repr expr ++
                 "\nAfter parse:\n" ++ case parseResult of
                                        Right parsed -> repr parsed
                                        Left err -> errorBundlePretty err) $
    case parseResult of
      Right parsed -> parsed == expr
      Left err -> False
  where
    parseResult = tryParseExpr "test" (exprToString expr)
    repr e = unlines [pPrintExpr e 0, "  = " ++ show e, " == " ++ exprToString e]

-- Specific issues to test
prop_operatorAssociativity :: Property
prop_operatorAssociativity = forAll genIdentifier $ \x ->
  forAll genIdentifier $ \y ->
  forAll genIdentifier $ \z ->
    let expr1 = "(" ++ x ++ " > " ++ y ++ ") > " ++ z
        expr2 = x ++ " > (" ++ y ++ " > " ++ z ++ ")"
    in tryParseExpr "test" expr1 /= tryParseExpr "test" expr2

-- Additional property to test identifier rejection at
prop_identifierRejectsReserved :: Property
prop_identifierRejectsReserved = forAll (elements reserved) $ \word ->
  case parse pIdentifier "" word of
    Left _ -> True
    Right _ -> False

-- Property to test valid identifiers
prop_identifierAcceptsValid :: Property
prop_identifierAcceptsValid = forAll genValidIdentifier $ \ident ->
  case parse pIdentifier "" ident of
    Right parsed -> parsed == ident
    Left _ -> False

-- Reserved words should not parse as identifiers
prop_rejectsReservedWords :: Property
prop_rejectsReservedWords = forAll (elements reserved) $ \word ->
  case tryParseExpr "test" word of
    Left _ -> True
    Right _ -> False

-- Function applications should associate correctly
prop_functionApplication :: Property
prop_functionApplication = forAll genIdentifier $ \f ->
  forAll genIdentifier $ \g ->
  forAll genIdentifier $ \x ->
    let input = f ++ " (" ++ g ++ " " ++ x ++ ")"
    in case tryParseExpr "test" input of
         Right (Apply _ f' (Apply _ g' x')) ->
           case (f', g', x') of
             (Var _ f'', Var _ g'', Var _ x'') ->
               f == f'' && g == g'' && x == x''
             _ -> False
         _ -> False

-- A fixed list of test programs survives a round trip of toString > parse
prop_inverseParsing :: Property
prop_inverseParsing =
    conjoin $ map testProgram examples
  where
    testProgram :: Program -> Property
    testProgram program =
        let
            programStr = programToString program
            parsedProgram = tryParseProgram "" programStr
        in
            case parsedProgram of
                Right reconstructed -> matchProg reconstructed program --counterexample debug (reconstructed == program)
                  where debug = unlines ["original program:", show program, pPrintProg program, "parsed program", show reconstructed, pPrintProg reconstructed, "String input:", programToString program]
                Left err -> counterexample ("Failed to parse: " ++ programStr ++ "\n" ++ errorBundlePretty err) False


matchProg :: Program -> Program -> Property
matchProg p1 p2
    -- Check if programs are directly equal
    | p1 == p2 = property True

    -- Sort lists by names and match using matchNeural and matchFn
    | otherwise = conjoin [
        matchList "functions" matchFn sortedFns1 sortedFns2,
        matchList "neurals" matchNeural sortedNeurals1 sortedNeurals2
        ]
  where
    -- Sorting functions and neurals by their names
    sortedFns1 = sortBy (comparing fst) (functions p1)
    sortedFns2 = sortBy (comparing fst) (functions p2)
    sortedNeurals1 = sortBy (comparing (\(n, _, _) -> n)) (neurals p1)
    sortedNeurals2 = sortBy (comparing (\(n, _, _) -> n)) (neurals p2)

    -- Auxiliary function to compare two lists element by element with context
    matchList :: String -> (a -> a -> Property) -> [a] -> [a] -> Property
    matchList label matcher xs ys = conjoin $ zipWith (checkMatch label matcher)  xs ys
      where
        checkMatch :: String -> (b -> b -> Property) -> b -> b -> Property
        checkMatch lbl matcher2 x y = counterexample ("Mismatch in " ++ lbl ++ ": ") (matcher2 x y)

matchFn :: FnDecl -> FnDecl -> Property
matchFn (name1, expr1) (name2, expr2)
    | name1 == name2 = counterexample (unlines ["In function " ++ name1 ++ ": ", unlines $ prettyPrintNoReq expr1, unlines $ prettyPrintNoReq expr2]) (matchExpr expr1 expr2)
    | otherwise = counterexample ("Function name mismatch: " ++ show name1 ++ " /= " ++ show name2) False

matchNeural :: NeuralDecl -> NeuralDecl -> Property
matchNeural (name1, rtype1, tag1) (name2, rtype2, tag2)
    | name1 /= name2 = counterexample ("Neural name mismatch: " ++ show name1 ++ " /= " ++ show name2) False
    | rtype1 /= rtype2 = counterexample ("In neural " ++ name1 ++ ": RType mismatch " ++ show rtype1 ++ " /= " ++ show rtype2) False
    | tag1 /= tag2 = counterexample ("In neural " ++ name1 ++ ": Tag mismatch " ++ show tag1 ++ " /= " ++ show tag2) False
    | otherwise = property True

matchExpr :: Expr -> Expr -> Property
matchExpr expr1 expr2
  | toStub expr1 /= toStub expr2 =
    counterexample ("Constructor mismatch: " ++ show (toStub expr1) ++ " /= " ++ show (toStub expr2)) False
  -- expressions are now of same constructor. Check each subexpression individually first.
  | getSubExprs expr1 /= getSubExprs expr2 =
    conjoin (zipWith matchExpr (getSubExprs expr1) (getSubExprs expr1)) .&&. expr1 === expr2
  -- all subexpressions match, we're only dealing with top-level information.
  -- Could hide the subexpressions here from the printout.
  | otherwise = expr1 === expr2

return []
test_parser = $quickCheckAll
