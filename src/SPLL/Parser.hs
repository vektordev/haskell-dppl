{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module SPLL.Parser (
  pProg
, pExpr
, pIdentifier
, pValue
, pCSV
, tryParseProgram
, tryParseExpr
, reserved
) where

import Control.Monad
import Data.Void
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad.Combinators.Expr
import Data.List.NonEmpty (NonEmpty (..))

import SPLL.Lang.Types
import SPLL.Lang.Lang
import SPLL.Typing.RType
import PredefinedFunctions (globalFEnv, parameterCount)
import SPLL.Prelude
import Data.Functor ((<&>))
import Control.Monad.State
import Data.Maybe (fromMaybe)

--import Text.Megaparsec.Debug (dbg)

dbg _ y = y
--dbg x y = traceShow x y

--TODO: This parser can by necessity not disambiguate Apply f arg from certain special-treatment builtin functions,
-- like InjF

--TODO: This can't parse type annotations.
-- At some point this deserves fixing.

type Parser = Parsec Void String
type MonadParser m = (MonadParsec Void String m, MonadPlus m, MonadFail m, MonadState Int m)

demandUniqueNumber :: MonadState Int m => m Int
demandUniqueNumber = do
  old <- get
  put (old + 1)
  return old

scTop :: MonadParser m => m ()
scTop = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

scExpr :: MonadParser m => m ()
scExpr = do
  L.space hspace1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")
  _ <- optional $ try $ do
    void eol
    void $ many (satisfy (\c -> c == ' ' || c == '\t' || c == '\n' || c == '\r'))
    col <- L.indentLevel
    guard (col > mkPos 1)
    scExpr
  return ()

sc :: MonadParser m => m ()
sc = scExpr

lexeme :: MonadParser m => m a -> m a
lexeme = L.lexeme sc

symbol :: MonadParser m => String -> m String
symbol = L.symbol sc

reserved :: [String]
reserved = ["data", "if", "then", "else", "let", "in", "theta", "subtree", "error", "ThetaTree", "Left", "Right", "Real", "Uniform", "Normal"]

keyword :: MonadParser m => String -> m String
keyword kw = lexeme $ try (string kw <* notFollowedBy (alphaNumChar <|> char '\'' <|> char '_'))

--Note: Won't parse capitalized constructors, if ever we add those.
pIdentifier :: MonadParser m => m String
pIdentifier = lexeme $ do
  x <- letterChar <|> char '_'
  xs <- many (alphaNumChar <|> char '\'' <|> char '_')
  let ident = (x:xs)
  if ident `elem` reserved
    then fail $ "reserved word: " ++ ident
    else return ident

pUniform :: MonadParser m => m Expr
pUniform = do
  _ <- symbol "Uniform"
  return uniform

pNormal :: MonadParser m => m Expr
pNormal = do
  _ <- symbol "Normal"
  return normal

pIfThenElse :: MonadParser m => [ADTDecl] -> m Expr
pIfThenElse adts = do
  _ <- keyword "if"
  a <- pExpr adts
  _ <- keyword "then"
  b <- pExpr adts
  _ <- keyword "else"
  c <- pExpr adts
  return (ifThenElse a b c)

pLetIn :: MonadParser m => [ADTDecl] -> m Expr
pLetIn adts = do
  keyword "let"
  lhs <- pExpr adts
  symbol "="
  definition <- pExpr adts
  keyword "in"
  scope <- pExpr adts
  destr <- letInDestructor lhs
  return $ destr definition scope

-- Parses the identifier part of the letIn and constructs a accessors for letIns
-- Return type is a \v, b -> Let n = v in b
letInDestructor :: MonadParser m => Expr -> m (Expr -> Expr -> Expr)
letInDestructor (Var _ name) = return $ letIn name
letInDestructor (InjF _ (Named "TCons") [a, b]) = do
  a' <- letInDestructor a
  b' <- letInDestructor b
  return $ \v body -> a' (tfst v) (b' (tsnd v) body)
letInDestructor (InjF _ (Named "left") [x]) = do
  x' <- letInDestructor x
  return $ \v -> x' (sfromLeftPartial v)
letInDestructor (InjF _ (Named "right") [x]) = do
  x' <- letInDestructor x
  return $ \v -> x' (sfromRightPartial v)
letInDestructor (Constant _ (VList EmptyList)) = return $ \v b -> ifThenElse (isNull v) b (Constant makeTypeInfo (VError "RHS of letin is longer than LHS"))
letInDestructor (InjF _ (Named "Cons") [x, xs]) = do
  x' <- letInDestructor x
  xs' <- letInDestructor xs
  id <- demandUniqueNumber
  let varName = "p_d" ++ show id
  return $ \v body -> letIn varName v (x' (lhead (var varName)) (xs' (ltail (var varName)) body))
letInDestructor _ = fail "LHS of a letIn sould be an identifier or a complex type of identifiers"

pError :: MonadParser m => m Expr
pError = do
  keyword "error"
  char '"'
  message <- many (noneOf "\"")
  char '"'
  return (Constant makeTypeInfo (VError message))

pExpr :: MonadParser m => [ADTDecl] -> m Expr
pExpr = expr

-- TODO: I think this parser should accept any pExpr instead of identifiers. Might get ambiguous parses though.

pTheta :: MonadParser m => [ADTDecl] -> m Expr
pTheta adts = dbg "theta" $ do
  keyword "theta"
  thetaExpr <- pExpr adts
  symbol "@"
  ix <- pInt
  return $ theta thetaExpr ix

pSubtree :: MonadParser m => [ADTDecl] -> m Expr
pSubtree adts = dbg "subtree" $ do
  keyword "subtree"
  thetaExpr <- pExpr adts
  symbol "@"
  ix <- pInt
  return $ subtree thetaExpr ix

construct1 :: (Expr -> Expr) -> [Expr] -> Expr
construct1 constructor [arg] = constructor arg
construct1 _ _ = error "tried to apply the wrong number of arguments."

construct2 :: (Expr -> Expr -> Expr) -> [Expr] -> Expr
construct2 constructor [arg1, arg2] = constructor arg1 arg2
construct2 _ _ = error "tried to apply the wrong number of arguments."

constructN :: Int -> ([Expr] -> Expr) -> [Expr] -> Expr
constructN n constructor args | n == length args = constructor args
constructN _ _ _ = error "tried to apply the wrong number of arguments."

-- Constructs a partially applied function, by wrapping the constructor in lambdas and using the bound variables as missing parameters
constructNPartial :: MonadParser m => Int -> ([Expr] -> Expr) -> [Expr] -> m Expr
constructNPartial expected constructor params = do
  let missingParamCnt = expected - length params
  substituteParamIDs <- replicateM missingParamCnt demandUniqueNumber
  let substituteParamNames = map (("p_m" ++) . show) substituteParamIDs
  let extendedArgs = params ++ map var substituteParamNames
  return $ foldl (flip (#->#)) (constructor extendedArgs) substituteParamNames

binaryFs :: [(String, Expr -> Expr -> Expr)]
binaryFs = [
  ("multF", (#*#)),
  ("multI", (#<*>#)),
  ("plusF", (#+#)),
  ("plusI", (#<+>#))
  ]

unaryFs :: [(String, Expr -> Expr)]
unaryFs = [
  ("negate", negF)
  ]

pValue :: MonadParser m => m Value
pValue = choice [pBool, try pFloat, pIntVal, try pUnitVal, pTupleVal, pEither, pAny, pList <&> constructVList, pThetaTree <&> VThetaTree]

pUnitVal :: MonadParser m => m Value
pUnitVal = do
  symbol "("
  symbol ")"
  return VUnit

pTupleVal :: MonadParser m => m Value
pTupleVal = do
  (symbol "(")
  val1 <- pValue
  _ <- symbol ","
  val2 <- pValue
  (symbol ")")
  return (VTuple val1 val2)

pConst :: MonadParser m => m Expr
pConst = Constant makeTypeInfo <$> choice
  [ pBool, try pUnsignedFloat, pUnsignedInt
  , try pUnitVal, pTupleVal, pEither, pAny
  , pList <&> constructVList, pThetaTree <&> VThetaTree
  ]

pBool :: MonadParser m => m Value
pBool = do
  b <- choice [keyword "True" >> return True, keyword "False" >> return False]
  return (VBool b)

-- Signed parsers: used by pValue (standalone values, .tst files, CSV).
pFloat :: MonadParser m => m Value
pFloat = dbg "float" $ VFloat <$> lexeme (L.signed sc L.float)

pIntVal :: MonadParser m => m Value
pIntVal = dbg "int" $ VInt <$> lexeme (L.signed sc L.decimal)

-- Unsigned parsers: used by pConst inside the expression atom.
-- The expression parser handles unary minus via the operator table,
-- so atoms must not greedily consume a leading '-'.
pUnsignedFloat :: MonadParser m => m Value
pUnsignedFloat = dbg "ufloat" $ VFloat <$> lexeme L.float

pUnsignedInt :: MonadParser m => m Value
pUnsignedInt = dbg "uint" $ VInt <$> lexeme L.decimal

pInt :: MonadParser m => m Int
pInt = do
  sign <- optional (symbol "-")
  i <- lexeme L.decimal
  case sign of
    Nothing -> return i
    Just "-" -> return (-i)

pEither :: MonadParser m => m Value
pEither = do
  side <- choice[keyword "Left", keyword "Right"]
  v <- pValue
  case side of
    "Left" -> return $ VEither (Left v)
    "Right" -> return $ VEither (Right v)
    s -> fail $ "Unrecognized Either constructor: " ++ s

pAny :: MonadParser m => m Value
pAny = do
  keyword "ANY"
  return VAny

pThetaTree :: MonadParser m => m ThetaTree
pThetaTree = do
  keyword "ThetaTree"
  symbol "["
  thetas <- (L.signed sc (lexeme L.float)) `sepBy` symbol ","
  symbol "]"
  symbol "["
  subtrees <- pThetaTree `sepBy` symbol ","
  symbol "]"
  return $ ThetaTree thetas subtrees

parseFromList :: MonadParser m => [(String, b)] -> m b
parseFromList kvlist = do
  key <- choice (map (symbol . fst) kvlist)
  case (lookup key kvlist) of
    Nothing -> error "unexpected parse error"
    Just value -> return value

rTypes :: [(String, RType)]
rTypes = [("Int", TInt), ("Float", TFloat), ("Bool", TBool), ("Symbol", TSymbol), ("Unit", TUnit)]

-- this function needs to handle compound types such as "Int -> Float" as well 
-- first, we want to try parsing a compound type, and if that fails assume that a simple type is there instead.
pType :: MonadParser m => m RType
pType = dbg "type" $ choice [pEitherType, try pCompoundType, pSimpleType]

pEitherType :: MonadParser m => m RType
pEitherType = dbg "EitherType" $ do
  keyword "Either"
  lType <- SPLL.Parser.pType
  rType <- SPLL.Parser.pType
  return $ TEither lType rType

pCompoundType :: MonadParser m => m RType
pCompoundType = dbg "CompoundType" $ parens $ do
  left <- SPLL.Parser.pType
  combinator <- pTypeCombinator
  right <- SPLL.Parser.pType
  return $ combinator left right
    where
      pTypeCombinator = parseFromList combinators
      combinators = [("->", TArrow), ("," , Tuple)]

pSimpleType :: MonadParser m => m RType
pSimpleType = dbg "SimpleType" $
  choice [try pUnitType, try $ parseFromList rTypes, pIdentifier <&> TADT]

pUnitType :: MonadParser m => m RType
pUnitType = do
  symbol "("
  symbol ")"
  return TUnit

pList :: MonadParser m => m [Value]
pList = do
  (symbol "[")
  values <- pCSV
  (symbol "]")
  return values

pListExpr :: MonadParser m => [ADTDecl] -> m Expr
pListExpr adts = do
  (symbol "[")
  exprs <- expr adts `sepBy` (symbol ",")
  (symbol "]")
  return (foldr cons nul exprs)

valueParser :: MonadParser m => m Value
valueParser = pValue

pCSV :: MonadParser m => m [Value]
pCSV = valueParser `sepBy` (symbol ",")

pDefinition :: MonadParser m => [ADTDecl] -> m (Either FnDecl NeuralDecl)
pDefinition adts = do
  x <- choice [fmap Right pNeural, fmap Left (pFunction adts)]
  return x

--TODO: Add validation via AutoNeural.
pNeural :: MonadParser m => m NeuralDecl
pNeural = dbg "neural" $ do
  _ <- keyword "neural"
  name <- pIdentifier
  _ <- symbol "::"
  ty <- SPLL.Parser.pType
  multiVal <- optional (symbol "of" *> pNeuralMultiValue)
  return (name, ty, multiVal)

pNeuralMultiValue :: MonadParser m => m MultiValue
pNeuralMultiValue = dbg "multiVal" $ do
  choice [try pMultiAuto, try pMultiContinuous, try pMultiTypeDef, try pMultiTypeRef, try pMultiTuple, pMultiDiscretes, pMultiADT, try pMultiEither]

-- | "_": auto-derive this slot's MultiValue from its RType (full enumeration for
-- discrete/Bool/ADT/Tuple/Either, continuous for Float; Int/Symbol cannot be derived).
pMultiAuto :: MonadParser m => m MultiValue
pMultiAuto = dbg "multiAuto" $ do
  _ <- lexeme $ char '_' <* notFollowedBy (alphaNumChar <|> char '\'' <|> char '_')
  return MultiAuto

-- | "Real": a continuous (Float) leaf within a composite MultiValue annotation.
pMultiContinuous :: MonadParser m => m MultiValue
pMultiContinuous = dbg "multiContinuous" $ do
  _ <- keyword "Real"
  return MultiContinuous

pMultiTypeDef :: MonadParser m => m MultiValue
pMultiTypeDef = do
  depth <- pInt
  name <- pIdentifier
  symbol "."
  inner <- pNeuralMultiValue
  return (resolveMultiValueTypeDecl depth inner (name, inner))

pMultiTypeRef :: MonadParser m => m MultiValue
pMultiTypeRef = pIdentifier <&> MultiTypeRef

pMultiDiscretes :: MonadParser m => m MultiValue
pMultiDiscretes = dbg "multiDisc" $ do
  symbol "["
  csv <- pCSV
  symbol "]"
  return $ MultiDiscretes csv

pMultiEither :: MonadParser m => m MultiValue
pMultiEither = dbg "multiEith" $ parens $ do
  l <- pNeuralMultiValue
  symbol "|"
  r <- pNeuralMultiValue
  return $ MultiEither l r

pMultiTuple :: MonadParser m => m MultiValue
pMultiTuple = dbg "multiTuple" $ parens $ do
  l <- pNeuralMultiValue
  symbol ","
  r <- pNeuralMultiValue
  return $ MultiTuple l r

pMultiADT :: MonadParser m => m MultiValue
pMultiADT = dbg "multiADT" $ do
  symbol "{"
  constrs <- sepBy (
    (do
      cName <- pIdentifier
      params <- many pNeuralMultiValue
      return (cName, params))
    ) (symbol "|")
  symbol "}"
  return $ MultiADT constrs

pFunction :: MonadParser m => [ADTDecl] -> m FnDecl
pFunction adts = dbg "function" $ do
  name <- pIdentifier
  args <- many pIdentifier
  _ <- symbol "="
  e <- pExpr adts
  let lambdas = foldr (#->#) e args
  return (name, lambdas)

pADT :: MonadParser m => m ADTDecl
pADT = dbg "ADT" $ do
  keyword "data"
  name <- pIdentifier
  symbol "="
  constrs <- pADTConstructor `sepBy` symbol "|"
  -- Optional trailing `depth N`: the default unroll depth used when a neural net
  -- auto-derives an enumeration of this (recursive) type. See ADTDecl.adtDepth.
  depth <- optional (keyword "depth" *> pInt)
  return $ ADTDecl {dataName=name, constructors=constrs, adtDepth=depth}

pADTConstructor :: MonadParser m => m ADTConstructorDecl
pADTConstructor = dbg "ADT Constr" $ do
  name <- pIdentifier
  fields <- try pADTField `sepBy` symbol ","
  return (name, fields)

pADTField :: MonadParser m => m (String, RType)
pADTField = do
    fieldName <- pIdentifier
    symbol "::"
    fieldType <- choice [SPLL.Parser.pType <&> Left, pIdentifier <&> Right]
    let fieldRT = case fieldType of
                    Left rt -> rt
                    Right adt -> TADT adt
    return (fieldName, fieldRT)

pProg :: MonadParser m => m Program
pProg = do
  adts <- dbg "trying ADTs" (many (try (scTop *> pADT)))
  defs <- dbg "trying definition" (many (try (scTop *> pDefinition adts)))
  scTop
  _ <- eof
  return (aggregateDefinitions adts defs)

-- | "neural encode :: T of M" registers a standalone PartitionPlan annotation for the
-- RType T (the registry; see SPLL.Lang.Types.encodeDecls), rather than declaring a
-- callable neural network -- 'encode' is therefore a reserved network name. Every other
-- NeuralDecl's "of" clause is sugar that also registers into this registry, keyed by
-- the declaration's target/source type (see 'neuralValueType').
aggregateDefinitions :: [ADTDecl] -> [Either FnDecl NeuralDecl] -> Program
aggregateDefinitions adts (Left fn : tail) = Program (fn:fns) neurals adtz enc
  where
    Program fns neurals adtz enc = aggregateDefinitions adts tail
aggregateDefinitions adts (Right nr@(name, ty, mtag) : tail)
  | name == "encode" = Program fns neurals adtz ((ty, fromMaybe MultiAuto mtag) : enc)
  | otherwise = Program fns (nr:neurals) adtz (sugar ++ enc)
  where
    Program fns neurals adtz enc = aggregateDefinitions adts tail
    sugar = case (mtag, neuralValueType ty) of
      (Just mv, Just target) -> [(target, mv)]
      _ -> []
aggregateDefinitions adts [] = Program [] [] adts []

tryParseExpr :: FilePath -> String -> Either (ParseErrorBundle String Void) Expr
tryParseExpr filename src = do
  (res, _) <- runParser (runStateT parseExpr 0) filename src
  return res

tryParseProgram :: FilePath -> String -> Either (ParseErrorBundle String Void) Program
tryParseProgram filename src = do
  (prog, _) <- runParser (runStateT pProg 0) filename src
  case normalize prog of
    Right prog -> Right prog
    Left err -> Left $ ParseErrorBundle ((FancyError 0 (Set.singleton (ErrorFail err))) :| []) emptyPosState

emptyPosState :: PosState String
emptyPosState = PosState "" 0 (initialPos "<string>") (mkPos 0) ""

pNull :: MonadParser m => m Expr
pNull = do
  _ <- symbol "[]"
  return $ nul

pTuple :: MonadParser m => [ADTDecl] -> m Expr
pTuple adts = parens $ do
  x <- expr adts
  _ <- symbol ","
  y <- expr adts
  return $ tuple x y


-- | Parse atomic expressions (no recursion)
atom :: MonadParser m => [ADTDecl] -> m Expr
atom adts = choice [
    pNull,
    try (pTuple adts),
    try (pListExpr adts),
    try (parens (expr adts)),  -- Parenthesized expressions first
    pUniform,     -- Built-in distributions
    pNormal,
    pConst,       -- Constants (numbers)
    var <$> pIdentifier  -- Variables last
  ] <* sc

-- | Parse expressions that start with keywords
keywordExpr :: MonadParser m => [ADTDecl] -> m Expr
keywordExpr adts = dbg "keywordExpr" $ choice [
    pIfThenElse adts,
    pLetIn adts,
    pLambda adts,
    pTheta adts,
    pSubtree adts,
    pError
  ] <* sc

-- | Lambda expressions
pLambda :: MonadParser m => [ADTDecl] -> m Expr
pLambda adts = do
    _ <- symbol "\\"
    params <- some pIdentifier
    _ <- symbol "->"
    body <- expr adts
    return $ foldr (#->#) body params

-- | Parse function application
-- This handles both normal application and built-in functions like multF
application :: MonadParser m => [ADTDecl] -> m Expr
application adts = dbg "application" $ do
    func <- try (atom adts)
    args <- try $ many (try (atom adts) <|> try (parens (expr adts)))
    case func of
        Var _ name -> case lookup name binaryFs of
            Just constructor -> return (construct2 constructor args)
            Nothing -> case lookup name unaryFs of
                Just constructor -> return (construct1 constructor args)
                Nothing -> case lookup name (globalFEnv adts) of
                  Just _ -> 
                    if length args == (parameterCount adts name) then
                      return (constructN (parameterCount adts name) (injF name) args)
                    else if length args < (parameterCount adts name) then
                      constructNPartial (parameterCount adts name) (injF name) args
                    else
                      fail $ "Function " ++ name ++ " expects " ++ show (parameterCount [] name) ++ " parameters, but got " ++ show (length args)
                  Nothing -> return $ foldl apply func args
        _ -> return $ foldl apply func args


-- | Main expression parser using makeExprParser
expr :: MonadParser m => [ADTDecl] -> m Expr
expr adts = dbg "expr" $ makeExprParser term opTable
  where
    term = choice [
        try (application adts),
        try (keywordExpr adts),
        atom adts
      ]

-- | Top level entry point
parseExpr :: MonadParser m => m Expr
parseExpr = sc *> expr [] <* eof

-- | Parse a parenthesized expression
parens :: MonadParser m => m a -> m a
parens = between (char '(' *> sc) (char ')' *> sc)

multLikeOpList :: [([Char], Expr -> Expr -> Expr)]
multLikeOpList = [("**", (#<*>#)), ("*", (#*#)), ("/", (#/#)), ("&&", (#&&#))]

addLikeOpList :: [([Char], Expr -> Expr -> Expr)]
addLikeOpList = [("++", (#<+>#)), ("~~", (#<->#)), ("+", (#+#)), ("-", \a b -> a #+# (negF b)), ("||", (#||#))]

listManipulationOpList :: [([Char], Expr -> Expr -> Expr)]
listManipulationOpList = [(":", (#:#))]

cmpOpList :: [([Char], Expr -> Expr -> Expr)]
cmpOpList = [(">", (#>#)), ("<", (#<#)), (":", (#:#)), ("==", (#==#))]

funLikeOps :: [([Char], Expr -> Expr)]
funLikeOps = [("not", (#!#))]

-- Fold negation into literal constants so that roundtrip works for negative literals.
smartNeg :: Expr -> Expr
smartNeg (Constant ti (VFloat f)) = Constant ti (VFloat (-f))
smartNeg (Constant ti (VInt i))   = Constant ti (VInt (-i))
smartNeg e                         = negF e

prefixOps :: MonadParser m => [Operator m Expr]
prefixOps = [Prefix (smartNeg <$ try (symbol "-" <* notFollowedBy (char '>')))]

mkInfixOp :: MonadParser m => [([Char], Expr -> Expr -> Expr)] -> [Operator m Expr]
mkInfixOp tbl = map infx tbl
  where infx (name, f) = InfixL (f <$ symbol name)

mkPrefixOp :: MonadParser m => [([Char], Expr -> Expr)] -> [Operator m Expr]
mkPrefixOp tbl = map infx tbl
  where infx (name, f) = Prefix (f <$ keyword name)


-- | Operator table (precedence and associativity)
opTable :: MonadParser m => [[Operator m Expr]]
opTable =
  [ mkPrefixOp funLikeOps ++ prefixOps,
    mkInfixOp multLikeOpList,
    mkInfixOp addLikeOpList,
    mkInfixOp listManipulationOpList,
    mkInfixOp cmpOpList
  ]


type ExprBuilder m = [Expr] -> m (Either String Expr)
type BuilderMap m = Map.Map String (ExprBuilder m)

-- | Normalize a Program
--  After normalization, all Vars should be properly resolved as either a ReadNN, a InjF, or a plain Var.
normalize :: Program -> Either String Program
normalize prog =
  let neuralMap = buildNeuralMap (neurals prog) :: BuilderMap (State Int)
      invMap = buildInvMap (adts prog)
      globalFunctionMap = globalFunctions prog
      injFMap = buildInjFMap prog
      paramMap = Map.unions [neuralMap, invMap, injFMap]  -- neural builders take precedence
      functionMap = Map.unions [globalFunctionMap, injFMap] -- InjF are in both Maps, because they can be partially applied, which means they can have zero parameters
  in if Map.disjoint invMap neuralMap && Map.disjoint invMap globalFunctionMap && Map.disjoint neuralMap globalFunctionMap
    then do
      --mapExprInProgram (normalizeExpr (builderMap, functionMap, Set.empty)) prog
      evalState (mapExprInProgram (normalizeExpr (paramMap, functionMap, Set.empty)) prog) 0
    else Left $ "Found identifiers that are in multiple scopes."

-- Build maps from identifiers to expression builders
buildNeuralMap :: MonadState Int m => [NeuralDecl] -> BuilderMap m
buildNeuralMap decls = Map.fromList
  [(name, \[arg] -> return $ Right $ readNN name arg) | (name, _, _) <- decls]

buildInvMap :: MonadState Int m => [ADTDecl] -> BuilderMap m
buildInvMap adts = Map.fromList
  [(name, \args -> case args of
    a | length a /= parameterCount adts name -> do
      let missingParamCnt = parameterCount adts name - length a
      substituteParamIDs <- replicateM missingParamCnt demandUniqueNumber
      let substituteParamNames = map (("p_m" ++) . show) substituteParamIDs
      let extendedArgs = args ++ map var substituteParamNames
      return $ Right $ foldl (flip (#->#)) (injF name extendedArgs) substituteParamNames
    _ -> return $ Right $ injF name args)
   | name <- fNames]
  where fNames = map fst (globalFEnv adts)

globalFunctions :: MonadState Int m =>  Program -> BuilderMap m
globalFunctions prog = Map.fromList ([(name, \[] -> return $ Right $ var name) | (name, _) <- functions prog])

buildInjFMap:: MonadState Int m => Program -> BuilderMap m
buildInjFMap prog = Map.fromList 
  [(name, \[] -> do
      substituteParamIDs <- replicateM (parameterCount (adts prog) name) demandUniqueNumber
      let substituteParamNames = map (("p_m" ++) . show) substituteParamIDs
      let args = map var substituteParamNames
      return $ Right $ foldl (flip (#->#)) (injF name args) substituteParamNames)
    | (name, _) <- globalFEnv (adts prog)]

-- Main expression normalization function
normalizeExpr :: MonadState Int m => (BuilderMap m, BuilderMap m, Set.Set String) -> Expr -> m (Either String Expr)
normalizeExpr env@(parametricBuilders, atomicBuilders, benign) expr =
  case expr of
    -- Handle scopes first, adding bound variables before processing sub-expressions
    Lambda ti name body -> do
      let body' = normalizeExpr (parametricBuilders, atomicBuilders, Set.insert name benign) body
      fmap (fmap (Lambda ti name)) body'

    -- For all other expressions, normalize sub-expressions first then check for Apply pattern
    _ -> do
      subExprs <- fmap sequence (mapM (normalizeExpr env) (getSubExprs expr))
      let mExpr = fmap (setSubExprs expr) subExprs
      case mExpr of
        Left s -> return $ Left s
        Right expr' ->
          case expr' of
            -- Start of an Apply chain
            Apply _ (Apply _ _ _) _ ->
              -- Need to collect all args in the chain and find base function.
              -- Collect from expr' (not expr) so the args keep their normalization.
              let (base, args) = collectApplyChain expr'
              in case base of
                Var _ fname | Just builder <- Map.lookup fname parametricBuilders -> do
                  build <- builder args
                  case build of
                    Left _ -> return $ Right expr' -- This prevents InjFs, which have multiple arguments from failing to build because here only one argument is applied
                    e -> return e
                _ -> return $ Right expr'
            Apply _ (Var _ fname) arg
              | not (Set.member fname benign)
              , Just builder <- Map.lookup fname parametricBuilders -> do
                build <- builder [arg]
                case build of
                  Left _ -> return $ Right expr' -- This prevents InjFs, which have multiple arguments from failing to build because here only one argument is applied
                  e -> return e
            Var _ fname
              | not (Set.member fname benign)
              , Just builder <- Map.lookup fname atomicBuilders -> builder []
            _ -> return $ Right expr'

--replaceExpr :: Expr -> Expr -> Expr
--replaceExpr

-- Returns (base expression, arguments in application order)
collectApplyChain :: Expr -> (Expr, [Expr])
collectApplyChain (Apply _ left arg) =
  let (base, args) = collectApplyChain left
  in (base, args ++ [arg])  -- maintain order of application
-- Quick and dirty fix for multi parameter InjFs. The normalizatzion first creates a 1 parameter InjF and then stops with the normalization
-- We bypass this by tricking the normalization  that the InjF is in reality an application on a variable
collectApplyChain (InjF t (Named name) args) = (Var t name, args)
collectApplyChain e = (e, [])

-- Helper to map over all expressions in a program
mapExprInProgram :: MonadState Int m => (Expr -> m (Either String Expr)) -> Program -> m (Either String Program)
mapExprInProgram f prog = do
  newFuncs <- mapM (\(name, expr) -> f expr >>= \e -> return (name, e)) (functions prog)
  let newFuncs' = mapM (\(s, e) -> (e <&> \ex -> (s, ex))) newFuncs
  case newFuncs' of
    Right fs -> return $ Right $ prog { functions = fs }
    Left err -> return $ Left err
