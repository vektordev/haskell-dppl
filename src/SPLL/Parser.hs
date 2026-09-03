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
import Data.Maybe (fromMaybe, isJust)

--import Text.Megaparsec.Debug (dbg)

dbg :: a -> b -> b
dbg _ y = y
--dbg x y = traceShow x y

--TODO: This parser can by necessity not disambiguate Apply f arg from certain special-treatment builtin functions,
-- like InjF

--TODO: This can't parse type annotations.
-- At some point this deserves fixing.

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
reserved = ["data", "if", "then", "else", "let", "in", "theta", "subtree", "error", "observe", "ThetaTree", "Left", "Right", "Real", "Uniform", "Normal"]

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
pIfThenElse adts_ = do
  _ <- keyword "if"
  a <- pExpr adts_
  _ <- keyword "then"
  b <- pExpr adts_
  _ <- keyword "else"
  c <- pExpr adts_
  return (ifThenElse a b c)

pLetIn :: MonadParser m => [ADTDecl] -> m Expr
pLetIn adts_ = do
  _ <- keyword "let"
  lhs <- pExpr adts_
  _ <- symbol "="
  definition <- pExpr adts_
  _ <- keyword "in"
  scope <- pExpr adts_
  destr <- letInDestructor lhs
  return $ destr definition scope

-- Parses the identifier part of the letIn and constructs a accessors for letIns
-- Return type is a \v, b -> Let n = v in b
letInDestructor :: MonadParser m => Expr -> m (Expr -> Expr -> Expr)
letInDestructor (Expr _ (Var name)) = return $ letIn name
letInDestructor (Expr _ (InjF (Named "TCons") [a, b])) = do
  a' <- letInDestructor a
  b' <- letInDestructor b
  return $ \v body -> a' (tfst v) (b' (tsnd v) body)
letInDestructor (Expr _ (InjF (Named "left") [x])) = do
  x' <- letInDestructor x
  return $ \v -> x' (sfromLeftPartial v)
letInDestructor (Expr _ (InjF (Named "right") [x])) = do
  x' <- letInDestructor x
  return $ \v -> x' (sfromRightPartial v)
letInDestructor (Expr _ (Constant (VList EmptyList))) = return $ \v b -> ifThenElse (isNull v) b (Expr makeTypeInfo (Constant (VError "RHS of letin is longer than LHS")))
letInDestructor (Expr _ (InjF (Named "Cons") [x, xs])) = do
  x' <- letInDestructor x
  xs' <- letInDestructor xs
  id_ <- demandUniqueNumber
  let varName = "p_d" ++ show id_
  return $ \v body -> letIn varName v (x' (lhead (var varName)) (xs' (ltail (var varName)) body))
letInDestructor _ = fail "LHS of a letIn sould be an identifier or a complex type of identifiers"

-- | @observe base pred@ -- conditioning as a total, Maybe-returning expression
-- (design mar-sum-types-observe §2/§5). Both arguments are atoms, as for any
-- other application, so a computed base or a lambda predicate is parenthesised:
-- @observe (camNN sym) (\\v -> v == 0)@. Desugars via 'SPLL.Prelude.observe'
-- into @let o = base in if pred o then right o else left ()@ over a fresh
-- binder -- there is no @Observe@ 'Expr' constructor and no inference rule of
-- its own; the existing let/if/Either machinery already gives the specified
-- semantics (@p(Just v) = p(base = v) * p(pred v)@, @p(Nothing)@ the rest of
-- the mass), and marginalising the binder out with @p(Just ANY)@ is the
-- renormalisation denominator.
pObserve :: MonadParser m => [ADTDecl] -> m Expr
pObserve adts_ = do
  _ <- keyword "observe"
  base <- atom adts_
  predicate <- atom adts_
  case predicate of
    -- A literal lambda is beta-reduced here rather than left as an 'Apply': the
    -- binder becomes the lambda's own parameter and the body becomes the
    -- condition verbatim. This is not cosmetic. Inference has to invert the
    -- condition back onto the binding, and it can only do that for occurrences
    -- it can see through -- an occurrence under an unreduced 'Apply' of a
    -- 'Lambda' defeats both point inversion and the set-valued witness
    -- fallback, so 'observe Normal (\v -> v > 0.0)' would refuse to compile
    -- while the equivalent hand-written let/if idiom compiles fine. Capture is
    -- not a concern: 'letIn' is an 'Apply' of a 'Lambda', so a free occurrence
    -- of the same name inside @base@ is evaluated outside the new binding and
    -- still refers to the outer one.
    Expr _ (Lambda param body) -> return $ observeBound param base body
    _ -> do
      binderId <- demandUniqueNumber
      return $ observe ("p_ob" ++ show binderId) base predicate

pError :: MonadParser m => m Expr
pError = do
  _ <- keyword "error"
  _ <- char '"'
  message <- many (noneOf "\"")
  _ <- char '"'
  return (Expr makeTypeInfo (Constant (VError message)))

pExpr :: MonadParser m => [ADTDecl] -> m Expr
pExpr = expr

-- TODO: I think this parser should accept any pExpr instead of identifiers. Might get ambiguous parses though.

pTheta :: MonadParser m => [ADTDecl] -> m Expr
pTheta adts_ = dbg "theta" $ do
  _ <- keyword "theta"
  thetaExpr <- pExpr adts_
  _ <- symbol "@"
  ix <- pInt
  return $ theta thetaExpr ix

pSubtree :: MonadParser m => [ADTDecl] -> m Expr
pSubtree adts_ = dbg "subtree" $ do
  _ <- keyword "subtree"
  thetaExpr <- pExpr adts_
  _ <- symbol "@"
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
pValue = choice [pBool, try pFloat, pIntVal, try pUnitVal, try pTupleVal, pEither, pAny, pList <&> constructVList, pThetaTree <&> VThetaTree, pADTVal]

-- | An ADT value: a constructor name applied to its field values, written by
-- juxtaposition as in the expression syntax -- @Leaf@, @Node Leaf Leaf@,
-- @Node (Node Leaf Leaf) Leaf@. This is what lets a .tst file (or a CLI @-x@)
-- name an ADT-valued query point; without it the corpus can only reach an ADT
-- program through a Bool/Float projection of it.
--
-- The parser has no access to the ADT declarations, so it takes the arity from
-- what is written; a wrong arity or an unknown constructor surfaces in typing,
-- not here. Fields are parsed as atoms, so a field that is itself a
-- constructor application, a @Left@/@Right@, or anything else written by
-- juxtaposition must be parenthesised.
pADTVal :: MonadParser m => m Value
pADTVal = VADT <$> pConstructorName <*> many pValueAtom

-- | An upper-case identifier that is not one of the value keywords the value
-- grammar already spells (@True@/@False@/@ANY@/@Left@/@Right@/@ThetaTree@).
pConstructorName :: MonadParser m => m String
pConstructorName = lexeme $ try $ do
  x <- upperChar
  xs <- many (alphaNumChar <|> char '\'' <|> char '_')
  let ident = x:xs
  if ident `elem` reserved || ident `elem` ["True", "False", "ANY"]
    then fail ("reserved word: " ++ ident)
    else return ident

-- | Values allowed in a constructor field position: everything that is not
-- itself an application. A parenthesised 'pValue' escapes the restriction.
pValueAtom :: MonadParser m => m Value
pValueAtom = choice
  [ pBool, try pFloat, pIntVal
  , try pUnitVal, try pTupleVal, parens pValue
  , pAny
  , pList <&> constructVList
  , pThetaTree <&> VThetaTree
  , VADT <$> pConstructorName <*> pure []
  ]

pUnitVal :: MonadParser m => m Value
pUnitVal = do
  _ <- symbol "("
  _ <- symbol ")"
  return VUnit

pTupleVal :: MonadParser m => m Value
pTupleVal = do
  _ <- (symbol "(")
  val1 <- pValue
  _ <- symbol ","
  val2 <- pValue
  _ <- (symbol ")")
  return (VTuple val1 val2)

pConst :: MonadParser m => m Expr
pConst = (\v -> Expr makeTypeInfo (Constant v)) <$> choice
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
  return (if isJust sign then -i else i)

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
  _ <- keyword "ANY"
  return VAny

pThetaTree :: MonadParser m => m ThetaTree
pThetaTree = do
  _ <- keyword "ThetaTree"
  _ <- symbol "["
  thetas <- (L.signed sc (lexeme L.float)) `sepBy` symbol ","
  _ <- symbol "]"
  _ <- symbol "["
  subtrees <- pThetaTree `sepBy` symbol ","
  _ <- symbol "]"
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
  _ <- keyword "Either"
  lType <- SPLL.Parser.pType
  rType_ <- SPLL.Parser.pType
  return $ TEither lType rType_

pCompoundType :: MonadParser m => m RType
pCompoundType = dbg "CompoundType" $ parens $ do
  left_ <- SPLL.Parser.pType
  combinator <- pTypeCombinator
  right_ <- SPLL.Parser.pType
  return $ combinator left_ right_
    where
      pTypeCombinator = parseFromList combinators
      combinators = [("->", TArrow), ("," , Tuple)]

pSimpleType :: MonadParser m => m RType
pSimpleType = dbg "SimpleType" $
  choice [try pUnitType, try $ parseFromList rTypes, pIdentifier <&> TADT]

pUnitType :: MonadParser m => m RType
pUnitType = do
  _ <- symbol "("
  _ <- symbol ")"
  return TUnit

pList :: MonadParser m => m [Value]
pList = do
  _ <- (symbol "[")
  values <- pCSV
  _ <- (symbol "]")
  return values

pListExpr :: MonadParser m => [ADTDecl] -> m Expr
pListExpr adts_ = do
  _ <- (symbol "[")
  exprs <- expr adts_ `sepBy` (symbol ",")
  _ <- (symbol "]")
  return (foldr cons nul exprs)

valueParser :: MonadParser m => m Value
valueParser = pValue

pCSV :: MonadParser m => m [Value]
pCSV = valueParser `sepBy` (symbol ",")

pDefinition :: MonadParser m => [ADTDecl] -> m (Either FnDecl NeuralDecl)
pDefinition adts_ = do
  x <- choice [fmap Right pNeural, fmap Left (pFunction adts_)]
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
  _ <- symbol "."
  inner <- pNeuralMultiValue
  return (resolveMultiValueTypeDecl depth inner (name, inner))

pMultiTypeRef :: MonadParser m => m MultiValue
pMultiTypeRef = pIdentifier <&> MultiTypeRef

pMultiDiscretes :: MonadParser m => m MultiValue
pMultiDiscretes = dbg "multiDisc" $ do
  _ <- symbol "["
  csv <- pCSV
  _ <- symbol "]"
  return $ MultiDiscretes csv

pMultiEither :: MonadParser m => m MultiValue
pMultiEither = dbg "multiEith" $ parens $ do
  l <- pNeuralMultiValue
  _ <- symbol "|"
  r <- pNeuralMultiValue
  return $ MultiEither l r

pMultiTuple :: MonadParser m => m MultiValue
pMultiTuple = dbg "multiTuple" $ parens $ do
  l <- pNeuralMultiValue
  _ <- symbol ","
  r <- pNeuralMultiValue
  return $ MultiTuple l r

pMultiADT :: MonadParser m => m MultiValue
pMultiADT = dbg "multiADT" $ do
  _ <- symbol "{"
  constrs <- sepBy (
    (do
      cName <- pIdentifier
      params <- many pNeuralMultiValue
      return (cName, params))
    ) (symbol "|")
  _ <- symbol "}"
  return $ MultiADT constrs

pFunction :: MonadParser m => [ADTDecl] -> m FnDecl
pFunction adts_ = dbg "function" $ do
  name <- pIdentifier
  args <- many pIdentifier
  _ <- symbol "="
  e <- pExpr adts_
  let lambdas = foldr (#->#) e args
  return (name, lambdas)

pADT :: MonadParser m => m ADTDecl
pADT = dbg "ADT" $ do
  _ <- keyword "data"
  name <- pIdentifier
  _ <- symbol "="
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
    _ <- symbol "::"
    fieldType <- choice [SPLL.Parser.pType <&> Left, pIdentifier <&> Right]
    let fieldRT = case fieldType of
                    Left rt -> rt
                    Right adt -> TADT adt
    return (fieldName, fieldRT)

pProg :: MonadParser m => m Program
pProg = do
  adtsDecls <- dbg "trying ADTs" (many (try (scTop *> pADT)))
  defs <- dbg "trying definition" (many (try (scTop *> pDefinition adtsDecls)))
  scTop
  _ <- eof
  return (aggregateDefinitions adtsDecls defs)

-- | "neural writeLogits :: T of M" registers a standalone PartitionPlan annotation for the
-- RType T (the registry; see SPLL.Lang.Types.writeLogitsDecls), rather than declaring a
-- callable neural network -- 'writeLogits' is therefore a reserved network name. Every other
-- NeuralDecl's "of" clause is sugar that also registers into this registry, keyed by
-- the declaration's target/source type (see 'neuralValueType').
aggregateDefinitions :: [ADTDecl] -> [Either FnDecl NeuralDecl] -> Program
aggregateDefinitions adts_ (Left fn : tail_) = Program (fn:fns) neurals_ adtz enc
  where
    Program fns neurals_ adtz enc = aggregateDefinitions adts_ tail_
aggregateDefinitions adts_ (Right nr@(name, ty, mtag) : tail_)
  | name == "writeLogits" = Program fns neurals_ adtz ((ty, fromMaybe MultiAuto mtag) : enc)
  | otherwise = Program fns (nr:neurals_) adtz (sugar ++ enc)
  where
    Program fns neurals_ adtz enc = aggregateDefinitions adts_ tail_
    sugar = case (mtag, neuralValueType ty) of
      (Just mv, Just target) -> [(target, mv)]
      _ -> []
aggregateDefinitions adts_ [] = Program [] [] adts_ []

tryParseExpr :: FilePath -> String -> Either (ParseErrorBundle String Void) Expr
tryParseExpr filename src = do
  (res, _) <- runParser (runStateT parseExpr 0) filename src
  return res

tryParseProgram :: FilePath -> String -> Either (ParseErrorBundle String Void) Program
tryParseProgram filename src = do
  (prog, _) <- runParser (runStateT pProg 0) filename src
  case normalize prog of
    Right prog_ -> Right prog_
    Left err -> Left $ ParseErrorBundle ((FancyError 0 (Set.singleton (ErrorFail err))) :| []) emptyPosState

emptyPosState :: PosState String
emptyPosState = PosState "" 0 (initialPos "<string>") (mkPos 0) ""

pNull :: MonadParser m => m Expr
pNull = do
  _ <- symbol "[]"
  return $ nul

-- | Parses "(expr)" and "(expr, expr)" sharing a single parse of the first
-- component. A prior version tried a standalone pTuple (parse expr, require
-- comma) before falling back to a standalone parenthesized-expr parser (parse
-- expr again); on a failed tuple guess that re-parsed the whole first
-- component from scratch. Since every nested paren re-triggers the same
-- doubling, a chain of N nested parenthesized subexpressions (e.g. a
-- right-nested if/accessor chain) cost O(2^N) instead of O(N) -- 12 levels of
-- nesting alone measured at 160+ seconds to parse (testCases/planEnumInlineWide).
pTuple :: MonadParser m => [ADTDecl] -> m Expr
pTuple adts_ = parens $ do
  x <- expr adts_
  rest <- optional (symbol "," *> expr adts_)
  return $ maybe x (tuple x) rest


-- | Parse atomic expressions (no recursion)
atom :: MonadParser m => [ADTDecl] -> m Expr
atom adts_ = choice [
    pNull,
    try (pListExpr adts_),
    try (pTuple adts_),  -- "(expr)" and "(expr, expr)" -- see pTuple
    pUniform,     -- Built-in distributions
    pNormal,
    pConst,       -- Constants (numbers)
    var <$> pIdentifier  -- Variables last
  ] <* sc

-- | Parse expressions that start with keywords
keywordExpr :: MonadParser m => [ADTDecl] -> m Expr
keywordExpr adts_ = dbg "keywordExpr" $ choice [
    pIfThenElse adts_,
    pLetIn adts_,
    pLambda adts_,
    pTheta adts_,
    pSubtree adts_,
    pObserve adts_,
    pError
  ] <* sc

-- | Lambda expressions
pLambda :: MonadParser m => [ADTDecl] -> m Expr
pLambda adts_ = do
    _ <- symbol "\\"
    params <- some pIdentifier
    _ <- symbol "->"
    body <- expr adts_
    return $ foldr (#->#) body params

-- | Parse function application
-- This handles both normal application and built-in functions like multF
application :: MonadParser m => [ADTDecl] -> m Expr
application adts_ = dbg "application" $ do
    func <- try (atom adts_)
    -- atom already covers "(expr)"/"(expr, expr)" via pTuple; a separate
    -- parens(expr) fallback here would re-parse the same paren contents a
    -- second time on every atom-alternative failure (see pTuple's comment).
    args <- try $ many (try (atom adts_))
    case func of
        Expr _ (Var name) -> case lookup name binaryFs of
            Just constructor -> return (construct2 constructor args)
            Nothing -> case lookup name unaryFs of
                Just constructor -> return (construct1 constructor args)
                Nothing -> case lookup name (globalFEnv adts_) of
                  Just _ ->
                    if length args == (parameterCount adts_ name) then
                      return (constructN (parameterCount adts_ name) (injF name) args)
                    else if length args < (parameterCount adts_ name) then
                      constructNPartial (parameterCount adts_ name) (injF name) args
                    else
                      fail $ "Function " ++ name ++ " expects " ++ show (parameterCount [] name) ++ " parameters, but got " ++ show (length args)
                  Nothing -> return $ foldl apply func args
        _ -> return $ foldl apply func args


-- | Main expression parser using makeExprParser
expr :: MonadParser m => [ADTDecl] -> m Expr
expr adts_ = dbg "expr" $ makeExprParser term opTable
  where
    term = choice [
        try (application adts_),
        try (keywordExpr adts_),
        atom adts_
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
smartNeg (Expr ti (Constant (VFloat f))) = Expr ti (Constant (VFloat (-f)))
smartNeg (Expr ti (Constant (VInt i)))   = Expr ti (Constant (VInt (-i)))
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
  [(name, \args -> return $ case args of
      [arg] -> Right $ readNN name arg
      _     -> Left ("Neural network '" ++ name ++ "' takes exactly one argument, but was applied to " ++ show (length args)))
   | (name, _, _) <- decls]

buildInvMap :: MonadState Int m => [ADTDecl] -> BuilderMap m
buildInvMap adts_ = Map.fromList
  [(name, \args -> case args of
    a | length a /= parameterCount adts_ name -> do
      let missingParamCnt = parameterCount adts_ name - length a
      substituteParamIDs <- replicateM missingParamCnt demandUniqueNumber
      let substituteParamNames = map (("p_m" ++) . show) substituteParamIDs
      let extendedArgs = args ++ map var substituteParamNames
      return $ Right $ foldl (flip (#->#)) (injF name extendedArgs) substituteParamNames
    _ -> return $ Right $ injF name args)
   | name <- fNames]
  where fNames = map fst (globalFEnv adts_)

globalFunctions :: MonadState Int m =>  Program -> BuilderMap m
globalFunctions prog = Map.fromList ([(name, atomicBuilder name (var name)) | (name, _) <- functions prog])

-- | An atomic builder stands for the identifier itself and is only ever looked
-- up in the no-argument position, so a non-empty argument list means the
-- normalizer applied it as if it were parametric.
atomicBuilder :: Monad m => String -> a -> [Expr] -> m (Either String a)
atomicBuilder _ built [] = return (Right built)
atomicBuilder name _ args = return (Left ("'" ++ name ++ "' takes no arguments here, but was applied to " ++ show (length args)))

buildInjFMap:: MonadState Int m => Program -> BuilderMap m
buildInjFMap prog = Map.fromList 
  [(name, \outerArgs -> case outerArgs of
      [] -> do
        substituteParamIDs <- replicateM (parameterCount (adts prog) name) demandUniqueNumber
        let substituteParamNames = map (("p_m" ++) . show) substituteParamIDs
        let args = map var substituteParamNames
        return $ Right $ foldl (flip (#->#)) (injF name args) substituteParamNames
      _ -> return (Left ("'" ++ name ++ "' takes no arguments here, but was applied to " ++ show (length outerArgs))))
    | (name, _) <- globalFEnv (adts prog)]

-- Main expression normalization function
normalizeExpr :: MonadState Int m => (BuilderMap m, BuilderMap m, Set.Set String) -> Expr -> m (Either String Expr)
normalizeExpr env@(parametricBuilders, atomicBuilders, benign) expr_ =
  case expr_ of
    -- Handle scopes first, adding bound variables before processing sub-expressions
    Expr ti (Lambda name body) -> do
      let body' = normalizeExpr (parametricBuilders, atomicBuilders, Set.insert name benign) body
      fmap (fmap (\b -> Expr ti (Lambda name b))) body'

    -- For all other expressions, normalize sub-expressions first then check for Apply pattern
    _ -> do
      subExprs <- fmap sequence (mapM (normalizeExpr env) (getSubExprs expr_))
      let mExpr = fmap (setSubExprs expr_) subExprs
      case mExpr of
        Left s -> return $ Left s
        Right expr' ->
          case expr' of
            -- Start of an Apply chain
            Expr _ (Apply (Expr _ (Apply _ _)) _) ->
              -- Need to collect all args in the chain and find base function.
              -- Collect from expr' (not expr_) so the args keep their normalization.
              let (base, args) = collectApplyChain expr'
              in case base of
                Expr _ (Var fname) | Just builder <- Map.lookup fname parametricBuilders -> do
                  build <- builder args
                  case build of
                    Left _ -> return $ Right expr' -- This prevents InjFs, which have multiple arguments from failing to build because here only one argument is applied
                    e -> return e
                _ -> return $ Right expr'
            Expr _ (Apply (Expr _ (Var fname)) arg)
              | not (Set.member fname benign)
              , Just builder <- Map.lookup fname parametricBuilders -> do
                build <- builder [arg]
                case build of
                  Left _ -> return $ Right expr' -- This prevents InjFs, which have multiple arguments from failing to build because here only one argument is applied
                  e -> return e
            Expr _ (Var fname)
              | not (Set.member fname benign)
              , Just builder <- Map.lookup fname atomicBuilders -> builder []
            _ -> return $ Right expr'

--replaceExpr :: Expr -> Expr -> Expr
--replaceExpr

-- Returns (base expression, arguments in application order)
collectApplyChain :: Expr -> (Expr, [Expr])
collectApplyChain (Expr _ (Apply left_ arg)) =
  let (base, args) = collectApplyChain left_
  in (base, args ++ [arg])  -- maintain order of application
-- Quick and dirty fix for multi parameter InjFs. The normalizatzion first creates a 1 parameter InjF and then stops with the normalization
-- We bypass this by tricking the normalization  that the InjF is in reality an application on a variable
collectApplyChain (Expr t (InjF (Named name) args)) = (Expr t (Var name), args)
collectApplyChain e = (e, [])

-- Helper to map over all expressions in a program
mapExprInProgram :: MonadState Int m => (Expr -> m (Either String Expr)) -> Program -> m (Either String Program)
mapExprInProgram f prog = do
  newFuncs <- mapM (\(name, expr_) -> f expr_ >>= \e -> return (name, e)) (functions prog)
  let newFuncs' = mapM (\(s, e) -> (e <&> \ex -> (s, ex))) newFuncs
  case newFuncs' of
    Right fs -> return $ Right $ prog { functions = fs }
    Left err -> return $ Left err
