{-# LANGUAGE ScopedTypeVariables #-}
-- | Per-value queries (task per-value-query-over-enumerated-slot,
-- "SPLL.PerValue"): a function whose signature marks one result slot
-- @Enumerated@ answers a probability query with the vector
-- @[P(slot = v, rest) | v <- domain]@.
--
-- The two properties that fix the meaning are checked on every program here:
-- element @v@ is the point query with the slot set to @v@ (within 1e-15,
-- dimension and impossibility flag included), and the vector's sum is the
-- query with the slot @ANY@. Both the fast path (the slot is the body's first
-- draw) and the fallback (one point query per value) are covered, on the
-- interpreter and on the Python and Julia backends.
module TestPerValue (perValueTests) where

import SPLL.Lang.Types
import SPLL.Typing.RType (RType(..))
import SPLL.Parser (tryParseProgram)
import SPLL.Prelude
import SPLL.IntermediateRepresentation
import qualified SPLL.CodeGenPyTorch
import qualified SPLL.CodeGenJulia
import End2EndTesting (qualifyConstructors, juliaTestFlags, pyMockDef, juliaMockDefs, networkMocks)
import TestCaseParser (corpusPplPath)
import TestSupport (bcConf, topKConf)

import Control.Monad (forM_, when, unless)
import Data.List (intercalate, isInfixOf)
import Data.Maybe (isJust, isNothing)
import Data.Text (pack, unpack, replace)
import System.Directory (getCurrentDirectory)
import System.Exit (ExitCode(..))
import System.IO (hPutStr, hClose)
import System.IO.Temp (withSystemTempFile)
import System.Process (readProcessWithExitCode)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertFailure, assertEqual, assertBool, Assertion)
import Text.Megaparsec (errorBundlePretty)

perValueTests :: TestTree
perValueTests = testGroup "PerValue"
  [ parserTests
  , validationTests
  , semanticsTests
  , refusalTests
  , structureTests
  , configTests
  , backendTests
  ]

-- ---------------------------------------------------------------------------
-- Programs

-- | The Guess-Who model at J = 20 attributes and 24 faces: the secret face is
-- drawn from @pick@, the perceiver reads the chosen face's attributes with
-- @see@, and the answers heard are the reading itself. The task's acceptance
-- program. The board is 24 face parameters selected by an @if@ chain: a
-- network applied to a value that depends on the enumerated face (@see (nth s
-- board)@) has no point query at this compiler, and the point query is what the
-- vector is checked against. 'guessWhoNthSrc' is that spelling.
guessWhoSrc :: String
guessWhoSrc = guessWhoSrcN faces

-- | The model at @n@ faces. The text backends get a smaller board: the
-- 24-deep @if@ chain of @main@'s own point query is nested too deeply for
-- Python's parser ("too many nested parentheses"), which is a property of the
-- point query this is checked against, not of the per-value function.
guessWhoSrcN :: Int -> String
guessWhoSrcN n = unlines
  [ faceDecl
  , "neural pick :: (Symbol -> Int) of [" ++ intercalate ", " (map show [0 .. n - 1]) ++ "]"
  , "neural see :: (Symbol -> Face)"
  , "main prior " ++ unwords boardParams ++ " ="
  , "  draw s = pick prior in"
  , "  draw truth = " ++ selectChain 0 ++ " in"
  , "  (s, truth)"
  , "posterior :: " ++ intercalate " -> " (replicate (n + 1) "Symbol") ++ " -> (Enumerated Int, Face)"
  , "posterior = main" ]
  where
    boardParams = [ "b" ++ show k | k <- [0 .. n - 1] ]
    selectChain k
      | k == n - 1 = "see b" ++ show k
      | otherwise = "(if s == " ++ show k ++ " then see b" ++ show k ++ " else " ++ selectChain (k + 1) ++ ")"

-- | The same model with the board as a list read by a recursive helper. Its
-- point query is intractable (the network's input depends on the enumerated
-- face), but the fast path makes the face a parameter of the given part, where
-- the input is deterministic, so the per-value query answers it. Checked
-- against the closed form.
guessWhoNthSrc :: String
guessWhoNthSrc = unlines
  [ faceDecl
  , pickDecl
  , "neural see :: (Symbol -> Face)"
  , "nth k xs = if k == 0 then head xs else nth (k - 1) (tail xs)"
  , "main prior board ="
  , "  draw s = pick prior in"
  , "  draw truth = see (nth s board) in"
  , "  (s, truth)"
  , "posterior :: Symbol -> [Symbol] -> (Enumerated Int, Face)"
  , "posterior = main" ]

faceDecl, pickDecl :: String
faceDecl = "data Face = Face " ++ intercalate ", " [ "a" ++ show j ++ "::Bool" | j <- [0 .. attrs - 1] ]
pickDecl = "neural pick :: (Symbol -> Int) of [" ++ intercalate ", " (map show [0 .. faces - 1]) ++ "]"

attrs, faces :: Int
attrs = 20
faces = 24

-- | The prior over faces: proportional to k + 1, except face 5, which has no
-- mass (so one element of every vector is an exact zero).
priorProbs :: [Double]
priorProbs = let w = [ if k == 5 then 0 else fromIntegral (k + 1) | k <- [0 .. faces - 1] ] in map (/ sum w) w

-- | Face k's reading of attribute j, as P(True). Attribute 0 reads True with
-- certainty on every face, so a transcript that heard a0 = False has
-- probability zero.
pTrue :: Int -> Int -> Double
pTrue _ 0 = 1.0
pTrue k j = (fromIntegral ((k * 7 + j * 3) `mod` 10) + 0.5) / 11

seeLogits :: Int -> [Double]
seeLogits k = concat [ [pTrue k j, 1 - pTrue k j] | j <- [0 .. attrs - 1] ]

-- | The interpreter's arguments: literal mock-NN envelopes.
guessWhoInterpArgs, guessWhoNthInterpArgs :: [IRValue]
guessWhoInterpArgs = literalMock priorProbs : [ literalMock (seeLogits k) | k <- [0 .. faces - 1] ]
guessWhoNthInterpArgs = [ literalMock priorProbs, listV [ literalMock (seeLogits k) | k <- [0 .. faces - 1] ] ]

literalMock :: [Double] -> IRValue
literalMock xs = VTuple (VInt 2) (listV (map VFloat xs))

-- | The text backends' arguments for the 'backendFaces'-face board: a Symbol
-- network is mocked as the identity, so the raw probability vectors are
-- passed in place of the handles.
guessWhoBackendArgs :: [IRValue]
guessWhoBackendArgs = listV (map VFloat (normalise (take backendFaces priorProbs)))
                      : [ listV (map VFloat (seeLogits k)) | k <- [0 .. backendFaces - 1] ]
  where normalise xs = map (/ sum xs) xs

backendFaces :: Int
backendFaces = 8

-- | P(s = k, heard) in closed form.
guessWhoReference :: [Maybe Bool] -> Int -> Double
guessWhoReference heard k =
  priorProbs !! k * product [ if b then pTrue k j else 1 - pTrue k j | (j, Just b) <- zip [0 ..] (take attrs heard) ]

listV :: [IRValue] -> IRValue
listV = VList . foldr ListCont EmptyList

face :: [Maybe Bool] -> IRValue
face answers = VADT "Face" [ maybe VAny VBool a | a <- take attrs (answers ++ repeat Nothing) ]

-- | Heard patterns: all ANY, a partial transcript, a fully concrete one, and a
-- transcript of probability zero.
heardPatterns :: [[Maybe Bool]]
heardPatterns =
  [ []
  , [Just True, Just False, Nothing, Just True]
  , [ Just (odd j || j == 0) | j <- [0 .. attrs - 1] ]
  , [Just False, Just True] ]

guessWhoHeard :: [IRValue]
guessWhoHeard = map face heardPatterns

-- | Queries against a pair-typed per-value function: each @rest@ under the
-- slot, plus the root @ANY@.
pairQueries :: [SigStep] -> [IRValue] -> [IRValue]
pairQueries path rests = VAny : [ setSlot path VAny r | r <- rests ]

-- | A tuple value with the slot at @path@ set to @v@; @rest@ supplies every
-- other component (a pair whose other half is ignored at the path).
setSlot :: [SigStep] -> IRValue -> IRValue -> IRValue
setSlot path v rest = go path rest
  where
    go [] _ = v
    go (SigFst : more) (VTuple a b) = VTuple (go more a) b
    go (SigSnd : more) (VTuple a b) = VTuple a (go more b)
    go (SigFst : more) VAny = VTuple (go more VAny) VAny
    go (SigSnd : more) VAny = VTuple VAny (go more VAny)
    go _ x = x

-- ---------------------------------------------------------------------------
-- Harness

parseOrFail :: String -> IO Program
parseOrFail src = case tryParseProgram "<per-value>" src of
  Left err -> assertFailure (errorBundlePretty err) >> error "unreachable"
  Right p -> return p

compileOrFail :: CompilerConfig -> Program -> IO IREnv
compileOrFail conf p = case compile conf p of
  Left err -> assertFailure err >> error "unreachable"
  Right env -> return env

-- | A per-value result, decoded: probabilities, dimensions, impossibility
-- flags and the domain, all in domain order.
data PerValue = PerValue { pvProbs :: [Double], pvDims :: [Double], pvImposs :: [Bool], pvValues :: [IRValue] }
  deriving Show

decodePerValue :: IRValue -> Either String PerValue
decodePerValue (VTuple (VTensor _ ps) (VTuple (VTensor _ ds) (VTuple (VTensor _ is) (VTensor _ vs)))) =
  PerValue <$> mapM float ps <*> mapM float ds <*> mapM bool is <*> pure vs
  where float (VFloat x) = Right x
        float x = Left ("not a float: " ++ show x)
        bool (VBool b) = Right b
        bool x = Left ("not a bool: " ++ show x)
decodePerValue v = Left ("not a per-value result: " ++ show v)

perValueQuery :: Program -> IREnv -> String -> [IRValue] -> IRValue -> IO PerValue
perValueQuery p env f args q = case runProbNamedC p env f args q of
  Left err -> assertFailure (f ++ " at " ++ show q ++ ": " ++ err) >> error "unreachable"
  Right v -> either (\e -> assertFailure e >> error "unreachable") return (decodePerValue v)

pointQuery :: Program -> IREnv -> String -> [IRValue] -> IRValue -> IO (Double, Double, Bool)
pointQuery p env f args q = case runProbNamedC p env f args q of
  Left err -> assertFailure (f ++ " at " ++ show q ++ ": " ++ err) >> error "unreachable"
  Right v@(VProbDim pr d) | Just imp <- resultImpossible v -> return (pr, d, imp)
  Right v -> assertFailure ("not a point result: " ++ show v) >> error "unreachable"

elementTolerance, sumTolerance :: Double
elementTolerance = 1e-15
sumTolerance = 1e-12

-- | The two defining properties at one query: every element is the point
-- query of @point@ with the slot set to that value, and the sum is the point
-- query with the slot ANY. Returns the vector, for further checks.
checkAgreement :: Program -> IREnv -> String -> String -> [SigStep] -> [IRValue] -> IRValue -> IO PerValue
checkAgreement p env f point path args q = do
  r <- perValueQuery p env f args q
  assertBool (f ++ ": empty domain") (not (null (pvValues r)))
  forM_ (zip4 (pvValues r) (pvProbs r) (pvDims r) (pvImposs r)) $ \(v, pr, d, imp) -> do
    (ppr, pd, pimp) <- pointQuery p env point args (setSlot path v q)
    let at = f ++ " at " ++ show q ++ ", slot = " ++ show v
    assertBool (at ++ ": element " ++ show pr ++ " vs point query " ++ show ppr) (abs (pr - ppr) <= elementTolerance)
    assertEqual (at ++ ": dimension") pd d
    assertEqual (at ++ ": impossibility") pimp imp
  (apr, _, _) <- pointQuery p env point args (setSlot path VAny q)
  assertBool (f ++ " at " ++ show q ++ ": sum " ++ show (sum (pvProbs r)) ++ " vs ANY query " ++ show apr)
    (abs (sum (pvProbs r) - apr) <= sumTolerance)
  return r
  where zip4 (a:as) (b:bs) (c:cs) (d:ds) = (a, b, c, d) : zip4 as bs cs ds
        zip4 _ _ _ _ = []

groupNamed :: IREnv -> String -> Maybe IRFunGroup
groupNamed (IREnv gs _ _) n = case [ g | g <- gs, groupName g == n ] of
  (g : _) -> Just g
  [] -> Nothing

refusalOf :: IREnv -> String -> String -> Maybe String
refusalOf env f lbl = groupNamed env f >>= fmap refusalReason . lookup lbl . refusedVariants

-- | Does the IR contain a node satisfying the predicate?
irAny :: (IRExpr -> Bool) -> IRExpr -> Bool
irAny pr e = pr e || any (irAny pr) (irChildren e)

irChildren :: IRExpr -> [IRExpr]
irChildren e = case e of
  IRIf a b c -> [a, b, c]
  IRSelect a b c -> [a, b, c]
  IROp _ a b -> [a, b]
  IRUnaryOp _ a -> [a]
  IRConstruct _ as -> as
  IRDestruct _ a -> [a]
  IRDensity _ _ a -> [a]
  IRCumulative _ _ a -> [a]
  IRLetIn _ a b -> [a, b]
  IRLambda _ a -> [a]
  IRApply a b -> [a, b]
  IRIsPossible _ a -> [a]
  IRBuiltin _ as -> as
  IRConformsTo _ a -> [a]
  _ -> []

isReduce :: IRExpr -> Bool
isReduce (IRBuiltin (BReduce _ _) _) = True
isReduce _ = False

callsVar :: String -> IRExpr -> Bool
callsVar n = irAny (\x -> case x of IRVar m -> m == n; _ -> False)

probBody :: IREnv -> String -> IO IRExpr
probBody env f = case groupNamed env f >>= probFun of
  Just (body, _) -> return body
  Nothing -> assertFailure ("no probability function for " ++ f) >> error "unreachable"

-- ---------------------------------------------------------------------------
-- Parsing

parserTests :: TestTree
parserTests = testGroup "signatures parse"
  [ testCase "a marked tuple component under parameter arrows" $ do
      p <- parseOrFail guessWhoNthSrc
      assertEqual "signature" [FnSignature "posterior" (TArrow TSymbol (TArrow (ListOf TSymbol) (Tuple TInt (TADT "Face")))) [[SigFst]]]
        (signatures p)
  , testCase "a tuple of three: the middle and the last component" $ do
      p <- parseOrFail "f :: (Int, Enumerated Bool, Bool)\nf = (1, (True, False))\ng :: (Int, (Bool, Enumerated Bool))\ng = (1, (True, False))\nmain = 1"
      assertEqual "paths" [[[SigSnd, SigFst]], [[SigSnd, SigSnd]]] (map sigEnumerated (signatures p))
      assertEqual "types" [Tuple TInt (Tuple TBool TBool)] (nubTypes (map sigType (signatures p)))
  , testCase "the whole result, and an unmarked signature" $ do
      p <- parseOrFail "f :: Enumerated Int\nf = 1\nmain :: Bool\nmain = True"
      assertEqual "marks" [[[]], []] (map sigEnumerated (signatures p))
  , testCase "a marker inside a parameter type is a parse error at the marker" $
      expectParseError "f :: Enumerated Int -> Int\nf x = x\nmain = 1" "cannot stand inside a parameter type"
  , testCase "a marker inside another marker is a parse error" $
      expectParseError "f :: Enumerated (Enumerated Int, Bool)\nf = (1, True)\nmain = 1" "inside another Enumerated"
  , testCase "a marker inside a list is a parse error" $
      expectParseError "f :: [Enumerated Int]\nf = [1]\nmain = 1" "a list element type"
  ]
  where
    nubTypes (t : ts) = t : nubTypes (filter (/= t) ts)
    nubTypes [] = []
    expectParseError src needle = case tryParseProgram "<per-value>" src of
      Right p -> assertFailure ("parsed: " ++ show (signatures p))
      Left err -> assertBool (errorBundlePretty err) (needle `isInfixOf` errorBundlePretty err)

-- ---------------------------------------------------------------------------
-- Validation

validationTests :: TestTree
validationTests = testGroup "signatures are checked"
  [ rejects "a signature with no definition" "g :: Bool\nmain = True" "has no definition"
  , rejects "two signatures for one name" "main :: Bool\nmain :: Bool\nmain = True" "more than one type signature"
  , rejects "two marked slots" "f :: (Enumerated Bool, Enumerated Bool)\nf = (True, False)\nmain = True"
      "marks 2 result slots Enumerated"
  , rejects "a definition taking a helper's name" "f :: (Enumerated Bool, Bool)\nf = (True, False)\nf__point = 1\nmain = True"
      "'f__point' is the name of a helper"
  , rejects "a declared type that is not the inferred one" "f :: (Enumerated Int, Int)\nf = (1, True)\nmain = True"
      "In the type signature of 'f'"
  , testCase "a correct unmarked signature changes nothing" $ do
      p <- parseOrFail "f :: Float -> Bool\nf x = Uniform < x\nmain :: Bool\nmain = f 0.25"
      env <- compileOrFail defaultCompilerConfig p
      (pr, _, _) <- pointQuery p env "main" [] (VBool True)
      assertBool (show pr) (abs (pr - 0.25) < 1e-12)
      assertBool "no helpers" (isNothing (groupNamed env "f__point"))
  ]
  where
    rejects name src needle = testCase name $ do
      p <- parseOrFail src
      case compile defaultCompilerConfig p of
        Right _ -> assertFailure "compiled"
        Left err -> assertBool err (needle `isInfixOf` err)

-- ---------------------------------------------------------------------------
-- Semantics on the interpreter

semanticsTests :: TestTree
semanticsTests = testGroup "elements are point queries, and sum to the ANY query"
  [ testCase "Guess-Who at J = 20, 24 faces (fast path)" $ do
      p <- parseOrFail guessWhoSrc
      env <- compileOrFail noIntegConf p
      forM_ (pairQueries [SigFst] [ VTuple VAny h | h <- guessWhoHeard ]) $ \q -> do
        r <- checkAgreement p env "posterior" "main" [SigFst] guessWhoInterpArgs q
        assertEqual "domain" (map VInt [0 .. faces - 1]) (pvValues r)
        assertEqual "the face without prior mass" 0 (pvProbs r !! 5)
      -- The zero-probability transcript is zero at every face.
      r0 <- perValueQuery p env "posterior" guessWhoInterpArgs (VTuple VAny (face [Just False]))
      assertBool (show (pvProbs r0)) (all (== 0) (pvProbs r0) && and (pvImposs r0))
  , testCase "Guess-Who with the board as a list: no point query, the fast path matches the closed form" $ do
      p <- parseOrFail guessWhoNthSrc
      env <- compileOrFail noIntegConf p
      assertBool "main has a point query after all; compare against it instead" (isNothing (groupNamed env "main" >>= probFun))
      forM_ heardPatterns $ \heard -> do
        r <- perValueQuery p env "posterior" guessWhoNthInterpArgs (VTuple VAny (face heard))
        forM_ (zip [0 ..] (pvProbs r)) $ \(k, pr) ->
          assertBool (show heard ++ ", face " ++ show k ++ ": " ++ show pr ++ " vs " ++ show (guessWhoReference heard k))
            (abs (pr - guessWhoReference heard k) <= 1e-15)
  , corpusCase "tupleDiscreteDistrib: a slot computed by an if (fallback)" "tupleDiscreteDistrib"
      "pv :: (Enumerated Int, Bool)\npv = main" [SigFst] [VTuple VAny (VBool True), VTuple VAny (VBool False), VTuple VAny VAny]
  , corpusCase "tupleCtorTestOfSharedDraw: a computed slot sharing a latent with the rest (fallback)" "tupleCtorTestOfSharedDraw"
      "pv :: (Enumerated Bool, Face)\npv = main" [SigFst]
      [ VTuple VAny (VADT "Face" [VBool True, VBool False]), VTuple VAny (VADT "Face" [VAny, VBool True]), VTuple VAny VAny ]
  , corpusCase "drawSharedDraw: the second component of (c, c) (fast path)" "drawSharedDraw"
      "pv :: (Bool, Enumerated Bool)\npv = main" [SigSnd] [VTuple (VBool True) VAny, VTuple (VBool False) VAny, VTuple VAny VAny]
  , srcCase "the whole result (fast path)" "pv :: Enumerated Int\npv = draw s = (if Uniform < 0.3 then 1 else (if Uniform < 0.5 then 2 else 3)) in s\nmain = 1"
      "pv" [] [VAny]
  , srcCase "the whole result, no draw (fallback)" "pv :: Enumerated Int\npv = if Uniform < 0.3 then 1 else (if Uniform < 0.5 then 2 else 3)\nmain = 1"
      "pv" [] [VAny]
  , srcCase "the slot is the second draw (fallback)"
      (unlines [ "main = draw t = Uniform < 0.4 in draw s = (if t then (if Uniform < 0.5 then 0 else 1) else 2) in (s, t)"
               , "pv :: (Enumerated Int, Bool)", "pv = main" ])
      "pv" [SigFst] [VTuple VAny (VBool True), VTuple VAny (VBool False), VTuple VAny VAny]
  , srcCaseWith "the middle of three components, with an argument (fast path)"
      (unlines [ "main q = draw b = (if Uniform < q then 1 else 2) in draw a = Uniform < 0.3 in (a, (b, a && (Uniform < 0.5)))"
               , "pv :: Float -> (Bool, Enumerated Int, Bool)", "pv x = main x" ])
      "pv" [SigSnd, SigFst]
      [ VTuple (VBool True) (VTuple VAny (VBool True)), VTuple VAny (VTuple VAny (VBool False)), VTuple (VBool False) (VTuple VAny VAny) ]
      [VFloat 0.25]
  , testCase "another function calling a per-value function gets its ordinary distribution" $ do
      p <- parseOrFail "pv :: (Enumerated Bool, Bool)\npv = draw c = Uniform < 0.3 in (c, c)\nmain = fst pv"
      env <- compileOrFail defaultCompilerConfig p
      (pr, _, _) <- pointQuery p env "main" [] (VBool True)
      assertBool (show pr) (abs (pr - 0.3) < 1e-12)
  ]
  where
    noIntegConf = defaultCompilerConfig { noIntegrate = True }
    corpusCase name base sig path qs = testCase name $ do
      src <- corpusPplPath base >>= readFile
      agree (src ++ "\n" ++ sig) "pv" path qs
    srcCase name src f path qs = srcCaseWith name src f path qs []
    srcCaseWith name src f path qs args = testCase name (agreeWith src f path qs args)
    agree src f path qs = agreeWith src f path qs []
    agreeWith src f path qs args = do
      p <- parseOrFail src
      env <- compileOrFail defaultCompilerConfig p
      forM_ qs (checkAgreement p env f (f ++ "__point") path args)

-- ---------------------------------------------------------------------------
-- Refusals

refusalTests :: TestTree
refusalTests = testGroup "slots without a finite domain are refused, naming the slot"
  [ refused "a continuous slot" defaultCompilerConfig
      "pv :: (Enumerated Float, Bool)\npv = draw x = Uniform in (x, x < 0.5)\nmain = 1"
      ["the Enumerated slot fst of 'pv' (Float)", "continuous"]
  , refused "an unbounded Int slot" defaultCompilerConfig
      "geo = if Uniform < 0.5 then 0 else 1 + geo\npv :: (Enumerated Int, Bool)\npv = (geo, True)\nmain = 1"
      ["the Enumerated slot fst of 'pv' (Int)", "no finite domain"]
  , refused "a domain over the materialization budget" defaultCompilerConfig { materializationCardinality = 2 }
      "pv :: Enumerated Int\npv = draw s = (if Uniform < 0.3 then 1 else (if Uniform < 0.5 then 2 else 3)) in s\nmain = 1"
      ["the Enumerated slot the whole result of 'pv' (Int)", "has 3 values, over the materialization budget of 2"]
  , refused "--batched" defaultCompilerConfig { batched = True }
      "pv :: (Enumerated Bool, Bool)\npv = draw c = Uniform < 0.3 in (c, c)\nmain = 1"
      ["not supported under --batched"]
  , testCase "the refusal is what a query reports" $ do
      p <- parseOrFail "pv :: (Enumerated Float, Bool)\npv = draw x = Uniform in (x, x < 0.5)\nmain = 1"
      env <- compileOrFail defaultCompilerConfig p
      case runProbNamedC p env "pv" [] (VTuple VAny (VBool True)) of
        Right v -> assertFailure ("answered: " ++ show v)
        Left err -> assertBool err ("continuous" `isInfixOf` err)
  ]
  where
    refused name conf src needles = testCase name $ do
      p <- parseOrFail src
      env <- compileOrFail conf p
      assertBool "probability function present" (isNothing (groupNamed env "pv" >>= probFun))
      case refusalOf env "pv" "prob" of
        Nothing -> assertFailure "no refusal recorded"
        Just why -> forM_ needles $ \n -> assertBool why (n `isInfixOf` why)

-- ---------------------------------------------------------------------------
-- Structure

structureTests :: TestTree
structureTests = testGroup "compiled structure"
  [ testCase "the fast path never reduces over the marked slot" $ do
      p <- parseOrFail guessWhoSrc
      env <- compileOrFail defaultCompilerConfig { noIntegrate = True } p
      body <- probBody env "posterior"
      assertBool "a reduction in the per-value body" (not (irAny isReduce body))
      assertBool "calls the prior" (callsVar "posterior__prior_prob" body)
      assertBool "calls the given part" (callsVar "posterior__given_prob" body)
      assertBool "no point-query fallback" (not (callsVar "posterior__point_prob" body))
      -- The slot is a parameter of the given part, so nothing enumerates it there either.
      given <- probBody env "posterior__given"
      assertBool "the given part takes the slot as its last parameter" (lastParam given == Just "s")
  , testCase "the fallback calls the point query once per value" $ do
      src <- corpusPplPath "tupleDiscreteDistrib" >>= readFile
      p <- parseOrFail (src ++ "\npv :: (Enumerated Int, Bool)\npv = main")
      env <- compileOrFail defaultCompilerConfig p
      body <- probBody env "pv"
      assertBool "calls the point query" (callsVar "pv__point_prob" body)
      assertBool "no fast-path helpers" (isNothing (groupNamed env "pv__given"))
  , testCase "a per-value function has no integrate and no writeLogits; the slot probe is not compiled" $ do
      p <- parseOrFail "pv :: (Enumerated Bool, Bool)\npv = draw c = Uniform < 0.3 in (c, c)\nmain = 1"
      env <- compileOrFail defaultCompilerConfig p
      g <- maybe (assertFailure "no group" >> error "unreachable") return (groupNamed env "pv")
      assertBool "integrate" (isNothing (integFun g))
      assertBool "writeLogits" (isNothing (writeLogitsFun g))
      assertBool "integrate refusal names the point function" (maybe False ("pv__point" `isInfixOf`) (refusalOf env "pv" "integ"))
      assertBool "generate" (isJust (genFun g))
      assertBool "slot probe compiled" (isNothing (groupNamed env "pv__slot"))
      assertBool "the point function keeps its integrate" (isJust (groupNamed env "pv__point" >>= integFun))
  ]
  where
    lastParam e = go e Nothing
      where go (IRLambda n b) _ = go b (Just n)
            go _ acc = acc

-- ---------------------------------------------------------------------------
-- topK, log space and branch counts are per element

configTests :: TestTree
configTests = testGroup "topK, log space and branch counts are the point query's, per element"
  [ testCase "topK: elements are the topK point queries (fallback)" $ do
      p <- parseOrFail guessWhoSrc
      let conf = (topKConf 0.02) { noIntegrate = True }
      env <- compileOrFail conf p
      assertBool "topK uses the fallback" (isNothing (groupNamed env "posterior__given"))
      forM_ [ VTuple VAny h | h <- take 2 guessWhoHeard ] $ \q -> do
        r <- perValueQuery p env "posterior" guessWhoInterpArgs q
        forM_ (zip (pvValues r) (pvProbs r)) $ \(v, pr) -> do
          (ppr, _, _) <- pointQuery p env "posterior__point" guessWhoInterpArgs (setSlot [SigFst] v q)
          assertBool (show v ++ ": " ++ show pr ++ " vs " ++ show ppr) (abs (pr - ppr) <= elementTolerance)
  , testCase "log space: elements are the log-space point queries (fast path)" $ do
      p <- parseOrFail guessWhoSrc
      let conf = defaultCompilerConfig { logSpace = True, noIntegrate = True }
      env <- compileOrFail conf p
      assertBool "fast path" (isJust (groupNamed env "posterior__given"))
      forM_ [ VTuple VAny h | h <- take 3 guessWhoHeard ] $ \q -> do
        r <- perValueQuery p env "posterior" guessWhoInterpArgs q
        forM_ (zip (pvValues r) (pvProbs r)) $ \(v, pr) -> do
          (ppr, _, _) <- pointQuery p env "main" guessWhoInterpArgs (setSlot [SigFst] v q)
          assertBool (show v ++ ": " ++ show pr ++ " vs " ++ show ppr)
            (pr == ppr || abs (pr - ppr) <= 1e-12 * max 1 (abs ppr))
  , testCase "branch counts: the layout gains a count vector, each the point query's" $
      forM_ [ ("pv :: (Enumerated Bool, Bool)\npv = draw c = Uniform < 0.3 in (c, c)\nmain = 1", [SigFst], [VTuple VAny (VBool True), VTuple VAny VAny])
            , ("pv :: Enumerated Int\npv = draw s = (if Uniform < 0.3 then 1 else (if Uniform < 0.5 then 2 else 3)) in s\nmain = 1", [], [VAny])
            , ("pv :: (Enumerated Int, Bool)\npv = (if Uniform < 0.5 then 0 else (if Uniform < 0.5 then 1 else 2), Uniform < 0.7)\nmain = 1", [SigFst], [VTuple VAny (VBool False)]) ] $ \(src, path, qs) -> do
        p <- parseOrFail src
        env <- compileOrFail bcConf p
        forM_ qs $ \q -> case runProbNamedC p env "pv" [] q of
          Right (VTuple (VTensor _ ps) (VTuple (VTensor _ _) (VTuple (VTensor _ bcs) (VTuple (VTensor _ _) (VTensor _ vs))))) -> do
            assertEqual "lengths" (length ps) (length bcs)
            forM_ (zip vs bcs) $ \(v, bc) -> case runProbNamedC p env "pv__point" [] (setSlot path v q) of
              Right (VProbDimBC _ _ pbc) -> assertEqual (src ++ " at " ++ show v ++ ": branch count") (VFloat pbc) bc
              other -> assertFailure ("point layout: " ++ show other)
          other -> assertFailure ("layout: " ++ show other)
  ]

-- ---------------------------------------------------------------------------
-- Python and Julia

backendTests :: TestTree
backendTests = testGroup "the text backends agree with their own point queries"
  [ testCase "Python: Guess-Who (fast path)" $ do
      p <- parseOrFail (guessWhoSrcN backendFaces)
      env <- compileOrFail defaultCompilerConfig { noIntegrate = True } p
      python p env "posterior" "main" [SigFst] guessWhoBackendArgs [ VTuple VAny h | h <- guessWhoHeard ]
  , testCase "Python: tupleCtorTestOfSharedDraw (fallback)" $ do
      (p, env) <- sharedDraw
      python p env "pv" "pv__point" [SigFst] [] sharedDrawQueries
  , testCase "Julia: Guess-Who (fast path) and tupleCtorTestOfSharedDraw (fallback)" $ do
      p <- parseOrFail (guessWhoSrcN backendFaces)
      env <- compileOrFail defaultCompilerConfig { noIntegrate = True } p
      (p2, env2) <- sharedDraw
      julia [ (p, env, "posterior", "main", [SigFst], guessWhoBackendArgs, [ VTuple VAny h | h <- guessWhoHeard ])
            , (p2, env2, "pv", "pv__point", [SigFst], [], sharedDrawQueries) ]
  ]
  where
    sharedDraw = do
      src <- corpusPplPath "tupleCtorTestOfSharedDraw" >>= readFile
      p <- parseOrFail (src ++ "\npv :: (Enumerated Bool, Face)\npv = main")
      env <- compileOrFail defaultCompilerConfig p
      return (p, env)
    -- Concrete rests only: a point query with the Face slot ANY reaches a mask
    -- variant the text backends retire (a VAnyExcept witness, see
    -- docs/observation-masks.md), which the interpreter-side tests cover.
    sharedDrawQueries = [ VTuple VAny (VADT "Face" [VBool True, VBool False]), VTuple VAny (VADT "Face" [VBool False, VBool True]) ]

-- | Run one per-value function's checks in one python3 process: every element
-- against the point query at that value, and the sum against the ANY query.
python :: Program -> IREnv -> String -> String -> [SigStep] -> [IRValue] -> [IRValue] -> Assertion
python p env f point path args qs = do
  projectDir <- getCurrentDirectory
  let src = unpack (replace (pack "from torch.nn import Module") (pack "\nclass Module:\n  pass\n")
                     (pack (intercalate "\n" (SPLL.CodeGenPyTorch.generateFunctions True env))))
      argList = concatMap ((", " ++) . SPLL.CodeGenPyTorch.pyVal) args
      check q = unlines
        [ "_r = " ++ f ++ ".forward(" ++ SPLL.CodeGenPyTorch.pyVal q ++ argList ++ ")"
        , "_vals = list(_r[1][1][1])"
        , "assert len(_vals) > 0"
        , "for _i, _v in enumerate(_vals):"
        , "    _q = " ++ pySetSlot path "_v" (SPLL.CodeGenPyTorch.pyVal q)
        , "    _p = " ++ point ++ ".forward(_q" ++ argList ++ ")"
        , "    if abs(_r[0][_i] - _p[0]) > " ++ show elementTolerance ++ " or _r[1][0][_i] != _p[1][0] or _r[1][1][0][_i] != _p[1][1]:"
        , "        raise ValueError('element ' + str(_v) + ': ' + str((_r[0][_i], _r[1][0][_i], _r[1][1][0][_i])) + ' vs ' + str((_p[0], _p[1][0], _p[1][1])))"
        , "_a = " ++ point ++ ".forward(" ++ SPLL.CodeGenPyTorch.pyVal (setSlot path VAny q) ++ argList ++ ")"
        , "if abs(sum(_r[0]) - _a[0]) > " ++ show sumTolerance ++ ":"
        , "    raise ValueError('sum ' + str(sum(_r[0])) + ' vs ANY ' + str(_a[0]))" ]
      script = "import sys\nsys.path.insert(0, " ++ show projectDir ++ ")\n"
               ++ concatMap pyMockDef (networkMocks p) ++ src ++ "\n" ++ concatMap check qs
  runScript "python3" [] ".py" script
  where
    -- The query with the slot replaced by the Python variable @v@, rebuilt from
    -- the rendered query so that ANY above the slot stays ANY elsewhere.
    pySetSlot [] v _ = v
    pySetSlot steps v q = "_set(" ++ q ++ ", " ++ show (map stepIx steps) ++ ", " ++ v ++ ")"
    stepIx SigFst = 0 :: Int
    stepIx SigSnd = 1

-- | The Julia twin of 'python', every program in one julia process.
julia :: [(Program, IREnv, String, String, [SigStep], [IRValue], [IRValue])] -> Assertion
julia programs = do
  projectDir <- getCurrentDirectory
  let body = concat
        [ "module " ++ m ++ "\nusing ..JuliaSPPLLib\n" ++ juliaMockDefs (networkMocks p)
          ++ intercalate "\n" (SPLL.CodeGenJulia.generateFunctions env) ++ "\nend\n"
          ++ concatMap (check m f point path args) qs
        | (i, (p, env, f, point, path, args, qs)) <- zip [0 :: Int ..] programs, let m = "PV" ++ show i ]
      script = "include(\"" ++ projectDir ++ "/juliaLib.jl\")\nusing .JuliaSPPLLib\n" ++ setDef ++ body
  runScript "julia" juliaTestFlags ".jl" script
  where
    jv m = SPLL.CodeGenJulia.juliaVal . qualifyConstructors m
    check m f point path args q =
      let argList = concatMap ((", " ++) . jv m) args
          setQ = case path of
            [] -> "_v"
            steps -> "_set(" ++ jv m q ++ ", " ++ show (map stepIx steps) ++ ", _v)"
      in unlines
        [ "_r = " ++ m ++ "." ++ f ++ "_prob(" ++ jv m q ++ argList ++ ")"
        , "_vals = _r[2][2][2]"
        , "length(_vals) > 0 || error(\"empty domain\")"
        , "for (_i, _v) in enumerate(_vals)"
        , "  _q = " ++ setQ
        , "  _p = " ++ m ++ "." ++ point ++ "_prob(_q" ++ argList ++ ")"
        , "  if abs(_r[1][_i] - _p[1]) > " ++ show elementTolerance ++ " || _r[2][1][_i] != _p[2][1] || _r[2][2][1][_i] != _p[2][2]"
        , "    error(\"element \" * string(_v) * \": \" * string((_r[1][_i], _r[2][1][_i], _r[2][2][1][_i])) * \" vs \" * string((_p[1], _p[2][1], _p[2][2])))"
        , "  end"
        , "end"
        , "_a = " ++ m ++ "." ++ point ++ "_prob(" ++ jv m (setSlot path VAny q) ++ argList ++ ")"
        , "abs(sum(_r[1]) - _a[1]) <= " ++ show sumTolerance ++ " || error(\"sum \" * string(sum(_r[1])) * \" vs ANY \" * string(_a[1]))" ]
    stepIx SigFst = 1 :: Int
    stepIx SigSnd = 2
    -- A query with the slot at an index path replaced; ANY above the slot
    -- expands to a pair of ANYs.
    setDef = unlines
      [ "function _set(q, path, v)"
      , "  isempty(path) && return v"
      , "  if q isa String && q == \"ANY\""
      , "    q = T(\"ANY\", \"ANY\")"
      , "  end"
      , "  path[1] == 1 ? T(_set(q[1], path[2:end], v), q[2]) : T(q[1], _set(q[2], path[2:end], v))"
      , "end" ]

runScript :: String -> [String] -> String -> String -> Assertion
runScript exe flags ext script = do
  let script' = if exe == "python3" then pySetDef ++ script else script
  (code, out, err) <- withSystemTempFile ("per_value" ++ ext) $ \path h -> do
    hPutStr h script'
    hClose h
    readProcessWithExitCode exe (flags ++ [path]) ""
  when (code /= ExitSuccess) $ assertFailure (exe ++ " failed:\n" ++ out ++ err)
  unless (null out) (return ())
  where
    pySetDef = unlines
      [ "def _set(q, path, v):"
      , "    if not path: return v"
      , "    from pythonLib import T as _T, isAny as _isAny"
      , "    if _isAny(q): q = _T('ANY', 'ANY')"
      , "    return _T(_set(q[0], path[1:], v), q[1]) if path[0] == 0 else _T(q[0], _set(q[1], path[1:], v))" ]
