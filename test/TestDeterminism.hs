-- | Milestone-2 tests for 'SPLL.Typing.Determinism' (design
-- @modality-typesystem-port@ §4): the forward determinism dataflow and its
-- call-graph fixpoint.
--
-- Two kinds of check:
--
--   * /unit/ cases on small hand-written programs pin the propagation rules
--     (anchors, randomness sources, let bindings, top-level calls, the
--     fixpoint);
--   * /corpus invariants/ assert across every @testCases/@ program that the
--     self-sufficient anchors (Constant / ThetaI / Subtree) are always known
--     and the randomness leaves (Uniform / Normal / ReadNN) never are.
module TestDeterminism (determinismTests) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, (@?=))

import SPLL.Lang.Types
import SPLL.Lang.Lang (getTypeInfo, getSubExprs)
import SPLL.Analysis (annotateEnumsProg)
import SPLL.Typing.ForwardChaining (annotateProg)
import SPLL.Typing.Determinism

import SPLL.Parser (tryParseProgram)
import TestCaseParser (parseProgram)
import End2EndTesting (getAllTestFiles)

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

-- | Parse + the two pre-inference annotation stages this pass depends on.
prep :: String -> Program
prep src = case tryParseProgram "test" src of
  Left err -> error ("parse failed: " ++ show err)
  Right p  -> annotateProg (annotateEnumsProg p)

-- | Every node of a program body, self first.
universe :: Expr -> [Expr]
universe e = e : concatMap universe (getSubExprs e)

allNodes :: Program -> [Expr]
allNodes prog = concatMap (universe . snd) (functions prog)

-- | Determinism values of every node matching a predicate.
detsWhere :: (Expr -> Bool) -> Program -> DetMap -> [Bool]
detsWhere p prog dm =
  [ isKnownAnchor dm (chainName (getTypeInfo e)) | e <- allNodes prog, p e ]

-- Node predicates ------------------------------------------------------------

isThetaNode, isConstNode, isNormalVar, isReadNN, isPlus :: Expr -> Bool
isThetaNode (ThetaI{})  = True
isThetaNode (Subtree{}) = True
isThetaNode _           = False
isConstNode (Constant{}) = True
isConstNode _            = False
isNormalVar (Var _ "Normal")  = True
isNormalVar (Var _ "Uniform") = True
isNormalVar _                 = False
isReadNN (ReadNN{}) = True
isReadNN _          = False
isPlus (InjF _ (Named "plus") _) = True
isPlus _                         = False

-- | Determinism of the result of a named top-level function — i.e. of the body
-- beneath its parameter lambdas (a bare 'Lambda' node is itself never an anchor,
-- so we peel to the value it returns).
rootDet :: String -> Program -> DetMap -> Bool
rootDet fname prog dm =
  case lookup fname (functions prog) of
    Nothing -> error ("no such function: " ++ fname)
    Just body -> isKnownAnchor dm (chainName (getTypeInfo (peel body)))
  where peel (Lambda _ _ b) = peel b
        peel e              = e

-- ---------------------------------------------------------------------------
-- Unit cases
-- ---------------------------------------------------------------------------

unitTests :: TestTree
unitTests = testGroup "unit rules"
  [ testCase "constants and theta are anchors" $ do
      let p  = prep "main t = theta t @ 0"
          dm = determinismMap p
      and (detsWhere isThetaNode p dm) @?= True

  , testCase "Normal is never an anchor" $ do
      let p  = prep "main = Normal + Normal"
          dm = determinismMap p
      or (detsWhere isNormalVar p dm) @?= False
      -- the plus over two randoms is itself non-deterministic
      detsWhere isPlus p dm @?= [False]

  , testCase "deterministic operands keep the result deterministic" $ do
      let p  = prep "main t = (theta t @ 0) + (theta t @ 1)"
          dm = determinismMap p
      detsWhere isPlus p dm @?= [True]
      rootDet "main" p dm @?= True

  , testCase "one random operand taints the result" $ do
      let p  = prep "main t = Normal + (theta t @ 0)"
          dm = determinismMap p
      detsWhere isPlus p dm @?= [False]
      -- but the theta sub-tree is still individually known
      and (detsWhere isThetaNode p dm) @?= True

  , testCase "let binds the argument's determinism" $ do
      let pDet  = prep "main t = let x = theta t @ 0 in x + 1.0"
          pRand = prep "main = let x = Normal in x + 1.0"
      rootDet "main" pDet  (determinismMap pDet)  @?= True
      rootDet "main" pRand (determinismMap pRand) @?= False

  , testCase "top-level call uses the function summary" $ do
      -- f is determinism-preserving; the call result follows the argument.
      let pDet  = prep "f y = y + 1.0\nmain t = f (theta t @ 0)"
          pRand = prep "f y = y + 1.0\nmain = f Normal"
      rootDet "main" pDet  (determinismMap pDet)  @?= True
      rootDet "main" pRand (determinismMap pRand) @?= False

  , testCase "summary of a randomness-introducing function is False" $ do
      let p = prep "f y = y + Normal\nmain t = f (theta t @ 0)"
      Map.lookup "f" (functionSummaries p) @?= Just False
      -- even with a deterministic argument the call is non-deterministic
      rootDet "main" p (determinismMap p) @?= False

  , testCase "summary of a pure function is True" $ do
      let p = prep "f y = y + 1.0\nmain t = f (theta t @ 0)"
      Map.lookup "f" (functionSummaries p) @?= Just True
  ]

-- ---------------------------------------------------------------------------
-- Corpus invariants
-- ---------------------------------------------------------------------------

corpusInvariants :: [(FilePath, Program)] -> TestTree
corpusInvariants progs = testGroup "corpus invariants"
  [ testCase "Constant / ThetaI / Subtree are always known anchors" $
      mapM_ (checkAll "anchor leaf not known"
               (\e -> isConstNode e || isThetaNode e) id) progs
  , testCase "Uniform / Normal / ReadNN are never known anchors" $
      mapM_ (checkAll "randomness leaf marked known"
               (\e -> isNormalVar e || isReadNN e) not) progs
  ]
  where
    checkAll msg pick expect (file, p) =
      let dm = determinismMap p
      in assertBool (msg ++ " in " ++ file)
                    (all expect (detsWhere pick p dm))

determinismTests :: IO TestTree
determinismTests = do
  files <- getAllTestFiles
  progs <- mapM (\(ppl, _tst) -> (,) ppl . prepProg <$> parseProgram ppl) files
  return $ testGroup "Determinism"
    [ unitTests
    , corpusInvariants progs
    ]
  where prepProg = annotateProg . annotateEnumsProg
