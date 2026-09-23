-- | The observation tree, leaf slots, correlation classes, and the masked
-- program (task @observation-mask-analysis@, design
-- @witnessed-per-query-capability@).
--
-- The groups mirror the task's acceptance criteria one for one: the tree walk,
-- the slot verdicts and correlation classes on the design's W\/O\/N\/I\/C\/B\/S
-- programs, the self-containment of every slot of the neural corpus programs,
-- the per-mask lattice verdicts, and pruning followed by the existing pipeline.
module TestObservationMask (observationMaskTests) where

import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.ObservationMask
import SPLL.Prelude
import SPLL.Parser (tryParseProgram)
import SPLL.IntermediateRepresentation
import SPLL.Typing.PType (PType(..))
import SPLL.Typing.RType (RType(..))
import TestCaseParser (corpusPplPath)

import Control.Monad (forM_)
import Data.List (find, sort)
import qualified Data.Set as Set
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertFailure, assertEqual, assertBool)

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

parseOrFail :: String -> IO Program
parseOrFail src = case tryParseProgram "<test>" src of
  Left err -> assertFailure ("parse failed: " ++ show err)
  Right p  -> return p

-- | The chain-named, RType-inferred program the analysis reads, plus the
-- declaration named.
analysed :: String -> String -> IO ([ADTDecl], [FnDecl], FnDecl)
analysed fname src = do
  prog <- parseOrFail src
  case rtypedProgram prog of
    Left err -> assertFailure ("typing failed: " ++ err)
    Right rtyped -> do
      -- Chain names are what latent identity is keyed by, so the analysis reads
      -- the chain-named program rather than the bare RType-inferred one.
      let env = chainNamedProgram rtyped
      case find ((== fname) . fst) (functions env) of
        Nothing -> assertFailure ("no such function: " ++ fname)
        Just d  -> return (adts env, functions env, d)

-- | Slot paths, rendered, in tree order.
slotNames :: [ADTDecl] -> ObsTree -> [String]
slotNames decls t = map (prettySlot decls) (obsSlots t)

treeOf :: String -> String -> IO ([ADTDecl], ObsTree, [FnDecl])
treeOf fname src = do
  (decls, fenv, decl) <- analysed fname src
  return (decls, observationTree decls decl, fenv)

-- | The slot verdicts, rendered as @(path, isSelfContained)@.
verdictsOf :: String -> String -> IO [(String, Bool)]
verdictsOf fname src = do
  (decls, tree, fenv) <- treeOf fname src
  return [ (prettySlot decls s, v == SelfContained)
         | (s, v) <- slotVerdicts decls fenv tree ]

-- | The correlation classes, rendered and sorted so the test does not depend on
-- class discovery order.
classesOf :: String -> String -> IO [[String]]
classesOf fname src = do
  (decls, tree, fenv) <- treeOf fname src
  return (sort (map (sort . map (prettySlot decls)) (correlationClasses (slotLatents decls fenv tree))))

-- | The mask table of one function, keyed by the design's tuple notation.
tableOf :: String -> String -> IO [(String, PType)]
tableOf fname src = do
  prog <- parseOrFail src
  case marginalReport defaultCompilerConfig prog of
    Left err -> assertFailure ("marginalReport failed: " ++ err)
    Right rs -> case find ((== fname) . fmName) rs of
      Nothing -> assertFailure ("no report for " ++ fname)
      Just r  -> case fmTable r of
        MaskTable rows -> return [ (prettyMask (fmEnumerated r) m, pt) | (m, pt) <- rows ]
        other          -> assertFailure ("expected a mask table, got " ++ show other)

-- | Assert one row of a mask table, by the design's @(_, ANY)@ spelling.
assertRow :: [(String, PType)] -> String -> PType -> IO ()
assertRow rows key expected = case lookup key rows of
  Nothing -> assertFailure ("no mask row " ++ key ++ " in " ++ show (map fst rows))
  Just pt -> assertEqual ("mask " ++ key) expected pt

-- ---------------------------------------------------------------------------
-- The design's programs
-- ---------------------------------------------------------------------------

progW, progO, progN, progI, progC, progB, progS1 :: String
progW  = "main = let x = Uniform in let y = x + Uniform in (x, y)"
progO  = "main = let x = Uniform in let y = Uniform in (x, (x+y+3.0, x+y+2.0))"
progN  = "main = let x = Uniform in let y = Uniform in (x+y, (x, y))"
progI  = "main = let x = Uniform in let y = Uniform in (x, y)"
progC  = "main = let x = Uniform in let y = x + Uniform in let z = y + Uniform in (x, (y, z))"
progB  = "main = let x = Uniform in (x, 1.0 - x)"
progS1 = "main = let x = Uniform in (x, Uniform)"

-- ---------------------------------------------------------------------------
-- 1. The tree walk
-- ---------------------------------------------------------------------------

treeWalkTests :: TestTree
treeWalkTests = testGroup "observation tree walk"
  [ testCase "nested tuples descend to three leaves" $ do
      (decls, t, _) <- treeOf "main" "main = (Uniform, (Uniform, Uniform))"
      assertEqual "slots" ["fst", "snd.fst", "snd.snd"] (slotNames decls t)

  , testCase "an Either under a tuple descends through the tag" $ do
      (decls, t, _) <- treeOf "main" "main = (Uniform, left Uniform)"
      assertEqual "slots" ["fst", "snd.fromLeft"] (slotNames decls t)

  , testCase "a single-occurrence let-bound tuple root is followed" $ do
      (decls, t, _) <- treeOf "main" "main = let t = (Uniform, Uniform) in t"
      assertEqual "slots" ["fst", "snd"] (slotNames decls t)

  , testCase "a root Var occurring twice is NOT followed" $ do
      -- `t` is read by `u`'s value as well as being the observation root, so the
      -- accessor path from the root no longer identifies the sub-expression and
      -- the descent must stop.
      (decls, t, _) <- treeOf "main"
        "main = let t = (Uniform, 0.5) in let u = fst t + 1.0 in t"
      assertEqual "slots" ["<root>"] (slotNames decls t)

  , testCase "an if root yields one leaf" $ do
      (decls, t, _) <- treeOf "main"
        "main = if Uniform < 0.5 then (1.0, 2.0) else (3.0, 4.0)"
      assertEqual "slots" ["<root>"] (slotNames decls t)
  ]

-- ---------------------------------------------------------------------------
-- 2. Slots, classes, self-containment
-- ---------------------------------------------------------------------------

classTests :: TestTree
classTests = testGroup "leaf slots and correlation classes"
  [ testCase "W has one class" $
      classesOf "main" progW >>= assertEqual "classes" [["fst", "snd"]]
  , testCase "O has one class" $
      classesOf "main" progO >>= assertEqual "classes" [["fst", "snd.fst", "snd.snd"]]
  , testCase "N has one class" $
      classesOf "main" progN >>= assertEqual "classes" [["fst", "snd.fst", "snd.snd"]]
  , testCase "C has one class" $
      classesOf "main" progC >>= assertEqual "classes" [["fst", "snd.fst", "snd.snd"]]
  , testCase "B has one class" $
      classesOf "main" progB >>= assertEqual "classes" [["fst", "snd"]]
  , testCase "I has two singleton classes" $
      classesOf "main" progI >>= assertEqual "classes" [["fst"], ["snd"]]

  , testCase "let x = Uniform in (x, Uniform): two classes, slot 1 enumerated" $ do
      classesOf "main" progS1 >>= assertEqual "classes" [["fst"], ["snd"]]
      verdictsOf "main" progS1
        >>= assertEqual "verdicts" [("fst", False), ("snd", True)]

  , testCase "I's slots are both enumerated although independent" $
      -- Independent, so two classes -- but each reads a latent drawn OUTSIDE it,
      -- which is what makes the existing per-field anySafe guard inexact.
      verdictsOf "main" progI
        >>= assertEqual "verdicts" [("fst", False), ("snd", False)]
  ]

-- ---------------------------------------------------------------------------
-- 3. The neural / applied-helper programs have no enumerated slots
-- ---------------------------------------------------------------------------

-- | Every corpus program whose slots must all come out self-contained: the
-- per-function-marginals encoder and the plan-guided enumeration family. Their
-- fields read distinct PartitionPlan leaves (or nothing random at all), so the
-- plan-guided engine keeps its per-leaf wildcard handling and gets no variants.
selfContainedCorpus :: [String]
selfContainedCorpus =
  [ "encode_per_function_marginals"
  , "planEnumContPair"
  , "planEnumInlineADT"
  , "planEnumContAffine"
  , "planEnumInline"
  , "planEnumContPoint"
  ]

corpusSelfContainedTests :: TestTree
corpusSelfContainedTests =
  testGroup "neural corpus programs have no enumerated slots"
    [ testCase name $ do
        path <- corpusPplPath name
        src  <- readFile path
        prog <- parseOrFail src
        case marginalReport defaultCompilerConfig prog of
          Left err -> assertFailure ("marginalReport failed: " ++ err)
          Right rs -> forM_ rs $ \r -> do
            assertEqual (fmName r ++ ": enumerated slots") [] (fmEnumerated r)
            assertEqual (fmName r ++ ": mask table") NoEnumeratedSlots (fmTable r)
    | name <- selfContainedCorpus ]

-- ---------------------------------------------------------------------------
-- 4. The mask table
-- ---------------------------------------------------------------------------

maskTableTests :: TestTree
maskTableTests = testGroup "per-mask capability (the masked program's PType)"
  [ testCase "W: (_,_) and (_,ANY) admitted, (ANY,_) is Bottom" $ do
      rows <- tableOf "main" progW
      assertRow rows "(_, _)"   Integrate
      assertRow rows "(_, ANY)" Integrate
      -- The convolution the design says must never be answered.
      assertRow rows "(ANY, _)" Bottom

  , testCase "N: every mask with at least two concrete slots is admitted" $ do
      rows <- tableOf "main" progN
      forM_ [ r | r@(k, _) <- rows, length (filter (== '_') k) >= 2 ] $ \(k, pt) ->
        assertBool ("mask " ++ k ++ " should be admitted, got " ++ show pt) (pt /= Bottom)

  , testCase "C: (_,(ANY,concrete)) is Bottom, (_,(ANY,ANY)) is admitted" $ do
      rows <- tableOf "main" progC
      assertRow rows "(_, ANY, _)"   Bottom
      assertRow rows "(_, ANY, ANY)" Integrate

  , testCase "the budget declines a function with too many enumerated slots" $ do
      prog <- parseOrFail progC
      let tight = defaultCompilerConfig { marginalSlots = 2 }
      case marginalReport tight prog of
        Left err -> assertFailure err
        Right rs -> case fmTable <$> find ((== "main") . fmName) rs of
          Just (OverBudget k b) -> assertEqual "budget" (3 :: Int, 2 :: Int) (k, b)
          other -> assertFailure ("expected OverBudget, got " ++ show other)

  , testCase "maskTable lists only functions that have one" $ do
      prog <- parseOrFail progW
      case maskTable defaultCompilerConfig prog of
        Left err -> assertFailure err
        Right t  -> assertEqual "functions" ["main"] (map fst t)
  ]

-- ---------------------------------------------------------------------------
-- 5. Pruning, and the pipeline running on the pruned program
-- ---------------------------------------------------------------------------

-- | Prune one function of a program and compile the result from the post-RInfer
-- seam, which is where a pruned program enters the pipeline.
prunedEnv :: String -> Mask -> String -> IO (Program, IREnv)
prunedEnv fname m src = do
  prog <- parseOrFail src
  case rtypedProgram prog of
    Left err -> assertFailure ("typing failed: " ++ err)
    Right rtyped -> do
      let decls  = adts rtyped
          pruned = rtyped
            { functions = [ if n == fname then pruneObservation decls m d else d
                          | d@(n, _) <- functions rtyped ] }
      case compileRTyped defaultCompilerConfig pruned of
        Left err  -> assertFailure ("compiling the pruned program failed: " ++ err)
        Right env -> return (pruned, env)

-- | The mask naming the given rendered slot paths of a function.
maskOf :: String -> String -> [String] -> IO Mask
maskOf fname src names = do
  (decls, t, _) <- treeOf fname src
  return (Set.fromList [ s | s <- obsSlots t, prettySlot decls s `elem` names ])

pruneTests :: TestTree
pruneTests = testGroup "pruneObservation and the pipeline below it"
  [ testCase "the empty mask is the identity on the declaration" $ do
      (decls, _, _) <- treeOf "main" progW
      prog <- parseOrFail progW
      case rtypedProgram prog of
        Left err -> assertFailure err
        Right rtyped -> do
          let d = head (functions rtyped)
          assertEqual "unchanged" d (pruneObservation decls Set.empty d)

  , testCase "a masked leaf becomes a Constant VAny carrying its rType" $ do
      (decls, _, _) <- treeOf "main" progW
      m <- maskOf "main" progW ["snd"]
      prog <- parseOrFail progW
      case rtypedProgram prog of
        Left err -> assertFailure err
        Right rtyped -> do
          let (_, body) = pruneObservation decls m (head (functions rtyped))
              holes = [ rType (getTypeInfo e)
                      | e <- flatten body, Constant VAny <- [node e] ]
          assertEqual "one hole, Float-typed" [TFloat] holes

  , testCase "W pruned to (ANY, y) has no probability function" $ do
      m <- maskOf "main" progW ["fst"]
      (prog, env) <- prunedEnv "main" m progW
      let q = VTuple (VFloat 0.5) (VFloat 1.0)
      case runProbC prog env [] q of
        Left _  -> return ()   -- the design's verdict: no compiled probability function
        Right v -> assertFailure ("expected no probability function, got " ++ show v)

  , testCase "N pruned at slot 2 answers 1.0 at dim 2" $ do
      m <- maskOf "main" progN ["snd.fst"]
      (prog, env) <- prunedEnv "main" m progN
      let q = VTuple (VFloat 0.9) (VTuple (VFloat 0.4) (VFloat 0.5))
      assertProbDim "N (x+y, (_, y))" (runProbC prog env [] q) 1.0 2.0

  , testCase "B pruned at slot 1 answers 1.0 at dim 1" $ do
      m <- maskOf "main" progB ["fst"]
      (prog, env) <- prunedEnv "main" m progB
      let q = VTuple (VFloat 0.3) (VFloat 0.7)
      assertProbDim "B (_, 1.0 - x)" (runProbC prog env [] q) 1.0 1.0
  ]

-- | Assert a probability query's (prob, dim) pair.
assertProbDim :: String -> Either CompilerError IRValue -> Double -> Double -> IO ()
assertProbDim what res expP expD = case res of
  Left err -> assertFailure (what ++ ": query failed: " ++ err)
  Right (VProbDim p d) -> do
    assertBool (what ++ ": probability " ++ show p ++ " /= " ++ show expP)
               (abs (p - expP) < 1e-4)
    assertEqual (what ++ ": dim") expD d
  Right v -> assertFailure (what ++ ": not a (prob, dim) pair: " ++ show v)

-- | Every node of an expression, itself included.
flatten :: Expr -> [Expr]
flatten e = e : concatMap flatten (getSubExprs e)

-- ---------------------------------------------------------------------------

observationMaskTests :: TestTree
observationMaskTests = testGroup "ObservationMask"
  [ treeWalkTests
  , classTests
  , corpusSelfContainedTests
  , maskTableTests
  , pruneTests
  ]
