{-# LANGUAGE ScopedTypeVariables #-}
-- | The observation tree, leaf slots, correlation classes, and the masked
-- program (task @observation-mask-analysis@, design
-- @witnessed-per-query-capability@).
--
-- The groups mirror the task's acceptance criteria one for one: the tree walk,
-- the slot verdicts and correlation classes on the design's W\/O\/N\/I\/C\/B\/S
-- programs, the self-containment of every slot of the neural corpus programs,
-- the per-mask lattice verdicts, and pruning followed by the existing pipeline.
-- The last group is task @per-mask-variants-by-pruning@'s: the variants, the
-- dispatcher, and the corpus-wide properties they must keep.
module TestObservationMask (observationMaskTests) where

import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.ObservationMask
import SPLL.Prelude
import SPLL.Parser (tryParseProgram)
import SPLL.IntermediateRepresentation
import SPLL.Typing.PType (PType(..))
import SPLL.Typing.RType (RType(..))
import TestCaseParser (corpusPplPath, listCorpusPplFiles)
import SPLL.MaskVariants (variantGroupName)
import qualified SPLL.CodeGenPyTorch

import Control.Exception (try, evaluate, SomeException, ErrorCall(..), fromException)
import Control.Monad (forM, forM_, when)
import Control.Monad.Random (evalRand)
import Data.List (find, sort, isInfixOf, isPrefixOf, intercalate)
import Data.Maybe (isJust, isNothing)
import qualified Data.Set as Set
import System.FilePath (takeBaseName, replaceExtension)
import System.Random (mkStdGen)
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
progW  = "main = draw x = Uniform in draw y = x + Uniform in (x, y)"
progO  = "main = draw x = Uniform in draw y = Uniform in (x, (x+y+3.0, x+y+2.0))"
progN  = "main = draw x = Uniform in draw y = Uniform in (x+y, (x, y))"
progI  = "main = draw x = Uniform in draw y = Uniform in (x, y)"
progC  = "main = draw x = Uniform in draw y = x + Uniform in draw z = y + Uniform in (x, (y, z))"
progB  = "main = draw x = Uniform in (x, 1.0 - x)"
progS1 = "main = draw x = Uniform in (x, Uniform)"

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
      (decls, t, _) <- treeOf "main" "main = draw t = (Uniform, Uniform) in t"
      assertEqual "slots" ["fst", "snd"] (slotNames decls t)

  , testCase "a root Var occurring twice is NOT followed" $ do
      -- `t` is read by `u`'s value as well as being the observation root, so the
      -- accessor path from the root no longer identifies the sub-expression and
      -- the descent must stop.
      (decls, t, _) <- treeOf "main"
        "main = draw t = (Uniform, 0.5) in draw u = fst t + 1.0 in t"
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

  , testCase "draw x = Uniform in (x, Uniform): two classes, slot 1 enumerated" $ do
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
-- 6. Variants and the dispatcher (task per-mask-variants-by-pruning)
-- ---------------------------------------------------------------------------

-- | A corpus program that compiles to at least one per-mask variant, with the
-- functions that have one.
data VariantProgram = VariantProgram
  { vpName  :: String
  , vpProg  :: Program
  , vpEnv   :: IREnv
  , vpFns   :: [(String, [Slot])]   -- ^ dispatching functions and their enumerated slots
  }

-- | Every ordinary corpus program (no @slow@ header) whose compile has a mask
-- dispatcher. The sweeps below are over exactly these.
corpusWithVariants :: IO [VariantProgram]
corpusWithVariants = do
  paths <- listCorpusPplFiles
  fmap concat $ forM paths $ \path -> do
    tst <- readFile (replaceExtension path "tst")
    if "slow" `elem` map (filter (/= '\r')) (lines tst) then return [] else do
      src <- readFile path
      case tryParseProgram path src of
        Left _ -> return []
        Right prog -> case (compile defaultCompilerConfig prog, marginalReport defaultCompilerConfig prog) of
          (Right env@(IREnv groups _ _), Right report) ->
            let bases = Set.fromList [ b | g <- groups, Just b <- [maskVariantOf g] ]
                fns = [ (fmName r, fmEnumerated r) | r <- report, fmName r `Set.member` bases ]
            in return [ VariantProgram (takeBaseName path) prog env fns | not (null fns) ]
          _ -> return []

-- | A query value with the slot at this accessor path replaced. 'Nothing' when
-- the value does not have the path's shape (a different Either arm, an empty
-- list, another constructor) -- that slot is then not there to mask.
setSlot :: Slot -> IRValue -> IRValue -> Maybe IRValue
setSlot [] new _ = Just new
setSlot (Accessor c i : rest) new v = case (c, i, v) of
  ("TCons", 0, VTuple a b) -> (\a' -> VTuple a' b) <$> setSlot rest new a
  ("TCons", _, VTuple a b) -> VTuple a <$> setSlot rest new b
  ("left", _, VEither (Left a)) -> VEither . Left <$> setSlot rest new a
  ("right", _, VEither (Right a)) -> VEither . Right <$> setSlot rest new a
  ("Cons", 0, VList (ListCont h t)) -> (\h' -> VList (ListCont h' t)) <$> setSlot rest new h
  ("Cons", _, VList (ListCont h t)) -> setSlot rest new (VList t) >>= \tv -> case tv of
      VList t' -> Just (VList (ListCont h t'))
      _        -> Nothing
  (_, _, VADT ctor fields) | ctor == c, i < length fields ->
      (\f' -> VADT ctor (take i fields ++ [f'] ++ drop (i + 1) fields)) <$> setSlot rest new (fields !! i)
  _ -> Nothing

applyMask :: Mask -> IRValue -> Maybe IRValue
applyMask m v = foldr (\s acc -> acc >>= setSlot s VAny) (Just v) (Set.toList m)

-- | A few forward samples of a zero-parameter function, from fixed seeds.
forwardSamples :: VariantProgram -> String -> IO [IRValue]
forwardSamples vp fname = fmap concat $ forM [1 .. 3 :: Int] $ \seed -> do
  r <- try (evaluate (forceValue (evalRand (runGenNamedC (vpProg vp) (vpEnv vp) fname []) (mkStdGen seed))))
  return $ case r of
    Right v | not (isError v) -> [v]
    Right _ -> []
    Left (_ :: SomeException) -> []
  where
    isError (VError _) = True
    isError _ = False

forceValue :: IRValue -> IRValue
forceValue v = length (show v) `seq` v

-- | Zero-parameter functions only: a forward sample needs no arguments.
nullary :: Program -> String -> Bool
nullary prog fname = case lookup fname (functions prog) of
  Just (Expr _ (Lambda _ _)) -> False
  Just _ -> True
  Nothing -> False

-- | A probability query, evaluated: 'Right' a value, 'Left' a refusal message
-- (an 'IRError' the interpreter raised, or a compile-level 'Left'). Any other
-- exception propagates: that is a crash.
probQuery :: VariantProgram -> String -> IRValue -> IO (Either String IRValue)
probQuery vp fname q = do
  r <- try (case runProbNamedC (vpProg vp) (vpEnv vp) fname [] q of
              Left err -> return (Left err)
              Right v  -> Right <$> evaluate (forceValue v))
  case r of
    Right x -> return x
    Left ex -> case fromException ex of
      Just (ErrorCall msg)
        | "Error during interpretation" `isPrefixOf` msg -> return (Left msg)
        | Just ticket <- knownCrash msg -> return (Left (knownPrefix ++ ticket ++ ": " ++ msg))
      _ -> ioError (userError ("crash: " ++ show (ex :: SomeException)))
  where
    knownCrash msg = case [ t | (needle, t) <- knownMaskCrashes, needle `isInfixOf` msg ] of
      (t : _) -> Just t
      []      -> Nothing

-- | Crashes a masked query reaches that are filed defects of the engines, not
-- of the dispatcher, each with its tracking docs task. A masked program is an
-- ordinary program, so a variant can expose an engine crash its unmasked
-- function never reached. The entry goes in the commit that fixes it.
knownMaskCrashes :: [(String, String)]
knownMaskCrashes =
  [ -- `draw heard = Face .. in isFace heard` at p(False): the constructor-test
    -- inverse's False witness reaches `isFace` as a value. Reached here by
    -- tupleCtorTestOfSharedDraw at (False, ANY).
    ("Parameter is not an ADT: VAnyExcept", "single-ctor-test-false-witness-crashes") ]

knownPrefix :: String
knownPrefix = "KNOWN CRASH "

variantTests :: TestTree
variantTests = testGroup "per-mask variants and the dispatcher"
  [ testCase "W's Python has the dispatcher and the two admitted variants" $ do
      prog <- corpusPplPath "letWitnessedSharedLatent" >>= readFile >>= parseOrFail
      py <- pythonOf defaultCompilerConfig prog
      -- (_, ANY) and (ANY, ANY) are admitted; (ANY, _) is the convolution.
      assertBool "class Main__m01" ("class Main__m01(" `isInfixOf` py)
      assertBool "class Main__m11" ("class Main__m11(" `isInfixOf` py)
      assertBool "no class for the refused (ANY, _)" (not ("class Main__m10(" `isInfixOf` py))
      assertBool "the dispatcher reads the mask" ("isAny(sample[0])" `isInfixOf` py)
      assertBool "the dispatcher calls a variant" ("main__m01.forward(sample)" `isInfixOf` py)

  , testCase "encode_per_function_marginals' Python is unchanged" $ do
      -- Every slot self-contained: no variant, no dispatcher, byte-identical
      -- to a compile that offers no variants at all.
      prog <- corpusPplPath "encode_per_function_marginals" >>= readFile >>= parseOrFail
      withVariants <- pythonOf defaultCompilerConfig prog
      without <- pythonOf defaultCompilerConfig { marginalSlots = 0 } prog
      assertEqual "emitted Python" without withVariants

  , testCase "the over-budget function gets no variants and one warning" $ do
      prog <- parseOrFail progC
      let tight = defaultCompilerConfig { marginalSlots = 2 }
      case compile tight prog of
        Left err -> assertFailure err
        Right (IREnv groups _ _) ->
          assertEqual "variant groups" [] [ groupName g | g <- groups, isJust (maskVariantOf g) ]
      case marginalBudgetWarnings tight prog of
        [w] -> do
          assertBool ("names the function: " ++ w) ("'main'" `isInfixOf` w)
          assertBool ("names the flag: " ++ w) ("--marginalSlots" `isInfixOf` w)
        ws -> assertFailure ("expected one warning, got " ++ show ws)

  , testCase "--pruneAnyChecks collapses the dispatcher to the all-concrete body" $ do
      prog <- parseOrFail progW
      case compile defaultCompilerConfig { pruneAnyChecks = True } prog of
        Left err -> assertFailure err
        Right (IREnv groups _ _) ->
          assertEqual "groups" ["main"] (map groupName groups)

  , testCase "a variant name a user function already holds: no variants, no clash" $ do
      let slotsW = [[Accessor "TCons" 0], [Accessor "TCons" 1]]
          clash = variantGroupName "main" slotsW (Set.fromList [[Accessor "TCons" 1]])
      prog <- parseOrFail (progW ++ "\n" ++ clash ++ " = 1.0")
      case compile defaultCompilerConfig prog of
        Left err -> assertFailure err
        Right (IREnv groups _ _) -> do
          assertEqual ("one group named " ++ clash) 1 (length [ () | g <- groups, groupName g == clash ])
          assertEqual "no variant groups" [] [ groupName g | g <- groups, isJust (maskVariantOf g) ]

  , testCase "writeLogits of a correlated tuple marginalises each slot through the dispatcher" $ do
      -- makeWriteLogitsPlan queries each slot with ANY in the others, which is
      -- exactly a masked query. (b, not b) shares b between its slots, so the
      -- let-fold fallback refuses the per-slot marginal (b unobserved, but
      -- read by the other slot); the variant answers it. The task's own
      -- examples, N and B, are continuous Uniform tuples, which writeLogits
      -- does not represent at all.
      prog <- parseOrFail "main = draw b = Uniform < 0.5 in (b, not b)"
      let written c = do
            r <- try (evaluate (either (Left . id) (Right . forceValue) (runWriteLogits c prog "main" [])))
            return (either (\(e :: SomeException) -> Left (show e)) id r)
      fallback <- written defaultCompilerConfig { marginalSlots = 0 }
      case fallback of
        Left e -> assertBool ("the fallback refuses: " ++ e) ("cannot compute marginal" `isInfixOf` e)
        Right v -> assertFailure ("the let-fold fallback was expected to refuse, got " ++ show v)
      dispatched <- written defaultCompilerConfig
      case dispatched of
        Right (VList l) -> do
          let xs = [ x | VFloat x <- foldr (:) [] l ]
          assertEqual "four Bool logit slots" 4 (length xs)
          forM_ xs $ \x -> assertBool ("every slot marginal is 0.5, got " ++ show xs) (abs (x - 0.5) < 1e-12)
        other -> assertFailure ("writeLogits through the dispatcher: " ++ show other)

  , testCase "the all-concrete body is the unmasked compile, byte for byte" $ do
      -- Before the optimizer: the dispatcher's else-arm, under the parameter
      -- lambdas and the query-type guard, is the body a compile without
      -- variants produces; every other group, and every other variant of a
      -- dispatching group, is identical outright.
      vps <- corpusWithVariants
      assertBool "the corpus has programs with variants" (length vps >= 30)
      forM_ vps $ \vp -> do
        let unopt c = either (\e -> error (vpName vp ++ ": " ++ e)) id (compileUnoptimized c (vpProg vp))
            IREnv withGs _ _ = unopt defaultCompilerConfig
            IREnv withoutGs _ _ = unopt defaultCompilerConfig { marginalSlots = 0 }
        assertEqual (vpName vp ++ ": base groups")
          (map groupName withoutGs) [ groupName g | g <- withGs, isNothing (maskVariantOf g) ]
        forM_ (zip withoutGs [ g | g <- withGs, isNothing (maskVariantOf g) ]) $ \(g0, g) -> do
          let same lbl f = assertEqual (vpName vp ++ "." ++ groupName g ++ " " ++ lbl)
                             (fmap (show . fst) (f g0)) (fmap (show . fst) (f g))
          same "gen" genFun
          same "normal" normalFun
          same "writeLogits" writeLogitsFun
          let undispatched f = fmap (show . allConcreteArm . fst) (f g)
          assertEqual (vpName vp ++ "." ++ groupName g ++ " prob") (fmap (show . fst) (probFun g0)) (undispatched probFun)
          assertEqual (vpName vp ++ "." ++ groupName g ++ " integ") (fmap (show . fst) (integFun g0)) (undispatched integFun)

  , testCase "totality per mask: every masked forward sample answers or refuses" $ do
      vps <- corpusWithVariants
      checked <- fmap sum $ forM vps $ \vp ->
        fmap sum $ forM [ f | f@(n, _) <- vpFns vp, nullary (vpProg vp) n ] $ \(fname, slots) -> do
          samples <- forwardSamples vp fname
          fmap sum $ forM samples $ \x ->
            fmap sum $ forM (masksOver slots) $ \m -> case applyMask m x of
              Nothing -> return (0 :: Int)
              Just q -> do
                r <- try (probQuery vp fname q)
                case r of
                  Left (ex :: SomeException) ->
                    assertFailure (vpName vp ++ "." ++ fname ++ " at " ++ show q ++ ": " ++ show ex)
                  Right _ -> return 1
      assertBool ("too few masked queries checked: " ++ show checked) (checked >= 300)

  , testCase "marginalisation consistency: a finite slot summed over its domain is its ANY" $ do
      vps <- corpusWithVariants
      checked <- fmap sum $ forM vps $ \vp ->
        fmap sum $ forM [ f | f@(n, _) <- vpFns vp, nullary (vpProg vp) n ] $ \(fname, slots) -> do
          domains <- slotDomains vp fname slots
          samples <- forwardSamples vp fname
          fmap sum $ forM [ (x, s, dom) | x <- take 1 samples, (s, dom) <- domains ] $ \(x, s, dom) ->
            fmap sum $ forM (masksOver (filter (/= s) slots)) $ \m ->
              case applyMask (Set.insert s m) x of
                Nothing -> return (0 :: Int)
                Just qAny -> do
                  anyR <- probQuery vp fname qAny
                  case anyR of
                    Right (VProbDim pAny dAny) -> do
                      terms <- forM dom $ \v -> case applyMask m x >>= setSlot s v of
                        Nothing -> return Nothing
                        Just q -> probQuery vp fname q >>= \r -> return (Just r)
                      let probs = [ p | Just (Right (VProbDim p d)) <- terms, p /= 0, d == dAny ]
                          stray = [ t | Just t@(Right (VProbDim p d)) <- terms, p /= 0, d /= dAny ]
                          known = [ e | Just (Left e) <- terms, knownPrefix `isPrefixOf` e ]
                          refused = [ e | Just (Left e) <- terms, not (knownPrefix `isPrefixOf` e) ]
                      if not (null known) then return 0 else do
                        when (not (null refused)) $
                          assertFailure (vpName vp ++ ": the ANY query answers but a point refuses: " ++ head refused)
                        assertEqual (vpName vp ++ ": no point at another dim") [] (map show stray)
                        assertBool (vpName vp ++ "." ++ fname ++ " at " ++ show qAny ++ ": "
                                    ++ show (sum probs) ++ " summed vs " ++ show pAny)
                          (abs (sum probs - pAny) <= 1e-9 * max 1 (abs pAny))
                        return 1
                    _ -> return 0
      assertBool ("too few slot marginals checked: " ++ show checked) (checked >= 30)
  ]
  where
    pythonOf conf prog = case compile conf prog of
      Left err -> assertFailure err
      Right env -> return (intercalate "\n" (SPLL.CodeGenPyTorch.generateFunctions True env))

-- | The enumerated slots of a function whose leaf has a finite domain, and the
-- domain, read off the leaf's 'RType'.
slotDomains :: VariantProgram -> String -> [Slot] -> IO [(Slot, [IRValue])]
slotDomains vp fname slots = case rtypedProgram (vpProg vp) of
  Left _ -> return []
  Right rtyped -> case find ((== fname) . fst) (functions rtyped) of
    Nothing -> return []
    Just decl -> do
      let decls = adts rtyped
          leaves = obsLeaves (observationTree decls decl)
      return [ (s, map valueToIRV vals)
             | (s, e, _) <- leaves, s `elem` slots
             , Right mv <- [autoDeriveMultiValue decls (rType (getTypeInfo e))]
             , multiValueIsFinite mv
             , let vals = multiValueToValueList mv
             , not (null vals), length vals <= 64 ]
  where valueToIRV = fmap (error "slotDomains: a closure in a finite domain")

-- | The all-concrete arm of a dispatched body: under the parameter lambdas and
-- the query-type guard, the else-arm of the dispatch. An undispatched body is
-- returned as it is.
allConcreteArm :: IRExpr -> IRExpr
allConcreteArm (IRLambda n b) = IRLambda n (allConcreteArm b)
allConcreteArm (IRIf c@(IRConformsTo _ _) b err) = IRIf c (allConcreteArm b) err
allConcreteArm (IRIf (IRIf (IRUnaryOp OpIsAny (IRVar _)) (IRConst (VBool False)) _) _ inner) = inner
allConcreteArm other = other

-- ---------------------------------------------------------------------------

observationMaskTests :: TestTree
observationMaskTests = testGroup "ObservationMask"
  [ treeWalkTests
  , classTests
  , corpusSelfContainedTests
  , maskTableTests
  , pruneTests
  , variantTests
  ]
