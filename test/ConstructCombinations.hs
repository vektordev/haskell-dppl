{-# LANGUAGE ScopedTypeVariables #-}
-- | Construct /combinations/ in IR, as opposed to the single constructs
-- 'CertifiedCensus.irConstructs' labels (docs-repo investigation
-- @ir-fuzz-certification-covers-real-construct-combinations@).
--
-- Three feature families per body:
--
--   * 'edgeFeatures': parent/child adjacency, @parent.slot > child@, where a
--     node's kind is its most specific label ('nodeKind') and the slot names
--     which operand the child is (an if's condition or arm, a map's function
--     or iterable, a let's bound expression or body).
--   * 'contextFeatures': scoping, @context >> kind@ for every node and every
--     enclosing operand slot on its path (a let anywhere inside a
--     comprehension iterable, an accessor anywhere inside a select arm). A
--     let's body is not a context: it is where everything after a binding
--     lives.
--   * 'shapeFeatures': the four combinations behind the bugs of
--     @construct-certification-misses-construct-combinations@, as syntactic
--     predicates.
--
-- The probe ('constructCombinationProbe') measures them over the corpus's
-- emitted IR and over the IR fuzz generator's and the typed fuzzer's samples,
-- and writes the counts as TSV. It is opt-in (@NEST_COMBINATION_PROBE=<dir>@),
-- not a tier: a measurement, not a check.
module ConstructCombinations
  ( nodeKind
  , edgeFeatures
  , contextFeatures
  , shapeFeatures
  , bodyFeatures
  , constructCombinationProbe
  ) where

import Control.Exception (SomeException, try, evaluate)
import Control.Monad (forM)
import Data.Char (isSpace)
import Data.Either (rights)
import Data.List (nub, sort, intercalate)
import Data.Maybe (catMaybes)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import System.Environment (lookupEnv)
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>))
import System.IO (hPutStrLn, stderr)
import System.Timeout (timeout)
import Test.QuickCheck (arbitrary, resize, vectorOf)
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)

import SPLL.IntermediateRepresentation
import SPLL.IR.Type (IRADTDecl(..))
import SPLL.IRTypeCheck (CheckedIR, checkedEnv)
import SPLL.Lang.Types (GenericValue(..), GenericList(..))
import SPLL.Prelude (compile)
import SPLL.CompilerConfig (defaultCompilerConfig, CompilerConfig(..))
import CertifiedCensus (allBodies, inferenceBodies, programCensus, uncertifiedConstructs, batchedProgramCensus, batchedUncertifiedConstructs)
import CorpusSweep (Corpus, CorpusEntry(..), corpusEntries, notSlowForCompileCost)
import IRFuzz (IRCase(..), Helper(..), BatchedIRCase(..), genIRCase, irCaseFunction, prepareBatchedIRCase)
import BackendAgreement (AgreementCase(..), BatchedCase(..), comparedBodies, batchedComparedBodies)
import TestFuzz (prepareAgreementCase, prepareAgreementNeighbour, prepareAgreementBatched, genAgreementProgram, agreementFuzzSize)

-- | The implicit ADT functions of an env, by role.
data AdtNames = AdtNames { adtCtors :: S.Set String, adtTests :: S.Set String, adtFields :: S.Set String }

adtNames :: [IRADTDecl] -> AdtNames
adtNames ds = AdtNames
  (S.fromList [ c | d <- ds, (c, _) <- irConstructors d ])
  (S.fromList [ "is" ++ c | d <- ds, (c, _) <- irConstructors d ])
  (S.fromList [ f | d <- ds, (_, fs) <- irConstructors d, (f, _) <- fs ])

-- | A node's kind: its most specific label.
nodeKind :: AdtNames -> IRExpr -> String
nodeKind names x = case x of
  IROp op _ _ -> "Op:" ++ show op
  IRUnaryOp op _ -> "Un:" ++ show op
  IRBuiltin b _ -> "B:" ++ builtinLabel b
  IRDensity d ls _ -> "Density:" ++ show d ++ " " ++ show ls
  IRCumulative d ls _ -> "Cumulative:" ++ show d ++ " " ++ show ls
  IRSample d -> "Sample:" ++ show d
  IRConstruct t _ -> "Con:" ++ show t
  IRDestruct a _ -> "Acc:" ++ ctor (show a)
  IRConst v -> "Const:" ++ valueKind v
  IRApply _ _ -> case fst (collectApplyChain x) of
    IRVar n | n `S.member` adtTests names -> "Apply:ADT test"
            | n `S.member` adtFields names -> "Apply:ADT field"
            | n `S.member` adtCtors names -> "Apply:ADT ctor"
            | otherwise -> "Apply:var"
    IRLambda _ _ -> "Apply:lambda"
    _ -> "Apply:other"
  IRVar n | n `S.member` adtTests names || n `S.member` adtFields names || n `S.member` adtCtors names -> "Var:ADT function"
          | otherwise -> "Var"
  _ -> ctor (show x)
  where
    ctor = takeWhile (not . isSpace)
    builtinLabel b = case b of
      BReduce op _ -> "BReduce " ++ show op
      BZip op -> "BZip " ++ show op
      _ -> ctor (show b)

valueKind :: IRValue -> String
valueKind v = case v of
  VList EmptyList -> "VList []"
  VList _ -> "VList ListCont"
  _ -> takeWhile (not . isSpace) (show v)

-- | The name of each operand slot of a node, in 'getIRSubExprs' order.
slotNames :: IRExpr -> [String]
slotNames x = case x of
  IRIf{} -> ["cond", "then", "else"]
  IRSelect{} -> ["cond", "then", "else"]
  IROp{} -> ["l", "r"]
  IRLetIn{} -> ["bound", "body"]
  IRLambda{} -> ["body"]
  IRApply{} -> ["fun", "arg"]
  IRBuiltin b args -> case b of
    BMap -> ["fun", "iter"]
    BMapList -> ["fun", "iter"]
    BTensor _ -> map (const "elem") args
    _ -> [ "op" ++ show i | i <- [0 .. length args - 1 :: Int] ]
  _ -> [ "op" ++ show i | i <- [0 .. length (getIRSubExprs x) - 1 :: Int] ]

-- | The node's children with their slot names, closure bodies of constants
-- included (as slot @closure@).
children :: IRExpr -> [(String, IRExpr)]
children x = zip (slotNames x) (getIRSubExprs x) ++ [ ("closure", b) | IRConst v <- [x], b <- valueExprs v ]
  where
    valueExprs v = case v of
      VTuple a b -> valueExprs a ++ valueExprs b
      VEither (Left a) -> valueExprs a
      VEither (Right b) -> valueExprs b
      VList l -> listExprs l
      VADT _ fs -> concatMap valueExprs fs
      VClosure _ _ body -> [body]
      _ -> []
    listExprs (ListCont a as) = valueExprs a ++ listExprs as
    listExprs _ = []

edgeFeatures :: AdtNames -> IRExpr -> [String]
edgeFeatures names = go
  where
    go x = [ nodeKind names x ++ "." ++ s ++ " > " ++ nodeKind names c | (s, c) <- children x ]
           ++ concatMap (go . snd) (children x)

-- | @context >> kind@ for each node and each distinct enclosing context.
contextFeatures :: AdtNames -> IRExpr -> [String]
contextFeatures names = go []
  where
    go ctxs x = [ c ++ " >> " ++ nodeKind names x | c <- ctxs ]
                ++ concat [ go (extend (nodeKind names x ++ "." ++ s) s) c | (s, c) <- children x ]
      where extend ctx s = if s == "body" && isLet x then ctxs else nub (ctx : ctxs)
    isLet IRLetIn{} = True
    isLet _ = False

-- | The four 2026-10-21 combinations, as syntactic predicates over one body.
-- A variable is resolved through the let bindings enclosing it (to depth 4),
-- since the compiler CSE-binds the conditions and arms these bugs lived in.
--
-- * @shape:let in comprehension iterable@: a map/zip/reduce/index operand
--   other than a map's function, or a tensor element, containing a let.
-- * @shape:select over tuple (literal arm)@ / @(non-literal arm)@: a select
--   with an arm that is tuple-shaped: a tuple construction or constant
--   (literal), or a variable, let or conditional that resolves to one.
-- * @shape:ctor test under an op guards a partial read@: a conditional
--   whose condition, resolved, holds a constructor test under an operator
--   (the test is not the whole condition), and one of whose arms reads a
--   field, head, tail or either side.
-- * @shape:wrapped empty-list probe guards a partial read@: the same, for
--   an @== []@ probe that is not the whole condition.
-- * @shape:wrapped structural guard guards a partial read@: the union of the
--   two above, constructor tests by accessor (@isLeft@) included.
shapeFeatures :: AdtNames -> IRExpr -> [String]
shapeFeatures names = nub . go M.empty
  where
    go env x = here env x ++ concat [ go (bindFor env x s) c | (s, c) <- children x ]
    bindFor env (IRLetIn v e _) "body" = M.insert v e env
    bindFor env _ _ = env

    here env x = case x of
      IRBuiltin b args ->
        [ "shape:let in comprehension iterable"
        | (s, a) <- zip (slotNames x) args, s /= "fun", isComprehension b, hasLet a ]
      _ -> []
      ++ case x of
        IRSelect _ a b ->
          [ "shape:select over tuple (literal arm)" | any literalTuple [a, b] ]
          ++ [ "shape:select over tuple (non-literal arm)" | any (\arm -> not (literalTuple arm) && tupleShaped env 4 arm) [a, b] ]
        _ -> []
      ++ case x of
        IRIf c a b -> guarded env c [a, b]
        IRSelect c a b -> guarded env c [a, b]
        _ -> []

    isComprehension b = case b of
      BMap -> True; BMapList -> True; BZip _ -> True; BReduce _ _ -> True; BIndex _ -> True
      BTensor _ -> True; _ -> False
    hasLet e = not (null [ () | IRLetIn{} <- universe e ])

    literalTuple e = case e of
      IRConstruct TgTuple _ -> True
      IRConst (VTuple _ _) -> True
      _ -> False
    tupleShaped env d e
      | d <= (0 :: Int) = False
      | otherwise = case e of
          _ | literalTuple e -> True
          IRVar v -> maybe False (tupleShaped env (d - 1)) (M.lookup v env)
          IRLetIn v r body -> tupleShaped (M.insert v r env) (d - 1) body
          IRIf _ a b -> tupleShaped env (d - 1) a || tupleShaped env (d - 1) b
          IRSelect _ a b -> tupleShaped env (d - 1) a || tupleShaped env (d - 1) b
          _ -> False

    guarded env c arms =
      let cond = resolve env 4 c
          resolvedArms = map (resolve env 4) arms
          partial = any (\arm -> not (null [ () | e <- universe arm, partialRead e ])) resolvedArms
          -- A partial read no conditional inside the arm guards again: the
          -- outer guard is all that protects it.
          bare = any (not . null . unguardedReads) resolvedArms
          ctorUnder = wrapped isCtorTest cond
          emptyUnder = wrapped isEmptyProbe cond
          anyUnder = wrapped (\e -> isCtorTest e || isEmptyProbe e) cond
      in (if not partial then [] else
           [ "shape:ctor test under an op guards a partial read" | ctorUnder ]
           ++ [ "shape:wrapped empty-list probe guards a partial read" | emptyUnder ]
           ++ [ "shape:wrapped structural guard guards a partial read" | anyUnder ])
         ++ (if not bare then [] else
           [ "shape:ctor test under an op guards an unguarded partial read" | ctorUnder ]
           ++ [ "shape:wrapped empty-list probe guards an unguarded partial read" | emptyUnder ]
           ++ [ "shape:wrapped structural guard guards an unguarded partial read" | anyUnder ])
    unguardedReads e = case e of
      IRIf{} -> []
      IRSelect{} -> []
      _ -> [ () | partialRead e ] ++ concatMap unguardedReads (getIRSubExprs e)
    -- The predicate holds strictly below the condition's root.
    wrapped p cond = not (p cond) && any p (concatMap universe (getIRSubExprs cond))
                     || (case cond of { IRUnaryOp _ i -> p i; _ -> False })
    isCtorTest e = case e of
      IRApply (IRVar n) _ -> n `S.member` adtTests names
      IRDestruct AcIsLeft _ -> True
      IRDestruct AcIsRight _ -> True
      _ -> False
    isEmptyProbe e = case e of
      IROp OpEq a b -> isEmpty a || isEmpty b
      _ -> False
    isEmpty e = case e of
      IRConst (VList EmptyList) -> True
      _ -> False
    partialRead e = case e of
      IRDestruct a _ -> a `elem` [AcHead, AcTail, AcFromLeft, AcFromRight]
      IRApply (IRVar n) _ -> n `S.member` adtFields names
      _ -> False

    -- Substitute let-bound variables, to a depth, so a CSE-bound condition
    -- or arm is seen.
    resolve env d e
      | d <= (0 :: Int) = e
      | otherwise = case e of
          IRVar v -> maybe e (resolve env (d - 1)) (M.lookup v env)
          _ -> rebuild e (map (resolve env (d - 1)) (getIRSubExprs e))
    rebuild e cs = case (e, cs) of
      (IRIf{}, [a, b, c]) -> IRIf a b c
      (IRSelect{}, [a, b, c]) -> IRSelect a b c
      (IROp op _ _, [a, b]) -> IROp op a b
      (IRUnaryOp op _, [a]) -> IRUnaryOp op a
      (IRDestruct acc _, [a]) -> IRDestruct acc a
      (IRApply{}, [a, b]) -> IRApply a b
      _ -> e

universe :: IRExpr -> [IRExpr]
universe e = e : concatMap universe (getIRSubExprs e)

-- | Every feature of a set of bodies under one env's ADTs.
bodyFeatures :: [IRADTDecl] -> [IRExpr] -> [String]
bodyFeatures adts bodies =
  sort (nub (concatMap (\b -> map ("edge " ++) (edgeFeatures names b) ++ map ("ctx " ++) (contextFeatures names b)
                                 ++ shapeFeatures names b) bodies))
  where names = adtNames adts

adtsOf :: CheckedIR -> [IRADTDecl]
adtsOf c = let IREnv _ adts _ = checkedEnv c in adts

envFeatures :: (IREnv -> [IRExpr]) -> IREnv -> [String]
envFeatures which env@(IREnv _ adts _) = bodyFeatures adts (which env)

-- ---------------------------------------------------------------------------
-- The probe

forced :: [String] -> IO (Maybe [String])
forced xs = do
  r <- timeout (60 * 1000 * 1000) (try (evaluate (length (concat xs) `seq` xs)))
  return $ case r of
    Just (Right ys) -> Just ys
    Just (Left (_ :: SomeException)) -> Nothing
    Nothing -> Nothing

-- | Per corpus program: its name, whether it is certified (its census holds
-- only certified constructs), and its feature set.
type ProgramUnit = (String, Bool, [String])

corpusBatchedUnits :: [CorpusEntry] -> IO [ProgramUnit]
corpusBatchedUnits es = fmap catMaybes $ forM es $ \e -> do
  let compiled = compile defaultCompilerConfig { batched = True } (ceProgram e)
      certified = null (batchedUncertifiedConstructs (batchedProgramCensus compiled))
  fmap (\fs -> (ceName e, certified, fs))
    <$> forced (either (const []) (envFeatures inferenceBodies . checkedEnv) compiled)

corpusScalarUnits :: [CorpusEntry] -> IO [ProgramUnit]
corpusScalarUnits es = fmap catMaybes $ forM es $ \e -> do
  let compiles = [ compile conf (ceProgram e) | conf <- [defaultCompilerConfig, defaultCompilerConfig { optimizerLevel = 0 }] ]
      feats = either (const []) (envFeatures allBodies . checkedEnv)
      certified = null (uncertifiedConstructs (programCensus compiles))
  fmap (\fs -> (ceName e, certified, fs)) <$> forced (nub (concatMap feats compiles))

writeUnits :: FilePath -> [ProgramUnit] -> IO ()
writeUnits path us = writeFile path (unlines [ intercalate "\t" (n : (if c then "certified" else "uncertified") : fs) | (n, c, fs) <- us ])

irCaseFeatures :: IRCase -> [String]
irCaseFeatures c = bodyFeatures (icADTs c) (irCaseFunction c : [ foldr IRLambda (hBody h) (map fst (hParams h)) | h <- icHelpers c ])

-- | A sample of the IR generator as the property draws it.
irSample :: Int -> Int -> [IRCase]
irSample n seed = unGen (vectorOf n genIRCase) (mkQCGen seed) 30

writeCounts :: FilePath -> [(String, [[String]])] -> IO ()
writeCounts path sources = do
  let counts = [ (name, length units, M.fromListWith (+) [ (f, 1 :: Int) | u <- units, f <- nub u ]) | (name, units) <- sources ]
      feats = sort (nub (concat [ M.keys m | (_, _, m) <- counts ]))
      header = intercalate "\t" ("feature" : [ name ++ "(" ++ show n ++ ")" | (name, n, _) <- counts ])
      row f = intercalate "\t" (f : [ show (M.findWithDefault 0 f m) | (_, _, m) <- counts ])
  writeFile path (unlines (header : map row feats))
  hPutStrLn stderr ("combination probe: wrote " ++ path)

-- | Opt-in: @NEST_COMBINATION_PROBE=<dir>@ writes @scalar.tsv@ and
-- @batched.tsv@ there. @NEST_COMBINATION_PROBE_IR_CASES@ sets the size of the
-- large IR-generator sample (default 6000).
constructCombinationProbe :: Corpus -> IO TestTree
constructCombinationProbe corpus = do
  out <- lookupEnv "NEST_COMBINATION_PROBE"
  nIR <- maybe 6000 read <$> lookupEnv "NEST_COMBINATION_PROBE_IR_CASES"
  return $ testGroup "Probe" [ testCase "ConstructCombinations" (probe dir nIR) | Just dir <- [out] ]
  where
   probe dir nIR = do
      createDirectoryIfMissing True dir
      writeFile (dir </> "started") ""
      -- The default-tier corpus, or (NEST_COMBINATION_PROBE_ALL) every program
      -- but those slow for their compile cost.
      everything <- maybe False (const True) <$> lookupEnv "NEST_COMBINATION_PROBE_ALL"
      let es = filter (if everything then notSlowForCompileCost else not . ceSlow) (corpusEntries corpus)
      hPutStrLn stderr ("combination probe: " ++ show (length es) ++ " corpus programs")
      cScalar <- corpusScalarUnits es
      cBatched <- corpusBatchedUnits es
      writeUnits (dir </> "corpus-scalar-units.tsv") cScalar
      writeUnits (dir </> "corpus-batched-units.tsv") cBatched
      let fixed = irSample 600 20261013
          big = irSample nIR 1
      fixedU <- catMaybes <$> mapM (forced . irCaseFeatures) fixed
      bigU <- catMaybes <$> mapM (forced . irCaseFeatures) big
      bFixed <- rights <$> mapM prepareBatchedIRCase fixed
      bBig <- rights <$> mapM prepareBatchedIRCase big
      let bFeat bc = let env@(IREnv _ adts _) = checkedEnv (bicEnv bc) in bodyFeatures adts (inferenceBodies env)
      bFixedU <- catMaybes <$> mapM (forced . bFeat) bFixed
      bBigU <- catMaybes <$> mapM (forced . bFeat) bBig
      -- The typed fuzzer's fixed sample, as BackendCoverage draws it.
      let draws = unGen (vectorOf 1000 ((,) <$> resize agreementFuzzSize genAgreementProgram <*> arbitrary))
                        (mkQCGen 20261006) agreementFuzzSize
      primary <- rights <$> mapM prepareAgreementCase draws
      neighbours <- rights . catMaybes <$> mapM prepareAgreementNeighbour draws
      let spll = primary ++ neighbours
      spllU <- catMaybes <$> mapM (\c -> forced (bodyFeatures (adtsOf (acEnv c)) (comparedBodies c))) spll
      spllB <- rights <$> mapM prepareAgreementBatched spll
      spllBU <- catMaybes <$> mapM (\c -> forced (bodyFeatures (adtsOf (bcEnv c)) (batchedComparedBodies c))) spllB
      writeCounts (dir </> "scalar.tsv")
        [ ("corpus", [ fs | (_, _, fs) <- cScalar ]), ("irgen600", fixedU), ("irgen" ++ show nIR, bigU), ("spll1000", spllU) ]
      writeCounts (dir </> "batched.tsv")
        [ ("corpus", [ fs | (_, _, fs) <- cBatched ]), ("irgen600", bFixedU), ("irgen" ++ show nIR, bBigU), ("spll1000", spllBU) ]
