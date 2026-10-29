{-# LANGUAGE PatternSynonyms #-}
-- | The stage-diff driver of design transformation-differential-testing
-- (milestone M4, task transformation-differential-testing-m4-isolation-automation).
--
-- Two programs that denote the same distribution -- typically a program and
-- a semantics-preserving rewrite of it ("Rewrites" in the test suite) -- are
-- compiled side by side, keeping every stage's output ('compileStages', the
-- programs @-d@ prints). The stages are compared in pipeline order, and the
-- first one whose outputs differ /more than the rewrite explains/ is reported:
-- that is where the defect entered.
--
-- What "the rewrite explains" means, for the annotated AST stages: the two
-- trees are aligned from each declaration's root. Where the two subtrees are
-- equal up to bound-variable names, every node pair is compared. Where they
-- differ, the pair still denotes the same value (it is the rewritten subterm,
-- or one of its ancestors), so its root's annotation is compared; the walk
-- then descends into the one child that differs, if exactly one does and the
-- nodes have the same shape, and stops otherwise. The node pairs reached
-- this way must carry the same 'RType' (type variables aside), the same
-- 'PType' (unless it is a function: 'isArrow') and, where both have one, the same value set (a node enumeration
-- cannot tag says nothing, so only two different sets disagree). Chain names are generated, and the modality
-- stage's laws name the engine that answers, which a rewrite is /meant/ to
-- change, so neither is compared.
--
-- The IR stages are compared by inventory: for each function group both sides
-- have, whether its generate and probability variants were built, refused or
-- absent. Not integrate: the answers below are probabilities, and a
-- cumulative variant one spelling gets and the other does not is the cdf
-- frontier, which is wider and would place every probability divergence
-- behind it. Then the answers: at @-O0@ (if they differ there, IR compilation
-- computed a different value) and at the given configuration (if they differ
-- only there, the optimizer did).
module SPLL.StageDiff
  ( StageDiffOpts(..)
  , defaultStageDiffOpts
  , StageRow(..)
  , StageReport(..)
  , stageDiff
  , stageDiffStages
  , renderStageReport
  , answersStage
  , optimizationStage
  , isDivergent
  ) where

import Control.Exception (SomeException, evaluate, try)
import Data.List (intercalate, sortOn)
import Data.Maybe (isJust, isNothing, mapMaybe)
import qualified Data.Map as Map

import SPLL.Lang.Types
import SPLL.Lang.Lang (getSubExprs)
import SPLL.Typing.RType (RType(..), TVarR(..))
import qualified SPLL.Typing.PType as PT
import SPLL.IntermediateRepresentation (IREnv(..), IRFunGroup(..), IRValue, pattern VProbDim)
import SPLL.CompilerConfig (CompilerConfig(..))
import SPLL.Typing.ModalityInfer (LawTable, Law(..), Justification(..))
import SPLL.Prelude (compile, compileStages, runProbC, StageSnapshot(..), StageValue(..))

data StageDiffOpts = StageDiffOpts
  { sdConfig :: CompilerConfig
    -- ^ The configuration both programs are compiled at.
  , sdQueries :: [(IRValue, [IRValue])]
    -- ^ Probability queries (sample, parameters) of @main@ to compare the
    -- answers at. Without any, only the structural stages are compared.
  , sdTolerance :: Double
    -- ^ Probabilities agree within this, relative above 1.
  }

defaultStageDiffOpts :: CompilerConfig -> StageDiffOpts
defaultStageDiffOpts conf = StageDiffOpts conf [] 0.0001

-- | What one stage shows.
data StageRow
  = Same
    -- ^ No difference beyond the rewrite.
  | Rewrite [String]
    -- ^ The parse stage: where the two programs differ, which is the rewrite.
  | Diverges [String]
    -- ^ A difference the rewrite does not explain.
  | Refuses String String
    -- ^ One side stopped here (which side, its error); the other went on.
  | BothRefuse String
    -- ^ Both stopped here.
  deriving (Show, Eq)

isDivergent :: StageRow -> Bool
isDivergent Diverges{} = True
isDivergent Refuses{} = True
isDivergent _ = False

data StageReport = StageReport
  { stageRows :: [(String, StageRow)]
    -- ^ Every stage either side ran, in pipeline order, then the two answer
    -- rows ('answersStage', 'optimizationStage') when there are queries.
  , firstDivergence :: Maybe (String, StageRow)
  }

-- | The pseudo-stage of the answers at @-O0@.
answersStage :: String
answersStage = "Answers at -O0 (IR compilation)"

-- | The pseudo-stage of the answers at the given configuration, when they
-- agree at @-O0@.
optimizationStage :: String
optimizationStage = "Answers at the given optimizer level (IR optimizer)"

-- | Compare two programs stage by stage. The first program is the
-- reference ("original"), the second the rewrite.
--
-- In 'IO' because a compiler or interpreter @error@ is a result here, not a
-- crash of the driver: a stage whose output raises when read is where that
-- side stopped, with the exception as its message ('settle'); an answer that
-- raises is a refusal.
stageDiff :: StageDiffOpts -> Program -> Program -> IO StageReport
stageDiff opts a b = do
  sa <- settle (compileStages conf a)
  sb <- settle (compileStages conf b)
  a0 <- answersAt conf0 a
  b0 <- answersAt conf0 b
  aO <- answersAt conf a
  bO <- answersAt conf b
  return (stageDiffStages opts sa sb (a0, b0) (aO, bO))
  where
    conf = sdConfig opts
    conf0 = conf { optimizerLevel = 0 }
    answersAt c p
      | null (sdQueries opts) = return Nothing
      | otherwise = Just . either (Left . crash) id <$> try (evaluate (forceAnswers (answers c p)))
    answers c p = case compile c p of
      Left err -> Left err
      Right env -> mapM (\(s, params) -> runProbC p env params s >>= probDim) (sdQueries opts)
    probDim (VProbDim pr d) = Right (pr, d)
    probDim v = Left ("not a probability result: " ++ show v)
    forceAnswers r = either (\e -> length e `seq` r) (\xs -> sum (map (\(p, d) -> p + fromIntegral d) xs) `seq` r) r

crash :: SomeException -> String
crash ex = "crash: " ++ show ex

-- | Force each snapshot as far as the comparison reads it, in pipeline
-- order, and the final result. The first that raises ends the list there,
-- with the exception as the compile's error.
settle :: ([StageSnapshot], Either CompilerError IREnv) -> IO ([StageSnapshot], Either CompilerError ())
settle (snaps, res) = go snaps
  where
    -- The list's spine is lazy too: the next cell exists only once the stage
    -- before it has decided it did not refuse, which can raise.
    go l = do
      cell <- try (evaluate l)
      case cell of
        Left ex -> return ([], Left (crash ex))
        Right [] -> do
          r <- try (evaluate (either (\e -> length e `seq` Left e) (\env -> length (inventory env) `seq` Right ()) res))
          return ([], either (Left . crash) id r)
        Right (x : xs) -> do
          r <- try (evaluate (forceSnap (snapValue x)))
          case r of
            Left ex -> return ([], Left (crash ex))
            Right () -> (\(rest, out) -> (x : rest, out)) <$> go xs
    forceSnap v = case v of
      StageProgram p -> length (show p) `seq` ()
      StageTyped p laws -> length (show p) `seq` Map.foldr (\l acc -> lawShape l `seq` acc) () laws
      StageIR env -> length (inventory env) `seq` ()
    lawShape (Law _ j) = case j of
      JDirac (Just v) -> length (show v)
      _ -> 0
    inventory (IREnv gs _ _) = concat [ groupName g ++ show (isJust (genFun g), isJust (probFun g), isJust (integFun g), map fst (refusedVariants g)) | g <- gs ]

type Answers = Maybe (Either String [(Double, Int)])

-- | 'stageDiff' on already computed stages and answers (at @-O0@, then at the
-- configuration). Exposed so a test can hand it a pipeline with a seeded
-- defect.
stageDiffStages :: StageDiffOpts -> ([StageSnapshot], Either CompilerError a) -> ([StageSnapshot], Either CompilerError b)
                -> (Answers, Answers) -> (Answers, Answers) -> StageReport
stageDiffStages opts (sa, ra) (sb, rb) (a0, b0) (aO, bO) = StageReport rows (lookupFirst rows)
  where
    labels = mergeOrder (map snapLabel sa) (map snapLabel sb) ++ [endLabel]
    rows = structural ++ answerRows
    structural = go labels Nothing Nothing
    -- The last snapshot seen on each side stands in for a stage that side
    -- skipped (it did not fire, so its program is the previous one).
    go [] _ _ = []
    go (l : ls) prevA prevB =
      let curA = maybe prevA Just (lookupSnap l sa)
          curB = maybe prevB Just (lookupSnap l sb)
          doneA = endedBefore l sa ra
          doneB = endedBefore l sb rb
          row | doneA && doneB = Just (BothRefuse (errOf ra))
              | doneA = Just (Refuses "original" (errOf ra))
              | doneB = Just (Refuses "rewritten" (errOf rb))
              | l == endLabel = Nothing
              | otherwise = Just (compareStage l curA curB)
      in maybe [] (\r -> [(l, r)]) row ++ if doneA || doneB then [] else go ls curA curB
    -- A side that refused has no snapshot at or after the stage it refused in.
    endedBefore l snaps r = case r of
      Left _ -> all (`elem` takeWhile (/= l) labels) (map snapLabel snaps) && l `notElem` map snapLabel snaps
      Right _ -> False
    errOf r = either id (const "") r
    structurallyOk = all (not . isDivergent . snd) structural
    answerRows
      | not structurallyOk = []
      | otherwise = case (a0, b0, aO, bO) of
          (Just x0, Just y0, Just xO, Just yO) ->
            let r0 = compareAnswers (sdTolerance opts) x0 y0
                rO = compareAnswers (sdTolerance opts) xO yO
            in [(answersStage, r0)] ++ [ (optimizationStage, rO) | not (isDivergent r0) ]
          _ -> []
    lookupFirst rs = case filter (isDivergent . snd) rs of
      (r : _) -> Just r
      [] -> Nothing

-- | The pseudo-stage after the last snapshot, where a compile that refused
-- after its last dumped stage (IR compilation proper, say) stops.
endLabel :: String
endLabel = "(after the last dumped stage)"

lookupSnap :: String -> [StageSnapshot] -> Maybe StageValue
lookupSnap l snaps = case [snapValue s | s <- snaps, snapLabel s == l] of
  (v : _) -> Just v
  [] -> Nothing

-- | Interleave two subsequences of the pipeline's stage order into one.
mergeOrder :: [String] -> [String] -> [String]
mergeOrder [] ys = ys
mergeOrder xs [] = xs
mergeOrder (x : xs) (y : ys)
  | x == y = x : mergeOrder xs ys
  | x `notElem` ys = x : mergeOrder xs (y : ys)
  | otherwise = y : mergeOrder (x : xs) ys

compareAnswers :: Double -> Either String [(Double, Int)] -> Either String [(Double, Int)] -> StageRow
compareAnswers tol x y = case (x, y) of
  (Right as, Right bs)
    | length as == length bs && and (zipWith agrees as bs) -> Same
    | otherwise -> Diverges [ "original " ++ show p ++ ", rewritten " ++ show q | (p, q) <- zip as bs, not (agrees p q) ]
  (Left ea, Left _) -> BothRefuse ea
  (Left ea, Right _) -> Refuses "original" ea
  (Right _, Left eb) -> Refuses "rewritten" eb
  where
    agrees (p1, d1) (p2, d2)
      | isNaN p1 || isNaN p2 = isNaN p1 && isNaN p2 && d1 == d2
      | p1 == 0 && p2 == 0 = True
      | otherwise = abs (p1 - p2) <= tol * max 1 (abs p1) && d1 == d2

compareStage :: String -> Maybe StageValue -> Maybe StageValue -> StageRow
compareStage l (Just va) (Just vb) = case (asProgram va, asProgram vb, va, vb) of
  (_, _, StageTyped pa la, StageTyped pb lb) -> rowOf (astDiffs pa pb ++ pointDiffs pa la pb lb)
  (Just pa, Just pb, _, _)
    | "Parsing" `elem` words l -> Rewrite (rewriteRegions pa pb)
    | otherwise -> rowOf (astDiffs pa pb)
  (_, _, StageIR ea, StageIR eb) -> rowOf (irDiffs ea eb)
  _ -> Same
  where
    rowOf [] = Same
    rowOf ds = Diverges ds
compareStage _ _ _ = Same

asProgram :: StageValue -> Maybe Program
asProgram (StageProgram p) = Just p
asProgram (StageTyped p _) = Just p
asProgram (StageIR _) = Nothing

-- ---------------------------------------------------------------------------
-- AST alignment
-- ---------------------------------------------------------------------------

-- | Equal up to the names of bound variables, annotations ignored.
alphaEq :: Expr -> Expr -> Bool
alphaEq = go Map.empty Map.empty
  where
    go ma mb (Expr _ x) (Expr _ y) = case (x, y) of
      (Var v, Var w) -> case (Map.lookup v ma, Map.lookup w mb) of
        (Just i, Just j) -> i == j
        (Nothing, Nothing) -> v == w
        _ -> False
      (Lambda v b1, Lambda w b2) ->
        let k = Map.size ma in go (Map.insert v k ma) (Map.insert w k mb) b1 b2
      _ -> sameLocalShape x y && and (zipWith (go ma mb) (toListF x) (toListF y))
    toListF = foldr (:) []

-- | The same constructor and arity, and the same name or value where it has
-- one -- except a lambda's binder, which 'alphaEq' accounts for.
sameLocalShape :: ExprF Expr -> ExprF Expr -> Bool
sameLocalShape x y = case (x, y) of
  (Var a, Var b) -> a == b
  (InjF a xs, InjF b ys) -> a == b && length xs == length ys
  (Lambda _ _, Lambda _ _) -> True
  (Constant a, Constant b) -> a == b
  (ReadNN a _, ReadNN b _) -> a == b
  (ThetaI _ i, ThetaI _ j) -> i == j
  (Subtree _ i, Subtree _ j) -> i == j
  (IfThenElse{}, IfThenElse{}) -> True
  (Apply{}, Apply{}) -> True
  _ -> False

-- | The node pairs the rewrite leaves comparable, per declaration both
-- programs have: (a path naming the node, the two nodes).
alignedPairs :: Program -> Program -> [(String, Expr, Expr)]
alignedPairs pa pb =
  concat [ walk d a b | (d, a) <- functions pa, Just b <- [lookup d (functions pb)] ]
  where
    walk path a b
      | alphaEq a b = everyPair path a b
      | otherwise = (path, a, b) : descend
      where
        ca = getSubExprs a
        cb = getSubExprs b
        differing = [ i | (i, x, y) <- zip3 [0 :: Int ..] ca cb, not (alphaEq x y) ]
        descend
          | sameLocalShape (node a) (node b) && length ca == length cb =
              concat [ if i `elem` differing then (if length differing == 1 then walk (childPath path a i) x y else [])
                       else everyPair (childPath path a i) x y
                     | (i, x, y) <- zip3 [0 ..] ca cb ]
          | otherwise = []
    everyPair path a b = (path, a, b) : concat [ everyPair (childPath path a i) x y | (i, x, y) <- zip3 [0 :: Int ..] (getSubExprs a) (getSubExprs b) ]

childPath :: String -> Expr -> Int -> String
childPath path parent i = path ++ "/" ++ shapeName (node parent) ++ "." ++ show i

shapeName :: ExprF Expr -> String
shapeName e = case e of
  IfThenElse{} -> "if"
  InjF (Named f) _ -> f
  Var v -> v
  Constant _ -> "const"
  Lambda x _ -> "\\" ++ x
  Apply{} -> "apply"
  ThetaI{} -> "theta"
  Subtree{} -> "subtree"
  ReadNN n _ -> n

-- | The annotation differences at the aligned node pairs.
astDiffs :: Program -> Program -> [String]
astDiffs pa pb = mapMaybe one (alignedPairs pa pb)
  where
    one (path, a, b) =
      let ta = ann a; tb = ann b
          ds = [ "rType " ++ show (rType ta) ++ " vs " ++ show (rType tb) | normR (rType ta) /= normR (rType tb) ]
            ++ [ "pType " ++ show (pType ta) ++ " vs " ++ show (pType tb) | not (isArrow ta || isArrow tb), normP (pType ta) /= normP (pType tb) ]
            ++ [ "tags " ++ show (tags ta) ++ " vs " ++ show (tags tb)
               | not (null (tags ta)), not (null (tags tb)), show (map normTag (tags ta)) /= show (map normTag (tags tb)) ]
      in if null ds then Nothing else Just (path ++ " [" ++ shapeName (node a) ++ "]: " ++ intercalate "; " ds)

-- | At the modality stage: an aligned pair where one node's law is a point
-- mass of known value and the other's is not, or the two values differ.
-- Which engine answers a node is the rewrite's business, and so is the shape
-- of its certificate (a constructor of points, or a point of unknown value),
-- but the value the analysis knows a node to take is the distribution's: the
-- compiler measures a known point from that value ('IRCompiler.lawPoint'),
-- so the rewrite cannot explain losing it.
pointDiffs :: Program -> LawTable -> Program -> LawTable -> [String]
pointDiffs pa la pb lb = mapMaybe one (alignedPairs pa pb)
  where
    one (path, a, b) =
      let pt laws e = case Map.lookup (chainName (ann e)) laws of
            Just (Law _ (JDirac (Just v))) -> Just v
            _ -> Nothing
          x = pt la a; y = pt lb b
      in if show x == show y then Nothing
         else Just (path ++ " [" ++ shapeName (node a) ++ "]: law " ++ point x ++ " vs " ++ point y)
    point = maybe "of no known value" (("a point mass at " ++) . show)

-- | A value set is a set: the order enumeration lists it in follows the
-- order of the program's branches, which an if-flip or a commutation changes.
-- Compared through 'show', so that a NaN equals itself.
normTag :: Tag -> Tag
normTag (DiscreteValues mv) = DiscreteValues (normMV mv)
  where
    normMV m = case m of
      MultiDiscretes vs -> MultiDiscretes (sortOn show (nubShow vs))
      MultiTuple x y -> MultiTuple (normMV x) (normMV y)
      MultiEither x y -> MultiEither (normMV x) (normMV y)
      MultiADT cs -> MultiADT (sortOn show [ (c, map normMV fs) | (c, fs) <- cs ])
      _ -> m
    nubShow = map snd . Map.toList . Map.fromList . map (\v -> (show v, v))

-- | A function value's 'PType' describes its body as compiled at that
-- spelling, not a distribution, and eta-equivalent spellings (@f@ and
-- @\\x -> f x@, which draw introduction makes of a callee) get different ones.
isArrow :: TypeInfo -> Bool
isArrow ti = case rType ti of
  TArrow _ _ -> True
  _ -> False

-- | Type variables carry generated names, so any two are taken to agree.
normR :: RType -> RType
normR t = case t of
  TVarR _ -> TVarR (TV "_")
  ListOf x -> ListOf (normR x)
  Tuple x y -> Tuple (normR x) (normR y)
  TEither x y -> TEither (normR x) (normR y)
  TArrow x y -> TArrow (normR x) (normR y)
  TTensor s x -> TTensor s (normR x)
  GreaterType x y -> GreaterType (normR x) (normR y)
  _ -> t

normP :: PT.PType -> PT.PType
normP t = case t of
  PT.TVar _ -> PT.TVar (PT.TV "_")
  PT.PArr x y -> PT.PArr (normP x) (normP y)
  _ -> t

-- | Where the parsed programs differ: the deepest node pairs the alignment
-- reaches that are not equal, and the declarations only one side has.
rewriteRegions :: Program -> Program -> [String]
rewriteRegions pa pb =
  concat [ regions d a b | (d, a) <- functions pa, Just b <- [lookup d (functions pb)] ]
  ++ [ "declaration " ++ d ++ " only in the original" | (d, _) <- functions pa, isNothing (lookup d (functions pb)) ]
  ++ [ "declaration " ++ d ++ " only in the rewrite" | (d, _) <- functions pb, isNothing (lookup d (functions pa)) ]
  where
    regions path a b
      | alphaEq a b = []
      | sameLocalShape (node a) (node b) && length ca == length cb, [i] <- differing =
          regions (childPath path a i) (ca !! i) (cb !! i)
      | otherwise = [path ++ " [" ++ shapeName (node a) ++ " -> " ++ shapeName (node b) ++ "]"]
      where
        ca = getSubExprs a
        cb = getSubExprs b
        differing = [ i | (i, x, y) <- zip3 [0 :: Int ..] ca cb, not (alphaEq x y) ]

-- ---------------------------------------------------------------------------
-- IR inventory
-- ---------------------------------------------------------------------------

irDiffs :: IREnv -> IREnv -> [String]
irDiffs (IREnv ga _ _) (IREnv gb _ _) =
  [ groupName g ++ ": " ++ lbl ++ " " ++ status g lbl field ++ " in the original, " ++ status h lbl field ++ " in the rewrite"
  | g <- ga, h <- gb, groupName g == groupName h
  , (lbl, field) <- [("gen", isJust . genFun), ("prob", isJust . probFun)]
  , status g lbl field /= status h lbl field ]
  where
    -- Not the reason: which engine declined, and so its message, is what a
    -- rewrite may change. That a variant is built is what it may not.
    status g lbl field
      | field g = "built"
      | otherwise = maybe "absent" (const "refused") (lookup lbl (refusedVariants g))

-- ---------------------------------------------------------------------------
-- Rendering
-- ---------------------------------------------------------------------------

renderStageReport :: StageReport -> String
renderStageReport r = unlines $
  [ "first divergence: " ++ maybe "none" (\(l, _) -> l) (firstDivergence r) ]
  ++ concatMap row (stageRows r)
  where
    row (l, s) = case s of
      Same -> ["  " ++ l ++ ": same"]
      Rewrite rs -> ("  " ++ l ++ ": the rewrite, at") : map ("      " ++) (take 8 rs)
      Diverges ds -> ("  " ++ l ++ ": DIVERGES") : map ("      " ++) (take 8 ds)
                     ++ [ "      (" ++ show (length ds - 8) ++ " more)" | length ds > 8 ]
      Refuses side e -> ["  " ++ l ++ ": the " ++ side ++ " stops here: " ++ cut e]
      BothRefuse e -> ["  " ++ l ++ ": both stop here: " ++ cut e]
    cut e = let one = takeWhile (/= '\n') e in if length one > 200 then take 200 one ++ "..." else one
