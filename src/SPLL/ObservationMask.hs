-- | The observation tree, its leaf slots, their latent sets, correlation
-- classes, and the masked (pruned) program.
--
-- Task @observation-mask-analysis@, task 2 of design
-- @witnessed-per-query-capability@. This module is /pure analysis and rewriting/:
-- it computes what a query's mask can be, and produces the program that mask
-- corresponds to. It runs no pipeline stage and emits no IR. Typing a masked
-- program (the mask table) lives in "SPLL.Prelude", which is the module allowed
-- to drive the pipeline.
--
-- The design's claim, restated so this module can be read on its own: a query
-- with @ANY@ holes is not a point query with a wildcard value, it is an
-- observation of a different /shape/. Making the mask a compile-time object
-- means deleting the masked slots from the program and inferring what remains
-- ('pruneObservation'), rather than threading a mask through inference.
module SPLL.ObservationMask
  ( -- * Accessor paths and slots
    Accessor(..)
  , Slot
  , Mask
  , prettyAccessor
  , prettySlot
  , prettyMask
    -- * The observation tree
  , ObsTree(..)
  , Binding(..)
  , LetEnv
  , observationTree
  , obsPath
  , obsLeaves
  , obsSlots
    -- * Latents
  , Latent(..)
  , latentsOverlap
  , slotLatents
  , localSlotLatents
    -- * Correlation and self-containment
  , correlationClasses
  , hasCorrelatedSlots
  , SlotVerdict(..)
  , slotVerdicts
  , selfContained
  , enumeratedSlots
    -- * The masked program
  , masksOver
  , pruneObservation
  , holeFor
    -- * Predicates shared with the pipeline
  , isObsConstructor
  , accessorStep
  ) where

import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.AlgebraicDataTypes (fieldAccessorOwners, findField)
import PredefinedFunctions (isObsConstructor)

import Data.List (foldl', isPrefixOf, intercalate, partition)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Set (Set)

-- ---------------------------------------------------------------------------
-- Accessor paths
-- ---------------------------------------------------------------------------

-- | One step of an accessor path: the constructor that was descended through,
-- and which of its fields.
--
-- The pair @(constructor, field index)@ rather than a closed enumeration of
-- @fst@\/@snd@\/@fromLeft@\/... because user ADT constructors have arbitrary
-- arity and their accessors are named per declaration. 'prettyAccessor' maps
-- the pair back to the name a user would write.
data Accessor = Accessor
  { accCtor  :: String
  , accField :: Int
  } deriving (Eq, Ord, Show)

-- | A leaf slot's identity: its accessor path from the observation root,
-- outermost step first. The root itself is @[]@.
type Slot = [Accessor]

-- | The set of leaf slots a query observes as @ANY@. A mask over an inner node
-- is spelled as the set of leaf slots beneath it.
type Mask = Set Slot

-- | The accessor name a user would write for one step.
prettyAccessor :: [ADTDecl] -> Accessor -> String
prettyAccessor decls (Accessor c i) = case (c, i) of
  ("TCons", 0)  -> "fst"
  ("TCons", 1)  -> "snd"
  ("Cons", 0)   -> "head"
  ("Cons", 1)   -> "tail"
  ("left", 0)   -> "fromLeft"
  ("right", 0)  -> "fromRight"
  _             -> fromMaybe (c ++ "." ++ show i) (adtFieldName decls c i)

adtFieldName :: [ADTDecl] -> String -> Int -> Maybe String
adtFieldName decls c i =
  case [ map fst fields | decl <- decls, (cName, fields) <- constructors decl, cName == c ] of
    (names:_) | i < length names -> Just (names !! i)
    _                            -> Nothing

-- | A slot rendered as a dotted accessor chain; the root reads @\<root\>@.
prettySlot :: [ADTDecl] -> Slot -> String
prettySlot _    []   = "<root>"
prettySlot decls path = intercalate "." (map (prettyAccessor decls) path)

-- | A mask rendered against the slot list it is a subset of, in the design's
-- tuple notation: a concrete slot is @_@, a masked one @ANY@.
prettyMask :: [Slot] -> Mask -> String
prettyMask slots m =
  "(" ++ intercalate ", " [ if s `Set.member` m then "ANY" else "_" | s <- slots ] ++ ")"

-- ---------------------------------------------------------------------------
-- The observation tree
-- ---------------------------------------------------------------------------

-- | A @let@ binding in scope at some point of the observation tree.
data Binding = Binding
  { bndName        :: String
  , bndValue       :: Expr
  -- | Occurrences of the bound variable in the binding's scope. The root-@Var@
  -- descent follows a binding only at exactly one occurrence, because a second
  -- occurrence means the value is observed in more than one place and the
  -- accessor path from the root no longer identifies it.
  , bndOccurrences :: Int
  -- | The environment at the binding /site/, which is what the bound value's
  -- free variables resolve in. Carrying it keeps shadowing honest.
  , bndEnv         :: LetEnv
  }

instance Show Binding where
  show b = "Binding " ++ show (bndName b) ++ " (occurrences " ++ show (bndOccurrences b) ++ ")"

-- | Innermost binding first.
type LetEnv = [Binding]

-- | The observation tree of a top-level function: constructor applications
-- descended into, everything else a leaf.
data ObsTree
  = ObsCon Slot String [ObsTree]
    -- ^ A constructor application: its own accessor path, the constructor name,
    -- and its fields in declaration order.
  | ObsLeaf Slot Expr LetEnv
    -- ^ A leaf slot: its accessor path from the root, the sub-expression
    -- observed there, and the @let@ environment in scope at it.
  deriving Show

-- | The path of a node.
obsPath :: ObsTree -> Slot
obsPath (ObsCon p _ _)  = p
obsPath (ObsLeaf p _ _) = p

-- | Every leaf, in tree order.
obsLeaves :: ObsTree -> [(Slot, Expr, LetEnv)]
obsLeaves (ObsLeaf p e env) = [(p, e, env)]
obsLeaves (ObsCon _ _ fs)   = concatMap obsLeaves fs

-- | Every leaf slot, in tree order. The order is the one masks and reports are
-- rendered in, and the one the dispatcher's @isAny@ tests will run in.
obsSlots :: ObsTree -> [Slot]
obsSlots t = [ s | (s, _, _) <- obsLeaves t ]

-- | The observation tree of a declaration.
--
-- Parameter lambdas are stripped, @let@ bodies descended, a single-occurrence
-- root @Var@ followed to its bound value, and the descent stops at a
-- constructor application, whose fields are descended in turn. Everything else
-- is a leaf. A root that is not a constructor tree has exactly one leaf: the
-- root itself.
observationTree :: [ADTDecl] -> FnDecl -> ObsTree
observationTree decls (_, body) = buildObs decls [] [] (stripParams body)

stripParams :: Expr -> Expr
stripParams (Expr _ (Lambda _ b)) = stripParams b
stripParams e                     = e

buildObs :: [ADTDecl] -> LetEnv -> Slot -> Expr -> ObsTree
buildObs decls env path e =
  case node core of
    InjF (Named c) args
      | isObsConstructor decls c ->
          ObsCon path c
            [ buildObs decls env' (path ++ [Accessor c i]) a | (i, a) <- zip [0 ..] args ]
    _ -> ObsLeaf path core env'
  where
    (env', core, _) = focus env e

-- ---------------------------------------------------------------------------
-- Focusing: the let chain, and the lens that puts a rewritten core back
-- ---------------------------------------------------------------------------

-- | One @let@ frame of a body, i.e. one @Apply (Lambda x b) v@.
data LetFrame = LetFrame
  { lfApplyTI  :: TypeInfo
  , lfLambdaTI :: TypeInfo
  , lfName     :: String
  , lfValue    :: Expr
  }

peelChain :: Expr -> ([LetFrame], Expr)
peelChain (Expr ti (Apply (Expr lti (Lambda x b)) v)) =
  let (fs, core) = peelChain b in (LetFrame ti lti x v : fs, core)
peelChain e = ([], e)

rebuildChain :: [LetFrame] -> Expr -> Expr
rebuildChain fs body =
  foldr (\f b -> Expr (lfApplyTI f) (Apply (Expr (lfLambdaTI f) (Lambda (lfName f) b)) (lfValue f))) body fs

-- | Descend an expression's @let@ chain to the node the observation is actually
-- /of/, returning the environment in scope there, that node, and a lens that
-- puts a replacement for it back into the original expression.
--
-- The lens is what makes 'pruneObservation' and 'observationTree' share one
-- descent: a leaf reached by following a single-occurrence root @Var@ lives in
-- a binding's /value/, not in the body, so a rewrite of it has to reach back up
-- the chain. Doing that by hand in a second traversal is how the two would come
-- to disagree about which sub-expression a slot names.
focus :: LetEnv -> Expr -> (LetEnv, Expr, Expr -> Expr)
focus env e
  | Var x <- node body
  , (before, LetFrame{lfValue = v} : after) <- break ((== x) . lfName) frames
  , occurrencesInScope x (map lfValue after ++ [body]) == 1
  = let (env2, core, reb) = focus (envAt (length before) frames env) v
    in ( env2
       , core
       , \new -> rebuildChain (before ++ [(frames !! length before){lfValue = reb new}] ++ after) body )
  | otherwise
  = (envAtEnd frames env, body, rebuildChain frames)
  where
    (frames, body) = peelChain e

-- | The environment as seen /inside/ the value of frame @i@: the frames bound
-- before it, plus whatever was already in scope.
envAt :: Int -> [LetFrame] -> LetEnv -> LetEnv
envAt i frames outer = framesToEnv (take i frames) outer

-- | The environment at the end of the chain: every frame is in scope.
envAtEnd :: [LetFrame] -> LetEnv -> LetEnv
envAtEnd frames outer = framesToEnv frames outer

-- | Turn a prefix of a let chain into an environment, innermost first, with each
-- binding carrying the environment at its own site.
framesToEnv :: [LetFrame] -> LetEnv -> LetEnv
framesToEnv frames outer = foldl' step outer (zip [0 ..] frames)
  where
    step acc (i, f) =
      Binding { bndName        = lfName f
              , bndValue       = lfValue f
              , bndOccurrences = occurrencesInScope (lfName f) (map lfValue (drop (i + 1) frames))
              , bndEnv         = acc
              } : acc

lookupBinding :: String -> LetEnv -> Maybe Binding
lookupBinding x env = case filter ((== x) . bndName) env of
  (b:_) -> Just b
  []    -> Nothing

-- | Free occurrences of @x@ across a list of expressions, shadowing-aware.
occurrencesInScope :: String -> [Expr] -> Int
occurrencesInScope x = sum . map (countVarOcc x)

countVarOcc :: String -> Expr -> Int
countVarOcc x e = case node e of
  Var y | y == x   -> 1
  Lambda y _ | y == x -> 0   -- shadowed: no free occurrence of the outer x below
  _ -> sum (map (countVarOcc x) (getSubExprs e))

-- ---------------------------------------------------------------------------
-- Latents
-- ---------------------------------------------------------------------------

-- | A random source a slot can depend on.
--
-- Identity is /per occurrence/, keyed by chain name: SPLL's @let@ is the eager
-- form, so two slots reading the same @let@-bound variable reach the same
-- 'Expr' node and therefore the same latent, while two syntactic @Uniform@s are
-- two draws and two latents.
data Latent
  = LDist ChainName
    -- ^ One draw: an inline @Uniform@\/@Normal@, or an occurrence of a
    -- probabilistic top-level function.
  | LNeural ChainName [Accessor]
    -- ^ A neural read, at the 'SPLL.AutoNeural.PartitionPlan' leaf it is read
    -- through. Accessor chains onto distinct plan leaves are distinct latents,
    -- which is what makes a neural ADT program's fields independent.
  deriving (Eq, Ord, Show)

-- | Do two latents denote sources that are not independent?
--
-- Equality for draws. For neural reads, /prefix overlap/: reading the whole
-- output and reading one field of it are the same source, while two distinct
-- fields are not. A path can only ever go as deep as the plan's own structure —
-- there is no accessor into a @MultiContinuous@ or @MultiDiscretes@ leaf — so
-- no two distinct incomparable paths can name the same plan leaf, and no
-- consultation of the 'MultiValue' is needed here.
latentsOverlap :: Latent -> Latent -> Bool
latentsOverlap (LDist a) (LDist b) = a == b
latentsOverlap (LNeural a p) (LNeural b q) = a == b && (p `isPrefixOf` q || q `isPrefixOf` p)
latentsOverlap _ _ = False

-- | The random sources each leaf slot transitively depends on, through @let@
-- bindings.
slotLatents :: [ADTDecl] -> [FnDecl] -> ObsTree -> [(Slot, Set Latent)]
slotLatents decls fenv t =
  [ (s, latentsOf decls fenv env [] e) | (s, e, env) <- obsLeaves t ]

-- | The latents a leaf slot depends on /without/ following anything bound
-- outside its own sub-expression.
--
-- This is the syntactic half of 'selfContained': a slot whose draws all happen
-- inside it is one nothing else can be reading.
localSlotLatents :: [ADTDecl] -> [FnDecl] -> ObsTree -> [(Slot, Set Latent)]
localSlotLatents decls fenv t =
  [ (s, latentsOf decls fenv [] [] e) | (s, e, _) <- obsLeaves t ]

latentsOf :: [ADTDecl] -> [FnDecl] -> LetEnv -> [String] -> Expr -> Set Latent
latentsOf decls fenv env seen e = case node e of
  Var "Uniform" -> Set.singleton (LDist (chainNameOf e))
  Var "Normal"  -> Set.singleton (LDist (chainNameOf e))
  ReadNN _ arg  -> Set.insert (LNeural (chainNameOf e) []) (descend arg)
  Var x
    | x `elem` seen -> Set.empty
    | Just b <- lookupBinding x env ->
        latentsOf decls fenv (bndEnv b) (x : seen) (bndValue b)
    | Just fbody <- lookup x fenv ->
        -- A reference to a top-level function is a fresh draw per occurrence if
        -- its body draws at all, so it contributes ONE latent keyed by this
        -- occurrence rather than the callee's own latents.
        if Set.null (latentsOf decls fenv [] (x : seen) fbody)
          then Set.empty
          else Set.singleton (LDist (chainNameOf e))
    | otherwise -> Set.empty   -- a parameter, or a name with no body in reach
  InjF (Named f) [a]
    | Just acc <- accessorStep decls f -> refine acc (descend a)
  _ -> Set.unions (map descend (getSubExprs e))
  where
    descend = latentsOf decls fenv env seen
    refine acc ls = case Set.toList ls of
      [LNeural cn p] -> Set.singleton (LNeural cn (p ++ [acc]))
      _              -> ls

chainNameOf :: Expr -> ChainName
chainNameOf = chainName . getTypeInfo

-- | The accessor step a named unary @InjF@ performs, if it is a deconstructor.
accessorStep :: [ADTDecl] -> String -> Maybe Accessor
accessorStep decls f = case f of
  "fst"       -> Just (Accessor "TCons" 0)
  "snd"       -> Just (Accessor "TCons" 1)
  "head"      -> Just (Accessor "Cons" 0)
  "tail"      -> Just (Accessor "Cons" 1)
  "fromLeft"  -> Just (Accessor "left" 0)
  "fromRight" -> Just (Accessor "right" 0)
  _ | f `elem` map fst (fieldAccessorOwners decls) ->
        let (c, i) = findField decls f in Just (Accessor c i)
    | otherwise -> Nothing

-- ---------------------------------------------------------------------------
-- Correlation classes and self-containment
-- ---------------------------------------------------------------------------

-- | Connected components of leaf slots under shared latents, in tree order
-- (each class ordered by first appearance, classes ordered by their first
-- member).
--
-- Every leaf slot is a node, so a slot sharing nothing is a singleton class.
-- That is what [[warn-correlated-slots]] wants as its trigger: /some class has
-- two or more slots/.
correlationClasses :: [(Slot, Set Latent)] -> [[Slot]]
correlationClasses table = map fst (foldl' insertSlot [] table)
  where
    -- A class in flight is (its slots, the union of their latents). Adding a
    -- slot merges every class it touches, which is what makes this transitive:
    -- slots 1 and 3 land in one class when both touch slot 2.
    insertSlot classes (s, ls) =
      let (touching, disjoint) = partition (\(_, cls) -> overlapsAny ls cls) classes
          slots'   = concatMap fst touching ++ [s]
          latents' = Set.unions (map snd touching ++ [ls])
      in disjoint ++ [(slots', latents')]
    overlapsAny ls ls' =
      or [ latentsOverlap a b | a <- Set.toList ls, b <- Set.toList ls' ]

-- | The trigger [[warn-correlated-slots]] asks for: does some correlation class
-- hold two or more slots?
--
-- That task is only @proposed@, so this is the one-line hook rather than a wired
-- warning: when it is approved, the diagnostic reads this and names the class's
-- slots. Nothing consults it today beyond the @--marginals@ report, which prints
-- the classes themselves.
hasCorrelatedSlots :: [[Slot]] -> Bool
hasCorrelatedSlots = any ((> 1) . length)

-- | Why a slot is enumerated, or that it is not.
data SlotVerdict
  = SelfContained
    -- ^ Every latent of the slot is drawn inside it (or is a neural plan leaf
    -- nothing else touches), and none is shared. The existing per-field
    -- @anySafe@ guard is exact here, so the slot needs no variant.
  | SharesLatents [Slot]
    -- ^ Enumerated: it shares a latent with these other slots.
  | ReadsOuterLatents [Latent]
    -- ^ Enumerated: these latents are drawn outside the slot's own
    -- sub-expression, so something else can read their density.
  deriving (Eq, Show)

-- | The verdict for every leaf slot, in tree order.
slotVerdicts :: [ADTDecl] -> [FnDecl] -> ObsTree -> [(Slot, SlotVerdict)]
slotVerdicts decls fenv t =
  [ (s, verdict s ls) | (s, ls) <- full ]
  where
    full  = slotLatents decls fenv t
    local = localSlotLatents decls fenv t
    verdict s ls
      | not (null shared)  = SharesLatents shared
      | not (null outer)   = ReadsOuterLatents outer
      | otherwise          = SelfContained
      where
        shared = [ s' | (s', ls') <- full, s' /= s
                      , or [ latentsOverlap a b | a <- Set.toList ls, b <- Set.toList ls' ] ]
        localLs = fromMaybe Set.empty (lookup s local)
        -- A neural read bound outside the slot is still self-contained when no
        -- other slot touches its plan leaf; that is the `shared` test above,
        -- already passed here. Only draws have to be syntactically local.
        outer = [ l | l@(LDist _) <- Set.toList ls, not (Set.member l localLs) ]

-- | Is this slot self-contained?
selfContained :: [ADTDecl] -> [FnDecl] -> ObsTree -> Slot -> Bool
selfContained decls fenv t s =
  lookup s (slotVerdicts decls fenv t) == Just SelfContained

-- | The complement of the self-contained slots, in tree order. These are the
-- slots a mask ranges over.
enumeratedSlots :: [ADTDecl] -> [FnDecl] -> ObsTree -> [Slot]
enumeratedSlots decls fenv t =
  [ s | (s, v) <- slotVerdicts decls fenv t, v /= SelfContained ]

-- ---------------------------------------------------------------------------
-- The masked program
-- ---------------------------------------------------------------------------

-- | Every mask over a set of enumerated slots, @2^k@ of them, the empty
-- (all-concrete) mask first.
masksOver :: [Slot] -> [Mask]
masksOver = map Set.fromList . subsequencesBySize
  where
    subsequencesBySize ss = concat [ ofSize n ss | n <- [0 .. length ss] ]
    ofSize 0 _      = [[]]
    ofSize _ []     = []
    ofSize n (x:xs) = map (x :) (ofSize (n - 1) xs) ++ ofSize n xs

-- | The hole a masked leaf is replaced by: @Constant VAny@ carrying the leaf's
-- 'RType'.
--
-- @Constant VAny@ cannot appear in a user program
-- ('SPLL.Validator.validateExpression' forbids it), so the marker is
-- unambiguous. To the stages after pruning a hole is just a constant: @Exact@
-- in the modality lattice, a premise-free clause in forward chaining, and — see
-- "SPLL.Analysis" — deliberately /no/ @DiscreteValues@ tag, since a hole's
-- domain is absent, not the singleton @{ANY}@.
holeFor :: Expr -> Expr
holeFor leaf = Expr (makeTypeInfo { rType = rType (getTypeInfo leaf) }) (Constant VAny)

-- | Replace every masked leaf's sub-expression by a hole.
--
-- Runs after RInfer, so the leaf's 'RType' is available to carry onto the hole.
-- Slots not in the mask, and everything outside the observation tree, are left
-- byte-identical — in particular the empty mask is the identity, which is what
-- makes the all-concrete variant today's body.
pruneObservation :: [ADTDecl] -> Mask -> FnDecl -> FnDecl
pruneObservation decls m (name, body) = (name, goParams body)
  where
    goParams (Expr ti (Lambda x b)) = Expr ti (Lambda x (goParams b))
    goParams e                      = prune [] e

    prune path e = reb (rewrite path core)
      where (_, core, reb) = focus [] e

    rewrite path core = case node core of
      InjF (Named c) args
        | isObsConstructor decls c ->
            Expr (getTypeInfo core) (InjF (Named c)
              [ prune (path ++ [Accessor c i]) a | (i, a) <- zip [0 ..] args ])
      _ | path `Set.member` m -> holeFor core
        | otherwise           -> core
