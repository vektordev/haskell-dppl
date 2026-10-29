{-# LANGUAGE DeriveFunctor #-}
-- | The IR's value vocabulary: values, value sets, shapes. Nothing here
-- mentions the surface AST; the frontend instantiates the expression
-- parameter with @Expr@ and the IR with @IRExpr@ (task
-- ir-package-boundary-b2-ir-value-vocabulary).
module SPLL.IR.Value
  ( CompilerError
  , ThetaTree(..)
  , GenericList(..)
  , ValueList
  , GenericValue(..)
  , isVEither, isVTuple, isVADT
  , valueContainsAny
  , GenericMultiValue(..)
  , Shape
  , Extent(..)
  , extentSize
  , shapeNumel
  , shapeRank
  , dropAxis
  , prettyShape
  , floatApproxEqThresh
  , elementAt
  , valueInMultiValue
  , multiValueToValueList
  , multiValueCardinality
  , constructVList
  ) where

import qualified Data.Bifunctor as Bifunctor
import Data.List (intercalate)
import Data.Maybe (fromMaybe)

type CompilerError = String

data ThetaTree = ThetaTree [Double] [ThetaTree] deriving (Show, Eq)

data GenericList a = EmptyList | ListCont a (GenericList a) | AnyList deriving (Show, Eq)
type ValueList a = GenericList (GenericValue a)

instance Functor GenericList where
  fmap _ EmptyList = EmptyList
  fmap f (ListCont x xs) = ListCont (f x) (fmap f xs) 
  fmap _ AnyList = AnyList

instance Foldable GenericList where
  foldMap _ EmptyList = mempty
  foldMap f (ListCont x xs) = f x `mappend` foldMap f xs
  foldMap _ AnyList = error "Cannot fold AnyLists"

instance Traversable GenericList where
  traverse _ EmptyList = pure EmptyList
  traverse f (ListCont x xs) = ListCont <$> f x <*> traverse f xs
  traverse _ AnyList = error "AnyLists are not traversable"


data GenericValue a = VBool Bool
           | VInt Int
           | VSymbol String
           | VFloat Double
           | VUnit
           | VList (GenericList (GenericValue a))
           | VTuple (GenericValue a) (GenericValue a)
           | VEither (Either (GenericValue a) (GenericValue a))
           | VThetaTree ThetaTree
           | VClosure [(String, a)] String a
           | VADT String [GenericValue a]
           -- | A tensor: a statically-shaped, flat, homogeneous block of
           -- values. The element list is in row-major order (outermost axis
           -- first) and its length is always @shapeNumel@ of the shape, which
           -- is the invariant every producer maintains and 'tensorWellFormed'
           -- checks.
           --
           -- Flat with an explicit shape, as against 'VList''s cons spine:
           -- extent is known statically, so an index is O(1) and a reduction
           -- is one pass rather than a walk. Produced and consumed only by the
           -- tensor builtins ('BTensor', 'BMap', 'BReduce', 'BIndex') -- the
           -- surface language has no syntax for it and the parser never builds
           -- one, so it is unreachable in a 'Value' that came from a .ppl
           -- file. It lives in 'GenericValue' rather than a type of its own
           -- because the interpreter's let-environments are typed as
           -- 'IRValue', and a mapped tensor has to be let-bindable for one map
           -- to feed two reduces (design ir-tensor-values).
           --
           -- Element type is unconstrained here: homogeneity of /primitives/
           -- is not a typing obligation at this layer but a codegen
           -- opportunity -- a tensor of float/int/bool lowers to a real torch
           -- tensor with an O(1) gather and a vectorized reduce, anything else
           -- falls back to a generic list.
           | VTensor Shape [GenericValue a]
           | VAny -- Only used for marginal queries
           | VAnyExcept [a] -- Only used for marginal queries
           | VError String
           deriving (Show, Eq)

instance Functor GenericValue where
  fmap _ (VInt x) = VInt x
  fmap _ (VBool x) = VBool x
  fmap _ (VSymbol x) = VSymbol x
  fmap _ (VFloat x) = VFloat x
  fmap _ VUnit = VUnit
  fmap f (VList x) = VList (fmap (fmap f) x)
  fmap f (VTuple x y) = VTuple (fmap f x) (fmap f y)
  fmap f (VEither (Left x)) = VEither (Left (fmap f x))
  fmap f (VEither (Right x)) = VEither (Right (fmap f x))
  fmap _ (VThetaTree x) = VThetaTree x
  fmap f (VClosure e n ex) = VClosure (map (Bifunctor.second f) e) n (f ex)
  fmap f (VADT n adt) = VADT n (map (fmap f) adt)
  fmap f (VTensor sh xs) = VTensor sh (map (fmap f) xs)
  fmap f (VAnyExcept x) = VAnyExcept (map f x)
  fmap _ VAny = VAny
  fmap _ (VError s) = VError s


isVTuple, isVEither, isVADT :: GenericValue a -> Bool
isVTuple (VTuple _ _) = True
isVTuple _ = False
isVEither (VEither _) = True
isVEither _ = False
isVADT (VADT _ _) = True
isVADT _ = False

-- | Whether a value has a placeholder 'VAny'/'VAnyExcept' anywhere in its
-- structure (e.g. 'VEither (Left VAny)') -- distinct from the value itself
-- being 'VAny'. Used to tell a witness that only partially determines a value
-- (recovered from a lossy inverse, e.g. isLeft's, which knows the tag but not
-- the payload) apart from a fully concrete one.
valueContainsAny :: GenericValue a -> Bool
valueContainsAny VAny = True
valueContainsAny (VAnyExcept _) = True
valueContainsAny (VEither (Left v)) = valueContainsAny v
valueContainsAny (VEither (Right v)) = valueContainsAny v
valueContainsAny (VTuple a b) = valueContainsAny a || valueContainsAny b
valueContainsAny (VADT _ vs) = any valueContainsAny vs
valueContainsAny (VList l) = listContainsAny l
  where
    listContainsAny EmptyList = False
    listContainsAny AnyList = True
    listContainsAny (ListCont x xs) = valueContainsAny x || listContainsAny xs
valueContainsAny _ = False

data GenericMultiValue a = MultiDiscretes [GenericValue a]
                | MultiTuple (GenericMultiValue a) (GenericMultiValue a)
                | MultiEither (GenericMultiValue a) (GenericMultiValue a)
                | MultiADT [(String, [GenericMultiValue a])]
                | MultiTypeRef String
                | MultiContinuous     -- ^ A continuous (Float) leaf, written "Real" in .ppl source.
                | MultiAuto           -- ^ Placeholder ("_" in .ppl source): auto-derive from the RType.
                deriving (Show, Eq, Functor)

constructVList :: [GenericValue a] -> GenericValue a
constructVList xs = VList $ foldr ListCont EmptyList xs

multiValueToValueList :: GenericMultiValue a -> [GenericValue a]
-- A continuous slot has no enumerable values: any composite containing it also has none.
multiValueToValueList MultiContinuous = []
multiValueToValueList MultiAuto = error "multiValueToValueList: unresolved auto-placeholder (_); this should have been resolved before discrete-value propagation"
multiValueToValueList (MultiTypeRef n) = error ("multiValueToValueList: unresolved recursion reference to '" ++ n ++ "'; resolveMultiValueTypeDecl should have unrolled it")
multiValueToValueList (MultiDiscretes vals) = vals
multiValueToValueList (MultiEither ls rs) = map (VEither . Left) lVals ++ map (VEither . Right) rVals
  where
    lVals = multiValueToValueList ls
    rVals = multiValueToValueList rs
multiValueToValueList (MultiTuple as bs) = [VTuple aVal bVal | aVal <- aVals, bVal <- bVals]
  where
    aVals = multiValueToValueList as
    bVals = multiValueToValueList bs
multiValueToValueList (MultiADT constrs) = concatMap (\(cn, fieldCombos) -> map (VADT cn) fieldCombos) constrFieldCombinations
  where allFieldCombinations = sequence . map multiValueToValueList
        constrFieldCombinations = map (Bifunctor.second allFieldCombinations) constrs

-- | The number of values 'multiValueToValueList' would yield, computed
-- structurally WITHOUT building the list. 'Nothing' when the domain is not
-- statically finite (exactly when 'multiValueIsFinite' is 'False'), so a
-- caller gets "no answer" rather than a misleading count.
--
-- This exists because the count is the only thing a budget check needs, and
-- the list it counts can be astronomically large: a depth-unrolled recursive
-- ADT is a cross-product, so @length . 'multiValueToValueList'@ is itself the
-- blow-up a budget check is there to avoid paying. 'Integer' rather than
-- 'Int' for the same reason -- the product overflows a machine word long
-- before any caller would want to materialize it, and an overflowed count
-- that wraps to something small would wave through exactly the domain the
-- budget exists to refuse.
multiValueCardinality :: GenericMultiValue a -> Maybe Integer
multiValueCardinality MultiContinuous = Nothing
multiValueCardinality MultiAuto = Nothing
multiValueCardinality (MultiTypeRef _) = Nothing
multiValueCardinality (MultiDiscretes vals) = if null vals then Nothing else Just (toInteger (length vals))
multiValueCardinality (MultiTuple a b) = (*) <$> multiValueCardinality a <*> multiValueCardinality b
multiValueCardinality (MultiEither a b) = (+) <$> multiValueCardinality a <*> multiValueCardinality b
-- Mirrors 'multiValueIsFinite'/'multiValueToValueList': a constructor's fields
-- multiply (the 'sequence' cross-product), constructors sum, and a nullary
-- constructor contributes the empty product, 1.
multiValueCardinality (MultiADT constrs)
  | null constrs = Nothing
  | otherwise = sum <$> mapM (fmap product . mapM multiValueCardinality . snd) constrs

valueInMultiValue :: Eq a => GenericMultiValue a -> GenericValue a -> Bool
valueInMultiValue MultiContinuous (VFloat _) = True
valueInMultiValue (MultiDiscretes d) x = x `elem` d
valueInMultiValue (MultiEither ml _) (VEither (Left l)) = valueInMultiValue ml l
valueInMultiValue (MultiEither _ mr) (VEither (Right r)) = valueInMultiValue mr r
valueInMultiValue (MultiTuple mf ms) (VTuple f s) = valueInMultiValue mf f && valueInMultiValue ms s
valueInMultiValue (MultiADT mConstrs) (VADT cName vals) = fromMaybe False (do
  constr <- lookup cName mConstrs
  return $ all (uncurry valueInMultiValue) (zip constr vals))
valueInMultiValue MultiAuto _ = error "valueInMultiValue: unresolved auto-placeholder (_); resolveMultiAuto should have run first"
valueInMultiValue (MultiTypeRef n) _ = error ("valueInMultiValue: unresolved recursion reference to '" ++ n ++ "'; resolveMultiValueTypeDecl should have unrolled it")
-- Any remaining pair is a value whose shape does not match the value set's, so
-- it is simply not a member.
valueInMultiValue _ _ = False

elementAt :: ValueList a -> Int -> GenericValue a
elementAt (ListCont x _) 0 = x
elementAt (ListCont _ xs) i = elementAt xs (i-1)
elementAt EmptyList _ = error "Index out of bounds"
elementAt AnyList _ = error "Cannot iterate AnyLists"
floatApproxEqThresh :: Double
floatApproxEqThresh = 1e-10

-- | The shape of a tensor: the extent of each axis, outermost first. The rank
-- is the length. Shared by the IR tensor value ('VTensor') and the surface
-- type @TTensor Shape RType@ (design tensors-in-core-language §2.2), so the
-- surface type lowers onto the IR value already carrying the shape, with
-- nothing to re-represent. Rank 0 is not a shape: the parser refuses
-- @Tensor[] τ@.
type Shape = [Extent]

-- | The extent of one axis.
--
-- A sum type with a single constructor on purpose (design
-- tensors-in-core-language §2.2, and §7 on why restrictive choices are the
-- cheap ones to lift): shape /variables/ are deliberately out (decision B), and spelling this @type Shape = [Int]@ would make admitting an
-- @EVar@ later a change to the arity of every shape pattern in the compiler
-- rather than one new constructor.
newtype Extent = EFixed Int
  deriving (Show, Eq, Ord)

extentSize :: Extent -> Int
extentSize (EFixed n) = n

-- | The number of elements a shape holds -- the product of its extents. A
-- rank-0 shape has one element by this rule, but rank 0 is not an inhabited
-- shape (see the note on 'shapeRank').
shapeNumel :: Shape -> Int
shapeNumel = product . map extentSize

shapeRank :: Shape -> Int
shapeRank = length

-- | Drop one axis from a shape, as a reduction or an index along that axis
-- does. 'Nothing' when the axis is out of range.
dropAxis :: Int -> Shape -> Maybe Shape
dropAxis i sh
  | i >= 0 && i < length sh = Just (take i sh ++ drop (i + 1) sh)
  | otherwise = Nothing

-- | A shape as the user writes it: @[3,4]@.
prettyShape :: Shape -> String
prettyShape sh = "[" ++ intercalate "," (map (show . extentSize) sh) ++ "]"
