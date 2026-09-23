module SPLL.Typing.AlgebraicDataTypes (
  implicitFunctionRTypes,
  implicitFunctionsRTypeProg,
  implicitFunctionNames,
  implicitFunctionImpl,
  implicitFunctionApplicable,
  implicitFunctionsToEnv,
  lookupRType,
  fieldAccessorOwners,
  findField,
  anyCtorTestMessage,
  accessorMismatchMessage,
  adtCdfMessage
) where
import SPLL.Lang.Types
import SPLL.Typing.RType
import SPLL.IntermediateRepresentation (IRExpr (..))
import Data.Function (on)
import Data.List (nubBy)
import Data.Vector.Internal.Check (HasCallStack)

implicitFunctionsRTypeProg :: Program -> [(String, RType)]
implicitFunctionsRTypeProg Program {adts=adtDecls} = concatMap implicitFunctionRTypes adtDecls

implicitFunctionRTypes :: ADTDecl -> [(String, RType)]
implicitFunctionRTypes ADTDecl{dataName=name, constructors=constrs} = concatMap (implicitFunctionRTypesConstr name) constrs

implicitFunctionRTypesConstr :: String -> ADTConstructorDecl -> [(String, RType)]
implicitFunctionRTypesConstr tyName (name, fields) = constructorRType tyName name (map snd fields): isRType tyName name : map (accessorRType tyName) fields

constructorRType :: String -> String -> [RType] -> (String, RType)
constructorRType tyName name rts = (name, foldr TArrow (TADT tyName) rts)

accessorRType :: String -> (String, RType) -> (String, RType)
accessorRType tyName (name, rt) = (name, TADT tyName `TArrow` rt)

isRType :: String -> String -> (String, RType)
isRType tyName name = ("is" ++ name, TADT tyName `TArrow` TBool)

implicitFunctionNames :: [ADTDecl] -> [String]
implicitFunctionNames decls = map fst (concatMap implicitFunctionRTypes decls)

-- | Every field accessor paired with the constructor whose field it reads,
-- with the *first* declaration of a name winning.
--
-- That tie-break is not a choice: 'findField' already resolves a duplicated
-- field name to the first constructor declaring it, and 'lookupRType' picks the
-- first entry too, so first-wins is what the type environment and the
-- interpreter both mean. The text backends used to emit one accessor per
-- constructor, which made Python last-wins (the later @def@ shadows the
-- earlier) and Julia accept-both (the two typed methods dispatch), so the same
-- program answered three different ways. They now emit one accessor per name,
-- from this list.
fieldAccessorOwners :: [ADTDecl] -> [(String, String)]
fieldAccessorOwners decls = nubBy ((==) `on` fst)
  [ (fName, cName)
  | decl <- decls, (cName, fields) <- constructors decl, (fName, _) <- fields ]

lookupRType :: String -> [ADTDecl] -> RType 
lookupRType name decl = case lookup name (concatMap implicitFunctionRTypes decl) of
  Just rt -> rt
  Nothing -> error $ "RType not found for adt function: " ++ name

-- Create an entry in the environment that wraps a call to the funnction in lambdas for each of its parameters
-- Final form: x3 -> x2 -> x1 -> x0 -> IRVar "constr_adt"
-- No need to invoke here, because this is only for the interpreter
implicitFunctionsToEnv :: ADTDecl -> [(String, IRExpr)]
implicitFunctionsToEnv decl = map (\(n, rt) -> (n, createLambdaFromRType rt 0 (IRVar $ n ++ "_adt"))) (implicitFunctionRTypes decl)

createLambdaFromRType :: RType -> Int -> IRExpr -> IRExpr
createLambdaFromRType (_ `TArrow` rt) idx inner = IRLambda ("x" ++ show idx) (createLambdaFromRType rt (idx + 1) inner)
createLambdaFromRType _ _ inner = inner

implicitFunctionImpl :: (Show a, HasCallStack) => [ADTDecl] -> String -> [GenericValue a] -> GenericValue a
implicitFunctionImpl decls fName [param] | fName `elem` isFNames = isImpl (drop 2 fName) param
  where isFNames = concatMap (map (("is" ++) . fst) . constructors) decls
implicitFunctionImpl decls fName param | fName `elem` constrFNames = VADT fName param
  where constrFNames = concatMap (map fst . constructors) decls
implicitFunctionImpl decls fName [param] =
  case param of
    VADT constr fields ->
      if constr /= cName then
        error (accessorMismatchMessage fName cName ++ " Got: " ++ constr)
      else
        fields !! fIdx
    _ -> error $ "Value must but be an ADT type for field lookup: " ++ show param
  where (cName, fIdx) = findField decls fName
implicitFunctionImpl _ fName params = error $ "somethigng went wrong with implicit function implementations. function: " ++ fName ++ " parameters: " ++ show params

-- | Is 'implicitFunctionImpl' defined at this argument?
--
-- Constructors are total, but the other two implicit functions are not: a field
-- accessor reads a field of *one* constructor (@b1@ has nothing to say about an
-- @A@), and a constructor test needs an ADT value to test. 'implicitFunctionImpl'
-- answers those with 'error', which is right for a runtime evaluation that
-- should never get there -- but 'PredefinedFunctions.propagateValues' walks a
-- whole enumerable domain through the forward function at compile time, and a
-- multi-constructor domain necessarily contains values every accessor is
-- undefined on. It asks this first and skips them, so an accessor's enumerated
-- domain is the values of its own constructor rather than a compiler crash.
implicitFunctionApplicable :: [ADTDecl] -> String -> [GenericValue a] -> Bool
implicitFunctionApplicable decls fName [param] | fName `elem` isFNames = isADTValue param
  where isFNames = concatMap (map (("is" ++) . fst) . constructors) decls
implicitFunctionApplicable decls fName _ | fName `elem` constrFNames = True
  where constrFNames = concatMap (map fst . constructors) decls
implicitFunctionApplicable decls fName [param] | fName `elem` implicitFunctionNames decls =
  case param of
    VADT constr _ -> constr == fst (findField decls fName)
    _ -> False
implicitFunctionApplicable _ _ _ = True

isADTValue :: GenericValue a -> Bool
isADTValue (VADT _ _) = True
isADTValue _ = False

isImpl :: Show a => String -> GenericValue a -> GenericValue a
isImpl constr (VADT name _) = VBool $ name == constr
isImpl constr VAny = error (anyCtorTestMessage constr)
-- TODO should also error if type is from the wrong ADT
isImpl _ x = error ("Parameter is not an ADT: " ++ show x)

-- | What every backend says when a constructor predicate is applied to a
-- marginal wildcard. A hole has no constructor yet, so both answers are wrong:
-- @True@ invents one, and @False@ asserts "not this constructor" and silently
-- deletes that branch's mass -- which is what the two scalar backends used to
-- do, while the interpreter crashed, so the same program answered differently
-- depending on where it ran (task
-- @is-ctor-on-any-slot-diverges-across-backends@). All three now refuse, with
-- this message, so the divergence cannot come back quietly.
--
-- Deliberately not extended to 'VAnyExcept': @isRed (VAnyExcept [Red])@ is
-- genuinely @False@ and answerable, which is separate work rather than a
-- refusal.
anyCtorTestMessage :: String -> String
anyCtorTestMessage ctor =
  "is" ++ ctor ++ ": constructor test on an unobserved value (ANY); the "
  ++ "enclosing inference must marginalise or refuse before testing a hole"

-- | What every runtime says when a field accessor is applied to a value built
-- by a constructor that has no such field -- @color Nil@, where @color@ is a
-- field of @Obj@.
--
-- An accessor's generated 'RType' is @TADT ty -> fieldType@: it accepts *any*
-- value of the ADT, so 'RInfer' cannot reject this. Refining the type per
-- constructor was considered and declined -- the constructor of a value is a
-- runtime property, and encoding it in the type is not something Haskell itself
-- solves in a principled way either. So the accessor stays partial and the
-- failure stays at run time; what this fixes is that the failure used to be
-- unreadable and different everywhere: a bare @AttributeError: \'Nil\' object
-- has no attribute \'color\'@ in Python, a @MethodError@ in Julia, and an
-- interpreter message that named the *field* where it said "type"
-- (@"Is type: Nil but should be: color"@).
--
-- The wording mirrors GHC's own diagnostic for the same mistake on a record
-- selector (@No match in record selector color@), extended with the owning
-- constructor, which is the fact that tells the reader why the call is wrong.
-- Every runtime appends the constructor it actually saw as @" Got: <name>"@;
-- the core below is byte-identical across the interpreter and all three text
-- backends, so a regression in one of them cannot hide.
accessorMismatchMessage :: String -> String -> String
accessorMismatchMessage accessor ctor =
  "No match in field accessor '" ++ accessor ++ "': it selects a field of "
  ++ "constructor '" ++ ctor ++ "' and is undefined on a value built by any "
  ++ "other constructor."

-- | What a @cdf()@ query says when the program it is asked about returns an
-- ADT. A cumulative distribution integrates along an order, and an ADT has
-- none: its constructors are an unordered sum, so there is no "at or below
-- @Node Leaf Leaf@" to accumulate. Defining one would mean fixing a
-- declaration order as semantics, which is a design decision rather than a
-- missing case, so the compiler refuses instead of inventing one. Point
-- queries (@p()@) are unaffected -- they compare structurally and need no
-- order. Pinned by TestRejection's @AdtCumulative@ group.
adtCdfMessage :: String -> String
adtCdfMessage tyName =
  "cdf(): no cumulative distribution is defined over the ADT '" ++ tyName
  ++ "' -- its constructors carry no order to integrate along. Use p() for a "
  ++ "point query on this program."

-- Returns constructor and field index
findField :: [ADTDecl] -> String -> (String, Int)
findField decls name = case mapM (mapM (mFindField 0) . constructors) decls of
  Left a -> a
  Right _ -> error ("Field not found: " ++ name)
  where
    -- Use the either monad to find the field so we can run this on all constructors and get one output. Could be done using list operators, but I assume its easier this way
    mFindField :: Int -> ADTConstructorDecl -> Either (String, Int) ()
    mFindField idx (cName, (fName, _):_) | fName == name = Left (cName, idx)
    mFindField idx (cName, _:fields) = mFindField (idx + 1) (cName, fields)
    mFindField _ _ = Right ()