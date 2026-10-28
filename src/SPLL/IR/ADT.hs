-- | The evaluation half of the implicit ADT functions (constructors, field
-- accessors and constructor tests): their names, arities, IR types, runtime
-- semantics and the messages every runtime shares. The frontend's @RType@
-- schemes for the same functions are in "SPLL.Typing.AlgebraicDataTypes".
module SPLL.IR.ADT (
  implicitFunctionNames,
  implicitFunctionArity,
  implicitFunctionIRTypes,
  implicitFunctionImpl,
  implicitFunctionApplicable,
  implicitFunctionsToEnv,
  fieldAccessorOwners,
  findField,
  anyCtorTestMessage,
  accessorMismatchMessage
) where
import SPLL.Lang.Types
import SPLL.IR.Type (IRType(..), irTypeOfRType)
import SPLL.IntermediateRepresentation (IRExpr (..))
import Data.Function (on)
import Data.List (nubBy)
import Data.Vector.Internal.Check (HasCallStack)

-- | Name and parameter count of every implicit function of the declarations,
-- constructor, then its test, then its accessors, per constructor.
implicitFunctionSignatures :: [ADTDecl] -> [(String, Int)]
implicitFunctionSignatures decls =
  [ sig | ADTDecl{constructors=cs} <- decls, (name, fields) <- cs
        , sig <- (name, length fields) : ("is" ++ name, 1) : [ (f, 1) | (f, _) <- fields ] ]

implicitFunctionNames :: [ADTDecl] -> [String]
implicitFunctionNames = map fst . implicitFunctionSignatures

-- | The number of parameters of an implicit function (0 for an unknown name).
implicitFunctionArity :: [ADTDecl] -> String -> Int
implicitFunctionArity decls name = maybe 0 id (lookup name (implicitFunctionSignatures decls))

-- | The 'IRType' of every implicit function. A constructor with a field of no
-- runtime type (a type variable, say, which a parsed declaration never has) is
-- left out, with its accessors.
implicitFunctionIRTypes :: [ADTDecl] -> [(String, IRType)]
implicitFunctionIRTypes decls = concat
  [ (name, foldr (ITArrow . snd) self fieldTys)
    : ("is" ++ name, self `ITArrow` ITBool)
    : [ (f, self `ITArrow` t) | (f, t) <- fieldTys ]
  | ADTDecl{dataName=tyName, constructors=cs} <- decls, (name, fields) <- cs
  , Just fieldTys <- [mapM (\(f, rt) -> (,) f <$> irTypeOfRType rt) fields]
  , let self = ITADT tyName ]

-- | Every field accessor paired with the constructor whose field it reads,
-- with the *first* declaration of a name winning.
--
-- No valid program has a duplicated field name any more:
-- 'SPLL.Validator.validateNoNameCollisions' rejects a field name declared by
-- two constructors, of one ADT or of two (task
-- adt-sibling-shared-field-accessor-unreachable -- with one accessor per name,
-- guarded on one owner, the other constructor's values could never be read
-- back). The tie-break below is therefore only a defensive identity for
-- callers that bypass validation. It was never a choice: 'findField' already resolves a duplicated
-- field name to the first constructor declaring it, and the type environment's accessor table picks the
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

-- Create an entry in the environment that wraps a call to the funnction in lambdas for each of its parameters
-- Final form: x3 -> x2 -> x1 -> x0 -> IRVar "constr_adt"
-- No need to invoke here, because this is only for the interpreter
implicitFunctionsToEnv :: ADTDecl -> [(String, IRExpr)]
implicitFunctionsToEnv decl = map (\(n, k) -> (n, lambdas k 0 (IRVar $ n ++ "_adt"))) (implicitFunctionSignatures [decl])
  where
    lambdas :: Int -> Int -> IRExpr -> IRExpr
    lambdas 0 _ inner = inner
    lambdas k idx inner = IRLambda ("x" ++ show idx) (lambdas (k - 1) (idx + 1) inner)

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
-- An accessor's generated type is @ADT ty -> fieldType@: it accepts *any*
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