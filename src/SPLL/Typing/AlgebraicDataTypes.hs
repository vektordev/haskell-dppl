module SPLL.Typing.AlgebraicDataTypes (
  implicitFunctionRTypes,
  implicitFunctionsRTypeProg,
  implicitFunctionNames,
  implicitFunctionImpl,
  implicitFunctionsToEnv,
  lookupRType
) where
import SPLL.Lang.Types
import SPLL.Typing.RType
import System.IO.Error.Lens (errno)
import SPLL.IntermediateRepresentation (IRExpr (..))

implicitFunctionsRTypeProg :: Program -> [(String, RType)]
implicitFunctionsRTypeProg Program {adts=adts} = concatMap implicitFunctionRTypes adts

implicitFunctionRTypes :: ADTDecl -> [(String, RType)]
implicitFunctionRTypes (name, constrs) = concatMap (implicitFunctionRTypesConstr name) constrs

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
createLambdaFromRType _ idx inner = inner

implicitFunctionImpl :: Show a => [ADTDecl] -> String -> [GenericValue a] -> GenericValue a
implicitFunctionImpl decls fName [param] | fName `elem` isFNames = isImpl (drop 2 fName) param
  where isFNames = concatMap (\(_, constrs) -> map (("is" ++) . fst) constrs) decls
implicitFunctionImpl decls fName param | fName `elem` constrFNames = VADT fName param
  where constrFNames = concatMap (\(_, constrs) -> map fst constrs) decls
implicitFunctionImpl decls fName [param] =
  case param of
    VADT constr fields ->
      if constr /= cName then
        error ("Value is of the wrong ADT type. Is type: " ++ constr ++ " but should be: " ++ fName)
      else
        fields !! fIdx
    _ -> error $ "Value mast but be an ADT type for field lookup: " ++ show param
  where (cName, fIdx) = findField decls fName
implicitFunctionImpl _ fName params = error $ "somethigng went wrong with implicit function implementations. function: " ++ fName ++ " parameters: " ++ show params

isImpl :: Show a => String -> GenericValue a -> GenericValue a
isImpl constr (VADT name _) = VBool $ name == constr
-- TODO should also error if type is from the wrong ADT
isImpl _ x = error ("Parameter is not an ADT: " ++ show x)

-- Returns constructor and field index
findField :: [ADTDecl] -> String -> (String, Int)
findField decls name = case mapM (\(_, constrs) -> mapM (mFindField 0) constrs) decls of
  Left a -> a
  Right _ -> error ("Field not found: " ++ name)
  where
    -- Use the either monad to find the field so we can run this on all constructors and get one output. Could be done using list operators, but I assume its easier this way
    mFindField :: Int -> ADTConstructorDecl -> Either (String, Int) ()
    mFindField idx (cName, (fName, _):_) | fName == name = Left (cName, idx)
    mFindField idx (cName, _:fields) = mFindField (idx + 1) (cName, fields)
    mFindField _ _ = Right ()