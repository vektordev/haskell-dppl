module SPLL.Typing.AlgebraicDataTypes (
  implicitFunctionRTypes,
  implicitFunctionsRTypeProg,
  implicitFunctionNames
) where
import SPLL.Lang.Types
import SPLL.Typing.RType

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

implicitFunctionNames :: Program -> [String]
implicitFunctionNames p = map fst (concatMap implicitFunctionRTypes (adts p))