module SPLL.Typing.AlgebraicDataTypes (
  implicitFunctionRTypes,
  implicitFunctionsRTypeProg,
  adtCdfMessage
) where
import SPLL.Lang.Types
import SPLL.Typing.RType

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
