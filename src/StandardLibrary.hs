module StandardLibrary where
import SPLL.IntermediateRepresentation (IRExpr(..), Operand (..))
import SPLL.Lang.Types

data StandardFunction = StandartFunction {functionName :: String, parameterCount :: Int, functionBody :: IRExpr}

stdIndexOf :: StandardFunction
stdIndexOf = StandartFunction {functionName = "indexOf", parameterCount = 2,
  functionBody=IRLambda "sample" (IRLambda "lst" 
    (IRIf (IROp OpEq (IRVar "lst") (IRConst $ VList EmptyList)) -- If lst is empty
      (IRError "Element not found in list") -- Then error
      (IRIf (IROp OpEq (IRHead (IRVar "lst")) (IRVar "sample")) --else if (head lst) == sample
        (IRConst $ VInt 0)  -- return 0
        (IROp OpPlus (IRConst $ VInt 1) (invokeStandardFunction stdIndexOf [IRVar "sample", IRTail (IRVar "lst")])))))} -- else return 1 + indexOf(sample, tail(lst))

stdListProd :: StandardFunction
stdListProd = StandartFunction {functionName="listProd", parameterCount=1,
  functionBody=IRLambda "lst" 
    (IRIf (IROp OpEq (IRVar "lst") (IRConst $ VList EmptyList)) -- If lst is empty
      (IRConst $ VFloat 1) -- Then 1
      (IROp OpMult (IRHead (IRVar "lst")) (invokeStandardFunction stdListProd [IRTail (IRVar "lst")])))}

invokeStandardFunction :: StandardFunction -> [IRExpr] -> IRExpr
invokeStandardFunction f params | length params /= parameterCount f = error $ "Wrong number of arguments for " ++ functionName f
invokeStandardFunction f params = foldl IRApply (IRVar (functionName f)) params

standardLibrary :: [StandardFunction]
standardLibrary = [stdIndexOf, stdListProd]

standardEnv :: [(String, IRExpr)]
standardEnv = map (\f -> (functionName f, functionBody f)) standardLibrary