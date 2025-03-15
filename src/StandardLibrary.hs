module StandardLibrary where
import SPLL.IntermediateRepresentation (IRExpr(..), Operand (OpEq, OpPlus))
import SPLL.Lang.Types

data StandardFunction = StandartFunction {functionName :: String, parameterCount :: Int, functionBody :: IRExpr}

stdIndexOf :: StandardFunction
stdIndexOf = StandartFunction {functionName = "indexOf", parameterCount = 2,
  functionBody=IRLambda "sample" (IRLambda "lst" 
    (IRIf (IROp OpEq (IRVar "lst") (IRConst $ VList EmptyList)) -- If lst is empty
      (IRError "Element not found in list") -- Then error
      (IRIf (IROp OpEq (IRHead (IRVar "lst")) (IRVar "sample")) --else if (head lst) == sample
        (IRConst $ VFloat 0)  -- return 0
        (IROp OpPlus (IRConst $ VFloat 1) (invokeStandardFunction stdIndexOf [IRVar "sample", IRTail (IRVar "lst")])))))} -- else return 1 + indexOf(sample, tail(lst))

invokeStandardFunction :: StandardFunction -> [IRExpr] -> IRExpr
invokeStandardFunction f params | length params /= parameterCount f = error $ "Wrong number of arguments for " ++ functionName f
invokeStandardFunction f params = IRInvoke $ foldl IRApply (IRVar (functionName f)) params

standardLibrary :: [StandardFunction]
standardLibrary = [stdIndexOf]

standardEnv :: [(String, IRExpr)]
standardEnv = map (\f -> (functionName f, functionBody f)) standardLibrary