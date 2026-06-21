module SPLL.Typing.Infer
  ( addTypeInfo
  ) where

import SPLL.Lang.Lang (Program)
import SPLL.Typing.RInfer
import SPLL.Typing.ModalityInfer (addModalityPTypeInfo)
import SPLL.Lang.Types (CompilerError)


addTypeInfo :: Program -> Either CompilerError Program
addTypeInfo p = addRTypeInfo p >>= addModalityPTypeInfo

