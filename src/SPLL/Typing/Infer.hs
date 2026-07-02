module SPLL.Typing.Infer
  ( addTypeInfo
  ) where

import SPLL.Lang.Lang (Program)
import SPLL.Typing.RInfer
import SPLL.Typing.ModalityInfer (addModalityPTypeInfo)
import SPLL.Typing.ForwardChaining (FCData, progToFCData)
import SPLL.Typing.Determinism (knownAnchors)
import SPLL.Lang.Types (CompilerError)

-- | RType inference, then the forward-chaining certificate, then the modality
-- pass. The certificate is built exactly once, between the two passes: it reads
-- rType (function arrows) but no pType, and the modality engine consults its
-- witnessed-binding verdict for the let rule (design
-- @modality-witnessed-inference@, milestone 2). Expects a chain-named program
-- (@annotateProg@ has run). The certificate is returned alongside the typed
-- program so the caller can thread the same FCData to the downstream consumers
-- (conditional annotation, IR codegen) instead of rebuilding it.
addTypeInfo :: Program -> Either CompilerError (Program, FCData)
addTypeInfo p = do
  rtyped <- addRTypeInfo p
  let fcData = progToFCData (knownAnchors p) rtyped
  typed <- addModalityPTypeInfo fcData rtyped
  return (typed, fcData)
