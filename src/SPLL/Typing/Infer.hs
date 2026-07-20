module SPLL.Typing.Infer
  ( addTypeInfo
  , addModalityInfo
  ) where

import SPLL.Lang.Lang (Program)
import SPLL.Typing.RInfer
import SPLL.Typing.ModalityInfer (addModalityPTypeInfo)
import SPLL.Typing.ForwardChaining (FCData, progToFCData)
import SPLL.Typing.Determinism (knownAnchors)
import SPLL.Lang.Types (CompilerError)

-- | RType inference, then the forward-chaining certificate, then the modality
-- pass, on a program that has not yet had any of the three run -- kept for
-- callers (tests, mainly) that still want the whole pipeline collapsed into one
-- entry point on a chain-named program. 'SPLL.Prelude.compile' no longer uses
-- this directly: it runs 'addRTypeInfo' first, before enum annotation/forward
-- chaining even see the program (so those passes, and any InjF-applicability
-- checks upstream of typing, can rely on real RType instead of 'NotSetYet', and
-- ill-typed programs are rejected before reaching them at all), then calls
-- 'addModalityInfo' for the remaining tail. See 'addModalityInfo' for the
-- certificate/modality half.
addTypeInfo :: Program -> Either CompilerError (Program, FCData)
addTypeInfo p = do
  rtyped <- addRTypeInfo p
  addModalityInfo rtyped

-- | The forward-chaining certificate, then the modality (PType) pass, on a
-- program that already carries RType info (and, in 'SPLL.Prelude.compile',
-- enum annotation + chain names too). The certificate is built exactly once:
-- it reads rType (function arrows) but no pType, and the modality engine
-- consults its witnessed-binding verdict for the let rule (design
-- @modality-witnessed-inference@, milestone 2). Expects a chain-named program
-- (@annotateProg@ has run). The certificate is returned alongside the typed
-- program so the caller can thread the same FCData to the downstream consumers
-- (conditional annotation, IR codegen) instead of rebuilding it.
addModalityInfo :: Program -> Either CompilerError (Program, FCData)
addModalityInfo rtyped = do
  let fcData = progToFCData (knownAnchors rtyped) rtyped
  typed <- addModalityPTypeInfo fcData rtyped
  return (typed, fcData)
