/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.Probability.KoalaBear
import ArkLib.ProofSystem.ToyProblem.Impl.IRS
import Lean.Compiler.IR

/-!
# Code-generation gates for the toy problem

This module makes the executable launch cone a checked API. Each probe is outside any
`noncomputable section`, and each source declaration must have a compiler IR declaration.
The companion `toyproblem-runtime` executable exercises the concrete algorithms.
-/

namespace ToyProblem.Codegen

open Lean Elab Command

elab "assert_toy_ir " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
    throwError "expected compiler IR for `{name}`"

/-- Out-of-section probe for the six-limb `KoalaBear.Ext6` sampler. -/
def ext6SamplerProbe := @KoalaBear.sampleExt6

/-- Out-of-section probe for the pinned `SampleableType KoalaBear.Ext6` implementation. -/
@[reducible] def ext6SampleableTypeProbe := @KoalaBear.sampleableTypeExt6

/-- Out-of-section probe for the interleaved message split. -/
def irsUnflattenProbe := @Impl.IRS.irsUnflatten

/-- Out-of-section probe for the interleaved message join. -/
def irsFlattenProbe := @Impl.IRS.irsFlatten

/-- Out-of-section probe for the interleaved Reed--Solomon encoder. -/
def irsEncoderProbe := @Impl.IRS.irsEncoder

/-- Out-of-section probe for the scalar checked erasure decoder. -/
def rsErasureDecoderProbe := @Spec.rsErasureDecoder

/-- Out-of-section probe for the total interleaved erasure decoder. -/
def irsErasureDecoderProbe := @Impl.IRS.irsErasureDecodeOrZero

/-- Out-of-section probe for the dynamic transition extractor. -/
def irsTransitionExtractorProbe := @Impl.IRS.irsTransitionExtractor

/-- Out-of-section probe for the round-by-round extractor. -/
def irsRbrExtractorProbe := @Impl.IRS.irsRbrExtractor

/-- Out-of-section probe for the exact straightline extractor. -/
def irsStraightlineExtractorProbe := @Impl.IRS.irsStraightlineExtractor

assert_toy_ir KoalaBear.sampleExt6
assert_toy_ir KoalaBear.sampleableTypeExt6
assert_toy_ir Impl.IRS.irsUnflatten
assert_toy_ir Impl.IRS.irsFlatten
assert_toy_ir Impl.IRS.irsEncoder
assert_toy_ir Spec.rsErasureDecoder
assert_toy_ir Impl.IRS.irsErasureDecodeOrZero
assert_toy_ir Impl.IRS.irsTransitionExtractor
assert_toy_ir Impl.IRS.irsRbrExtractor
assert_toy_ir Impl.IRS.irsStraightlineExtractor

end ToyProblem.Codegen
