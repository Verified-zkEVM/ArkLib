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
def ext6SamplerProbe := @KoalaBear.Ext6.sample

/-- Out-of-section probe for the pinned `SampleableType KoalaBear.Ext6` implementation. -/
@[reducible] def ext6SampleableTypeProbe := @KoalaBear.Ext6.sampleableType

/-- Out-of-section probe for the interleaved message split. -/
def unflattenProbe := @Impl.IRS.unflatten

/-- Out-of-section probe for the interleaved message join. -/
def flattenProbe := @Impl.IRS.flatten

/-- Out-of-section probe for the interleaved Reed--Solomon encoder. -/
def encoderProbe := @Impl.IRS.encoder

/-- Out-of-section probe for the scalar checked erasure decoder. -/
def rsErasureDecoderProbe := @Spec.rsErasureDecoder

/-- Out-of-section probe for the total interleaved erasure decoder. -/
def erasureDecoderProbe := @Impl.IRS.erasureDecodeOrZero

/-- Out-of-section probe for the dynamic transition extractor. -/
def transitionExtractorProbe := @Impl.IRS.transitionExtractor

/-- Out-of-section probe for the round-by-round extractor. -/
def rbrExtractorProbe := @Impl.IRS.rbrExtractor

/-- Out-of-section probe for the exact straightline extractor. -/
def straightlineExtractorProbe := @Impl.IRS.straightlineExtractor

/-- Out-of-section probes for the executable C6.2 protocol objects. -/
def proverProbe := @Spec.prover
def oracleVerifierProbe := @Spec.oracleVerifier
def oracleReductionProbe := @Spec.oracleReduction

/-- Out-of-section probes for the executable C6.9 protocol objects. -/
def simplifiedProverProbe := @SimplifiedIOR.prover
def simplifiedOracleVerifierProbe := @SimplifiedIOR.oracleVerifier
def simplifiedOracleReductionProbe := @SimplifiedIOR.oracleReduction

/-- Out-of-section probe for the C6.9 virtual output-oracle implementation. -/
def simplifiedOutputSimulationProbe := @SimplifiedIOR.outputSimulation

/-- Out-of-section probe for the C6.9 round-by-round extractor. -/
def simplifiedRbrExtractorProbe := @Impl.IRS.simplifiedRbrExtractor

/-- Out-of-section probe for the C6.9 exact straightline extractor. -/
def simplifiedStraightlineExtractorProbe :=
  @Impl.IRS.simplifiedStraightlineExtractor

assert_toy_ir KoalaBear.Ext6.sample
assert_toy_ir KoalaBear.Ext6.sampleableType
assert_toy_ir Impl.IRS.unflatten
assert_toy_ir Impl.IRS.flatten
assert_toy_ir Impl.IRS.encoder
assert_toy_ir Spec.rsErasureDecoder
assert_toy_ir Impl.IRS.erasureDecodeOrZero
assert_toy_ir Impl.IRS.transitionExtractor
assert_toy_ir Impl.IRS.rbrExtractor
assert_toy_ir Impl.IRS.straightlineExtractor
assert_toy_ir Spec.prover
assert_toy_ir Spec.oracleVerifier
assert_toy_ir Spec.oracleReduction
assert_toy_ir SimplifiedIOR.prover
assert_toy_ir SimplifiedIOR.oracleVerifier
assert_toy_ir SimplifiedIOR.oracleReduction
assert_toy_ir SimplifiedIOR.outputSimulation
assert_toy_ir Impl.IRS.simplifiedRbrExtractor
assert_toy_ir Impl.IRS.simplifiedStraightlineExtractor

end ToyProblem.Codegen
