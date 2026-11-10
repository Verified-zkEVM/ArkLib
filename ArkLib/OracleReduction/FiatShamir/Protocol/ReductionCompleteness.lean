/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.FiatShamir.Protocol
public import ArkLib.OracleReduction.Security.Basic
/-!
# Completeness of the protocol-to-reduction compatibility view

The compatibility prover claims acceptance with a trivial output witness. Its consistency and
output-relation checks therefore coincide exactly with the protocol's Boolean acceptance event,
including stateful ambient oracle effects.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal
variable {n : Nat} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {Stmt Wit σ : Type} [∀ i, SampleableType (pSpec.Challenge i)]
set_option backward.isDefEq.respectTransparency false in
/-- The compatibility reduction has exactly the protocol's completeness error. -/
@[simp] theorem InteractiveProtocol.toReduction_completeness_iff
    (P : InteractiveProtocol oSpec Stmt Wit pSpec) (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (relation : Set (Stmt × Wit)) (ε : ℝ≥0) :
    P.toReduction.completeness init impl relation ε ↔
      P.completeness init impl relation ε := by
  simp only [Proof.completeness, Reduction.completeness, InteractiveProtocol.completeness,
    OptionT.prEvent_eq_run]
  apply forall_congr'
  intro stmt
  apply forall_congr'
  intro wit
  apply imp_congr_right
  intro _
  simp [Reduction.run, Prover.run, Verifier.run, InteractiveProtocol.toReduction,
    InteractiveProver.toReductionProver, InteractiveVerifier.toReductionVerifier,
    InteractiveProtocol.run, Option.getM, ← monadLift_liftM_OptionT, acceptRejectRel,
    OptionT.lift]
