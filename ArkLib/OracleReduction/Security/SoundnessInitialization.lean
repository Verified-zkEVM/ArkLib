/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Security.GuardedSoundness

/-!
# Averaging ordinary soundness over the initial oracle state
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- A soundness bound valid from each deterministic initial state also holds after sampling
an arbitrary initial state. -/
theorem soundness_of_forall_pure {V : Verifier oSpec StmtIn StmtOut pSpec}
    {L₁ : Set StmtIn} {L₂ : Set StmtOut} {ε : ℝ≥0}
    (h : ∀ s : σ, V.soundness (pure s) impl L₁ L₂ ε) :
    V.soundness init impl L₁ L₂ ε := by
  intro Aux Out wit P stmt hstmt
  dsimp only
  rw [OptionT.prEvent_eq_run]
  apply prEvent_bind_le_of_forall_le_of_support _ _ _
  intro s _
  simpa only [soundness, OptionT.prEvent_eq_run, pure_bind, OptionT.run_mk] using
    h s Aux Out wit P stmt hstmt

/-- Express ordinary soundness directly at the prover/verifier boundary, retaining the shared
oracle state and treating rejection as an absent output. -/
theorem soundness_iff_run {V : Verifier oSpec StmtIn StmtOut pSpec}
    {L₁ : Set StmtIn} {L₂ : Set StmtOut} {ε : ℝ≥0} :
    V.soundness init impl L₁ L₂ ε ↔
    ∀ (Aux Out : Type) (wit : Aux) (P : Prover oSpec StmtIn Aux StmtOut Out pSpec)
      (stmt : StmtIn), stmt ∉ L₁ →
      Pr{let v ← (do
        let z ← (do
          let s ← init
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (P.run stmt wit)).run s)
        (simulateQ impl (V.run stmt z.1.1)).run z.2)}[
          v.1.elim False (fun v => v ∈ L₂)] ≤ ε := by
  unfold soundness
  apply forall_congr'; intro Aux
  apply forall_congr'; intro Out
  apply forall_congr'; intro wit
  apply forall_congr'; intro P
  apply forall_congr'; intro stmt
  apply forall_congr'; intro _
  apply Iff.of_eq
  apply congrArg (fun r : ENNReal => r ≤ (ε : ENNReal))
  rw [OptionT.prEvent_eq_run]
  simp only [StateT.run'_eq, Reduction.run_run_eq_bind, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, QueryImpl.addLift_def,
    liftComp_eq_liftM, QueryImpl.simulateQ_add_liftM_left, QueryImpl.liftTarget_self,
    bind_assoc]
  apply prEvent_bind_congr
  intro s
  rw [prEvent_map]
  apply prEvent_bind_congr
  intro z
  rw [bind_pure_comp, prEvent_map]
  apply prEvent_congr
  intro v
  cases v.1 <;> rfl

/-- For a guarded verifier, ordinary soundness is precisely a bound on its deterministic
accepted transcript event in the actual prover execution. -/
theorem GuardedForm.soundness_iff {V : Verifier oSpec StmtIn StmtOut pSpec}
    (G : V.GuardedForm) {L₁ : Set StmtIn} {L₂ : Set StmtOut} {ε : ℝ≥0} :
    V.soundness init impl L₁ L₂ ε ↔
    ∀ (Aux Out : Type) (wit : Aux) (P : Prover oSpec StmtIn Aux StmtOut Out pSpec)
      (stmt : StmtIn), stmt ∉ L₁ →
      Pr{let z ← (do
          let s ← init
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (P.run stmt wit)).run s)}[
          G.check stmt z.1.1 = true ∧ G.out stmt z.1.1 ∈ L₂] ≤ ε := by
  rw [soundness_iff_run]
  apply forall_congr'; intro Aux
  apply forall_congr'; intro Out
  apply forall_congr'; intro wit
  apply forall_congr'; intro P
  apply forall_congr'; intro stmt
  apply forall_congr'; intro _
  apply Iff.of_eq
  apply congrArg (fun r : ENNReal => r ≤ (ε : ENNReal))
  simp only [G.run_state, bind_pure_comp, prEvent_map]
  apply prEvent_congr
  intro z
  cases G.check stmt z.1.1 <;> simp

end Verifier
