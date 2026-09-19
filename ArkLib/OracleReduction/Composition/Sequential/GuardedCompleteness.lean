/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Goodman, ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded
public import ArkLib.OracleReduction.Composition.Sequential.Append.Completeness

/-!
# Completeness of sequential composition with rejecting deterministic verifiers

A guarded verifier checks its transcript and either returns a deterministic verdict or rejects.
These verifiers leave the shared oracle state unchanged. Composition requires the second
reduction to be complete from every shared state and the prover execution to factor at the seam.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

private theorem probEvent_guarded_map {α β : Type} (oa : ProbComp α)
    (check : α → Bool) (f : α → β) (p : β → Prop) :
    Pr[p | (do
      let a ← (liftM oa : OptionT ProbComp α)
      if check a then pure (f a) else failure)] =
      Pr[fun a => check a = true ∧ p (f a) | oa] := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro a
  by_cases hc : check a = true <;> simp [hc]

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- A guarded reduction runs its prover and then deterministically accepts or rejects the
resulting transcript. Rejected transcripts produce no reduction output. -/
theorem run_eq_of_guarded_verifier
    (R : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (G : R.verifier.GuardedForm) (stmt : Stmt₁) (wit : Wit₁) :
    (R.run stmt wit).run = (R.prover.run stmt wit >>= fun r =>
      pure (if G.check stmt r.1 then some (r, G.out stmt r.1) else none)) := by
  unfold Reduction.run
  simp only [OptionT.run_bind, Option.elimM]
  rw [show ((liftM (R.prover.run stmt wit) : OptionT (OracleComp _) _)).run =
    R.prover.run stmt wit >>= fun r => pure (some r) from rfl]
  rw [bind_assoc]
  refine bind_congr fun r => ?_
  rw [pure_bind]
  simp only [Option.elim_some, Verifier.run]
  rw [G.verify_eq stmt r.1]
  by_cases hc : G.check stmt r.1 = true <;> simp [hc]

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  [∀ i, SampleableType (pSpec₁.Challenge i)]

/-- For a guarded verifier, completeness requires its check to pass, its verdict and witness
to satisfy the output relation, and the prover's output statement to agree with that verdict. -/
theorem completeness_iff_of_guarded_verifier
    (R : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (G : R.verifier.GuardedForm)
    (rel₁ : Set (Stmt₁ × Wit₁)) (rel₂ : Set (Stmt₂ × Wit₂)) (ε : ℝ≥0) :
    R.completeness init impl rel₁ rel₂ ε ↔
      ∀ stmt wit, (stmt, wit) ∈ rel₁ →
        1 - (ε : ℝ≥0∞) ≤ Pr[fun q => G.check stmt q.1.1 = true ∧
          (G.out stmt q.1.1, q.1.2.2) ∈ rel₂ ∧ q.1.2.1 = G.out stmt q.1.1 | do
          (simulateQ (QueryImpl.addLift impl challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (R.prover.run stmt wit)).run (← init)] := by
  unfold completeness
  simp only [run_eq_of_guarded_verifier R G]
  have hrun (stmt : Stmt₁) (wit : Wit₁) :
      (OptionT.mk do
        (simulateQ (QueryImpl.addLift impl challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (R.prover.run stmt wit >>= fun r =>
            pure (if G.check stmt r.1 then some (r, G.out stmt r.1) else none))).run'
            (← init)) = (do
      let q ← (liftM (do
        (simulateQ (QueryImpl.addLift impl challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (R.prover.run stmt wit)).run (← init)) : OptionT ProbComp _)
      if G.check stmt q.1.1 then pure (q.1, G.out stmt q.1.1) else failure) := by
    apply OptionT.ext
    simp only [ChallengeIdx, Challenge, QueryImpl.addLift_def,
      PFunctor.Handler.liftTarget_self, bind_pure_comp, simulateQ_map, StateT.run'_eq,
      StateT.run_map, Functor.map_map, OptionT.mk_bind, OptionT.run_bind,
      OptionT.run_monadLift, monadLift_self, OptionT.run_mk, Option.elimM_map,
      Option.elim_some, liftM_bind, bind_assoc]
    simp only [map_eq_bind_pure_comp]
    refine bind_congr fun s => ?_
    refine bind_congr fun q => ?_
    by_cases hc : G.check stmt q.1.1 = true <;> simp [hc]
  simp only [hrun, probEvent_guarded_map]

/-- Completeness from every deterministic oracle state implies completeness from any initial
state distribution. The verifier is guarded, so initialization is the only outer mixture. -/
theorem completeness_of_guarded_states
    (R : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (V : R.verifier.GuardedForm)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {ε : ℝ≥0}
    (h : ∀ s : σ, R.completeness (pure s) impl rel₁ rel₂ ε) :
    R.completeness init impl rel₁ rel₂ ε := by
  rw [completeness_iff_of_guarded_verifier R V]
  intro stmt wit hRel
  have hstate (s : σ) :=
    (completeness_iff_of_guarded_verifier R V rel₁ rel₂ ε).mp (h s) stmt wit hRel
  have hbound := mul_le_probEvent_bind (p := fun _ : σ => True)
    (r := 1) (r' := 1 - (ε : ℝ≥0∞)) (mx := init)
    (by simp) (fun s _ _ => by simpa only [pure_bind] using hstate s)
  simpa only [one_mul] using hbound

variable [∀ i, SampleableType (pSpec₂.Challenge i)]

/-- Quantitative completeness from equality of simulated prover programs at every input
and initial shared state. The suffix is complete from every deterministic state. -/
theorem append_completeness_of_guarded_prover_factorization
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (V₁ : R₁.verifier.GuardedForm) (V₂ : R₂.verifier.GuardedForm)
    (hFactor : R₁.prover.SimulatedAppendFactorization R₂.prover impl)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
    {rel₃ : Set (Stmt₃ × Wit₃)} {ε₁ ε₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ ε₁)
    (h₂ : ∀ s : σ, R₂.completeness (pure s) impl rel₂ rel₃ ε₂) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (ε₁ + ε₂) := by
  let VA : (R₁.append R₂).verifier.GuardedForm := V₁.append V₂
  rw [completeness_iff_of_guarded_verifier R₁ V₁] at h₁
  rw [completeness_iff_of_guarded_verifier _ VA]
  intro stmt wit hRel
  have hfirst := h₁ stmt wit hRel
  have hsecond (s : σ) :=
    (completeness_iff_of_guarded_verifier R₂ V₂ rel₂ rel₃ ε₂).mp (h₂ s)
  have herr : 1 - ((ε₁ + ε₂ : ℝ≥0) : ℝ≥0∞) ≤
      (1 - (ε₁ : ℝ≥0∞)) * (1 - (ε₂ : ℝ≥0∞)) := by
    rw [ENNReal.coe_add, tsub_add_eq_tsub_tsub,
      ENNReal.mul_sub (by intros; finiteness), mul_one]
    exact tsub_le_tsub_left (mul_le_of_le_one_left zero_le tsub_le_self) _
  refine herr.trans ?_
  dsimp only [Reduction.append]
  simp only [hFactor stmt wit,
    StateT.run_bind, StateT.run_pure]
  rw [← bind_assoc]
  refine mul_le_probEvent_bind hfirst ?_
  intro q₁ _ hGood
  have hnext := hsecond q₁.2 q₁.1.2.1 q₁.1.2.2 (by
    rw [hGood.2.2]
    exact hGood.2.1)
  rw [bind_pure_comp]
  simpa only [pure_bind, probEvent_map, Function.comp_def, VA,
    Verifier.GuardedForm.append, FullTranscript.append_fst, FullTranscript.append_snd,
    hGood.1, Bool.true_and, ← hGood.2.2] using hnext

/-- Sequential composition preserves completeness for guarded verifiers when the prover execution
factors at the seam and stage two is complete from every shared oracle state. Its error is at most
the sum of the component errors. The seam condition permits effectful output when the second
protocol is empty or starts with a prover message. -/
theorem append_completeness_of_guarded_verifiers
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (V₁ : R₁.verifier.GuardedForm) (V₂ : R₂.verifier.GuardedForm)
    (hSeam : ∀ hn : 0 < n,
      R₁.prover.OutputIsPure ∨ pSpec₂.dir ⟨0, hn⟩ = .P_to_V)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
    {rel₃ : Set (Stmt₃ × Wit₃)} {ε₁ ε₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ ε₁)
    (h₂ : ∀ s : σ, R₂.completeness (pure s) impl rel₂ rel₃ ε₂) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (ε₁ + ε₂) :=
  append_completeness_of_guarded_prover_factorization R₁ R₂ V₁ V₂
    (Prover.simulatedAppendFactorization_of_seam R₁.prover R₂.prover hSeam impl) h₁ h₂

/-- Guarded verifiers compose perfectly when prover execution factors at the seam and the suffix
is perfectly complete from every deterministic shared state. -/
theorem append_perfectCompleteness_of_guarded_verifiers
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (V₁ : R₁.verifier.GuardedForm) (V₂ : R₂.verifier.GuardedForm)
    (hSeam : ∀ hn : 0 < n,
      R₁.prover.OutputIsPure ∨ pSpec₂.dir ⟨0, hn⟩ = .P_to_V)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
    {rel₃ : Set (Stmt₃ × Wit₃)}
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : ∀ s : σ, R₂.perfectCompleteness (pure s) impl rel₂ rel₃) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  simpa only [perfectCompleteness, add_zero] using
    append_completeness_of_guarded_verifiers R₁ R₂ V₁ V₂ hSeam h₁ h₂

end Reduction
