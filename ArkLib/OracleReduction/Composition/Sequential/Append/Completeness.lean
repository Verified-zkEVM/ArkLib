/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Goodman, ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.Append.Simulation

/-!
# Completeness of sequential composition under explicit state assumptions

A pure verifier can be evaluated after the prover without changing the shared oracle state.
Exact simulated prover factorization and suffix completeness from every shared state give an
additive bound on the composition error. The structural seam and purity corollaries supply
sufficient execution hypotheses.

## References

* [Richard Goodman, completeness](https://github.com/Verified-zkEVM/ArkLib/pull/635).
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- A reduction with a deterministic, non-failing verifier runs its prover and evaluates the
verdict on the resulting transcript. -/
theorem run_eq_of_pure_verifier
    (R : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (V : R.verifier.PureForm) (stmt : Stmt₁) (wit : Wit₁) :
    (R.run stmt wit).run = (R.prover.run stmt wit >>= fun r =>
      pure (some (r, V.verify stmt r.1))) := by
  unfold Reduction.run
  simp only [OptionT.run_bind, Option.elimM]
  rw [show ((liftM (R.prover.run stmt wit) : OptionT (OracleComp _) _)).run =
    R.prover.run stmt wit >>= fun r => pure (some r) from rfl]
  rw [bind_assoc]
  refine bind_congr fun r => ?_
  rw [pure_bind]
  simp only [Option.elim_some, Verifier.run, V.verify_eq]
  rfl

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  [∀ i, SampleableType (pSpec₁.Challenge i)]

/-- For a pure verifier, completeness is an event about the prover's result and the verifier's
verdict; the final shared oracle state is retained in the computation. -/
theorem completeness_iff_of_pure_verifier
    (R : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (V : R.verifier.PureForm)
    (rel₁ : Set (Stmt₁ × Wit₁)) (rel₂ : Set (Stmt₂ × Wit₂)) (ε : ℝ≥0) :
    R.completeness init impl rel₁ rel₂ ε ↔
      ∀ stmt wit, (stmt, wit) ∈ rel₁ →
        1 - (ε : ℝ≥0∞) ≤ Pr[fun q =>
          (V.verify stmt q.1.1, q.1.2.2) ∈ rel₂ ∧ q.1.2.1 = V.verify stmt q.1.1 | do
          (simulateQ (QueryImpl.addLift impl challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (R.prover.run stmt wit)).run (← init)] := by
  unfold completeness
  simp only [run_eq_of_pure_verifier R V]
  have hrun (stmt : Stmt₁) (wit : Wit₁) :
      (OptionT.mk do
        (simulateQ (QueryImpl.addLift impl challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (R.prover.run stmt wit >>= fun r => pure (some (r, V.verify stmt r.1)))).run'
            (← init)) =
      (liftM ((fun q => (q.1, V.verify stmt q.1.1)) <$> (do
        (simulateQ (QueryImpl.addLift impl challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (R.prover.run stmt wit)).run (← init))) : OptionT ProbComp _) := by
    apply OptionT.ext
    simp [StateT.run'_eq]
  simp only [hrun, OptionT.probEvent_liftM, probEvent_map, Function.comp_def]

/-- Completeness from every deterministic oracle state implies completeness from any initial
state distribution. The verifier is pure, so initialization is the only outer mixture. -/
theorem completeness_of_pure_states
    (R : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (V : R.verifier.PureForm)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {ε : ℝ≥0}
    (h : ∀ s : σ, R.completeness (pure s) impl rel₁ rel₂ ε) :
    R.completeness init impl rel₁ rel₂ ε := by
  rw [completeness_iff_of_pure_verifier R V]
  intro stmt wit hRel
  have hstate (s : σ) :=
    (completeness_iff_of_pure_verifier R V rel₁ rel₂ ε).mp (h s) stmt wit hRel
  have hbound := mul_le_probEvent_bind (p := fun _ : σ => True)
    (r := 1) (r' := 1 - (ε : ℝ≥0∞)) (mx := init)
    (by simp) (fun s _ _ => by simpa only [pure_bind] using hstate s)
  simpa only [one_mul] using hbound

variable [∀ i, SampleableType (pSpec₂.Challenge i)]

/-- Quantitative completeness from equality of simulated prover programs at every input
and initial shared state. The suffix is complete from every deterministic state. -/
theorem append_completeness_of_prover_factorization
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (V₁ : R₁.verifier.PureForm) (V₂ : R₂.verifier.PureForm)
    (hFactor : R₁.prover.SimulatedAppendFactorization R₂.prover impl)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
    {rel₃ : Set (Stmt₃ × Wit₃)} {ε₁ ε₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ ε₁)
    (h₂ : ∀ s : σ, R₂.completeness (pure s) impl rel₂ rel₃ ε₂) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (ε₁ + ε₂) := by
  let VA : (R₁.append R₂).verifier.PureForm := {
    verify := fun stmt tr => V₂.verify (V₁.verify stmt tr.fst) tr.snd
    verify_eq := fun stmt tr => by
      change (do
        let stmt₂ ← R₁.verifier.verify stmt tr.fst
        R₂.verifier.verify stmt₂ tr.snd) = _
      rw [V₁.verify_eq, pure_bind, V₂.verify_eq] }
  rw [completeness_iff_of_pure_verifier R₁ V₁] at h₁
  rw [completeness_iff_of_pure_verifier _ VA]
  intro stmt wit hRel
  have hfirst := h₁ stmt wit hRel
  have hsecond (s : σ) :=
    (completeness_iff_of_pure_verifier R₂ V₂ rel₂ rel₃ ε₂).mp (h₂ s)
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
    rw [hGood.2]
    exact hGood.1)
  rw [bind_pure_comp]
  simpa only [pure_bind, probEvent_map, Function.comp_def, VA,
    FullTranscript.append_fst, FullTranscript.append_snd, ← hGood.2] using hnext

/-- Sequential composition preserves completeness for pure verifiers when the prover execution
factors at the seam and stage two is complete from every shared oracle state. Its error is at most
the sum of the component errors. The seam condition permits effectful output when the second
protocol is empty or starts with a prover message. -/
theorem append_completeness_of_pure_verifiers
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (V₁ : R₁.verifier.PureForm) (V₂ : R₂.verifier.PureForm)
    (hSeam : ∀ hn : 0 < n,
      R₁.prover.OutputIsPure ∨ pSpec₂.dir ⟨0, hn⟩ = .P_to_V)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
    {rel₃ : Set (Stmt₃ × Wit₃)} {ε₁ ε₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ ε₁)
    (h₂ : ∀ s : σ, R₂.completeness (pure s) impl rel₂ rel₃ ε₂) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (ε₁ + ε₂) :=
  append_completeness_of_prover_factorization R₁ R₂ V₁ V₂
    (Prover.simulatedAppendFactorization_of_seam R₁.prover R₂.prover hSeam impl) h₁ h₂

/-- Pure verifiers compose perfectly when prover execution factors at the seam and the suffix
is perfectly complete from every deterministic shared state. -/
theorem append_perfectCompleteness_of_pure_verifiers
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (V₁ : R₁.verifier.PureForm) (V₂ : R₂.verifier.PureForm)
    (hSeam : ∀ hn : 0 < n,
      R₁.prover.OutputIsPure ∨ pSpec₂.dir ⟨0, hn⟩ = .P_to_V)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
    {rel₃ : Set (Stmt₃ × Wit₃)}
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : ∀ s : σ, R₂.perfectCompleteness (pure s) impl rel₂ rel₃) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  simpa only [perfectCompleteness, add_zero] using
    append_completeness_of_pure_verifiers R₁ R₂ V₁ V₂ hSeam h₁ h₂

/-- Typeclass convenience form of append completeness for pure verifier verdicts and pure
left prover output. Oracle queries in prover messages are permitted. -/
theorem append_completeness_of_pure
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    [R₁.prover.OutputIsPure] [R₁.verifier.IsPure] [R₂.verifier.IsPure]
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
    {rel₃ : Set (Stmt₃ × Wit₃)} {ε₁ ε₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ ε₁)
    (h₂ : ∀ s : σ, R₂.completeness (pure s) impl rel₂ rel₃ ε₂) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (ε₁ + ε₂) := by
  obtain ⟨f₁, hf₁⟩ := Verifier.IsPure.is_pure (V := R₁.verifier)
  obtain ⟨f₂, hf₂⟩ := Verifier.IsPure.is_pure (V := R₂.verifier)
  exact append_completeness_of_pure_verifiers R₁ R₂ ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩
    (fun _ => Or.inl inferInstance) h₁ h₂

/-- Pure verifiers and pure left prover output preserve perfect completeness when the suffix
is perfectly complete from every deterministic shared state. -/
theorem append_perfectCompleteness_of_pure
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    [R₁.prover.OutputIsPure] [R₁.verifier.IsPure] [R₂.verifier.IsPure]
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
    {rel₃ : Set (Stmt₃ × Wit₃)}
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : ∀ s : σ, R₂.perfectCompleteness (pure s) impl rel₂ rel₃) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  simpa only [perfectCompleteness, add_zero] using
    append_completeness_of_pure R₁ R₂ h₁ h₂

/-- Exact simulated prover factorization preserves perfect completeness for pure verifiers
when the suffix is perfectly complete from every initial-state distribution. -/
theorem append_perfectCompleteness_of_prover_factorization
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (V₁ : R₁.verifier.PureForm) (V₂ : R₂.verifier.PureForm)
    (hFactor : R₁.prover.SimulatedAppendFactorization R₂.prover impl)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
    {rel₃ : Set (Stmt₃ × Wit₃)}
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : ∀ start : ProbComp σ, R₂.perfectCompleteness start impl rel₂ rel₃) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  simpa only [perfectCompleteness, add_zero] using
    append_completeness_of_prover_factorization R₁ R₂ V₁ V₂ hFactor h₁
      (fun s => h₂ (pure s))

end Reduction

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type}
  {ι₁ ι₂ ι₃ : Type} {OStmt₁ : ι₁ → Type} {OStmt₂ : ι₂ → Type} {OStmt₃ : ι₃ → Type}
  [∀ i, OracleInterface (OStmt₁ i)] [∀ i, OracleInterface (OStmt₂ i)]
  [∀ i, OracleInterface (OStmt₃ i)]
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec₁.Message i)] [∀ i, OracleInterface (pSpec₂.Message i)]
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
  {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
  {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- Oracle reductions inherit state-aware completeness through their proved execution
commutation with `toReduction`. Purity concerns the resulting ordinary verifier. -/
theorem append_completeness_of_pure_verifiers
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (V₁ : R₁.toReduction.verifier.PureForm) (V₂ : R₂.toReduction.verifier.PureForm)
    (hSeam : ∀ hn : 0 < n,
      R₁.prover.OutputIsPure ∨ pSpec₂.dir ⟨0, hn⟩ = .P_to_V)
    {ε₁ ε₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ ε₁)
    (h₂ : ∀ s : σ, R₂.completeness (pure s) impl rel₂ rel₃ ε₂) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (ε₁ + ε₂) := by
  unfold completeness
  rw [append_toReduction]
  exact Reduction.append_completeness_of_pure_verifiers
    R₁.toReduction R₂.toReduction V₁ V₂ hSeam h₁ h₂

/-- Perfect completeness of appended oracle reductions under pure verdicts and state-aware
second-stage completeness. -/
theorem append_perfectCompleteness_of_pure_verifiers
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (V₁ : R₁.toReduction.verifier.PureForm) (V₂ : R₂.toReduction.verifier.PureForm)
    (hSeam : ∀ hn : 0 < n,
      R₁.prover.OutputIsPure ∨ pSpec₂.dir ⟨0, hn⟩ = .P_to_V)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : ∀ s : σ, R₂.perfectCompleteness (pure s) impl rel₂ rel₃) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  change (R₁.append R₂).completeness init impl rel₁ rel₃ 0
  simpa only [add_zero] using
    append_completeness_of_pure_verifiers R₁ R₂ V₁ V₂ hSeam h₁ h₂

end OracleReduction
