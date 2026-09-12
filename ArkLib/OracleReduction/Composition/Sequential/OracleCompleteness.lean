/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.GuardedNary

/-!
# Guarded completeness for sequential oracle reductions

Oracle reductions use the proved execution commutation with their ordinary reductions. All
suffix correctness premises refer to the actual shared state passed by the preceding component.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type}
  {ι₁ ι₂ ι₃ : Type} {OStmt₁ : ι₁ → Type} {OStmt₂ : ι₂ → Type} {OStmt₃ : ι₃ → Type}
  [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)] [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec₁.Message i)] [∀ i, OracleInterface (pSpec₂.Message i)]
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
  {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
  {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- Oracle reductions with guarded ordinary verifiers compose with the sum of their errors
when prover execution factors at the seam and the suffix is complete from every shared state. -/
theorem append_completeness_of_guarded_verifiers
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (V₁ : R₁.toReduction.verifier.GuardedForm) (V₂ : R₂.toReduction.verifier.GuardedForm)
    (hSeam : ∀ hn : 0 < n,
      R₁.prover.OutputIsPure ∨ pSpec₂.dir ⟨0, hn⟩ = .P_to_V)
    {ε₁ ε₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ ε₁)
    (h₂ : ∀ s : σ, R₂.completeness (pure s) impl rel₂ rel₃ ε₂) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (ε₁ + ε₂) := by
  unfold completeness
  rw [append_toReduction]
  exact Reduction.append_completeness_of_guarded_verifiers
    R₁.toReduction R₂.toReduction V₁ V₂ hSeam h₁ h₂

/-- Oracle reductions with guarded ordinary verifiers compose perfectly when prover execution
factors at the seam and the suffix is perfectly complete from every shared state. -/
theorem append_perfectCompleteness_of_guarded_verifiers
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (V₁ : R₁.toReduction.verifier.GuardedForm) (V₂ : R₂.toReduction.verifier.GuardedForm)
    (hSeam : ∀ hn : 0 < n,
      R₁.prover.OutputIsPure ∨ pSpec₂.dir ⟨0, hn⟩ = .P_to_V)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : ∀ s : σ, R₂.perfectCompleteness (pure s) impl rel₂ rel₃) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  change (R₁.append R₂).completeness init impl rel₁ rel₃ 0
  simpa only [add_zero] using
    append_completeness_of_guarded_verifiers R₁ R₂ V₁ V₂ hSeam h₁ h₂

end OracleReduction

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- Pure prover outputs and guarded ordinary verifiers compose with the sum of the component
errors when every oracle reduction is complete from every deterministic shared state. -/
theorem seqCompose_completeness_of_guarded_verifiers
    {m : ℕ} (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    (Wit : Fin (m + 1) → Type)
    [∀ i j, OracleInterface (OStmt i j)]
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, OracleInterface ((pSpec i).Message j)]
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : (i : Fin (m + 1)) → Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (R : ∀ i, OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i))
    (ε : Fin m → ℝ≥0)
    (hP : ∀ i, (R i).prover.OutputIsPure)
    (hV : ∀ i, (R i).toReduction.verifier.GuardedForm)
    (h : ∀ i s, (R i).completeness (pure s) impl (rel i.castSucc) (rel i.succ) (ε i)) :
    (seqCompose Stmt OStmt Wit R).completeness init impl (rel 0) (rel (Fin.last m))
      (∑ i, ε i) := by
  unfold completeness
  rw [seqCompose_toReduction]
  exact Reduction.seqCompose_completeness_of_guarded_verifiers
    (fun i => Stmt i × ∀ j, OStmt i j) Wit init impl rel
    (fun i => (R i).toReduction) ε hP hV h

/-- Pure prover outputs and guarded ordinary verifiers preserve perfect completeness of a finite
oracle-reduction chain when every component is perfectly complete from every shared state. -/
theorem seqCompose_perfectCompleteness_of_guarded_verifiers
    {m : ℕ} (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    (Wit : Fin (m + 1) → Type)
    [∀ i j, OracleInterface (OStmt i j)]
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, OracleInterface ((pSpec i).Message j)]
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : (i : Fin (m + 1)) → Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (R : ∀ i, OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i))
    (hP : ∀ i, (R i).prover.OutputIsPure)
    (hV : ∀ i, (R i).toReduction.verifier.GuardedForm)
    (h : ∀ i s, (R i).perfectCompleteness (pure s) impl (rel i.castSucc) (rel i.succ)) :
    (seqCompose Stmt OStmt Wit R).perfectCompleteness init impl (rel 0) (rel (Fin.last m)) := by
  change (seqCompose Stmt OStmt Wit R).completeness init impl (rel 0) (rel (Fin.last m)) 0
  simpa only [Finset.sum_const_zero] using
    seqCompose_completeness_of_guarded_verifiers Stmt OStmt Wit init impl rel R
      (fun _ => 0) hP hV h

end OracleReduction
