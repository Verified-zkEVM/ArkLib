/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.FRIBinius.Prelude
public import ArkLib.ProofSystem.RingSwitching.Packing.TensorPrefix
public import ArkLib.ProofSystem.Binius.BinaryBasefold.General

/-!
# Fused FRI-Binius communication and error budget

The tensor batching head is followed by one interleaved sumcheck/folding loop and the repeated
query check. Unlike the unfused ring-switching composition, no standalone ring-switching
sumcheck precedes the folding loop. The empty frontier only reformats the head's output.

The error family records the batching error and the existing fold/query errors.
`fullVerifier_rbrKnowledgeSoundnessWorstCase` in `General.lean` certifies this family for
the fused verifier. The scalar bound here aggregates those component budgets arithmetically.
The wire types use the existing mathematical tensor profile; the real-valued budgets are
noncomputable mathematical quantities, not verifier computations.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over Binary
  Towers*][DP24]
-/

@[expose] public section

namespace Binius.FRIBinius.Unrolled

open OracleSpec OracleComp ProtocolSpec Module
open RingSwitching RingSwitching.Packing
open scoped NNReal

variable (κ : ℕ) {L : Type} [Field L] [Fintype L] [DecidableEq L] [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
  [Fact (Fintype.card K = 2)] [Algebra K L]
variable (β : Basis (Fin (2 ^ κ)) K L)
variable {ℓ' R ϑ : ℕ} [NeZero ℓ'] [NeZero R] [NeZero ϑ] [Fact (ϑ ∣ ℓ')]
variable (h_rate : ℓ' + R < 2 ^ κ)

/-- The original tensor-carrier message followed by the vector batching challenge. -/
noncomputable abbrev headSpec := Head.pSpec (M := (biniusProfile κ L K β).A)
  (PackingData.ofBasis (biniusProfile κ L K β).basis) (BatchingRule.eqFold L κ)

/-- Batching, a zero-message frontier, and one fold-and-query wire. -/
noncomputable abbrev pSpec (γ : ℕ) := headSpec κ K β ++ₚ
  ((!p[] : ProtocolSpec 0) ++ₚ BinaryBasefold.fullPSpec K β γ
    (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate))

/-- The batching error plus the existing per-challenge fold and query errors. -/
noncomputable def fullError (γ : ℕ) :
    (pSpec κ K β (ϑ := ϑ) h_rate γ).ChallengeIdx → ℝ≥0 :=
  Sum.elim (fun _ => (κ : ℝ≥0) / Fintype.card L)
    (Sum.elim (fun _ => 0)
      (BinaryBasefold.FullBinaryBasefold.fullRbrKnowledgeError K β γ
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)) ∘ ChallengeIdx.sumEquiv.symm) ∘
    ChallengeIdx.sumEquiv.symm

/-- The fused scalar budget contains only one sumcheck loss of `2ℓ'/|L|`. -/
noncomputable def concreteError (γ : ℕ) : ℝ≥0 :=
  ((κ : ℝ≥0) + 2 * ℓ') / Fintype.card L +
    (2 ^ (ℓ' + R) : ℝ≥0) / Fintype.card L +
    ((1 / 2 : ℝ≥0) + 1 / (2 * 2 ^ R)) ^ γ

omit [Field L] [DecidableEq L] [SampleableType L] [NeZero ℓ'] [NeZero R] in
/-- The closed-form fused budget is batching plus one Binary Basefold budget. -/
theorem concreteError_eq (γ : ℕ) :
    concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ =
      (κ : ℝ≥0) / Fintype.card L +
        BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ' R γ := by
  simp only [concreteError, BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError,
    add_div]
  ring

omit [DecidableEq K] [Fact (Fintype.card K = 2)] [NeZero R] in
/-- The empty frontier adds no error; the batching vector is one challenge message. -/
theorem fullError_sum (γ : ℕ) :
    (∑ i, fullError κ K β (ϑ := ϑ) h_rate γ i) =
      (κ : ℝ≥0) / Fintype.card L +
        ∑ i, BinaryBasefold.FullBinaryBasefold.fullRbrKnowledgeError K β γ
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) i := by
  classical
  have hcard : Fintype.card (headSpec κ K β).ChallengeIdx = 1 := by
    change Fintype.card
      (CoordinateWise.ScalarRound.pSpecScalar Unit Unit).ChallengeIdx = 1
    decide
  unfold fullError
  simp only [Function.comp_def]
  rw [Equiv.sum_comp ChallengeIdx.sumEquiv.symm, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [Equiv.sum_comp ChallengeIdx.sumEquiv.symm, Fintype.sum_sum_type]
  simp [hcard]

omit [DecidableEq K] in
/-- Aggregating the component budgets gives the fused, not the unfused, bound. -/
theorem fullError_sum_le_concrete (γ : ℕ) :
    (∑ i, fullError κ K β (ϑ := ϑ) h_rate γ i) ≤
      concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ := by
  rw [fullError_sum, concreteError_eq]
  exact add_le_add_right
    (BinaryBasefold.FullBinaryBasefold.fullRbrKnowledgeError_sum_le_concrete K β γ
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)) _

end Binius.FRIBinius.Unrolled
