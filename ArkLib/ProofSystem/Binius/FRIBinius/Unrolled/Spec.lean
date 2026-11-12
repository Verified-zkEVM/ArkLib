/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Binius.FRIBinius.Prelude
public import ArkLib.ProofSystem.RingSwitching.Packing.TensorPrefix
public import ArkLib.ProofSystem.Binius.BinaryBasefold.ProductClaim

/-!
# Unrolled FRI-Binius: communication and error budget

The tensor batching head is followed by the Binary Basefold opening of its product claim, whose
sum-check-and-fold loop runs the ring-switching product sum-check itself. No separate
ring-switching sum-check precedes it.

`fullError` assigns the batching loss to the head's challenge and the opening's errors
(`ProductClaim.openingError`) to the remaining challenges. `fullError_sum_le_concrete` bounds
its sum by `concreteError`, `(κ + 2ℓ')/|L| + 2^(ℓ' + R)/|L| + (1/2 + 1/(2 · 2^R))^γ`.
`concreteError_add_eq` shows that this is the separate-sum-check bound of
`FRIBinius.RingSwitch.fullError_sum_le` minus one sum-check term `2ℓ'/|L|`. These are bounds on
challenge-error sums, not on running time.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over Binary
  Towers*][DP24], §5.2, equation (43).
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

/-- The batching head followed by the Binary Basefold opening wire. -/
noncomputable abbrev pSpec (γ : ℕ) :=
  TensorPrefix.headPSpec (biniusProfile κ L K β) ++ₚ
    ((!p[] : ProtocolSpec 0) ++ₚ BinaryBasefold.fullPSpec K β γ
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate))

/-- The batching loss on the head's challenge, then the errors of the Binary Basefold opening. -/
noncomputable def fullError (γ : ℕ) :
    (pSpec κ K β (ϑ := ϑ) h_rate γ).ChallengeIdx → ℝ≥0 :=
  Sum.elim (fun _ => (κ : ℝ≥0) / Fintype.card L)
    (BinaryBasefold.ProductClaim.openingError K β γ (ϑ := ϑ) (h_rate := h_rate)) ∘
    ChallengeIdx.sumEquiv.symm

/-- The closed-form bound with one sum-check term `2ℓ'/|L|`. -/
noncomputable def concreteError (γ : ℕ) : ℝ≥0 :=
  ((κ : ℝ≥0) + 2 * ℓ') / Fintype.card L +
    (2 ^ (ℓ' + R) : ℝ≥0) / Fintype.card L +
    ((1 / 2 : ℝ≥0) + 1 / (2 * 2 ^ R)) ^ γ

omit [Field L] [DecidableEq L] [SampleableType L] [NeZero ℓ'] [NeZero R] in
/-- The closed-form bound is the batching loss plus the Binary Basefold bound. -/
theorem concreteError_eq (γ : ℕ) :
    concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ =
      (κ : ℝ≥0) / Fintype.card L +
        BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ' R γ := by
  simp only [concreteError, BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError,
    add_div]
  ring

omit [Field L] [DecidableEq L] [SampleableType L] [NeZero ℓ'] [NeZero R] in
/-- Adding one sum-check term `2ℓ'/|L|` to `concreteError` gives the bound of the composition
with a separate ring-switching sum-check (`FRIBinius.RingSwitch.fullError_sum_le`). -/
theorem concreteError_add_eq (γ : ℕ) :
    concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ + (ℓ' : ℝ≥0) * (2 / Fintype.card L) =
      (κ : ℝ≥0) / Fintype.card L + (ℓ' : ℝ≥0) * (2 / Fintype.card L) +
        BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ' R γ := by
  rw [concreteError_eq]
  ring

omit [DecidableEq K] [Fact (Fintype.card K = 2)] [NeZero R] in
/-- The challenge-error sum is the batching loss plus the opening's sum. -/
theorem fullError_sum (γ : ℕ) :
    (∑ i, fullError κ K β (ϑ := ϑ) h_rate γ i) =
      (κ : ℝ≥0) / Fintype.card L +
        ∑ i, BinaryBasefold.ProductClaim.openingError K β γ (ϑ := ϑ) (h_rate := h_rate) i := by
  unfold fullError
  refine (Equiv.sum_comp ChallengeIdx.sumEquiv.symm (Sum.elim _ _)).trans ?_
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
    Head.card_challengeIdx, one_smul]

omit [DecidableEq K] in
/-- The challenge-error sum is at most `concreteError`. -/
theorem fullError_sum_le_concrete (γ : ℕ) :
    (∑ i, fullError κ K β (ϑ := ϑ) h_rate γ i) ≤
      concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ := by
  rw [fullError_sum, concreteError_eq]
  exact add_le_add_right
    (BinaryBasefold.ProductClaim.openingError_sum_le_concrete K β γ
      (ϑ := ϑ) (h_rate := h_rate)) _

end Binius.FRIBinius.Unrolled
