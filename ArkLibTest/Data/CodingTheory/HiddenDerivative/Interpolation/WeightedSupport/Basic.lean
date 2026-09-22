/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Basic

/-!
# Weighted support acceptance tests

* The coarse cutoff is strict: at `D = 3`, the exponent of `X Y₀` has coarse weight `4`, so it is
  eligible for `L = 5` and not for `L = 4`.
* At `d = 0`, `D = 1`, `L = 1` only the constant monomial is eligible, so the space has
  dimension `1`.
* Finiteness needs `0 < D`: at `D = 0` every power of `Y₀` is eligible.
* The total-jet-degree bound at `D = 2`, `L = 5`, and the source's
  `decoder_bounds_of_mem_weightedSupportSpace`, derived from the two degree bounds.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- At `d = 2`, `D = 3`, `W = 0`, the exponent of `X Y₀` has coarse weight `1 + 3 = 4`: it is
eligible for the cutoff `5` and, since the cutoff is strict, not for the cutoff `4`. -/
example : WeightedSupportEligible 3 2 0 5 (Finsupp.single none 1 + Finsupp.single (some 0) 1) ∧
    ¬ WeightedSupportEligible 3 2 0 4 (Finsupp.single none 1 + Finsupp.single (some 0) 1) := by
  have hw :
      fullHigherJetWeight (d := 2) (Finsupp.single none 1 + Finsupp.single (some 0) 1) = 0 := by
    simp [fullHigherJetWeight, Finsupp.weight_single, jetHigherWeight]
  have ht : totalJetDegree (d := 2) (Finsupp.single none 1 + Finsupp.single (some 0) 1) = 1 := by
    simp [totalJetDegree, Finsupp.weight_single]
  simp only [WeightedSupportEligible, hw, ht]
  norm_num

/-- At `d = 0`, `D = 1`, `W = 0`, `L = 1`, the only eligible exponent is `0`. -/
private theorem weightedSupportEligible_one_iff (u : JetVariable 0 →₀ ℕ) :
    WeightedSupportEligible 1 0 0 1 u ↔ u = 0 := by
  have hw : fullHigherJetWeight u = 0 := by
    simp [fullHigherJetWeight, Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option,
      jetHigherWeight]
  have hdeg := degree_eq_add_totalJetDegree u
  simp only [WeightedSupportEligible, hw, le_refl, true_and, one_mul]
  norm_cast
  rw [Nat.lt_one_iff, ← hdeg, Finsupp.degree_eq_zero_iff]

/-- The weighted support space at `d = 0`, `D = 1`, `W = 0`, `L = 1` is spanned by `1`, so its
dimension is `1`. -/
example : Module.finrank ℚ (weightedSupportSpace ℚ 1 0 0 1) = 1 := by
  rw [finrank_weightedSupportSpace_eq_card Nat.one_pos]
  have : weightedSupportExponents 1 0 0 1 Nat.one_pos = {0} := by
    ext u
    simp [weightedSupportEligible_one_iff]
  simp [this]

/-- Finiteness needs `0 < D`: at `D = 0` and cutoff `1`, every power of `Y₀` is eligible. -/
example (d W : ℕ) : ¬ {u : JetVariable d →₀ ℕ | WeightedSupportEligible 0 d W 1 u}.Finite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => Finsupp.single (some 0) k)
    (fun a b h => by simpa using congrArg (fun u => u (some 0)) h) fun k => ?_
  refine ⟨?_, by simp⟩
  simp [fullHigherJetWeight, Finsupp.weight_single, jetHigherWeight]

/-- At `D = 2` and `L = 5`, an eligible exponent has total jet degree below `5 / 2`, hence at most
`2`. -/
example {d W : ℕ} {u : JetVariable d →₀ ℕ} (hu : WeightedSupportEligible 2 d W 5 u) :
    totalJetDegree u ≤ 2 := by
  have h := totalJetDegree_lt_of_weightedSupportEligible (by norm_num) hu
  have h' : (totalJetDegree u : ℝ) < 3 := h.trans (by norm_num)
  exact Nat.lt_succ_iff.mp (by exact_mod_cast h')

/-- Source shape (`decoder_bounds_of_mem_weightedSupportSpace`): with `0 < m`, `0 < A`,
`L ≤ D (2m)` and `L ≤ m A`, the total jet degree is below `2 m` and the differential weighted
degree is below `m A`. -/
example {F : Type*} [Field F] {D d W m A : ℕ} {L : ℝ} (hD : 0 < D) (hm : 0 < m) (hA : 0 < A)
    (hjet : L ≤ (D : ℝ) * (2 * m)) (hweight : L ≤ (m * A : ℕ)) {Q : DifferentialPolynomial F d}
    (hQ : Q ∈ weightedSupportSpace F D d W L) :
    jetTotalDegree Q < 2 * m ∧ differentialWeightedDegree D Q < m * A :=
  ⟨jetTotalDegree_lt_of_mem_weightedSupportSpace hD (by omega) (by exact_mod_cast hjet) hQ,
    differentialWeightedDegree_lt_of_mem_weightedSupportSpace (Nat.mul_pos hm hA) hweight hQ⟩
