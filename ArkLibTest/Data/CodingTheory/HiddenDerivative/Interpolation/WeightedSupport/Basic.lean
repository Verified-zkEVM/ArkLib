/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Basic

/-!
# Acceptance cases for weighted-support spaces

These cases check eligibility of concrete monomials at the strict cutoff and at the higher-jet
budget, show that for `D = 0` the eligible set is infinite (so `0 < D` is needed for
`weightedSupportEligible_finite`), compute the dimensions `0` and `1` of two small weighted support
spaces, and derive the source's `Field`-valued decoder bounds and its
`exactInterpolationMonomialWeight_lt_of_weightedSupportEligible`.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-! ### Eligibility of concrete monomials -/

/-- `Y₀` has coarse weight `0 + 2 * 1 = 2`, which is below the cutoff `3`. -/
example : WeightedSupportEligible 2 1 0 3 (Finsupp.single (some 0) 1) := by
  simp [WeightedSupportEligible, fullHigherJetWeight, Finsupp.weight_single, jetHigherWeight,
    totalJetDegree_eq_sum]
  norm_num

/-- The cutoff is strict: `Y₀` has coarse weight `2` and is not eligible at `L = 2`. -/
example : ¬ WeightedSupportEligible 2 1 0 2 (Finsupp.single (some 0) 1) := by
  simp [WeightedSupportEligible, totalJetDegree_eq_sum]

/-- For `d = 2`, `Y₂` has higher-jet weight `1`, so it is not eligible for the budget `W = 0`
however large the cutoff. -/
example : ¬ WeightedSupportEligible 1 2 0 100 (Finsupp.single (some 2) 1) := by
  simp [WeightedSupportEligible, fullHigherJetWeight, Finsupp.weight_single, jetHigherWeight]

/-! ### `0 < D` is needed for finiteness -/

/-- For `D = 0` every power of `Y₀` is eligible at `W = 0`, `L = 1`, so the eligible set is
infinite. -/
example : {u : JetVariable 1 →₀ ℕ | WeightedSupportEligible 0 1 0 1 u}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (Finsupp.single (some 0) k : JetVariable 1 →₀ ℕ))
    (fun a b h => by simpa using congrArg (fun u => u (some 0)) h) fun k => ?_
  simp [WeightedSupportEligible, fullHigherJetWeight, Finsupp.weight_single, jetHigherWeight]

/-! ### Small dimensions -/

/-- At the cutoff `L = 0` no exponent is eligible, so the space has dimension `0`. -/
example : Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 0 one_pos) = 0 := by
  rw [finrank_weightedSupportSpace_eq_card, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro u hu
  have h := (mem_weightedSupportExponents.mp hu).2
  have : (0 : ℝ) ≤ ((u none + 1 * totalJetDegree u : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

/-- At `D = 1`, `L = 1` only the constant monomial is eligible: its coarse weight
`u X + totalJetDegree u` is the degree of `u`. -/
example : Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 1 one_pos) = 1 := by
  rw [finrank_weightedSupportSpace_eq_card, Finset.card_eq_one]
  refine ⟨0, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun u hu => ?_⟩⟩
  · simp [WeightedSupportEligible, fullHigherJetWeight, totalJetDegree_eq_sum]
  · have h := (mem_weightedSupportExponents.mp hu).2
    have hlt : u none + 1 * totalJetDegree u < 1 := by exact_mod_cast h
    have hdeg : u.degree = 0 := by rw [degree_eq_add_totalJetDegree]; omega
    exact (Finsupp.degree_eq_zero_iff u).mp hdeg

/-! ### Source-shaped statements -/

/-- The source's `exactInterpolationMonomialWeight_lt_of_weightedSupportEligible`, whose
`exactInterpolationMonomialWeight D u` is the specialization weight
`Finsupp.weight (differentialWeight D) u`. -/
example {D d W B : ℕ} {L : ℝ} (hL : L ≤ B) {u : JetVariable d →₀ ℕ}
    (hu : WeightedSupportEligible D d W L u) :
    Finsupp.weight (differentialWeight D) u < B :=
  weight_differentialWeight_lt_of_weightedSupportEligible hL hu

/-- The source's `decoder_bounds_of_mem_weightedSupportSpace`, stated over a field. -/
example {F : Type*} [Field F] {D d W m A : ℕ} {L : ℝ} {hD : 0 < D} (hm : 0 < m) (hA : 0 < A)
    (hjet : L ≤ (D : ℝ) * (2 * m)) (hweight : L ≤ (m * A : ℕ))
    {Q : DifferentialPolynomial F d} (hQ : Q ∈ weightedSupportSpace F D d W L hD) :
    jetTotalDegree Q < 2 * m ∧ differentialWeightedDegree D Q < m * A :=
  decoder_bounds_of_mem_weightedSupportSpace hm hA hjet hweight hQ

/-- A concrete decoder bound: at `D = 2`, `L = 4 = D * (2 * 1)`, every member of the weighted
support space has total jet degree below `2`. -/
example {Q : DifferentialPolynomial ℚ 1} (hQ : Q ∈ weightedSupportSpace ℚ 2 1 0 4 two_pos) :
    jetTotalDegree Q < 2 :=
  jetTotalDegree_lt_of_mem_weightedSupportSpace (t := 1 * 2) two_pos (by norm_num) hQ
