/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Interpolation
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.InterpolationParams

/-!
# Acceptance cases for affine interpolation

The numerical cases check the parameter choice and the full-constraint sufficient condition.
The free-budget example distinguishes that condition from (4.5) in [CWYZ26].
Further cases give a positive `Z`-degree and show that it needs `A ≤ n`.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

open ReedSolomon

/-- The standing hypotheses hold at `d = 16`, `n = 100`, `η = 1/2`, where `√ρ = 2/5`. -/
private theorem affineParams_16_100 : AffineParams 16 100 (1 / 2) := by
  have hsqrt : √((16 : ℕ) / ((100 : ℕ) : ℝ)) = 2 / 5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
    norm_num
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [hsqrt]; norm_num
  · norm_num

/-- The parameters feed the interpolation: an interpolant exists at those budgets. -/
example {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι] (domain : ι ↪ F)
    (f g : ι → F) {d : ℕ} {η : ℝ} (h : AffineParams d (Fintype.card ι) η) :
    ∃ Q, IsAffineInterpolant domain f g d (affineThreshold d (Fintype.card ι) η)
      (affineMultiplicity η) (affineYZBudget d (Fintype.card ι) η)
      (affineRootBudget d (Fintype.card ι) η) Q :=
  exists_isAffineInterpolant domain f g h.surplus

/-- An explicit parameter choice has these exact finite budgets. -/
private theorem budgets_16_100 :
    affineMultiplicity (1 / 2) = 4 ∧ affineYZBudget 16 100 (1 / 2) = 42 ∧
    affineThreshold 16 100 (1 / 2) = 90 ∧ affinePersistenceThreshold 16 100 (1 / 2) = 64 ∧
    affineRootBudget 16 100 (1 / 2) = 19 := by
  have hsqrt : √((16 : ℝ) / 100) = 2 / 5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
    norm_num
  have hceil : ⌈(675 : ℝ) / 16⌉₊ = 43 := by
    apply (Nat.ceil_eq_iff (by norm_num)).mpr
    norm_num
  unfold affineRootBudget affineYZBudget affineThreshold affinePersistenceThreshold
  norm_num only [Nat.cast_ofNat]
  have hsqrt' : √((4 : ℝ) / 25) = 2 / 5 := by
    convert hsqrt using 2; norm_num
  rw [hsqrt']
  norm_num [affineMultiplicity, hceil]

-- The 146 unknowns exceed the truncated count 145, but not the full constraint count 150.
open Polynomial.SymbolicInterpolation in
example : (monomialSupport 1 (4 * 5 - 3) (2 + 1) (3 + 1)).card = 146 ∧
    5 * (constraintSupport 4 (3 + 1)).card = 150 ∧
    5 * (∑ s ∈ Finset.range (min (4 - 1) 2 + 1), (4 - s) * (3 + 1 - s)) = 145 := by
  norm_num [card_monomialSupport, card_constraintSupport, Finset.sum_range_succ]

/-- The parameters also give an interpolant with positive `Z`-degree, since `A ≤ n`. -/
example {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι] (domain : ι ↪ F)
    (f g : ι → F) {d : ℕ} {η : ℝ} (h : AffineParams d (Fintype.card ι) η) :
    ∃ Q, IsAffineInterpolant domain f g d (affineThreshold d (Fintype.card ι) η)
      (affineMultiplicity η) (affineYZBudget d (Fintype.card ι) η)
      (affineRootBudget d (Fintype.card ι) η) Q ∧ 0 < Q.degreeOf none :=
  exists_isAffineInterpolant_degreeOf_pos domain f g h.threshold_le h.surplus

-- At `d = 16`, `n = 100`, `η = 1/2`, some interpolant has `Z`-degree between `1` and `19`.
example {F : Type*} [Field F] [DecidableEq F] (domain : Fin 100 ↪ F) (f g : Fin 100 → F) :
    ∃ Q, IsAffineInterpolant domain f g 16 90 4 42 19 Q ∧
      1 ≤ Q.degreeOf none ∧ Q.degreeOf none ≤ 19 := by
  have h : AffineParams 16 (Fintype.card (Fin 100)) (1 / 2) := by
    rw [Fintype.card_fin]
    exact affineParams_16_100
  obtain ⟨hm, hD, hA, -, hM⟩ := budgets_16_100
  obtain ⟨Q, hQ, hpos⟩ :=
    exists_isAffineInterpolant_degreeOf_pos domain f g h.threshold_le h.surplus
  rw [Fintype.card_fin, hm, hD, hA, hM] at hQ
  exact ⟨Q, hQ, hpos, hQ.rootDegree_le⟩

-- The bound `A ≤ n` is needed: an empty domain meets the surplus condition at `M = 0`,
-- while `M = 0` caps the `Z`-degree at zero.
open Polynomial.SymbolicInterpolation in
example {F : Type*} [Field F] [DecidableEq F] (domain : Empty ↪ F) (f g : Empty → F) :
    Fintype.card Empty * (constraintSupport 1 (0 + 1)).card <
      (monomialSupport 0 (1 * 1 - 0) (0 + 1) (0 + 1)).card ∧
    ¬ ∃ Q, IsAffineInterpolant domain f g 0 1 1 0 0 Q ∧ 0 < Q.degreeOf none := by
  refine ⟨by norm_num [card_monomialSupport], fun ⟨Q, hQ, hpos⟩ ↦ ?_⟩
  have := hQ.rootDegree_le
  omega

/-- info: 'ReedSolomon.exists_isAffineInterpolant_degreeOf_pos' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_isAffineInterpolant_degreeOf_pos
