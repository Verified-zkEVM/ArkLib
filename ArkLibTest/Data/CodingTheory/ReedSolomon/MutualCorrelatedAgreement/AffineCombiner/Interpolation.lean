/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Interpolation
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.InterpolationParams
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

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
  exists_isAffineInterpolant_degreeOf_none_pos domain f g h.threshold_le h.surplus

/-- At `d = 16`, `n = 100`, `η = 1/2`, some interpolant has `Z`-degree in `[1, 19]`. -/
private theorem exists_interpolant_16_100 {F : Type*} [Field F] [DecidableEq F]
    (domain : Fin 100 ↪ F) (f g : Fin 100 → F) :
    ∃ Q, IsAffineInterpolant domain f g 16 90 4 42 19 Q ∧
      1 ≤ Q.degreeOf none ∧ Q.degreeOf none ≤ 19 := by
  have h : AffineParams 16 (Fintype.card (Fin 100)) (1 / 2) := by
    rw [Fintype.card_fin]
    exact affineParams_16_100
  obtain ⟨hm, hD, hA, -, hM⟩ := budgets_16_100
  obtain ⟨Q, hQ, hpos⟩ :=
    exists_isAffineInterpolant_degreeOf_none_pos domain f g h.threshold_le h.surplus
  rw [Fintype.card_fin, hm, hD, hA, hM] at hQ
  exact ⟨Q, hQ, hpos, hQ.rootDegree_le⟩

private instance : Fact (Nat.Prime 101) := ⟨by norm_num⟩

/-- The points `0, …, 99` of `F₁₀₁` as the evaluation domain. -/
private def domain100 : Fin 100 ↪ ZMod 101 :=
  ⟨fun i ↦ (i : ℕ), fun i j h ↦ Fin.ext (by
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at this)⟩

-- Over `F₁₀₁` with `n = 100` points, every word pair has such an interpolant.
example (f g : Fin 100 → ZMod 101) :
    ∃ Q, IsAffineInterpolant domain100 f g 16 90 4 42 19 Q ∧
      1 ≤ Q.degreeOf none ∧ Q.degreeOf none ≤ 19 :=
  exists_interpolant_16_100 domain100 f g

-- The `m`-th power factor holds over `ℤ`, outside polynomial targets:
-- with `Z ↦ 2` and `X ↦ 6`, the monomial `Z X` evaluates to a multiple of `2²`.
example : (2 : ℤ) ^ 2 ∣ MvPolynomial.aeval (fun w : AffineVar ↦ w.elim (2 : ℤ) ![6, 1])
    (MvPolynomial.monomial (Finsupp.single none 1 + Finsupp.single (some 0) 1) (1 : ℤ)) :=
  pow_dvd_aeval_of_affineWeight_le (by simp) (by simp) fun e he ↦ by
    simp only [MvPolynomial.support_monomial, one_ne_zero, ite_false, Finset.mem_singleton] at he
    subst he
    simp

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

/-- info: 'ReedSolomon.exists_isAffineInterpolant_degreeOf_none_pos' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_isAffineInterpolant_degreeOf_none_pos

/-- info: 'ReedSolomon.pow_dvd_aeval_of_affineWeight_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.pow_dvd_aeval_of_affineWeight_le
