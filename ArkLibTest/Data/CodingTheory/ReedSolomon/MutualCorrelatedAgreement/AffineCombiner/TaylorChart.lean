/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.TaylorChart
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance cases for the Taylor chart of a linear multiplier family

A quadratic family `(1, X, X²)` over `𝔽₅` checks the reconstruction beyond affine lines.
The coefficient functional of `X` checks a cut other than an evaluation.
The family `(1, X)` checks that the Reed–Solomon multipliers are the lines `a + b X`.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

open ReedSolomon Polynomial

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

variable {K : Type*} [Field K]

/-- The quadratic family `(1, X, X²)`. -/
private noncomputable def quadraticFamily : Fin 3 → K[X] := ![1, X, X ^ 2]

/-- The regular equation `Z - Y`, whose root along a multiplier is the multiplier itself. -/
private noncomputable def regularR : MvPolynomial AffineVar K :=
  MvPolynomial.X none - MvPolynomial.X (some 1)

/-- The equation `Z² - Y`, of `(Y, Z)`-degree `2`. -/
private noncomputable def squareR : MvPolynomial AffineVar K :=
  MvPolynomial.X none ^ 2 - MvPolynomial.X (some 1)

private theorem pderiv_regularR : MvPolynomial.pderiv none (regularR (K := K)) = 1 := by
  simp [regularR]

/-- The multiplier of the quadratic family is `a₀ + a₁ X + a₂ X²`. -/
private theorem familyMultiplier_quadraticFamily (a : Fin 3 → K) :
    familyMultiplier quadraticFamily a = C (a 0) + C (a 1) * X + C (a 2) * X ^ 2 := by
  simp [familyMultiplier_apply, quadraticFamily, Fin.sum_univ_three]

/-- A quadratic multiplier `a₀ + a₁ X + a₂ X²` has degree at most `2`. -/
private theorem degree_familyMultiplier_quadraticFamily_le (a : Fin 3 → K) :
    (familyMultiplier quadraticFamily a).degree ≤ 2 := by
  rw [familyMultiplier_quadraticFamily]
  compute_degree!

/-- The root of `Z - Y` along `a₀ + a₁ X + a₂ X²` is the multiplier itself. -/
private theorem multiplierEval_regularR (a : Fin 3 → K) :
    multiplierEval (familyMultiplier quadraticFamily a)
      (expand K 1 (familyMultiplier quadraticFamily a)) regularR = 0 := by
  simp [regularR]

/-- The separant of `Z - Y` is `1` along every multiplier. -/
private theorem eval_multiplierEval_pderiv_regularR (L P : K[X]) (c : K) :
    (multiplierEval L P (MvPolynomial.pderiv none regularR)).eval c ≠ 0 := by
  simp [pderiv_regularR]

/-- The separant of `Z - Y` in the chart is the constant `1`. -/
private theorem chartSeparant_regularR (c : K) :
    chartSeparant c quadraticFamily (regularR (K := K)) = 1 := by
  rw [chartSeparant_eq, pderiv_regularR, map_one]

/-- The equation `Z - Y` has `(Y, Z)`-degree at most `1`. -/
private theorem weightedTotalDegree_regularR_le :
    (regularR (K := K)).weightedTotalDegree affineYZWeight ≤ 1 := by
  rw [regularR, ← MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
  exact Submodule.sub_mem _ (MvPolynomial.X_mem_restrictWeightedDegree _ 1 _ (by simp))
    (MvPolynomial.X_mem_restrictWeightedDegree _ 1 _ (by simp))

/-- The equation `Z² - Y` has `(Y, Z)`-degree at most `2`. -/
private theorem weightedTotalDegree_squareR_le :
    (squareR (K := K)).weightedTotalDegree affineYZWeight ≤ 2 := by
  rw [squareR, ← MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
  have hZ := MvPolynomial.pow_mem_restrictWeightedDegree
    (MvPolynomial.X_mem_restrictWeightedDegree (R := K) affineYZWeight 1 none (by simp)) 2
  exact Submodule.sub_mem _ (by simpa using hZ)
    (MvPolynomial.X_mem_restrictWeightedDegree _ 2 _ (by simp))

-- The reconstruction of degree `2` recovers the quadratic root `a₀ + a₁ X + a₂ X²` over `𝔽₅`
-- at every center and coefficient vector.
example (a : Fin 3 → ZMod 5) (c : ZMod 5) :
    chartPolynomial c quadraticFamily regularR 1 2
        (chartPoint c 1 a (familyMultiplier quadraticFamily a)) =
      familyMultiplier quadraticFamily a :=
  chartPolynomial_point c quadraticFamily regularR (p := 5) (r := 0) (by simp)
    (degree_familyMultiplier_quadraticFamily_le a) (multiplierEval_regularR a)
    (eval_multiplierEval_pderiv_regularR _ _ c)

-- Over `𝔽₂` with `s = 2`, the root `expand 2 P = a₀ + a₂ X²` of `Z - Y` along the multiplier
-- `a₀ + a₂ X²` is reconstructed as `P = a₀ + a₂ X` from its chart point.
example (a₀ a₂ c : ZMod 2) :
    chartPolynomial c quadraticFamily regularR 2 1
        (chartPoint c 2 ![a₀, 0, a₂] (C a₀ + C a₂ * X)) = C a₀ + C a₂ * X := by
  refine chartPolynomial_point c quadraticFamily regularR (p := 2) (r := 1) (by norm_num)
    ?_ ?_ (eval_multiplierEval_pderiv_regularR _ _ c)
  · compute_degree!
  · simp [regularR, familyMultiplier_quadraticFamily]

-- With `(Y, Z)`-degree `h = 2`, `τ = 3` and `l = 2`, the numerator has degree at most
-- `1 + τ (h - 1) = 1 + 3 · 1 = 4`.
example (c : ZMod 5) : (chartNumerator c quadraticFamily squareR 3 2).totalDegree ≤ 4 :=
  totalDegree_chartNumerator_le (h := 2) c quadraticFamily weightedTotalDegree_squareR_le
    (by norm_num)

-- The cut of the coefficient functional of `X`, with `s = 1`, `d = 2` and `τ = 3`, takes the
-- value `a₁` at the point of the quadratic root, since the separant is `1`.
example (a : Fin 3 → ZMod 5) (c : ZMod 5) :
    MvPolynomial.aeval (chartPoint c 1 a (familyMultiplier quadraticFamily a))
      (chartFunctionalCut c quadraticFamily regularR 1 2 3 (lcoeff (ZMod 5) 1)) = a 1 := by
  rw [aeval_chartFunctionalCut c quadraticFamily regularR (by norm_num) _ _
      (by simp [chartSeparant_regularR]),
    chartPolynomial_point c quadraticFamily regularR (p := 5) (r := 0) (by simp)
      (degree_familyMultiplier_quadraticFamily_le a) (multiplierEval_regularR a)
      (eval_multiplierEval_pderiv_regularR _ _ c), chartSeparant_regularR, map_one, one_pow,
    one_mul, familyMultiplier_quadraticFamily]
  simp

-- The same coefficient cut vanishes exactly when `a₁ = 0`, so it is not trivially zero.
example (a : Fin 3 → ZMod 5) (c : ZMod 5) :
    MvPolynomial.aeval (chartPoint c 1 a (familyMultiplier quadraticFamily a))
      (chartFunctionalCut c quadraticFamily regularR 1 2 3 (lcoeff (ZMod 5) 1)) = 0 ↔
        a 1 = 0 := by
  rw [chartFunctionalCut_eq_zero_iff c quadraticFamily regularR (by norm_num) _ _
      (by simp [chartSeparant_regularR]),
    chartPolynomial_point c quadraticFamily regularR (p := 5) (r := 0) (by simp)
      (degree_familyMultiplier_quadraticFamily_le a) (multiplierEval_regularR a)
      (eval_multiplierEval_pderiv_regularR _ _ c), familyMultiplier_quadraticFamily]
  simp

-- The agreement cut of the coefficient of `X` with the constant target `t` takes the value
-- `a₁ - t` at the point of the quadratic root.
example (a : Fin 3 → ZMod 5) (c t : ZMod 5) :
    MvPolynomial.aeval (chartPoint c 1 a (familyMultiplier quadraticFamily a))
      (chartAgreementCut c quadraticFamily regularR 1 2 3 (lcoeff (ZMod 5) 1)
        (MvPolynomial.C t)) = a 1 - t := by
  rw [aeval_chartAgreementCut c quadraticFamily regularR (by norm_num) _ _ _
      (by simp [chartSeparant_regularR]),
    chartPolynomial_point c quadraticFamily regularR (p := 5) (r := 0) (by simp)
      (degree_familyMultiplier_quadraticFamily_le a) (multiplierEval_regularR a)
      (eval_multiplierEval_pderiv_regularR _ _ c), chartSeparant_regularR, map_one, one_pow,
    one_mul, familyMultiplier_quadraticFamily]
  simp

-- The agreement cut with a target in the chart variables vanishes exactly when the
-- coefficient of `X` matches the coordinate `a₂`.
example (a : Fin 3 → ZMod 5) (c : ZMod 5) :
    MvPolynomial.aeval (chartPoint c 1 a (familyMultiplier quadraticFamily a))
      (chartAgreementCut c quadraticFamily regularR 1 2 3 (lcoeff (ZMod 5) 1)
        (MvPolynomial.X (.inr 2))) = 0 ↔ a 1 = a 2 := by
  rw [chartAgreementCut_eq_zero_iff c quadraticFamily regularR (by norm_num) _ _ _
      (by simp [chartSeparant_regularR]),
    chartPolynomial_point c quadraticFamily regularR (p := 5) (r := 0) (by simp)
      (degree_familyMultiplier_quadraticFamily_le a) (multiplierEval_regularR a)
      (eval_multiplierEval_pderiv_regularR _ _ c), familyMultiplier_quadraticFamily]
  simp [chartPoint]

-- With `(Y, Z)`-degree `1`, `s = 1` and `d = 2`, every functional cut has degree at most `4`.
example (c : ZMod 5) (Λ : (ZMod 5)[X] →ₗ[ZMod 5] ZMod 5) :
    (chartFunctionalCut c quadraticFamily regularR 1 2 3 Λ).totalDegree ≤ 4 :=
  totalDegree_chartFunctionalCut_le (s := 1) (d := 2) c quadraticFamily
    weightedTotalDegree_regularR_le (by norm_num) le_rfl Λ

-- With `(Y, Z)`-degree `2`, `s = 1`, `d = 2` and a linear target, every agreement cut has degree
-- at most `2 s d h = 8`.
example (c : ZMod 5) (Λ : (ZMod 5)[X] →ₗ[ZMod 5] ZMod 5) :
    (chartAgreementCut c quadraticFamily squareR 1 2 3 Λ
      (MvPolynomial.X (.inr 2))).totalDegree ≤ 8 :=
  totalDegree_chartAgreementCut_le (s := 1) (d := 2) c quadraticFamily
    weightedTotalDegree_squareR_le (by norm_num) le_rfl Λ (by simp [MvPolynomial.totalDegree_X])

-- The family `(1, X)` gives the Reed–Solomon lines `a + b X`.
example (a b : ZMod 5) : familyMultiplier affineFamily ![a, b] = C a + C b * X := by
  simp [affineMultiplier]

/-- info: 'ReedSolomon.familyMultiplier_affineFamily' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.familyMultiplier_affineFamily

/-- info: 'ReedSolomon.chartFlatten_C' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.chartFlatten_C

/-- info: 'ReedSolomon.chartFlatten_X' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.chartFlatten_X

/-- info: 'ReedSolomon.aeval_chartFlatten' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.aeval_chartFlatten

/-- info: 'ReedSolomon.pderiv_familyEquation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.pderiv_familyEquation

/-- info: 'ReedSolomon.chartEquation_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.chartEquation_eq

/-- info: 'ReedSolomon.chartSeparant_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.chartSeparant_eq

/-- info: 'ReedSolomon.pderiv_chartEquation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.pderiv_chartEquation

/-- info: 'ReedSolomon.aeval_chartEquation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.aeval_chartEquation

/-- info: 'ReedSolomon.aeval_chartSeparant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.aeval_chartSeparant

/-- info: 'ReedSolomon.aeval_chartEquation_point' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.aeval_chartEquation_point

/-- info: 'ReedSolomon.aeval_chartSeparant_point' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.aeval_chartSeparant_point

/-- info: 'ReedSolomon.differentialSpecialization_specializedFamilyEquation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.differentialSpecialization_specializedFamilyEquation

/-- info: 'ReedSolomon.aeval_chartSeparant_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.aeval_chartSeparant_eq

/-- info: 'ReedSolomon.aeval_chartNumerator' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.aeval_chartNumerator

/-- info: 'ReedSolomon.chartCoefficient_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.chartCoefficient_zero

/-- info: 'ReedSolomon.degree_chartPolynomial_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.degree_chartPolynomial_le

/-- info: 'ReedSolomon.eval_chartPolynomial_center' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.eval_chartPolynomial_center

/-- info: 'ReedSolomon.map_chartPolynomial' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.map_chartPolynomial

/-- info: 'ReedSolomon.aeval_chartFunctionalCut' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.aeval_chartFunctionalCut

/-- info: 'ReedSolomon.chartFunctionalCut_eq_zero_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.chartFunctionalCut_eq_zero_iff

/-- info: 'ReedSolomon.chartPolynomial_point' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.chartPolynomial_point

/-- info: 'ReedSolomon.totalDegree_aeval_chartSubstitution_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.totalDegree_aeval_chartSubstitution_le

/-- info: 'ReedSolomon.totalDegree_chartEquation_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.totalDegree_chartEquation_le

/-- info: 'ReedSolomon.totalDegree_chartSeparant_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.totalDegree_chartSeparant_le

/-- info: 'ReedSolomon.chartSeparant_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.chartSeparant_eq_zero

/-- info: 'ReedSolomon.totalDegree_chartNumerator_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.totalDegree_chartNumerator_le

/-- info: 'ReedSolomon.totalDegree_chartNumerator_le_of_pos' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.totalDegree_chartNumerator_le_of_pos

/-- info: 'ReedSolomon.totalDegree_chartFunctionalCut_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.totalDegree_chartFunctionalCut_le

/-- info: 'ReedSolomon.familyMultiplier_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.familyMultiplier_apply

/-- info: 'ReedSolomon.aeval_chartAgreementCut' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.aeval_chartAgreementCut

/-- info: 'ReedSolomon.chartAgreementCut_eq_zero_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.chartAgreementCut_eq_zero_iff

/-- info: 'ReedSolomon.totalDegree_chartAgreementCut_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.totalDegree_chartAgreementCut_le
