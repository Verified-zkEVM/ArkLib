/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.TaylorSeries

/-! # Acceptance cases for the power series root of Lemma 3.11 -/

open ReedSolomon MvPolynomial

/-- The line equation `Z - Y`. -/
private noncomputable def lineR : MvPolynomial AffineVar ℚ :=
  X none - X (some 1)

/-- The equation `Z² - Y`. -/
private noncomputable def sqrtR : MvPolynomial AffineVar ℚ :=
  X none ^ 2 - X (some 1)

/-- The equation `Z² - X²`, singular at the origin. -/
private noncomputable def singularR : MvPolynomial AffineVar ℚ :=
  X none ^ 2 - X (some 0) ^ 2

-- For `Z - Y` at `z = α + β t₀`, the series root is `E(W) = β W`.
example (t₀ α β : ℚ) (E : PowerSeries ℚ) (hE0 : PowerSeries.constantCoeff E = 0)
    (hE : (affineSeriesEquation t₀ α β lineR).eval (PowerSeries.C (α + β * t₀) + E) = 0) :
    E = PowerSeries.C β * PowerSeries.X :=
  (existsUnique_powerSeries_root lineR t₀ α β (α + β * t₀) (by simp [lineR])
    (by simp [lineR])).unique ⟨hE0, by rwa [← eval_affineSeriesEquation]⟩
    ⟨by simp, by simp [lineR]⟩

-- The chart coefficient `c₁` of `Z - Y` is the slope `β`.
example (t₀ α β : ℚ) :
    chartCoefficient t₀ affineFamily lineR (Sum.elim (fun _ ↦ α + β * t₀) ![α, β]) 1 = β := by
  rw [← coeff_C_add_eq_chartCoefficient lineR t₀ α β (α + β * t₀) (by simp [lineR])
    (E := PowerSeries.C β * PowerSeries.X) (by simp)
    (by rw [eval_affineSeriesEquation]; simp [lineR])]
  simp [PowerSeries.coeff_C]

-- The polynomial root `α + β X` of `Z - Y` expands at `t₀` as `(α + β t₀) + β W`.
example (t₀ α β : ℚ) :
    ((Polynomial.taylor t₀ (Polynomial.C α + Polynomial.C β * Polynomial.X) :
      Polynomial ℚ) : PowerSeries ℚ) =
      PowerSeries.C (α + β * t₀) + PowerSeries.C β * PowerSeries.X :=
  coe_taylor_eq_C_add_of_multiplierEval_eq_zero lineR t₀ α β (α + β * t₀)
    (by simp [lineR, affineMultiplier]) (by simp) (by simp [lineR]) (by simp)
    (by rw [eval_affineSeriesEquation]; simp [lineR])

/-- The series root of `Z² - (1 + X)` at `z = 1` is `√(1 + W)`, with `c₁ = 1/2`. -/
private theorem coeff_one_sqrt_root (E : PowerSeries ℚ) (hE0 : PowerSeries.constantCoeff E = 0)
    (hE : (affineSeriesEquation 0 1 1 sqrtR).eval (PowerSeries.C 1 + E) = 0) :
    PowerSeries.coeff 1 E = 1 / 2 := by
  have h := congrArg (PowerSeries.coeff 1) hE
  rw [eval_affineSeriesEquation] at h
  simp [sqrtR, pow_two, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hE0] at h
  linarith

-- At `t₀ = 0`, `α = β = z = 1`, the separant of `Z² - Y` is `S(1, 1, 1) = 2z = 2`.
example : aeval (Sum.elim (fun _ ↦ (1 : ℚ)) ![1, 1]) (chartSeparant 0 affineFamily sqrtR) = 2 := by
  rw [aeval_chartSeparant]
  simp [sqrtR, pderiv_X]

-- At `j = 1`, the identity `c₁ = N₁ / S` with `c₁ = 1/2` and `S = 2` gives `N₁(1, 1, 1) = 1`.
example (E : PowerSeries ℚ) (hE0 : PowerSeries.constantCoeff E = 0)
    (hE : (affineSeriesEquation 0 1 1 sqrtR).eval (PowerSeries.C 1 + E) = 0) :
    aeval (Sum.elim (fun _ ↦ (1 : ℚ)) ![1, 1]) (chartNumerator 0 affineFamily sqrtR 1 1) = 1 := by
  have hS : eval (fun v ↦ v.elim (1 : ℚ) ![0, 1 + 1 * 0]) (pderiv none sqrtR) ≠ 0 := by
    simp [sqrtR, pderiv_X]
  have hsep :
      aeval (Sum.elim (fun _ ↦ (1 : ℚ)) ![1, 1]) (chartSeparant 0 affineFamily sqrtR) = 2 := by
    rw [aeval_chartSeparant]
    simp [sqrtR, pderiv_X]
  have h := coeff_eq_chartNumerator_div_of_constantCoeff_eq_zero sqrtR 0 1 1 1 hS hE0 hE
    (j := 1) le_rfl
  rw [coeff_one_sqrt_root E hE0 hE, hsep] at h
  norm_num at h
  exact h.symm

-- `Z² - (1 + X)` has a series root at `z = 1`, since `R_Z = 2 ≠ 0` there.
example : ∃! E : PowerSeries ℚ, PowerSeries.constantCoeff E = 0 ∧
    aeval (fun v ↦ v.elim (PowerSeries.C 1 + E)
      ![PowerSeries.C 0 + PowerSeries.X,
        PowerSeries.C (1 + 1 * 0) + PowerSeries.C 1 * PowerSeries.X]) sqrtR = 0 :=
  existsUnique_powerSeries_root sqrtR 0 1 1 1 (by simp [sqrtR]) (by simp [sqrtR, pderiv_X])

-- Without `R_Z ≠ 0`, uniqueness fails: `Z² - X²` at the origin has the roots `±W`.
example : ¬ ∃! E : PowerSeries ℚ, PowerSeries.constantCoeff E = 0 ∧
    aeval (fun v ↦ v.elim (PowerSeries.C 0 + E)
      ![PowerSeries.C 0 + PowerSeries.X,
        PowerSeries.C (0 + 0 * 0) + PowerSeries.C 0 * PowerSeries.X]) singularR = 0 := by
  rintro ⟨E, -, huniq⟩
  have h₁ := huniq PowerSeries.X ⟨by simp, by simp [singularR]⟩
  have h₂ := huniq (-PowerSeries.X) ⟨by simp, by simp [singularR]⟩
  have h := congrArg (PowerSeries.coeff 1) (h₁.trans h₂.symm)
  norm_num at h

-- The singular example satisfies the root hypothesis but not the separant hypothesis.
example : eval (fun v ↦ v.elim 0 ![0, 0 + 0 * 0]) singularR = 0 ∧
    eval (fun v ↦ v.elim 0 ![0, 0 + 0 * 0]) (pderiv none singularR) = 0 := by
  simp [singularR, pderiv_X]

/--
info: 'ReedSolomon.existsUnique_powerSeries_root' depends on axioms: [propext, Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.existsUnique_powerSeries_root

/--
info: 'ReedSolomon.coe_taylor_eq_C_add_of_multiplierEval_eq_zero' depends on axioms: [propext,
 Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.coe_taylor_eq_C_add_of_multiplierEval_eq_zero

/--
info: 'ReedSolomon.coeff_eq_chartNumerator_div_of_constantCoeff_eq_zero' depends on axioms:
 [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.coeff_eq_chartNumerator_div_of_constantCoeff_eq_zero

/--
info: 'ReedSolomon.coeff_C_add_eq_chartCoefficient' depends on axioms: [propext,
 Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.coeff_C_add_eq_chartCoefficient

/--
info: 'ReedSolomon.coe_taylor_multiplierEval_affineMultiplier' depends on axioms:
[propext, Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.coe_taylor_multiplierEval_affineMultiplier
