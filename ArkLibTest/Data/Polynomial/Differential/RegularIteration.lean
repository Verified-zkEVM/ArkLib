/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.RegularIteration
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-!
# Acceptance tests for fixed-jet uniqueness

* The source statement over a field: two bounded solutions of degree at most `D < p`, in
  characteristic `p`, with the same regular jet through the highest active jet variable, are
  equal. It follows from the left-regular form.
* For `y' = y` at center `0` over `ℚ`, the residual coefficients of `1 + X` and `1 + X + X ^ 2`
  at order `1` differ by `(2 choose 1) * 1 * 1 = 2`, computed by
  `coeff_shiftedJetSubstitution_sub_eq_of_taylor_coeff_eq`.
* Over `ZMod 2` the solutions `1` and `1 + X ^ 2` of `y' = 0` have the same jet through order
  `1` and are different, and the slope `(2 choose 1) * 1` vanishes, so the slope hypothesis of
  `eq_of_polynomialJet_eq_of_isLeftRegular` is needed.
* For `y' = 0` stored at depth `2`, where `Y₁` is the highest active jet variable, the unique
  coefficient that lifts `1` at order `1` is `0`.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-- Source shape: over a field of characteristic `p` with `D < p`, a regular jet through the
highest active jet variable determines a bounded solution. -/
example {F : Type*} [Field F] {p d D : ℕ} [CharP F p] (hp : p.Prime) (hD : D < p)
    {Q : DifferentialPolynomial F d} {s : Fin (d + 1)} (hs : IsHighestActiveJet Q s)
    (center : F) {P P' : BoundedSolution Q D}
    (hjet : polynomialJet (d := s.val) center P.polynomial =
      polynomialJet (d := s.val) center P'.polynomial)
    (hreg : IsRegularJet Q s center (polynomialJet center P.polynomial)) :
    P = P' :=
  BoundedSolution.eq_of_polynomialJet_eq_of_isHighestActiveJet hs center hjet
    fun k _ hkD ↦ (isUnit_iff_ne_zero.mpr (mul_ne_zero
      (Polynomial.natCast_choose_ne_zero_of_lt_charP hp (by omega) (Nat.le_add_left _ _))
      hreg.2)).isRegular.left

/-- The equation `y' = y`, as the differential polynomial `Y₁ - Y₀`. -/
private abbrev expEquation : DifferentialPolynomial ℚ 1 :=
  X (some 1) - X (some 0)

/-- For `y' = y`, the residual coefficients of `1 + X` and `1 + X + X ^ 2` at order `1` differ
by `2`. The value comes from the coefficient-difference identity. -/
example : (shiftedJetSubstitution 0 (1 + Polynomial.X + Polynomial.X ^ 2) expEquation).coeff 1 -
    (shiftedJetSubstitution 0 (1 + Polynomial.X) expEquation).coeff 1 = 2 := by
  rw [coeff_shiftedJetSubstitution_sub_eq_of_taylor_coeff_eq (k := 1) one_pos expEquation 0
    (fun i hi ↦ by interval_cases i <;> simp [Polynomial.coeff_X, Polynomial.coeff_one])]
  simp [separant, jetEvaluation, expEquation, pderiv_X, Fin.last, Polynomial.coeff_X,
    Polynomial.coeff_one]

/-- The equation `y' = 0` over `ZMod 2`. -/
private abbrev constEquation : DifferentialPolynomial (ZMod 2) 1 :=
  X (some 1)

private theorem differentialSpecialization_constEquation (P : Polynomial (ZMod 2)) :
    differentialSpecialization constEquation P = Polynomial.derivative P := by
  simp [constEquation, differentialSpecialization, differentialSpecializationHom,
    Polynomial.hasseDeriv_one]

/-- Over `ZMod 2`, `1` and `1 + X ^ 2` both solve `y' = 0`, have degree at most `2` and the same
jet through order `1` at `0`, and differ; the slope `(2 choose 1) * 1` at `k = 1` is zero. -/
example :
    differentialSpecialization constEquation 1 = 0 ∧
      differentialSpecialization constEquation (1 + Polynomial.X ^ 2) = 0 ∧
      polynomialJet (d := 1) (0 : ZMod 2) 1 = polynomialJet (d := 1) 0 (1 + Polynomial.X ^ 2) ∧
      (1 : Polynomial (ZMod 2)) ≠ 1 + Polynomial.X ^ 2 ∧
      ((1 + 1).choose 1 : ZMod 2) *
        jetEvaluation (separant constEquation (Fin.last 1)) 0 (polynomialJet 0 1) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp
  · rw [differentialSpecialization_constEquation]
    simp only [Polynomial.derivative_add, Polynomial.derivative_one, Polynomial.derivative_X_pow,
      zero_add]
    rw [show ((2 : ℕ) : ZMod 2) = 0 by decide, map_zero, zero_mul]
  · funext i
    fin_cases i <;>
      simp [polynomialJet]
  · intro h
    have := congrArg (Polynomial.coeff · 2) h
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_one] at this
  · have : ((Nat.choose (1 + 1) 1 : ℕ) : ZMod 2) = 0 := by decide
    rw [this, zero_mul]

/-- `y' = 0` stored at depth `2`. -/
private abbrev constEquation₂ : DifferentialPolynomial ℚ 2 :=
  X (some 1)

private theorem isHighestActiveJet_constEquation₂ : IsHighestActiveJet constEquation₂ 1 := by
  classical
  refine ⟨by simp [DependsOnJet, jetDegree], fun j hj ↦ ?_⟩
  simp [DependsOnJet, jetDegree, degreeOf_X, hj.ne']

/-- At the highest active jet variable `Y₁` of `y' = 0` in depth `2`, the unique coefficient
lifting `1` at order `1` is `0`. -/
example (γ : ℚ) :
    (Polynomial.X - Polynomial.C 0) ^ (1 + 1) ∣ differentialSpecialization constEquation₂
        (1 + Polynomial.hassePerturbation 0 γ (1 + (1 : Fin 3).val)) ↔ γ = 0 := by
  have hlift := existsUnique_regularLiftCoefficient_centered_of_isHighestActiveJet (k := 1)
    one_pos constEquation₂ isHighestActiveJet_constEquation₂ 0 1
    (by simp [differentialSpecialization, differentialSpecializationHom])
    (by
      simp [separant, jetEvaluation, constEquation₂, pderiv_X])
  have hzero : (Polynomial.X - Polynomial.C 0) ^ (1 + 1) ∣ differentialSpecialization
      constEquation₂ (1 + Polynomial.hassePerturbation 0 (0 : ℚ) (1 + (1 : Fin 3).val)) := by
    rw [Polynomial.hassePerturbation, map_zero, zero_mul, add_zero]
    simp [differentialSpecialization, differentialSpecializationHom]
  constructor
  · exact fun h ↦ hlift.unique h hzero
  · rintro rfl
    exact hzero

end

end PolynomialDifferential
