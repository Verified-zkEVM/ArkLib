/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.RationalTaylor
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for rational Taylor coefficients

The main example is the first-order equation `y' = y`, written as `Q = Y₁ - Y₀`, at center `0`.
Its separant is `1`. Over `ℚ` the affine equation at `l = 2` forces the rational coefficient
`c₂ = c₁ / 2`, the second Taylor coefficient of `c₁ * exp x` when `c₀ = c₁`. Over `ZMod 2` the
binomial pivot `(2 choose 1)` vanishes, the rational coefficient `c₂` is `0`, and the affine
equation fails, so the pivot hypothesis of `rationalTaylorCoefficient_residual` is needed.

A second example, `y' = 2x` (`Q = Y₁ - 2X`) with the polynomial solution `X ^ 2`, checks
`rationalTaylorCoefficient_eq_solution` over `ℚ`, and shows over `ZMod 2` that its binomial
hypothesis is needed: there the solution's Taylor coefficient `1` differs from the rational
coefficient `0`.

The file also checks the numerator degree bound at a constant equation, where
`jetTotalDegree Q = 0`, and the sufficiency of the common exponent `2K - 3` in the worst case.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-- The equation `y' = y`, as the differential polynomial `Y₁ - Y₀`. -/
private abbrev expEquation (F : Type*) [CommRing F] : DifferentialPolynomial F 1 :=
  X (some 1) - X (some 0)

/-- The separant of `Y₁ - Y₀` is `1`. -/
private theorem jetEvaluation_separant_expEquation (F : Type*) [CommRing F] [Nontrivial F]
    (jet : Fin 2 → F) :
    jetEvaluation (separant (expEquation F) (Fin.last 1)) 0 jet = 1 := by
  simp [separant, jetEvaluation, expEquation, pderiv_X, Fin.last]

/-- Along `c₀ + c₁ x`, the equation `y' - y` has coefficient `-c₁` at `x ^ 1`. -/
private theorem coeff_one_expEquation_prefix (F : Type*) [CommRing F] (c : ℕ → F) :
    (Polynomial.taylor 0 (differentialSpecialization (expEquation F)
      (Polynomial.centeredCoefficientPrefix 0 c 2))).coeff 1 = -c 1 := by
  rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, Polynomial.centeredCoefficientPrefix_succ,
    Polynomial.centeredCoefficientPrefix_succ, Polynomial.centeredCoefficientPrefix_zero]
  simp [differentialSpecialization, differentialSpecializationHom, expEquation,
    Polynomial.coeff_C]

/-- Over `ℚ`, the rational coefficient of `x ^ 2` for `y' = y` is `c₁ / 2`. -/
example (jet : Fin 2 → ℚ) : rationalTaylorCoefficient 0 (expEquation ℚ) jet 2 = jet 1 / 2 := by
  have h := rationalTaylorCoefficient_residual_prefix 0 (expEquation ℚ) jet 2 (by norm_num)
    (by rw [jetEvaluation_separant_expEquation]; norm_num) (by norm_num)
  rw [jetEvaluation_separant_expEquation, coeff_one_expEquation_prefix] at h
  have h1 : rationalTaylorCoefficient 0 (expEquation ℚ) jet 1 = jet 1 :=
    rationalTaylorCoefficient_initial 0 (expEquation ℚ) jet 1
  rw [h1] at h
  norm_num at h
  linarith

/-- Over `ZMod 2`, with `c₀ = 0` and `c₁ = 1`, the pivot `(2 choose 1)` is zero and the rational
coefficient of `x ^ 2` is `0`. -/
private theorem rationalTaylorCoefficient_expEquation_zmod_two :
    rationalTaylorCoefficient 0 (expEquation (ZMod 2)) ![0, 1] 2 = 0 := by
  have hchoose : ((Nat.choose 2 1 : ℕ) : ZMod 2) = 0 := by decide
  rw [rationalTaylorCoefficient, rationalTaylorNumerator,
    dite_eq_right_of_eq_false (eq_false (by norm_num)), hchoose]
  simp

/-- The pivot hypothesis is needed: over `ZMod 2` the separant is nonzero at the jet, but the
affine equation of `rationalTaylorCoefficient_residual_prefix` at `l = 2` fails. -/
example :
    jetEvaluation (separant (expEquation (ZMod 2)) (Fin.last 1)) 0 ![0, 1] ≠ 0 ∧
      (Polynomial.taylor 0 (differentialSpecialization (expEquation (ZMod 2))
          (Polynomial.centeredCoefficientPrefix 0
            (rationalTaylorCoefficient 0 (expEquation (ZMod 2)) ![0, 1]) 2))).coeff (2 - 1) +
        (((Nat.choose 2 1 : ℕ) : ZMod 2) *
          rationalTaylorCoefficient 0 (expEquation (ZMod 2)) ![0, 1] 2) *
          jetEvaluation (separant (expEquation (ZMod 2)) (Fin.last 1)) 0 ![0, 1] ≠ 0 := by
  rw [jetEvaluation_separant_expEquation, rationalTaylorCoefficient_expEquation_zmod_two,
    coeff_one_expEquation_prefix]
  have h1 : rationalTaylorCoefficient 0 (expEquation (ZMod 2)) ![0, 1] 1 = 1 :=
    rationalTaylorCoefficient_initial 0 (expEquation (ZMod 2)) ![0, 1] 1
  rw [h1]
  decide

/-- The equation `y' = 2x`, as the differential polynomial `Y₁ - 2X`. -/
private abbrev linearEquation (F : Type*) [CommRing F] : DifferentialPolynomial F 1 :=
  X (some 1) - 2 * X none

/-- `X ^ 2` solves `y' = 2x` over every commutative ring. -/
private theorem differentialSpecialization_linearEquation (F : Type*) [CommRing F] :
    differentialSpecialization (linearEquation F) (Polynomial.X ^ 2) = 0 := by
  simp [linearEquation, differentialSpecialization, differentialSpecializationHom,
    Polynomial.hasseDeriv_one, one_add_one_eq_two, Polynomial.C_ofNat]

/-- The separant of `Y₁ - 2X` is `1`. -/
private theorem jetEvaluation_separant_linearEquation (F : Type*) [CommRing F] [Nontrivial F]
    (jet : Fin 2 → F) :
    jetEvaluation (separant (linearEquation F) (Fin.last 1)) 0 jet = 1 := by
  simp [separant, jetEvaluation, linearEquation, pderiv_X, Fin.last]

/-- Over `ℚ`, the rational coefficient of `x ^ 2` computed from the jet of the solution `X ^ 2`
is its Taylor coefficient `1`. -/
example : rationalTaylorCoefficient 0 (linearEquation ℚ) (polynomialJet 0 (Polynomial.X ^ 2)) 2 =
    1 := by
  rw [rationalTaylorCoefficient_eq_solution 0 (linearEquation ℚ) (Polynomial.X ^ 2)
    (differentialSpecialization_linearEquation ℚ)
    (by rw [jetEvaluation_separant_linearEquation]; norm_num) 2
    (fun i hi hi2 ↦ by
      obtain rfl : i = 2 := by omega
      norm_num)]
  simp [Polynomial.coeff_X_pow]

/-- The binomial hypothesis of `rationalTaylorCoefficient_eq_solution` is needed: over `ZMod 2`,
`X ^ 2` still solves `y' = 2x` and the separant is `1`, but `(2 choose 1) = 0`, the rational
coefficient of `x ^ 2` is `0`, and the Taylor coefficient is `1`. -/
example : rationalTaylorCoefficient 0 (linearEquation (ZMod 2))
      (polynomialJet 0 (Polynomial.X ^ 2)) 2 ≠
    (Polynomial.taylor 0 (Polynomial.X ^ 2 : Polynomial (ZMod 2))).coeff 2 := by
  have hchoose : ((Nat.choose 2 1 : ℕ) : ZMod 2) = 0 := by decide
  rw [rationalTaylorCoefficient, rationalTaylorNumerator,
    dite_eq_right_of_eq_false (eq_false (by norm_num)), hchoose]
  simp [Polynomial.coeff_X_pow]

/-- The numerator degree bound needs no positivity of `jetTotalDegree Q`: for the constant
equation `Q = 1`, the bound is `1` at every index. -/
example (l : ℕ) :
    (rationalTaylorNumerator 0 (1 : DifferentialPolynomial ℚ 1) l).totalDegree ≤ 1 := by
  have h := totalDegree_rationalTaylorNumerator_le 0 (1 : DifferentialPolynomial ℚ 1) l
  have h0 : jetTotalDegree (1 : DifferentialPolynomial ℚ 1) = 0 := by
    simpa using (jetTotalDegree_le_iff (1 : DifferentialPolynomial ℚ 1) 0).mpr
      (by simp [totalJetDegree])
  simpa [h0] using h

/-- For `r = 0` and `K = 4`, the exponent `2K - 3 = 5` is sufficient and is attained at `l = 3`,
so `4` is not sufficient. -/
example : TaylorExponentSufficient 0 4 (2 * 4 - 3) ∧ ¬ TaylorExponentSufficient 0 4 4 := by
  refine ⟨taylorExponentSufficient_two_mul_sub_three 0 4, fun h ↦ ?_⟩
  have := h 3
  norm_num at this

end

end PolynomialDifferential
