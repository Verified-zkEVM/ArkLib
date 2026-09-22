/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.DirectRegularLift
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for direct regular lifting

* The source statement over a field: below a prime characteristic `p > D`, a regular initial jet
  and a solution of degree at most `D` with that jet force the solution to be the iterate.
* For `y' = y` at center `0` over `ℚ`, one step from `1 + X` computes `1 + X + X ^ 2 / 2`, whose
  residual is `-X ^ 2 / 2`; by `solution_iff_eq_regularIterate` there is no solution of degree at
  most `2` with jet `(1, 1)`.
* For `Q = Y₀` with `r = D = 0`, the starting polynomial `P₀ = X` has degree above `r`, the zero
  polynomial is a solution with the same jet, and it is not the iterate `X`. So the degree
  hypothesis on `P₀` in `eq_regularIterate_of_polynomialJet_eq` is needed.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-- Source shape: below a prime characteristic `p > D`, a regular initial jet determines the
solution as the iterate. -/
example {F : Type*} [Field F] {p r D : ℕ} [CharP F p] (hp : p.Prime) (hD : D < p)
    (Q : DifferentialPolynomial F r) (center : F) {P₀ P : Polynomial F}
    (hP₀ : P₀.natDegree ≤ r)
    (hreg : IsRegularJet Q (Fin.last r) center (polynomialJet center P₀))
    (hdegree : P.degree ≤ D) (hsolution : differentialSpecialization Q P = 0)
    (hjet : polynomialJet (d := r) center P = polynomialJet center P₀) :
    P = regularIterate Q center P₀ (D - r) :=
  eq_regularIterate_of_polynomialJet_eq Q center hP₀ hdegree hsolution hjet
    fun k _ hkD ↦ isUnit_iff_ne_zero.mpr (mul_ne_zero
      (Polynomial.natCast_choose_ne_zero_of_lt_charP hp (by omega) (Nat.le_add_left _ _))
      hreg.2)

/-- The equation `y' = y`, as the differential polynomial `Y₁ - Y₀`. -/
private abbrev expEquation : DifferentialPolynomial ℚ 1 :=
  X (some 1) - X (some 0)

private theorem differentialSpecialization_expEquation (P : Polynomial ℚ) :
    differentialSpecialization expEquation P = Polynomial.derivative P - P := by
  simp [expEquation, differentialSpecialization, differentialSpecializationHom,
    Polynomial.hasseDeriv_one]

private theorem slope_expEquation (k : ℕ) (P : Polynomial ℚ) :
    ((k + 1).choose 1 : ℚ) * jetEvaluation (separant expEquation (Fin.last 1)) 0
      (polynomialJet 0 P) = k + 1 := by
  simp [separant, jetEvaluation, expEquation, pderiv_X, Fin.last]

/-- One direct step for `y' = y` from `1 + X` adds `X ^ 2 / 2`. -/
private theorem regularIterate_expEquation_one :
    regularIterate expEquation 0 (1 + Polynomial.X) 1 =
      1 + Polynomial.X + Polynomial.C (1 / 2) * Polynomial.X ^ 2 := by
  have hres : (shiftedJetSubstitution 0 (1 + Polynomial.X) expEquation).coeff 1 = -1 := by
    rw [← taylor_differentialSpecialization, differentialSpecialization_expEquation]
    simp
  rw [regularIterate_succ, regularIterate_zero, regularLift, regularLiftCoefficient,
    slope_expEquation, hres, Polynomial.hassePerturbation, Ring.inverse_eq_inv]
  norm_num

/-- The residual of the iterate is `-X ^ 2 / 2`, so it is not a solution. -/
private theorem differentialSpecialization_regularIterate_expEquation_one :
    differentialSpecialization expEquation (regularIterate expEquation 0 (1 + Polynomial.X) 1) =
      -(Polynomial.C (1 / 2) * Polynomial.X ^ 2) := by
  rw [regularIterate_expEquation_one, differentialSpecialization_expEquation]
  simp only [Polynomial.derivative_add, Polynomial.derivative_one, Polynomial.derivative_X,
    Polynomial.derivative_C_mul_X_pow]
  norm_num

/-- `y' = y` has no polynomial solution of degree at most `2` with jet `(1, 1)` at `0`. -/
example : ¬∃ P : Polynomial ℚ, P.degree ≤ 2 ∧ differentialSpecialization expEquation P = 0 ∧
    polynomialJet (d := 1) 0 P = polynomialJet 0 (1 + Polynomial.X) := by
  rintro ⟨P, hP⟩
  obtain ⟨rfl, -, hsolution⟩ := (solution_iff_eq_regularIterate expEquation 0 (D := 2)
    (by compute_degree!) (fun k _ _ ↦ by
      rw [slope_expEquation]
      exact isUnit_iff_ne_zero.mpr (by positivity)) P).mp hP
  rw [differentialSpecialization_regularIterate_expEquation_one, neg_eq_zero] at hsolution
  have := congrArg (Polynomial.coeff · 2) hsolution
  simp at this

/-- `Y₀` as a differential polynomial of order `0`: the equation `y = 0`. -/
private abbrev zeroEquation : DifferentialPolynomial ℚ 0 :=
  X (some 0)

/-- Without `P₀.natDegree ≤ r`, the conclusion of `eq_regularIterate_of_polynomialJet_eq` fails:
`0` solves `y = 0`, has degree at most `0` and the jet of `X` at `0`, and differs from the
iterate `X`. The slope hypothesis is vacuous here. -/
example :
    (0 : Polynomial ℚ).degree ≤ (0 : ℕ) ∧ differentialSpecialization zeroEquation 0 = 0 ∧
      polynomialJet (d := 0) (0 : ℚ) 0 = polynomialJet 0 Polynomial.X ∧
      (0 : Polynomial ℚ) ≠ regularIterate zeroEquation 0 Polynomial.X (0 - 0) := by
  refine ⟨by simp, by simp, ?_, ?_⟩
  · funext i
    fin_cases i
    simp [polynomialJet]
  · simp [Polynomial.X_ne_zero.symm]

end

end PolynomialDifferential
