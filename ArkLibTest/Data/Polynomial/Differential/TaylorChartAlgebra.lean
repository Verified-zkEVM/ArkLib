/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for symbolic Taylor chart equations

For the equation `y = 0`, the order-zero chart reconstructs the constant initial value, and its
agreement equation vanishes exactly at that value. With zero separant, every agreement equation
vanishes while the reconstruction can remain nonzero, showing why the regularity hypothesis is
needed.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial Polynomial

/-- The order-zero equation `y = 0`. -/
private abbrev valueEquation : DifferentialPolynomial (Polynomial ℚ) 0 := X (some 0)

/-- At the Hasse jet with value `v`, the symbolic agreement equation vanishes at value `v`. -/
example (a x v : ℚ) :
    aeval (fun _ : Fin 1 ↦ v)
        (map (Polynomial.evalRingHom a)
          (taylorAgreementEquationOver (F := ℚ) (Polynomial.C 0) valueEquation 1
            (Polynomial.C x) (Polynomial.C v))) = 0 := by
  have hS : aeval (fun _ : Fin 1 ↦ v) (map (Polynomial.evalRingHom a)
      (initialJetSeparant (Polynomial.C 0) valueEquation)) ≠ 0 := by
    simp [valueEquation, initialJetSeparant, separant, pderiv_X, Fin.last]
  apply (aeval_map_taylorAgreementEquationOver_eq_zero_iff (Polynomial.aeval a)
    (Polynomial.C 0) valueEquation 1 (fun _ : Fin 1 ↦ v) hS (Polynomial.C x)
    (Polynomial.C v)).2
  simp [valueEquation, rationalTaylorPolynomial, rationalTaylorCoefficient,
    rationalTaylorNumerator, Polynomial.centeredCoefficientPrefix]

/-- A zero separant makes all agreement equations vanish, even when the reconstruction is `1`. -/
example :
    aeval (fun _ : Fin 1 ↦ (1 : ℚ))
        (initialJetSeparant (0 : ℚ) (0 : DifferentialPolynomial ℚ 0)) = 0 ∧
      aeval (fun _ : Fin 1 ↦ (1 : ℚ))
        (taylorAgreementEquation (0 : ℚ) (0 : DifferentialPolynomial ℚ 0) 1 2 0 0) = 0 ∧
      rationalTaylorPolynomial (0 : ℚ) (0 : DifferentialPolynomial ℚ 0) 1
        (fun _ : Fin 1 ↦ 1) = Polynomial.C 1 := by
  constructor
  · simp [initialJetSeparant, separant, Fin.last]
  constructor
  · simp [taylorAgreementEquation, commonTaylorNumerator, initialJetSeparant, separant,
      rationalTaylorNumerator, Fin.last]
  · simp [rationalTaylorPolynomial, rationalTaylorCoefficient, rationalTaylorNumerator,
      Polynomial.centeredCoefficientPrefix]

end

end PolynomialDifferential
