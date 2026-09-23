/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.Basic

/-!
# Acceptance tests for differential-polynomial specialization

These ordinary-import examples distinguish the independent variable from the jet variables and
exercise the comparison between specialization and scalar jet evaluation.
-/

namespace PolynomialDifferential

noncomputable section

open Polynomial

private def valueAndFirstJet : DifferentialPolynomial ℚ 1 :=
  MvPolynomial.X none + MvPolynomial.X (some 0) +
    MvPolynomial.X (some (Fin.last 1))

/-- Specialization sends the three distinct generators to `X`, `P`, and the first Hasse
derivative of `P`. -/
example (P : ℚ[X]) :
    differentialSpecialization valueAndFirstJet P = Polynomial.X + P + hasseDeriv 1 P := by
  simp [valueAndFirstJet, differentialSpecialization, differentialSpecializationHom]

/-- Evaluation after specialization agrees with evaluation on the polynomial's scalar jet. -/
example (P : ℚ[X]) (a : ℚ) :
    (differentialSpecialization valueAndFirstJet P).eval a =
      jetEvaluation valueAndFirstJet a (polynomialJet a P) :=
  eval_differentialSpecialization valueAndFirstJet P a

private abbrev naturalBase : ℕ[X] := X ^ 2 + 2 * X + 3

private abbrev naturalDirection : ℕ[X] := 2 * X ^ 2 + X + 1

/-- Concrete order-zero, first, and second Hasse jets over `ℕ` record an affine sum. -/
example :
    polynomialJet (d := 2) 0 naturalBase = ![3, 2, 1] ∧
      polynomialJet (d := 2) 0 naturalDirection = ![1, 1, 2] ∧
      polynomialJet (d := 2) 0 (naturalBase + Polynomial.C 3 * naturalDirection) =
        ![6, 5, 7] := by
  constructor
  · ext j
    fin_cases j <;>
      rw [polynomialJet, Polynomial.hasseJet_eq_taylor_coeff] <;>
      norm_num [naturalBase, Polynomial.taylor, Polynomial.coeff_X,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_one]
  constructor
  · ext j
    fin_cases j <;>
      rw [polynomialJet, Polynomial.hasseJet_eq_taylor_coeff] <;>
      norm_num [naturalDirection, Polynomial.taylor, Polynomial.coeff_X,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_one]
  · ext j
    fin_cases j <;>
      rw [polynomialJet, Polynomial.hasseJet_eq_taylor_coeff] <;>
      norm_num [naturalBase, naturalDirection, Polynomial.taylor, Polynomial.coeff_X,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_one]

end

end PolynomialDifferential
