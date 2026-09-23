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

/-- The affine jet identity holds even over the semiring `ℕ`. -/
example (P Q : ℕ[X]) (a z : ℕ) :
    polynomialJet (d := 2) a (P + Polynomial.C z * Q) =
      fun j ↦ polynomialJet (d := 2) a P j + z * polynomialJet (d := 2) a Q j :=
  polynomialJet_add_C_mul a z P Q

end

end PolynomialDifferential
