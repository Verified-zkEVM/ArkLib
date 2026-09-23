/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveCertificate
import Mathlib.FieldTheory.RatFunc.Basic

open MvPolynomial Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

namespace SymbolicInterpolationTest

/-- One center and the single source column `Y₀`. -/
noncomputable def centers : Fin 1 ↪ ℚ :=
  ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩

noncomputable def received : Fin 1 → ℚ[X] := fun _ => 0

def columns : Fin 1 → SourceColumn 0 := fun _ => ⟨0, 1, Fin.elim0⟩

/-- The rank-zero construction yields an equation vanishing on the received constant. -/
example : ∃ cert : Certificate 1 1 0 1 0 0 centers received,
    cert.Q ≠ 0 ∧ differentialSpecialization
      (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) 0) cert.Q) 0 = 0 := by
  have hcolumns : Function.Injective columns := by
    intro i j _
    exact Subsingleton.elim _ _
  have hweight : ∀ j, Finsupp.weight (differentialWeight 0) (columns j).exponent < 1 := by
    intro j
    simp [weight_differentialWeight_eq, columns, SourceColumn.exponent]
  have hdegree : ∀ j, totalJetDegree (columns j).exponent ≤ 1 := by
    intro j
    simp [columns]
  have hY : (columns 0).polynomial =
      (MvPolynomial.X (some 0) : DifferentialPolynomial ℚ[X] 0) := by
    simpa [columns, SourceColumn.polynomial, SourceColumn.exponent] using
      (MvPolynomial.X_pow_eq_monomial (n := some 0) (e := 1) :
        (MvPolynomial.X (some 0) : DifferentialPolynomial ℚ[X] 0) ^ 1 =
          MvPolynomial.monomial (Finsupp.single (some 0) 1) 1).symm
  have hsub : unscaledLocalSubstitution 0 (Polynomial.C (centers 0)) (received 0)
      ((columns 0).polynomial : DifferentialPolynomial ℚ[X] 0) =
        MvPolynomial.monomial
          (Finsupp.single (localT 0) 1 + Finsupp.single (localE 0) 1) 1 := by
    rw [hY, unscaledLocalSubstitution_Y_zero]
    simp only [received, localCorrection, Finset.univ_eq_empty, Finset.sum_empty]
    rw [← pow_one (MvPolynomial.X (localT 0)), ← pow_one (MvPolynomial.X (localE 0)),
      MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul_monomial]
    norm_num
  have hcoeff : ∀ e : LowContactIndex 0 1,
      (unscaledLocalSubstitution 0 (Polynomial.C (centers 0)) (received 0)
        ((columns 0).polynomial : DifferentialPolynomial ℚ[X] 0)).coeff e.1 = 0 := by
    intro e
    have hne : e.1 ≠ Finsupp.single (localT 0) 1 + Finsupp.single (localE 0) 1 := by
      intro he
      have hweight : localContactOrder 0
          (Finsupp.single (localT 0) 1 + Finsupp.single (localE 0) 1) = 1 := by
        rw [localContactOrder, map_add, Finsupp.weight_single, Finsupp.weight_single]
        simp
      have hlow := e.2
      rw [he, hweight] at hlow
      omega
    rw [hsub, MvPolynomial.coeff_monomial]
    simp [Ne.symm hne]
  have hrank : ((supportedLocalConstraintMatrix 1
      (fun i => Polynomial.C (centers i)) received columns).map
        (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ 0 := by
    have hmatrix : localConstraintMatrix 1
        (fun i => Polynomial.C (centers i)) received columns = 0 := by
      apply Matrix.ext
      intro row j
      rcases row with ⟨i, e⟩
      fin_cases i
      fin_cases j
      rw [localConstraintMatrix_apply]
      simpa [centers, received, columns] using hcoeff e
    rw [rank_map_supportedLocalConstraintMatrix, hmatrix]
    rw [Matrix.map_zero _ (map_zero _)]
    exact (Matrix.rank_zero).le
  obtain ⟨cert⟩ := exists_certificate_of_monomial_rank_bound
    (d := 0) (D := 0) (m := 1) (A := 1) (k := 1) (ℓ := 0) (ν := 1) (r := 0)
    (hbudget := by norm_num) (hkD := by omega) centers received
    (by intro i; simp [received]) columns hcolumns
    (by intro j; simp [columns]) hdegree hweight
    (algebraMap ℚ[X] (RatFunc ℚ)) (IsFractionRing.injective _ _) hrank (by simp)
  refine ⟨cert, cert.nonzero, ?_⟩
  have hs := cert.specialization_sound (E := ℚ) (RingHom.id ℚ) 0
  exact hs.2.2 Finset.univ 0 (by norm_num) (by simp) (by intro i hi; simp [received])

end SymbolicInterpolationTest
