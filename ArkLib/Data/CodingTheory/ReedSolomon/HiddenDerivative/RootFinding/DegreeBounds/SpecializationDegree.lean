/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Kai Zhe Zheng
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.WitnessCounting
public import Mathlib.Algebra.Polynomial.BigOperators
/-!
# Degree bounds for differential specialization

This file proves the weighted-degree bound used to control the exceptional witness points in
differential root counting.  If `P` has degree at most `D`, substituting
`X, P, P⁽¹⁾, ..., P⁽ᵈ⁾` into a differential polynomial cannot produce a univariate degree
larger than the weight that assigns `1` to `X` and `D - j` to `Y_j`.

The proof is the coefficient-field-general form of the argument in the authorized
`kz99/rs-ld-mca` source file `RSListDecoding/Lemmas/GlobalBudgets.lean`, pinned in the project
provenance record.  It is included here from first principles rather than relying on the source's
prime-field-specific statement.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial
open scoped BigOperators

variable {F : Type*} {d D : ℕ}

/-- Every polynomial substituted for a differential variable has degree at most that variable's
root-specialization weight. -/
theorem natDegree_differentialVariable_le [CommSemiring F] (P : F[X])
    (hP : P.natDegree ≤ D) (v : JetVariable d) :
    (match v with
      | none => X
      | some j => hasseDeriv j P).natDegree ≤ differentialWeight D v := by
  cases v with
  | none => exact Polynomial.natDegree_X_le
  | some j =>
      exact (Polynomial.natDegree_hasseDeriv_le P j.val).trans
        (Nat.sub_le_sub_right hP j.val)

/-- Differential specialization cannot increase degree past the corresponding weighted total
degree.  The statement includes the zero polynomial and zero-weight variables. -/
theorem natDegree_differentialSpecialization_le [CommSemiring F]
    (Q : DifferentialPolynomial F d) (P : F[X]) (hP : P.natDegree ≤ D) :
    (differentialSpecialization Q P).natDegree ≤ differentialWeightedDegree D Q := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum Q]
  simp only [differentialSpecialization, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro u hu
  rw [MvPolynomial.eval₂Hom_monomial]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le u.support
    (fun v => (match v with
      | none => X
      | some j => hasseDeriv j P) ^ u v)).trans ?_
  calc
    ∑ v ∈ u.support,
        ((match v with
          | none => X
          | some j => hasseDeriv j P) ^ u v).natDegree
        ≤ ∑ v ∈ u.support, u v * differentialWeight D v := by
          apply Finset.sum_le_sum
          intro v _hv
          exact Polynomial.natDegree_pow_le.trans
            (Nat.mul_le_mul_left (u v) (natDegree_differentialVariable_le P hP v))
    _ = Finsupp.weight (differentialWeight D) u := by
          rw [Finsupp.weight_apply]
          simp only [Finsupp.sum, nsmul_eq_mul, Nat.cast_id]
    _ ≤ differentialWeightedDegree D Q :=
      MvPolynomial.le_weightedTotalDegree _ hu

/-- Partial differentiation removes the differentiated variable's full weight.
Natural subtraction also covers a zero derivative or a weight larger than the original degree. -/
theorem weightedTotalDegree_pderiv_le_sub [CommSemiring F]
    (weight : JetVariable d → ℕ) (v : JetVariable d) (Q : DifferentialPolynomial F d) :
    (MvPolynomial.pderiv v Q).weightedTotalDegree weight ≤
      Q.weightedTotalDegree weight - weight v := by
  classical
  rw [MvPolynomial.weightedTotalDegree]
  apply Finset.sup_le
  intro u hu
  have hcoeff : MvPolynomial.coeff u (MvPolynomial.pderiv v Q) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hu
  have horiginal : MvPolynomial.coeff (u + Finsupp.single v 1) Q ≠ 0 := by
    intro hzero
    rw [MvPolynomial.coeff_pderiv, hzero, zero_mul] at hcoeff
    exact hcoeff rfl
  have hsupport : u + Finsupp.single v 1 ∈ Q.support :=
    MvPolynomial.mem_support_iff.mpr horiginal
  have h := MvPolynomial.le_weightedTotalDegree weight hsupport
  rw [map_add, Finsupp.weight_single] at h
  simp only [one_smul] at h
  omega

/-- Partial differentiation cannot increase a natural-valued weighted total degree. -/
theorem weightedTotalDegree_pderiv_le [CommSemiring F]
    (weight : JetVariable d → ℕ) (v : JetVariable d) (Q : DifferentialPolynomial F d) :
    (MvPolynomial.pderiv v Q).weightedTotalDegree weight ≤
      Q.weightedTotalDegree weight :=
  (weightedTotalDegree_pderiv_le_sub weight v Q).trans (Nat.sub_le _ _)

/-- The separant specialization saves the full `D-s` degree of its differentiated jet. -/
theorem natDegree_differentialSpecialization_separant_le_sub [CommSemiring F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (P : F[X])
    (hP : P.natDegree ≤ D) :
    (differentialSpecialization (separant Q s) P).natDegree ≤
      differentialWeightedDegree D Q - (D - s.val) :=
  (natDegree_differentialSpecialization_le (separant Q s) P hP).trans
    (weightedTotalDegree_pderiv_le_sub (differentialWeight D) (some s) Q)

/-- Specializing a separant has degree at most the original differential polynomial's weighted
degree. -/
theorem natDegree_differentialSpecialization_separant_le [CommSemiring F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (P : F[X])
    (hP : P.natDegree ≤ D) :
    (differentialSpecialization (separant Q s) P).natDegree ≤
      differentialWeightedDegree D Q := by
  exact (natDegree_differentialSpecialization_le (separant Q s) P hP).trans
    (weightedTotalDegree_pderiv_le (differentialWeight D) (some s) Q)

/-- Root-counting form: every bounded solution's separant specialization obeys the same weighted
degree budget as the equation. -/
theorem _root_.PolynomialDifferential.BoundedSolution.natDegree_separant_le
    [CommSemiring F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (solution : BoundedSolution Q D) :
    (differentialSpecialization (separant Q s) solution.polynomial).natDegree ≤
      differentialWeightedDegree D Q := by
  apply natDegree_differentialSpecialization_separant_le Q s solution.polynomial
  exact Polynomial.natDegree_le_of_degree_le solution.degree_le

/-- A strict differential weighted-degree budget gives the strict separant-specialization degree
bound used to count exceptional field points. -/
theorem _root_.PolynomialDifferential.BoundedSolution.natDegree_separant_lt
    [CommSemiring F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (solution : BoundedSolution Q D) {bound : ℕ}
    (hQ : differentialWeightedDegree D Q < bound) :
    (differentialSpecialization (separant Q s) solution.polynomial).natDegree < bound :=
  (solution.natDegree_separant_le Q s).trans_lt hQ

/-- Root-counting wrapper with the canonical weighted-degree exceptional-point budget already
discharged.  The only remaining solution-specific input is injectivity of the bounded-polynomial
jet at each regular witness point. -/
theorem boundedSolution_counting_pow_le_weightedDegree [Field F] [Finite F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (D Δ : ℕ)
    (roots : Finset (BoundedSolution Q D))
    (hSeparantNonzero : ∀ solution ∈ roots,
      differentialSpecialization (separant Q s) solution.polynomial ≠ 0)
    (hJetInj : ∀ point : F,
      Set.InjOn (fun solution : BoundedSolution Q D ↦
        polynomialJet (d := d) point solution.polynomial)
        {solution | solution ∈ roots ∧ IsRegularWitness s solution point})
    (hDegree : jetDegree Q s ≤ Δ) :
    (Nat.card F - differentialWeightedDegree D Q) * roots.card ≤
      Nat.card F * Δ * Nat.card F ^ d := by
  apply boundedSolution_counting_pow_le Q s D (differentialWeightedDegree D Q) Δ roots
    hSeparantNonzero
  · intro solution _hsolution
    exact solution.natDegree_separant_le Q s
  · exact hJetInj
  · exact hDegree

end

end ReedSolomon.HiddenDerivative
