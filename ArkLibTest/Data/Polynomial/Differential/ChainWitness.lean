/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.ChainWitness
import ArkLib.Data.Polynomial.Differential.WitnessCount
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance tests for chain witnesses

* Over `ZMod 2`, every point is a regular chain witness for the solutions `1` and `1 + X ^ 2` of
  `y' = 0`, and the two have the same jet at `0` through order `1`. So the binomial hypothesis of
  `ChainWitness.eq_of_polynomialJet_eq` is needed at `D = 2`, where `(2 choose 1) = 0`.
* Over `ZMod 2`, `0` solves `Y₀ ^ 2 = 0` and has no chain witness, and at `D = 0` the conclusion
  of `exists_chainWitness` fails for it. The equation violates only the cast hypothesis.
* Over a field, the forms with the characteristic guard `D < ringChar F` (and, for
  `exists_chainWitness`, `jetDegree Q j < ringChar F` for a bounded solution) follow.
-/

namespace PolynomialDifferential

noncomputable section

open Polynomial

/-! ### The binomial hypothesis of fixed-jet uniqueness is needed -/

/-- The equation `y' = 0` over `ZMod 2`, as the differential polynomial `Y₁`. -/
private abbrev constEquation : DifferentialPolynomial (ZMod 2) 1 :=
  MvPolynomial.X (some 1)

private theorem highestActiveJet_constEquation : highestActiveJet constEquation = some 1 := by
  have hdep : DependsOnJet constEquation 1 := by simp [DependsOnJet, jetDegree]
  cases hs : highestActiveJet constEquation with
  | none => exact absurd hdep (by simpa using (highestActiveJet_eq_none_iff _).mp hs 1)
  | some j =>
      have h := isHighestActiveJet_of_highestActiveJet_eq_some hs
      by_contra hne
      have hj : j = 0 := by
        fin_cases j
        · rfl
        · exact absurd rfl hne
      exact h.2 1 (by rw [hj]; decide) hdep

private theorem differentialSpecialization_constEquation (P : (ZMod 2)[X]) :
    differentialSpecialization constEquation P = derivative P := by
  simp [constEquation, differentialSpecialization, differentialSpecializationHom,
    hasseDeriv_one]

/-- Every point is a regular chain witness for every solution of `y' = 0`: the separant is `1`. -/
private theorem chainWitness_constEquation {P : (ZMod 2)[X]} (hP : derivative P = 0) (a : ZMod 2) :
    ChainWitness constEquation P a :=
  .regular highestActiveJet_constEquation
    (by rw [differentialSpecialization_constEquation, hP])
    (by simp [separant, constEquation, jetEvaluation])

private theorem derivative_one_add_X_sq : derivative (1 + X ^ 2 : (ZMod 2)[X]) = 0 := by
  rw [derivative_add, derivative_one, derivative_X_pow, show ((2 : ℕ) : ZMod 2) = 0 by decide,
    map_zero, zero_mul, zero_add]

/-- The binomial hypothesis of `ChainWitness.eq_of_polynomialJet_eq` cannot be dropped. -/
example : ChainWitness constEquation 1 0 ∧ ChainWitness constEquation (1 + X ^ 2) 0 ∧
    polynomialJet (d := 1) 0 (1 : (ZMod 2)[X]) = polynomialJet 0 (1 + X ^ 2) ∧
    (1 : (ZMod 2)[X]) ≠ 1 + X ^ 2 ∧ ((1 + 1).choose 1 : ZMod 2) = 0 := by
  refine ⟨chainWitness_constEquation derivative_one 0,
    chainWitness_constEquation derivative_one_add_X_sq 0, ?_, fun h ↦ ?_, by decide⟩
  · funext i
    fin_cases i
    · simp [polynomialJet]
    · simp [polynomialJet, hasseDeriv_one]
  · simpa [coeff_X_pow, coeff_one] using congrArg (coeff · 2) h

/-! ### The cast hypothesis of `exists_chainWitness` is needed -/

private abbrev squareEquation : DifferentialPolynomial (ZMod 2) 0 :=
  MvPolynomial.X (some 0) ^ 2

private theorem separant_squareEquation : separant squareEquation 0 = 0 := by
  rw [separant, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self, mul_one]
  change MvPolynomial.C ((2 : ℕ) : ZMod 2) * MvPolynomial.X (some 0) ^ 1 = 0
  rw [ZMod.natCast_self, MvPolynomial.C_0, zero_mul]

private theorem highestActiveJet_zero :
    highestActiveJet (0 : DifferentialPolynomial (ZMod 2) 0) = none :=
  (highestActiveJet_eq_none_iff _).mpr (by simp [DependsOnJet, jetDegree])

/-- `0` has no chain witness for `Y₀ ^ 2 = 0` over `ZMod 2`: the only stage below `Y₀ ^ 2` has
separant `0`, and `0` has no active jet. -/
private theorem not_chainWitness_squareEquation (a : ZMod 2) :
    ¬ChainWitness squareEquation 0 a := by
  intro h
  cases h with
  | @regular _ _ _ s _ _ hreg =>
      rw [Fin.fin_one_eq_zero s, separant_squareEquation] at hreg
      exact hreg (by simp [jetEvaluation])
  | @singular _ _ _ s _ _ hnext =>
      rw [Fin.fin_one_eq_zero s, separant_squareEquation] at hnext
      cases hnext with
      | regular hs => rw [highestActiveJet_zero] at hs; exact absurd hs (by simp)
      | singular hs => rw [highestActiveJet_zero] at hs; exact absurd hs (by simp)

private theorem differentialWeightedDegree_squareEquation :
    differentialWeightedDegree 0 squareEquation = 0 := by
  unfold differentialWeightedDegree MvPolynomial.weightedTotalDegree
  simp only [squareEquation]
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.support_monomial]
  simp [Finsupp.weight_apply]

/-- The cast hypothesis of `exists_chainWitness` cannot be dropped: `Y₀ ^ 2` is nonzero and `0`
is a solution of degree `0`, but no nonzero constant `R` has its non-roots among the chain
witnesses. -/
example : ¬∃ R : (ZMod 2)[X], R ≠ 0 ∧
    R.natDegree ≤ differentialWeightedDegree 0 squareEquation - (0 - 0) ∧
    ∀ a, R.eval a ≠ 0 → ChainWitness squareEquation 0 a := by
  rintro ⟨R, hR, hdeg, hcover⟩
  rw [differentialWeightedDegree_squareEquation] at hdeg
  rw [eq_C_of_natDegree_le_zero hdeg] at hR hcover
  exact not_chainWitness_squareEquation 0
    (hcover 0 (by simpa using fun h ↦ hR (by rw [h, C_0])))

/-! ### Forms with the characteristic guard -/

/-- `ChainWitness.eq_of_polynomialJet_eq` over a field with the guard `D < ringChar F`. -/
example {F : Type*} [Field F] {d D : ℕ} {Q : DifferentialPolynomial F d} {P P' : F[X]} {a : F}
    (h : ChainWitness Q P a) (h' : ChainWitness Q P' a)
    (hP : P.degree ≤ D) (hP' : P'.degree ≤ D) (hD : D < ringChar F)
    (hjet : polynomialJet (d := d) a P = polynomialJet a P') : P = P' :=
  h.eq_of_polynomialJet_eq h' hP hP'
    (fun _ _ ↦ natCast_choose_ne_zero_of_ringChar (Or.inr hD) _) hjet

/-- `exists_chainWitness` over a field with the guards `D < ringChar F` and
`jetDegree Q j < ringChar F`, for a bounded solution. -/
example {F : Type*} [Field F] {d D : ℕ} (Q : DifferentialPolynomial F d) (hQ : Q ≠ 0)
    (hchar : D < ringChar F ∧ ∀ j, jetDegree Q j < ringChar F) (P : BoundedSolution Q D) :
    ∃ R : F[X], R ≠ 0 ∧ R.natDegree ≤ differentialWeightedDegree D Q - (D - d) ∧
      ∀ a, R.eval a ≠ 0 → ChainWitness Q P.polynomial a :=
  exists_chainWitness hQ (fun j ↦ jetDegreeCastsNeZero_of_ringChar (Or.inr (hchar.2 j)))
    P.equation (natDegree_le_of_degree_le P.degree_le)

end

end PolynomialDifferential
