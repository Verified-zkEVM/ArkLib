/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Multiplicity

/-!
# Acceptance tests for global vanishing at agreeing polynomials

* With `D = 1`, `d = 0`, `A = 2`, `m = 1` and `M = W = 0`, the polynomial `Y₀ - r` lies in the
  exact space and satisfies the order-one constraints at every point `(a, r)`. The theorem then
  says that a polynomial of degree at most `1` equal to `r` at two distinct points of `ℤ` is the
  constant `r`.
* With `A = 0` the theorem holds without any positivity hypothesis, since the exact space is `{0}`.
* The source statement over a field, with its hypothesis `0 < m * A`, is an instance.
* The weighted-degree form: `Y₀ - r` has weighted degree `1 < 1 * 2` at `D = 1`, and the local
  constraints are only needed on the two agreement indices.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

private theorem hdD₀₁ : (0 : ℕ) < 1 := by decide

/-- `Y₀ - r` satisfies the multiplicity-one constraints at `(center, r)`. -/
private theorem satisfiesLocalConstraints_one_Y_zero_sub (center r : ℤ) :
    SatisfiesLocalConstraints (d := 0) 1 center r (X (some 0) - C r) := by
  rw [SatisfiesLocalConstraints, localConstraintAt, LinearMap.comp_apply, projectLowContact,
    weightedTruncation_eq_zero_iff]
  have h : (unscaledLocalSubstitution 0 center r).toLinearMap (X (some 0) - C r) =
      X (localT 0) * (X (localE 0) + localJetSum 0) := by
    simp only [AlgHom.toLinearMap_apply, map_sub, unscaledLocalSubstitution_Y_zero, algHom_C,
      algebraMap_eq, mul_add, T_mul_localJetSum]
    ring
  rw [h]
  simpa using mul_mem_restrictWeightedOrder
    (X_mem_restrictWeightedOrder (R := ℤ) (localContactWeight 0) (localT 0) le_rfl)
    (by simp : X (localE 0) + localJetSum 0 ∈
      restrictWeightedOrder (R := ℤ) (localContactWeight 0) 0)

/-- `Y₀ - r` has specialization weight `1 < 1 * 2` and lies in the exact space. -/
private theorem Y_zero_sub_mem (r : ℤ) :
    (X (some 0) - C r : DifferentialPolynomial ℤ 0) ∈
      exactInterpolationSpace ℤ 1 2 0 1 0 0 hdD₀₁ := by
  refine Submodule.sub_mem _ ?_ ?_
  · rw [X, monomial_mem_exactInterpolationSpace]
    left
    simp [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight,
      Finsupp.weight_single, jetFirstWeight, jetHigherWeight, differentialWeight]
  · rw [← monomial_zero', monomial_mem_exactInterpolationSpace]
    left
    simp [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight]

/-- A polynomial over `ℤ` of degree at most `1` that equals `r` at `a ≠ b` is the constant `r`. -/
example (P : Polynomial ℤ) (hP : P.natDegree ≤ 1) (r a b : ℤ) (hab : a ≠ b)
    (ha : P.eval a = r) (hb : P.eval b = r) : P = Polynomial.C r := by
  have h := differentialSpecialization_eq_zero_of_mem_exactInterpolationSpace_of_agreements
    hdD₀₁ id (fun _ ↦ r) {a, b} (Y_zero_sub_mem r)
    (fun i ↦ satisfiesLocalConstraints_one_Y_zero_sub i r) P hP (Set.injOn_id _)
    (by rw [Finset.card_pair hab]) (fun i hi ↦ by
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ha
      · rw [Finset.mem_singleton.mp hi]; exact hb)
  rw [← sub_eq_zero]
  simpa [differentialSpecialization, differentialSpecializationHom] using h

/-- With `A = 0` no agreement and no positivity hypothesis is needed. -/
example (Q : DifferentialPolynomial ℤ 0) (hQ : Q ∈ exactInterpolationSpace ℤ 1 0 0 1 0 0 hdD₀₁)
    (hconstraints : ∀ i : ℤ, SatisfiesLocalConstraints 1 i 0 Q) (P : Polynomial ℤ)
    (hP : P.natDegree ≤ 1) : differentialSpecialization Q P = 0 :=
  differentialSpecialization_eq_zero_of_mem_exactInterpolationSpace_of_agreements hdD₀₁ id
    (fun _ ↦ 0) ∅ hQ hconstraints P hP (by simp) (by simp) (by simp)

/-- Source shape: the statement over a field with the hypothesis `0 < m * A`. -/
example {ι F : Type*} [Field F] {D A d m M W : ℕ} (_hbudget : 0 < m * A) (hdD : d < D)
    (points received : ι → F) (indices : Finset ι) {Q : DifferentialPolynomial F d}
    (hQspace : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (points i) (received i) Q)
    (P : Polynomial F) (hPdegree : P.natDegree ≤ D) (hpoints : Set.InjOn points (indices : Set ι))
    (hcard : A ≤ indices.card) (hagreements : ∀ i ∈ indices, P.eval (points i) = received i) :
    differentialSpecialization Q P = 0 :=
  differentialSpecialization_eq_zero_of_mem_exactInterpolationSpace_of_agreements hdD points
    received indices hQspace hconstraints P hPdegree hpoints hcard hagreements

/-- `Y₀ - r` has weighted degree at most `1` at ambient degree `1`. -/
private theorem differentialWeightedDegree_Y_zero_sub_le (r : ℤ) :
    differentialWeightedDegree 1 (X (some 0) - C r : DifferentialPolynomial ℤ 0) ≤ 1 := by
  rw [differentialWeightedDegree, ← mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
  refine Submodule.sub_mem _ (X_mem_restrictWeightedDegree _ _ _ ?_) ?_
  · simp [differentialWeight]
  · rw [mem_restrictWeightedDegree_iff_weightedTotalDegree_le, weightedTotalDegree_C]
    exact Nat.zero_le _

/-- The weighted-degree form: a polynomial over `ℤ` of degree at most `1` that equals `r` at
`a ≠ b` is the constant `r`, with the constraints required only at `a` and `b`. -/
example (P : Polynomial ℤ) (hP : P.natDegree ≤ 1) (r a b : ℤ) (hab : a ≠ b)
    (ha : P.eval a = r) (hb : P.eval b = r) : P = Polynomial.C r := by
  have h := differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt (D := 1) (A := 2)
    (m := 1) id (fun _ ↦ r) {a, b} ((differentialWeightedDegree_Y_zero_sub_le r).trans_lt
      (by decide))
    (fun i _ ↦ satisfiesLocalConstraints_one_Y_zero_sub i r) P hP (Set.injOn_id _)
    (by rw [Finset.card_pair hab]) (fun i hi ↦ by
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ha
      · rw [Finset.mem_singleton.mp hi]; exact hb)
  rw [← sub_eq_zero]
  simpa [differentialSpecialization, differentialSpecializationHom] using h
