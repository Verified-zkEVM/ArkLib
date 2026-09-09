/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Global.Multiplicity
import Mathlib.Algebra.Field.ZMod
/-!
# Canaries for global polynomial multiplicity

The examples use the nonconsecutive points `1` and `4` in `ZMod 7`. They protect local
injectivity, the strict degree inequality, and the satisfiable zero boundaries of the
`WithBot`-valued degree theorem.
-/

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential

noncomputable section

open Polynomial

local instance globalMultiplicityPrimeSeven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

private def nonconsecutivePoints : Fin 2 ↪ ZMod 7 where
  toFun i := if i = 0 then 1 else 4
  inj' := by decide

/-- The natural-degree theorem specializes to two nonconsecutive double roots. Supplying
`hpoints` and `hdegree` by name pins the injectivity and strictness boundaries of the API. -/
example {W : (ZMod 7)[X]}
    (hdiv : ∀ i : Fin 2, (X - C (nonconsecutivePoints i)) ^ 2 ∣ W)
    (hdegree : W.natDegree < 4) :
    W = 0 := by
  exact Polynomial.eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
    (points := nonconsecutivePoints) (indices := Finset.univ)
    (multiplicity := 2) (requiredPoints := 2)
    (hpoints := nonconsecutivePoints.injective.injOn) (hcard := by simp)
    (hdiv := by simpa using hdiv) (hdegree := by simpa using hdegree)

private def threeNonconsecutivePoints : Fin 3 ↪ ZMod 7 where
  toFun i := if i = 0 then 1 else if i = 1 then 4 else 6
  inj' := by decide

private def exactVanishingEquation : DifferentialPolynomial (ZMod 7) 0 :=
  MvPolynomial.X (some 0) - MvPolynomial.X none

private theorem exactVanishingEquation_mem :
    exactVanishingEquation ∈
      exactInterpolationSpace (ZMod 7) 1 2 0 1 0 0 (by omega) := by
  apply Submodule.sub_mem
  · rw [MvPolynomial.X]
    apply monomial_mem_exactInterpolationSpace.mpr
    exact Or.inl (by
      simp [ExactInterpolationEligibleExponent, firstJetExponent,
        fullHigherJetWeight, exactInterpolationMonomialWeight, Finsupp.weight_single])
  · rw [MvPolynomial.X]
    apply monomial_mem_exactInterpolationSpace.mpr
    exact Or.inl (by
      simp [ExactInterpolationEligibleExponent, firstJetExponent,
        fullHigherJetWeight, exactInterpolationMonomialWeight, Finsupp.weight_single])

private theorem unscaledLocalSubstitution_exactVanishingEquation (center : ZMod 7) :
    unscaledLocalSubstitution 0 center center exactVanishingEquation =
      MvPolynomial.X (localT 0) * MvPolynomial.X (localE 0) -
        MvPolynomial.X (localT 0) := by
  simp [exactVanishingEquation, localCorrection]

private theorem exactVanishingEquation_satisfies (center : ZMod 7) :
    SatisfiesLocalConstraints 1 center center exactVanishingEquation := by
  rw [SatisfiesLocalConstraints, localConstraintAt, LinearMap.comp_apply]
  change projectLowContact (R := ZMod 7) (d := 0) 1
    (unscaledLocalSubstitution 0 center center exactVanishingEquation) = 0
  rw [unscaledLocalSubstitution_exactVanishingEquation, projectLowContact_eq_zero_iff]
  intro e he
  simp only [MvPolynomial.X]
  rw [MvPolynomial.monomial_mul,
    MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_monomial]
  split_ifs with h₁ h₂
  · subst e
    simp [localContactOrder, Finsupp.weight_single] at he
  · subst e
    simp [localContactOrder, Finsupp.weight_single] at he
  · subst e
    simp [localContactOrder, Finsupp.weight_single] at he
  · rfl

/-- Full I6 composition over three nonconsecutive agreement points while only two are required.
The nonzero equation `Y₀ - X` satisfies the exact interpolation support and every local
constraint for the received word `received = points`; specialization at `P = X` is therefore
zero. This protects the orientation `requiredPoints ≤ indices.card` in the composed theorem. -/
example :
    exactVanishingEquation ≠ 0 ∧
      differentialSpecialization exactVanishingEquation
        (Polynomial.X : (ZMod 7)[X]) = 0 := by
  constructor
  · intro hzero
    have hcoeff := congrArg
      (MvPolynomial.coeff (Finsupp.single (some (0 : Fin 1)) 1)) hzero
    simp [exactVanishingEquation] at hcoeff
  · apply differentialSpecialization_eq_zero_of_mem_exactInterpolationSpace_of_agreements
        (D := 1) (A := 2) (m := 1) (M := 0) (W := 0)
        (hbudget := by omega) (hdD := by omega)
        (points := threeNonconsecutivePoints) (received := threeNonconsecutivePoints)
        (indices := Finset.univ) (hQspace := exactVanishingEquation_mem)
        (hconstraints := fun i ↦ exactVanishingEquation_satisfies
          (threeNonconsecutivePoints i))
        (P := Polynomial.X) (hPdegree := by simp)
        (hpoints := threeNonconsecutivePoints.injective.injOn)
        (hcard := by simp)
    intro i _hi
    simp

private def exactBoundaryPolynomial : (ZMod 7)[X] :=
  (X - C 1) ^ 2 * (X - C 4) ^ 2

/-- Strictness is necessary: the product of the two prescribed squared factors is nonzero and
has degree exactly the total multiplicity. -/
example :
    exactBoundaryPolynomial ≠ 0 ∧
      exactBoundaryPolynomial.natDegree = 4 ∧
      ∀ i : Fin 2,
        (X - C (nonconsecutivePoints i)) ^ 2 ∣ exactBoundaryPolynomial := by
  constructor
  · exact (((monic_X_sub_C (1 : ZMod 7)).pow 2).mul
      ((monic_X_sub_C (4 : ZMod 7)).pow 2)).ne_zero
  constructor
  · rw [exactBoundaryPolynomial,
      natDegree_mul (pow_ne_zero 2 (X_sub_C_ne_zero 1))
        (pow_ne_zero 2 (X_sub_C_ne_zero 4)),
      natDegree_pow, natDegree_pow, natDegree_X_sub_C, natDegree_X_sub_C]
  · intro i
    fin_cases i <;> simp [nonconsecutivePoints, exactBoundaryPolynomial]

private def collidingPoints (_i : Fin 2) : ZMod 7 := 1

private def collisionPolynomial : (ZMod 7)[X] :=
  (X - C 1) ^ 2

/-- Injectivity is necessary: counting the same double root twice would incorrectly claim total
multiplicity four for this nonzero quadratic. -/
example :
    ¬Set.InjOn collidingPoints (Finset.univ : Finset (Fin 2)) ∧
      (∀ i : Fin 2, (X - C (collidingPoints i)) ^ 2 ∣ collisionPolynomial) ∧
      collisionPolynomial.natDegree < 4 ∧ collisionPolynomial ≠ 0 := by
  constructor
  · intro hinjective
    have hzero_one : (0 : Fin 2) = 1 := hinjective (by simp) (by simp) rfl
    simp at hzero_one
  constructor
  · intro i
    simp [collidingPoints, collisionPolynomial]
  constructor
  · rw [collisionPolynomial, natDegree_pow, natDegree_X_sub_C]
    omega
  · exact ((monic_X_sub_C (1 : ZMod 7)).pow 2).ne_zero

/-- Empty agreement data and zero required points remain satisfiable for the zero polynomial when
the `WithBot`-valued degree formulation is used. -/
example {F : Type*} [Field F] (points : Empty → F) :
    (0 : F[X]) = 0 := by
  apply Polynomial.eq_zero_of_degree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
      points ∅ 5 0
  · simp
  · simp
  · simp
  · simp

/-- Zero multiplicity is likewise a valid boundary for the zero polynomial in the degree
formulation, even with a positive required-point count. -/
example : (0 : (ZMod 7)[X]) = 0 := by
  apply Polynomial.eq_zero_of_degree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
      nonconsecutivePoints Finset.univ 0 2
  · exact nonconsecutivePoints.injective.injOn
  · simp
  · simp
  · simp

end

end ReedSolomon.HiddenDerivative
