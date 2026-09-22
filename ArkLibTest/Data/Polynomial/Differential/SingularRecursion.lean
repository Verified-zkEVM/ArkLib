/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.SingularRecursion
import Mathlib.Data.ZMod.Basic

/-!
# Acceptance tests for the singular recursion

* Over `ℚ`, `P = 0` solves `Y₀ ^ 2 = 0`. `exists_regularRecursionLeaf` gives a regular leaf; an
  explicit one is the separant `2 * Y₀`, reached by one singular step, and the jet of `0` at any
  point is regular for it.
* Over `ZMod 2`, `P = 0` solves `Y₀ ^ 2 = 0` but there is no regular leaf: the cast hypothesis of
  `exists_regularRecursionLeaf` is needed.
* `X = 0` has no bounded solution, while the zero equation has one, so the terminal theorem needs
  `Q ≠ 0`.
* The source statement, with its `ringChar` bounds, follows from the general one.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-- `Y₀ ^ 2` in depth `0`, over a commutative semiring. -/
private abbrev squareEquation (F : Type) [CommSemiring F] : DifferentialPolynomial F 0 :=
  X (some 0) ^ 2

private theorem jetDegree_squareEquation (F : Type) [CommSemiring F] [Nontrivial F] :
    jetDegree (squareEquation F) 0 = 2 := by
  classical
  rw [jetDegree, squareEquation, X_pow_eq_monomial, degreeOf_monomial_eq _ _ one_ne_zero]
  simp

private theorem highestActiveJet_squareEquation (F : Type) [CommSemiring F] [Nontrivial F] :
    highestActiveJet (squareEquation F) = some 0 := by
  cases h : highestActiveJet (squareEquation F) with
  | none =>
      have := (highestActiveJet_eq_none_iff _).mp h 0
      simp [DependsOnJet, jetDegree_squareEquation] at this
  | some j => rw [Fin.fin_one_eq_zero j]

/-- `P = 0` solves `Y₀ ^ 2 = 0` over every commutative semiring. -/
private theorem differentialSpecialization_squareEquation_zero (F : Type) [CommSemiring F] :
    differentialSpecialization (squareEquation F) 0 = 0 := by
  rw [← differentialSpecializationHom_apply, map_pow, differentialSpecializationHom_apply,
    differentialSpecialization_jet, map_zero, zero_pow two_ne_zero]

/-- The separant of `Y₀ ^ 2` is `2 * Y₀`. -/
private theorem separant_squareEquation (F : Type) [CommSemiring F] :
    separant (squareEquation F) 0 = C 2 * X (some 0) := by
  have h : separant (squareEquation F) 0 = 2 * X (some 0) := by
    simp [separant, sq, pderiv_X]
    ring
  rw [h, map_ofNat C 2]

/-- The separant of `2 * Y₀` is `2`. -/
private theorem separant_separant_squareEquation (F : Type) [CommSemiring F] :
    separant (separant (squareEquation F) 0) 0 = C 2 := by
  rw [separant_squareEquation]
  simp [separant, pderiv_X]

/-! ### A regular leaf over `ℚ` -/

/-- The general theorem gives a regular leaf for `P = 0` and `Y₀ ^ 2`. -/
example : Nonempty (RegularRecursionLeaf (squareEquation ℚ) 0) :=
  exists_regularRecursionLeaf (by simp [squareEquation])
    (fun _ ↦ jetDegreeCastsNeZero_of_ringChar (Or.inl ringChar.eq_zero))
    (differentialSpecialization_squareEquation_zero ℚ)

/-- The explicit leaf: the separant `2 * Y₀`, one singular step from `Y₀ ^ 2`. -/
private def squareLeaf : RegularRecursionLeaf (squareEquation ℚ) 0 where
  equation := separant (squareEquation ℚ) 0
  activeJet := 0
  reachable := Relation.ReflTransGen.single
    (singularStep_separant _ (highestActiveJet_squareEquation ℚ))
  solves := by
    rw [separant_squareEquation, ← differentialSpecializationHom_apply, map_mul,
      differentialSpecializationHom_apply, differentialSpecializationHom_apply,
      differentialSpecialization_jet, map_zero, mul_zero]
  separantSpecialization_ne_zero := by
    rw [separant_separant_squareEquation, differentialSpecialization_C]
    simp
  highestActiveJet_eq := by
    have h : jetDegree (separant (squareEquation ℚ) 0) 0 = 1 := by
      rw [jetDegree_separant_eq_sub_one _ _ (by simp [jetDegree_squareEquation]),
        jetDegree_squareEquation]
    cases hs : highestActiveJet (separant (squareEquation ℚ) 0) with
    | none =>
        have := (highestActiveJet_eq_none_iff _).mp hs 0
        simp [DependsOnJet, h] at this
    | some j => rw [Fin.fin_one_eq_zero j]
  castsNeZero := fun _ ↦ jetDegreeCastsNeZero_of_ringChar (Or.inl ringChar.eq_zero)

/-- At every point, the jet of `0` is regular for the leaf equation `2 * Y₀`. -/
example (c : ℚ) : IsRegularJet squareLeaf.equation 0 c (polynomialJet c 0) := by
  refine squareLeaf.isRegularJet_of_eval_ne_zero c ?_
  change (differentialSpecialization (separant (separant (squareEquation ℚ) 0) 0) 0).eval c ≠ 0
  rw [separant_separant_squareEquation, differentialSpecialization_C]
  simp

/-! ### The cast hypothesis is needed -/

/-- Over `ZMod 2`, `P = 0` solves `Y₀ ^ 2 = 0` but reaches no regular leaf. Every equation reached
from `Y₀ ^ 2` is `Y₀ ^ 2` or its separant `0`, and both have separant `0`. -/
example : IsEmpty (RegularRecursionLeaf (squareEquation (ZMod 2)) 0) := by
  have hsep : separant (squareEquation (ZMod 2)) 0 = 0 := by
    rw [separant_squareEquation, show (C 2 : DifferentialPolynomial (ZMod 2) 0) = 0 by
      rw [C_eq_zero]; decide, zero_mul]
  have hreach : ∀ Q, Relation.ReflTransGen (SingularStep (F := ZMod 2) (d := 0)) Q
      (squareEquation (ZMod 2)) → Q = squareEquation (ZMod 2) ∨ Q = 0 := by
    intro Q hQ
    induction hQ using Relation.ReflTransGen.head_induction_on with
    | refl => exact Or.inl rfl
    | head hstep _ ih =>
        obtain ⟨s, hs, rfl⟩ := hstep
        rcases ih with h | h
        · rw [h, Fin.fin_one_eq_zero s, hsep]
          exact Or.inr rfl
        · rw [h] at hs ⊢
          have := (highestActiveJet_eq_none_iff (0 : DifferentialPolynomial (ZMod 2) 0)).mpr
            (by simp [DependsOnJet, jetDegree])
          rw [this] at hs
          exact absurd hs (Option.some_ne_none s).symm
  refine ⟨fun leaf ↦ leaf.separantSpecialization_ne_zero ?_⟩
  rw [Fin.fin_one_eq_zero leaf.activeJet]
  rcases hreach _ leaf.reachable with h | h <;> rw [h]
  · rw [hsep, ← differentialSpecializationHom_apply, map_zero]
  · rw [separant, map_zero, ← differentialSpecializationHom_apply, map_zero]

/-! ### Equations with no active jet -/

/-- `X = 0` has no bounded solution. -/
example : IsEmpty (BoundedSolution (X none : DifferentialPolynomial ℚ 1) 3) := by
  refine isEmpty_boundedSolution_of_highestActiveJet_eq_none (X_ne_zero _) ?_
  rw [highestActiveJet_eq_none_iff]
  intro j
  simp [DependsOnJet, jetDegree, degreeOf_X]

/-- The zero equation has the bounded solution `0`, so `Q ≠ 0` is needed above. -/
example : Nonempty (BoundedSolution (0 : DifferentialPolynomial ℚ 1) 3) :=
  ⟨⟨0, by rw [← differentialSpecializationHom_apply, map_zero]⟩⟩

/-! ### Source-shaped statement -/

/-- The source form of `exists_regularRecursionLeaf`, under `D < ringChar F` and
`jetDegree Q j < ringChar F` for every `j`. -/
example {F : Type*} [CommSemiring F] [NoZeroDivisors F] [Nontrivial F] {d D : ℕ}
    (Q : DifferentialPolynomial F d) (hQ : Q ≠ 0)
    (hchar : D < ringChar F ∧ ∀ j, jetDegree Q j < ringChar F) (P : BoundedSolution Q D) :
    Nonempty (RegularRecursionLeaf Q P.polynomial) :=
  exists_regularRecursionLeaf_of_boundedSolution hQ
    (fun j ↦ jetDegreeCastsNeZero_of_ringChar (Or.inr (hchar.2 j))) P

end

end PolynomialDifferential
