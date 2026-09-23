/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.TaylorChartBaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for common regular centers after coefficient extension

The algebraic-closure case follows from the common-center theorem for an injective coefficient
map. A concrete nonempty family over `ZMod 2` exercises the positive theorem. Over the finite
field itself, the nonzero polynomial `X ^ 2 - X` vanishes everywhere, showing why the target
domain must be infinite.
-/

open Polynomial PolynomialDifferential

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- A regular solution over `ZMod 2` has a common regular center after embedding into its
algebraic closure. -/
example (Q : DifferentialPolynomial (ZMod 2) 0) (S : Finset ((ZMod 2)[X]))
    (hS : ∀ P ∈ S, differentialSpecialization (separant Q 0) P ≠ 0) :
    ∃ center : AlgebraicClosure (ZMod 2), ∀ P ∈ S,
      jetEvaluation
        (separant (MvPolynomial.map (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2))) Q) 0)
        center
        (polynomialJet center
          (P.map (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2))))) ≠ 0 := by
  let f : ZMod 2 →+* AlgebraicClosure (ZMod 2) := algebraMap _ _
  exact exists_forall_jetEvaluation_ne_zero_map f f.injective Q S 0 hS

/-- The nonempty family containing zero has a common regular center after extending scalars. -/
example :
    let Q : DifferentialPolynomial (ZMod 2) 0 :=
      (MvPolynomial.X none ^ 2 - MvPolynomial.X none) * MvPolynomial.X (some 0)
    ∃ center : AlgebraicClosure (ZMod 2),
      ∀ P ∈ ({(0 : (ZMod 2)[X])} : Finset ((ZMod 2)[X])),
        jetEvaluation
          (separant
            (MvPolynomial.map (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2))) Q) 0)
          center
          (polynomialJet center
            (P.map (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2))))) ≠ 0 := by
  intro Q
  have hspec : differentialSpecialization (separant Q 0) (0 : (ZMod 2)[X]) =
      (Polynomial.X ^ 2 - Polynomial.X : (ZMod 2)[X]) := by
    simp [Q, separant, differentialSpecialization, differentialSpecializationHom]
  have hspec_ne : differentialSpecialization (separant Q 0) (0 : (ZMod 2)[X]) ≠ 0 := by
    rw [hspec]
    intro h
    have hc := congrArg (fun P : (ZMod 2)[X] ↦ P.coeff 2) h
    norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  have hregular : ∀ P ∈ ({(0 : (ZMod 2)[X])} : Finset ((ZMod 2)[X])),
      differentialSpecialization (separant Q 0) P ≠ 0 := by
    intro P hP
    have hP0 : P = 0 := Finset.mem_singleton.mp hP
    subst P
    exact hspec_ne
  let f : ZMod 2 →+* AlgebraicClosure (ZMod 2) := algebraMap _ _
  exact exists_forall_jetEvaluation_ne_zero_map f f.injective Q {0} 0 hregular

/-- The finite-field equation with separant `X ^ 2 - X` has no regular center, since every
element of `ZMod 2` is a root. -/
example :
    let Q : DifferentialPolynomial (ZMod 2) 0 :=
      (MvPolynomial.X none ^ 2 - MvPolynomial.X none) * MvPolynomial.X (some 0)
    differentialSpecialization (separant Q 0) (0 : (ZMod 2)[X]) ≠ 0 ∧
      ¬ ∃ center : ZMod 2,
        jetEvaluation (separant Q 0) center (polynomialJet center (0 : (ZMod 2)[X])) ≠ 0 := by
  intro Q
  have hspec : differentialSpecialization (separant Q 0) (0 : (ZMod 2)[X]) =
      (Polynomial.X ^ 2 - Polynomial.X : (ZMod 2)[X]) := by
    simp [Q, separant, differentialSpecialization, differentialSpecializationHom]
  have heval (center : ZMod 2) :
      jetEvaluation (separant Q 0) center (polynomialJet center (0 : (ZMod 2)[X])) =
        (Polynomial.X ^ 2 - Polynomial.X : (ZMod 2)[X]).eval center := by
    rw [← eval_differentialSpecialization, hspec]
  constructor
  · rw [hspec]
    intro h
    have hc := congrArg (fun P : (ZMod 2)[X] ↦ P.coeff 2) h
    norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · rintro ⟨center, hcenter⟩
    rw [heval] at hcenter
    have hval : center.val < 2 := center.val_lt
    have hcases : center.val = 0 ∨ center.val = 1 := by omega
    rcases hcases with hzero | hone
    · have hc : center = 0 := by
        rw [← ZMod.natCast_zmod_val center, hzero]
        norm_num
      subst center
      exact hcenter (by
        rw [Polynomial.eval_sub, Polynomial.eval_X_pow, Polynomial.eval_X]
        norm_num)
    · have hc : center = 1 := by
        rw [← ZMod.natCast_zmod_val center, hone]
        norm_num
      subst center
      exact hcenter (by
        rw [Polynomial.eval_sub, Polynomial.eval_X_pow, Polynomial.eval_X]
        norm_num)
