/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
import Mathlib.FieldTheory.Finite.Extension

/-!
# Reed–Solomon agreement acceptance tests

Concrete examples compute agreement sets over `ZMod 2` and its degree-two extension, including a
boundary case where a noninjective coefficient map creates agreement.
-/

noncomputable section

open Polynomial ReedSolomon

private abbrev E₄ := FiniteField.Extension (ZMod 2) 2 2
local instance : DecidableEq E₄ := Classical.decEq _

private def repeatedDomain : Fin 3 → ZMod 2 := fun i => if i.val = 1 then 1 else 0

private def twoPointDomain : Fin 2 ↪ ZMod 2 where
  toFun i := i.val
  inj' := by
    intro i j hij
    apply Fin.ext
    have hval : i.val % 2 = j.val % 2 := by
      simpa [ZMod.val_natCast] using congrArg ZMod.val hij
    simpa [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hval

@[simp] private theorem twoPointDomain_apply (i : Fin 2) :
    twoPointDomain i = (i.val : ZMod 2) := rfl

/-- The polynomial `X` agrees with zero at the first of two evaluation points, over the base
field and its degree-two extension. -/
example :
    polynomialAgreementSet twoPointDomain (fun _ ↦ 0) (X : (ZMod 2)[X]) = {0} ∧
      polynomialAgreementSet
        (twoPointDomain.trans
          ⟨algebraMap (ZMod 2) E₄, (algebraMap (ZMod 2) E₄).injective⟩)
        (fun _ ↦ algebraMap (ZMod 2) E₄ (0 : ZMod 2))
        ((X : (ZMod 2)[X]).map (algebraMap (ZMod 2) E₄)) = {0} ∧
      polynomialAgreementSet
        (twoPointDomain.trans
          ⟨algebraMap (ZMod 2) E₄, (algebraMap (ZMod 2) E₄).injective⟩)
        (fun _ ↦ algebraMap (ZMod 2) E₄ (0 : ZMod 2))
        ((X : (ZMod 2)[X]).map (algebraMap (ZMod 2) E₄)) =
          polynomialAgreementSet twoPointDomain (fun _ ↦ 0) (X : (ZMod 2)[X]) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [polynomialAgreementSet, Polynomial.eval_X]
  · ext i
    fin_cases i <;> simp [polynomialAgreementSet, Polynomial.eval_X]
  · exact polynomialAgreementSet_map twoPointDomain (algebraMap (ZMod 2) E₄)
      (algebraMap (ZMod 2) E₄).injective (fun _ ↦ 0) (X : (ZMod 2)[X])

/-- A noninjective coefficient map can create agreement: reducing `2 * X` modulo two creates
agreement at the point `1` that was absent over the integers. -/
example :
    (polynomialAgreementSet (⟨fun _ : Fin 1 ↦ (1 : ℤ), fun _ _ _ ↦ Subsingleton.elim _ _⟩)
      (fun _ ↦ 0) (2 * X : ℤ[X])).card = 0 ∧
      (polynomialAgreementSet
        (⟨fun _ : Fin 1 ↦ (1 : ZMod 2), fun _ _ _ ↦ Subsingleton.elim _ _⟩)
        (fun _ ↦ 0)
        ((2 * X : ℤ[X]).map (Int.castRingHom (ZMod 2)))).card = 1 := by
  constructor
  · have hset :
        polynomialAgreementSet
          (⟨fun _ : Fin 1 ↦ (1 : ℤ), fun _ _ _ ↦ Subsingleton.elim _ _⟩)
          (fun _ ↦ 0) (2 * X : ℤ[X]) = ∅ := by
      ext i
      constructor
      · intro hi
        rw [mem_polynomialAgreementSet] at hi
        have hei : i = 0 := Subsingleton.elim _ _
        subst i
        change (2 * X : ℤ[X]).eval 1 = 0 at hi
        norm_num [Polynomial.eval_mul] at hi
      · intro hi
        simp at hi
    simp [hset]
  · have hmap : ((2 * X : ℤ[X]).map (Int.castRingHom (ZMod 2))) = 0 := by
      simp [CharTwo.two_eq_zero]
    rw [hmap]
    simp [polynomialAgreementSet]

/-- Agreement counts are preserved on a finite indexed domain with repeated evaluation points. -/
example :
    (Finset.univ.filter fun i : Fin 3 =>
      (X : (ZMod 2)[X]).eval (repeatedDomain i) = (0 : ZMod 2)).card = 2 ∧
      (Finset.univ.filter fun i : Fin 3 =>
        ((X : (ZMod 2)[X]).map (algebraMap (ZMod 2) E₄)).eval
            (algebraMap (ZMod 2) E₄ (repeatedDomain i)) = (0 : E₄)).card = 2 := by
  have hsource : (Finset.univ.filter fun i : Fin 3 =>
      (X : (ZMod 2)[X]).eval (repeatedDomain i) = (0 : ZMod 2)).card = 2 := by
    have hset : (Finset.univ.filter fun i : Fin 3 =>
        (X : (ZMod 2)[X]).eval (repeatedDomain i) = (0 : ZMod 2)) = {0, 2} := by
      ext i
      fin_cases i <;> norm_num [Polynomial.eval_X, repeatedDomain]
    rw [hset]
    norm_num
  refine ⟨hsource, ?_⟩
  simpa [Polynomial.eval_X] using
    (card_polynomialAgreement_map (algebraMap (ZMod 2) E₄)
      (algebraMap (ZMod 2) E₄).injective repeatedDomain
      (fun _ ↦ 0) X).trans hsource

/-- Injectivity is necessary: reducing `2 * X` from `ℤ` modulo two creates one agreement at `1`.
-/
example :
    (Finset.univ.filter fun _i : Fin 1 =>
      (2 * X : ℤ[X]).eval (1 : ℤ) = (0 : ℤ)).card = 0 ∧
      (Finset.univ.filter fun _i : Fin 1 =>
        ((2 * X : ℤ[X]).map (Int.castRingHom (ZMod 2))).eval (1 : ZMod 2) =
          (0 : ZMod 2)).card = 1 := by
  constructor
  · norm_num [Polynomial.eval_mul]
  · have hmap : ((2 * X : ℤ[X]).map (Int.castRingHom (ZMod 2))) = 0 := by
      simp [CharTwo.two_eq_zero]
    rw [hmap]
    simp
