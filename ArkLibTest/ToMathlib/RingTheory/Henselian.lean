/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.ToMathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Acceptance cases for Hensel's lemma without monicity, with uniqueness -/

open PowerSeries

-- The non-monic `X U² - U + 1` has a root over `ℤ⟦X⟧` lifting `1` modulo `X`.
example : ∃ a : PowerSeries ℤ,
    (Polynomial.C X * Polynomial.X ^ 2 - Polynomial.X + 1 : Polynomial (PowerSeries ℤ)).IsRoot a ∧
      a - 1 ∈ Ideal.span {X} := by
  refine IsAdicComplete.exists_isRoot_sub_mem _ 1 ?_ ?_
  · simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, one_pow, mul_one,
      sub_add_cancel]
    exact Ideal.subset_span rfl
  · have : (Polynomial.derivative (Polynomial.C X * Polynomial.X ^ 2 - Polynomial.X + 1 :
        Polynomial (PowerSeries ℤ))).eval 1 = -1 + 2 * X := by
      simp [Polynomial.derivative_mul]
      ring
    rw [this]
    refine IsUnit.map _ (isUnit_iff_constantCoeff.mpr ?_)
    simp

-- The lift of `1` is unique, whatever the root found by the Newton iteration.
example (a b : PowerSeries ℤ)
    (ha : (Polynomial.C X * Polynomial.X ^ 2 - Polynomial.X + 1 :
      Polynomial (PowerSeries ℤ)).IsRoot a) (ha₁ : a - 1 ∈ Ideal.span {X})
    (hb : (Polynomial.C X * Polynomial.X ^ 2 - Polynomial.X + 1 :
      Polynomial (PowerSeries ℤ)).IsRoot b) (hb₁ : b - 1 ∈ Ideal.span {X}) : a = b := by
  refine Polynomial.eq_of_isRoot_of_sub_mem (IsAdicComplete.le_jacobson _) ?_ ha ha₁ hb hb₁
  have : (Polynomial.derivative (Polynomial.C X * Polynomial.X ^ 2 - Polynomial.X + 1 :
      Polynomial (PowerSeries ℤ))).eval 1 = -1 + 2 * X := by
    simp [Polynomial.derivative_mul]
    ring
  rw [this]
  refine IsUnit.map _ (isUnit_iff_constantCoeff.mpr ?_)
  simp

-- The Jacobson hypothesis cannot be dropped from `Polynomial.eq_of_isRoot_of_sub_mem`.
-- Over `ZMod 6` with `I = (3)`, the polynomial `2X` has the distinct roots `0` and `3`.
-- They agree modulo `I`, and `f'(0) = 2` is a unit modulo `I`.
example :
    let I : Ideal (ZMod 6) := Ideal.span {3}
    let f : Polynomial (ZMod 6) := Polynomial.C 2 * Polynomial.X
    IsUnit (Ideal.Quotient.mk I (f.derivative.eval 0)) ∧ f.IsRoot 0 ∧ (0 - 0 : ZMod 6) ∈ I ∧
      f.IsRoot 3 ∧ (3 - 0 : ZMod 6) ∈ I ∧ (0 : ZMod 6) ≠ 3 := by
  intro I f
  have h3 : (3 : ZMod 6) ∈ I := Ideal.mem_span_singleton_self 3
  refine ⟨?_, by simp [f], by simp, ?_, by simpa using h3, by decide⟩
  · refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I 2) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    have h : (f.derivative.eval 0 * 2 - 1 : ZMod 6) = 3 := by
      simp only [f, Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_one, Polynomial.eval_zero]
      decide
    rw [h]
    exact h3
  · simp only [f, Polynomial.IsRoot.def, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    decide

-- The lemma recovers the Henselian property of adically complete rings.
example {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] : HenselianRing R I :=
  ⟨IsAdicComplete.le_jacobson I,
    fun f _ a₀ h₁ h₂ ↦ IsAdicComplete.exists_isRoot_sub_mem f a₀ h₁ h₂⟩

/--
info: 'IsAdicComplete.exists_isRoot_sub_mem' depends on axioms: [propext, Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsAdicComplete.exists_isRoot_sub_mem

/--
info: 'Polynomial.eq_of_isRoot_of_sub_mem' depends on axioms: [propext, Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.eq_of_isRoot_of_sub_mem

/--
info: 'IsAdicComplete.existsUnique_isRoot_sub_mem' depends on axioms: [propext, Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsAdicComplete.existsUnique_isRoot_sub_mem
