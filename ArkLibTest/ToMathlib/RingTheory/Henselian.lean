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
  refine Polynomial.eq_of_isRoot_of_sub_mem (IsAdicComplete.le_jacobson _) _ ?_ ha ha₁ hb hb₁
  have : (Polynomial.derivative (Polynomial.C X * Polynomial.X ^ 2 - Polynomial.X + 1 :
      Polynomial (PowerSeries ℤ))).eval 1 = -1 + 2 * X := by
    simp [Polynomial.derivative_mul]
    ring
  rw [this]
  refine IsUnit.map _ (isUnit_iff_constantCoeff.mpr ?_)
  simp

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
