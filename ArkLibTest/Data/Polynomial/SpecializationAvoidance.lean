/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.SpecializationAvoidance
import Mathlib.Algebra.Field.ZMod

/-! Root counting through an injective map, avoidance from a finite candidate set over a small
prime field, sharpness of the candidate bound, and the infinite-domain corollary. -/

open Polynomial

namespace SpecializationAvoidanceTest

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- The case `x := C`: a nonzero `B : F[X][X]` vanishes at `C w` for at most `natDegree B` points.
example {F : Type*} [Field F] (B : F[X][X]) (hB : B ≠ 0) (S : Finset F)
    (hS : ∀ w ∈ S, B.eval (C w) = 0) : S.card ≤ B.natDegree :=
  card_le_natDegree_of_injOn_of_eval_eq_zero hB C_injective.injOn hS

/-- `(T ^ 2 - 1) * Y + 1` over `ZMod 5`. Its leading coefficient vanishes at `T = 1` and `T = 4`.
-/
noncomputable def linear5 : (ZMod 5)[X][X] := C (X ^ 2 - C 1) * X + C 1

theorem linear5_coeff_ne_zero : (X ^ 2 - C 1 : (ZMod 5)[X]) ≠ 0 :=
  (monic_X_pow_sub_C (1 : ZMod 5) two_ne_zero).ne_zero

theorem linear5_natDegree : linear5.natDegree = 1 :=
  natDegree_linear linear5_coeff_ne_zero

theorem linear5_leadingCoeff : linear5.leadingCoeff = X ^ 2 - C 1 :=
  leadingCoeff_linear linear5_coeff_ne_zero

theorem linear5_ne_zero : linear5 ≠ 0 := fun h ↦
  linear5_coeff_ne_zero (by rw [← linear5_leadingCoeff, h, leadingCoeff_zero])

-- Over `ZMod 5`, with `T := univ` and `forbidden := {0}`, the finite candidate form gives a
-- nonzero `t` that keeps the outer degree; hence `t ^ 2 ≠ 1`.
example : ∃ t : ZMod 5, t ≠ 0 ∧ t ^ 2 ≠ 1 := by
  obtain ⟨t, -, ht0, hne, hdegree⟩ :=
    exists_mem_map_evalRingHom_ne_zero_of_card_add_natDegree_lt_card linear5_ne_zero
      (T := Finset.univ) (forbidden := {0}) (by
        rw [linear5_leadingCoeff, natDegree_X_pow_sub_C]
        decide)
  refine ⟨t, by simpa using ht0, fun ht ↦ leadingCoeff_ne_zero.mpr hne ?_⟩
  have hcoeff : linear5.coeff 1 = X ^ 2 - C 1 := by
    rw [← linear5_natDegree]
    exact linear5_leadingCoeff
  rw [leadingCoeff, hdegree, linear5_natDegree, coeff_map, hcoeff, coe_evalRingHom, eval_sub,
    eval_pow, eval_X, eval_C, ht, sub_self]

-- The strict inequality cannot be weakened: for `c = T - 1` over `ZMod 3` with
-- `forbidden = {0, 2}`, `forbidden.card + c.natDegree = 3 = univ.card`, and no candidate survives.
example : ({0, 2} : Finset (ZMod 3)).card + (X - C 1 : (ZMod 3)[X]).natDegree =
      (Finset.univ : Finset (ZMod 3)).card ∧
    ¬∃ t ∈ (Finset.univ : Finset (ZMod 3)), t ∉ ({0, 2} : Finset (ZMod 3)) ∧
      (X - C 1 : (ZMod 3)[X]).eval t ≠ 0 := by
  refine ⟨by rw [natDegree_X_sub_C]; decide, ?_⟩
  rintro ⟨t, -, ht, hne⟩
  obtain rfl : t = 1 := by clear hne; revert t; decide
  simp at hne

/-- The polynomial `T * Y + 1`; its leading coefficient `T` vanishes only at `T = 0`. -/
noncomputable def canary {R : Type*} [CommRing R] : R[X][X] := C X * X + C 1

theorem canary_natDegree {R : Type*} [CommRing R] [Nontrivial R] :
    (canary : R[X][X]).natDegree = 1 :=
  natDegree_linear X_ne_zero

theorem canary_ne_zero {R : Type*} [CommRing R] [Nontrivial R] : (canary : R[X][X]) ≠ 0 :=
  fun h ↦ by simpa [h] using (canary_natDegree (R := R))

-- Over `ℚ`, avoiding `{1}` returns some `t ∉ {0, 1}`: the returned `t` keeps degree 1, which
-- fails at `t = 0`, where the canary becomes the constant `1`.
example : ∃ t : ℚ, t ≠ 0 ∧ t ≠ 1 ∧ ((canary : ℚ[X][X]).map (evalRingHom t)).natDegree = 1 := by
  obtain ⟨t, ht1, -, hdegree⟩ := exists_map_evalRingHom_ne_zero_avoiding (canary : ℚ[X][X])
    canary_ne_zero {1}
  rw [canary_natDegree] at hdegree
  refine ⟨t, fun ht0 ↦ ?_, by simpa using ht1, hdegree⟩
  subst ht0
  simp [canary] at hdegree

-- Over `ℤ`, the corollary without a forbidden set also avoids `t = 0`.
example : ∃ t : ℤ, t ≠ 0 := by
  obtain ⟨t, -, hdegree⟩ := exists_map_evalRingHom_ne_zero (canary : ℤ[X][X]) canary_ne_zero
  refine ⟨t, fun ht0 ↦ ?_⟩
  rw [canary_natDegree, ht0] at hdegree
  simp [canary] at hdegree

end SpecializationAvoidanceTest
