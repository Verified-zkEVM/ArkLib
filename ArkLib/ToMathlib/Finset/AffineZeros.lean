/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Zeros of a nonzero affine function of two variables

Let `a`, `b`, `c` be elements of a finite field with `q` elements, not all zero.
Then the map `(x, y) ↦ a + x b + y c` vanishes at most `q` times.
This is the degree-one, two-variable case of the Schwartz–Zippel count.

When `c ≠ 0`, each `x` fixes `y`.
When `c = 0` and `b ≠ 0`, the value of `x` is fixed.
When only `a ≠ 0`, there is no zero at all.

## Main statements

* `Finset.card_filter_add_mul_add_mul_eq_zero_le`: the zero count is at most `q`.
-/

@[expose] public section

namespace Finset

/-- A nonzero affine function of two variables has at most `q` zeros.

The coefficients `a`, `b`, `c` lie in a finite field with `q` elements and are not all zero.
Then `a + x b + y c = 0` has at most `q` solutions `(x, y)`. -/
theorem card_filter_add_mul_add_mul_eq_zero_le {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] {a b c : K} (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    #{x : K × K | a + x.1 * b + x.2 * c = 0} ≤ Fintype.card K := by
  by_cases hc : c = 0
  · subst hc
    by_cases hb : b = 0
    · subst hb
      have ha : a ≠ 0 := by simpa using h
      simp [ha]
    · refine (card_le_card (t := univ.image fun y : K ↦ (-a / b, y))
        fun x hx ↦ mem_image.mpr ⟨x.2, mem_univ _, ?_⟩).trans card_image_le
      have hx := (mem_filter.mp hx).2
      ext
      · field_simp
        linear_combination -hx
      · rfl
  · refine (card_le_card (t := univ.image fun y : K ↦ (y, -(a + y * b) / c))
      fun x hx ↦ mem_image.mpr ⟨x.1, mem_univ _, ?_⟩).trans card_image_le
    have hx := (mem_filter.mp hx).2
    ext
    · rfl
    · field_simp
      linear_combination -hx

end Finset
