/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.LinearCombination

/-!
# Agreement of two lines at all but finitely many parameters

Let `a, b, c, d : ι → K` be families in a field `K`, and consider the two lines
`z ↦ a i + z * b i` and `z ↦ c i + z * d i` at each index `i`. For a fixed `z` they can agree at
`i` without `a i = c i` and `b i = d i` only when `b i ≠ d i` and `z = (c i - a i) / (b i - d i)`.
So on a finite set `s` of indices, outside at most `#{i ∈ s | b i ≠ d i}` values of `z`, the lines
agree at `i ∈ s` exactly when both coefficients agree. Indices with `b i = d i` contribute no
exceptional value: there the lines agree for one `z` exactly when they agree for all.

## Main statements

* `Finset.exists_card_le_forall_add_mul_eq_add_mul_iff`: the exceptional set and its size.
-/

@[expose] public section

namespace Finset

/-- Outside a set of at most `#{i ∈ s | b i ≠ d i}` parameters `z`, the lines `a i + z * b i` and
`c i + z * d i` agree at `i ∈ s` exactly when `a i = c i` and `b i = d i`. The bound is attained
when the values `(c i - a i) / (b i - d i)` over the indices with `b i ≠ d i` are distinct. -/
theorem exists_card_le_forall_add_mul_eq_add_mul_iff {K ι : Type*} [Field K] [DecidableEq K]
    (s : Finset ι) (a b c d : ι → K) :
    ∃ exceptional : Finset K, exceptional.card ≤ #{i ∈ s | b i ≠ d i} ∧
      ∀ z ∉ exceptional, ∀ i ∈ s, a i + z * b i = c i + z * d i ↔ a i = c i ∧ b i = d i := by
  refine ⟨{i ∈ s | b i ≠ d i}.image fun i ↦ (c i - a i) / (b i - d i), card_image_le, ?_⟩
  intro z hz i hi
  refine ⟨fun h ↦ ?_, fun ⟨hac, hbd⟩ ↦ by rw [hac, hbd]⟩
  by_cases hbd : b i = d i
  · rw [hbd] at h
    exact ⟨add_right_cancel h, hbd⟩
  · refine absurd (mem_image.mpr ⟨i, mem_filter.mpr ⟨hi, hbd⟩, ?_⟩) hz
    rw [div_eq_iff (sub_ne_zero.mpr hbd)]
    linear_combination -h

end Finset
