/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite sums over shifted natural-number ranges

`Finset.sumRangeFrom f start length` sums `f` on the half-open natural interval beginning at
`start`. The splitting and substitution lemmas let large executable calculations be checked in
bounded modules and then assembled without unfolding the already checked chunks.
-/

@[expose] public section

namespace Finset

variable {α : Type*} [AddCommMonoid α]

/-- Sum `f` over `start, ..., start + length - 1`. -/
def sumRangeFrom (f : ℕ → α) (start length : ℕ) : α :=
  ∑ i ∈ range length, f (start + i)

/-- Split a shifted range sum into adjacent chunks. -/
theorem sumRangeFrom_add (f : ℕ → α) (start a b : ℕ) :
    sumRangeFrom f start (a + b) =
      sumRangeFrom f start a + sumRangeFrom f (start + a) b := by
  simp only [sumRangeFrom, sum_range_add]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [Nat.add_assoc]

/-- Combine four adjacent shifted range sums. -/
theorem sumRangeFrom_four (f : ℕ → α) (start a b c d : ℕ) :
    sumRangeFrom f start (a + b + c + d) =
      sumRangeFrom f start a + sumRangeFrom f (start + a) b +
        sumRangeFrom f (start + a + b) c +
          sumRangeFrom f (start + a + b + c) d := by
  rw [show a + b + c + d = a + (b + c + d) by omega, sumRangeFrom_add,
    show b + c + d = b + (c + d) by omega, sumRangeFrom_add, sumRangeFrom_add]
  simp only [add_assoc]

/-- Substitute four checked adjacent chunk values without unfolding their sums. -/
theorem sumRangeFrom_four_eq (f : ℕ → α) (start a b c d : ℕ) (va vb vc vd : α)
    (ha : sumRangeFrom f start a = va)
    (hb : sumRangeFrom f (start + a) b = vb)
    (hc : sumRangeFrom f (start + a + b) c = vc)
    (hd : sumRangeFrom f (start + a + b + c) d = vd) :
    sumRangeFrom f start (a + b + c + d) = va + vb + vc + vd :=
  (sumRangeFrom_four f start a b c d).trans
    (congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ha hb) hc) hd)

/-- Substitute two checked adjacent chunk values without unfolding their sums. -/
theorem sumRangeFrom_two_eq (f : ℕ → α) (start a b : ℕ) (va vb : α)
    (ha : sumRangeFrom f start a = va)
    (hb : sumRangeFrom f (start + a) b = vb) :
    sumRangeFrom f start (a + b) = va + vb :=
  (sumRangeFrom_add f start a b).trans (congrArg₂ (· + ·) ha hb)

end Finset
