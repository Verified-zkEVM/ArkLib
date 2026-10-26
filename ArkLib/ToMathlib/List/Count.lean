/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Data.List.Count

/-!
# Recovering permutations from cast multiplicities

Equality of cast key counts implies exact list permutation when the natural-number cast is
injective on the relevant counts. A length bound below an explicit characteristic supplies this
condition without assuming a finite key type or cancellation in the coefficient monoid.
-/

@[expose] public section

namespace List

/-- An injective natural-number cast preserves enough information to recover a permutation
from equality of every cast key count. -/
theorem perm_of_cast_count_eq {κ R : Type*} [DecidableEq κ] [NatCast R]
    (xs ys : List κ) (hinj : Function.Injective (Nat.cast : ℕ → R))
    (hcounts : ∀ k, (xs.count k : R) = (ys.count k : R)) : xs.Perm ys := by
  exact perm_iff_count.mpr fun k ↦ hinj (hcounts k)

/-- Below the characteristic, equality of cast counts determines exact multiplicities and
therefore permutation. Both list lengths are bounded; the ambient monoid need not be
cancellative. -/
theorem perm_of_cast_count_eq_of_length_lt_char {κ R : Type*} [DecidableEq κ]
    [AddMonoidWithOne R] (p : ℕ) [CharP R p] (xs ys : List κ)
    (hxs : xs.length < p) (hys : ys.length < p)
    (hcounts : ∀ k, (xs.count k : R) = (ys.count k : R)) : xs.Perm ys := by
  have hne : ∀ {a b : ℕ}, b < p → a < b → (a : R) ≠ (b : R) := by
    intro a b hb hab hcast
    have hpos : 0 < a + (p - b) := by omega
    have hsmall : a + (p - b) < p := by omega
    apply Nat.not_dvd_of_pos_of_lt hpos hsmall
    apply (CharP.cast_eq_zero_iff R p _).mp
    have hsum : b + (p - b) = p := by omega
    rw [Nat.cast_add, hcast, ← Nat.cast_add, hsum, CharP.cast_eq_zero]
  apply perm_iff_count.mpr
  intro k
  have hx : xs.count k < p := lt_of_le_of_lt count_le_length hxs
  have hy : ys.count k < p := lt_of_le_of_lt count_le_length hys
  rcases lt_trichotomy (xs.count k) (ys.count k) with hlt | heq | hlt
  · exact False.elim (hne hy hlt (hcounts k))
  · exact heq
  · exact False.elim (hne hx hlt (hcounts k).symm)

end List
