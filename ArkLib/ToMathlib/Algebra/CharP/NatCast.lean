/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Int.Cast.Basic

/-!
# Natural numbers that stay nonzero up to a bound

A ring has no small vanishing counts up to L when no natural number in 1, ..., L casts to zero.

Characteristic zero gives it for every L, and characteristic p gives it for every L below p.

Counts up to L then inject into the ring.
-/

@[expose] public section

variable (R : Type*) [AddGroupWithOne R]

/-- No natural number from 1 to L casts to zero in R. -/
def NatCastNeZeroUpTo (L : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n ≤ L → (n : R) ≠ 0

namespace NatCastNeZeroUpTo

variable {R}

/-- A smaller bound inherits the property. -/
theorem mono {L L' : ℕ} (h : NatCastNeZeroUpTo R L) (hL : L' ≤ L) : NatCastNeZeroUpTo R L' :=
  fun n hn hnL => h n hn (hnL.trans hL)

/-- Counts up to the bound inject into R. -/
theorem natCast_inj {L : ℕ} (h : NatCastNeZeroUpTo R L) {a b : ℕ} (ha : a ≤ L) (hb : b ≤ L)
    (hab : (a : R) = b) : a = b := by
  rcases le_total a b with hle | hle
  · by_contra hne
    exact h (b - a) (by omega) (by omega) (by rw [Nat.cast_sub hle, hab, sub_self])
  · by_contra hne
    exact h (a - b) (by omega) (by omega) (by rw [Nat.cast_sub hle, hab, sub_self])

variable (R)

/-- In characteristic p, every bound below p works. -/
theorem of_lt (p : ℕ) [CharP R p] {L : ℕ} (hL : L < p) : NatCastNeZeroUpTo R L :=
  fun n hn hnL h => absurd (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff R p n).1 h)) (by omega)

/-- In characteristic zero, every bound works. -/
theorem of_charZero [CharZero R] (L : ℕ) : NatCastNeZeroUpTo R L :=
  fun _ hn _ => Nat.cast_ne_zero.2 hn.ne'

end NatCastNeZeroUpTo
