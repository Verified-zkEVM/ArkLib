/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.List.Nodup

/-!
# Explicit finite-field candidate prefixes

This file constructs duplicate-free parameter lists without enumerating an
entire field.  The prime-field prefix consists of the casts of
`0, ..., bound - 1`; it is duplicate-free whenever `bound` does not exceed the
characteristic.
-/

namespace ArkLib.FiniteFieldCandidates

/-- The first `bound` elements of the prime subfield, in their natural order. -/
def primeFieldPrefix (F : Type*) [AddMonoidWithOne F] (bound : ℕ) : List F :=
  (List.range bound).map fun i : ℕ ↦ (i : F)

@[simp]
theorem length_primeFieldPrefix (F : Type*) [AddMonoidWithOne F] (bound : ℕ) :
    (primeFieldPrefix F bound).length = bound := by
  simp [primeFieldPrefix]

/-- Natural casts below the characteristic are distinct. -/
theorem nodup_primeFieldPrefix_of_le_char
    (F : Type*) [AddMonoidWithOne F] [IsRightCancelAdd F]
    (p bound : ℕ) [CharP F p]
    (hbound : bound ≤ p) :
    (primeFieldPrefix F bound).Nodup := by
  rw [primeFieldPrefix, List.nodup_map_iff_inj_on List.nodup_range]
  intro left hleft right hright hequal
  exact CharP.natCast_injOn_Iio F p
    (lt_of_lt_of_le (List.mem_range.mp hleft) hbound)
    (lt_of_lt_of_le (List.mem_range.mp hright) hbound) hequal

end ArkLib.FiniteFieldCandidates
