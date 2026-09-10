/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryWordSemantics

/-!
# Canonical binary word bounds

These proof-side lemmas relate physical width to numeric value for canonical words. They do not
pad, normalize, construct shape tapes, or perform any runtime conversion.
-/

@[expose] public section

namespace Computation.BinaryWordMachine

/-- Removing a low bit preserves the absence of high zero padding. -/
theorem Canonical.tail {x : Bool} {xs : Word} (h : Canonical (x :: xs)) : Canonical xs := by
  cases xs with
  | nil => exact Or.inl rfl
  | cons y ys =>
    rcases h with h | h
    · cases h
    · exact Or.inr (by simpa using h)

/-- A nonempty canonical word has a true highest bit, which gives a numeric lower bound. -/
theorem Canonical.leading_bound (xs : Word) (h : Canonical xs) (hn : xs ≠ []) :
    2 ^ xs.length ≤ 2 * value xs := by
  induction xs with
  | nil => exact (hn rfl).elim
  | cons x xs ih =>
    cases xs with
    | nil =>
      rcases h with h | h
      · cases h
      · have hx : x = true := by simpa using h
        subst x
        decide
    | cons y ys =>
      have ht := ih h.tail (by simp)
      simp only [List.length_cons, Nat.pow_succ, value] at ht ⊢
      omega

/-- Canonical nonempty counters are strictly positive, so a literal decrement progresses. -/
theorem Canonical.value_pos (xs : Word) (h : Canonical xs) (hn : xs ≠ []) : 0 < value xs := by
  have hb := h.leading_bound xs hn
  have hp : 0 < 2 ^ xs.length := Nat.pow_pos (by decide)
  omega

/-- A reduced canonical scalar fits within the physical width of its modulus. -/
theorem Canonical.width_le_of_value_lt (xs ys : Word) (h : Canonical xs)
    (hv : value xs < value ys) : xs.length ≤ ys.length := by
  by_cases hn : xs = []
  · simp [hn]
  · have hb := h.leading_bound xs hn
    have hy := value_lt_width ys
    have hp : 2 ^ xs.length < 2 ^ (ys.length + 1) := by
      rw [Nat.pow_succ]
      omega
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hp
    omega

end Computation.BinaryWordMachine
