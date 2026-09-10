/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.Combinatorics.CubicStaircase
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# A quadratic lower bound for staircase counts

Choosing a nonnegative exponent `u<L` leaves `D*(L-u)` possible values of another
integer exponent. The strict cutoff rounds upward. Summing these slots dominates
the triangular area `D*(max L 0)^2/2`, with no limiting argument or error term.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace QuadraticStaircase

/-- The number of pairs below a strict weighted cutoff. -/
def count (D : ℕ) (cutoff : ℝ) : ℕ :=
  ∑ exponent ∈ Finset.range ⌈cutoff⌉₊, ⌈(D : ℝ) * (cutoff - exponent)⌉₊

/-- A slot records the unweighted exponent and its remaining weighted exponent. -/
def Slot (D : ℕ) (L : ℝ) :=
  Σ s : Fin ⌈L⌉₊, Fin ⌈(D : ℝ) * (L - s.val)⌉₊

instance (D : ℕ) (L : ℝ) : Fintype (Slot D L) :=
  inferInstanceAs (Fintype (Σ s : Fin ⌈L⌉₊, Fin ⌈(D : ℝ) * (L - s.val)⌉₊))

/-- The dependent slot count is the displayed finite sum. -/
theorem card_slot (D : ℕ) (L : ℝ) : Fintype.card (Slot D L) = count D L := by
  change Fintype.card (Σ s : Fin ⌈L⌉₊, Fin ⌈(D : ℝ) * (L - s.val)⌉₊) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun s ↦ ⌈(D : ℝ) * (L - s)⌉₊) ⌈L⌉₊

/-- Decode a slot as the weighted and unweighted exponents. -/
def Slot.exponents {D : ℕ} {L : ℝ} (a : Slot D L) : ℕ × ℕ :=
  (a.2.val, a.1.val)

/-- Slot coordinates uniquely determine the slot. -/
theorem Slot.exponents_injective (D : ℕ) (L : ℝ) :
    Function.Injective (Slot.exponents (D := D) (L := L)) := by
  rintro ⟨s, x⟩ ⟨t, y⟩ h
  have hs : s = t := Fin.ext (congrArg Prod.snd h)
  subst t
  exact congrArg (Sigma.mk s) (Fin.ext (congrArg Prod.fst h))

/-- Every represented pair satisfies the strict cutoff. -/
theorem Slot.weighted_degree_lt {D : ℕ} {L : ℝ} (a : Slot D L) :
    (a.exponents.1 : ℝ) + D * a.exponents.2 < D * L := by
  have hx : (a.2.val : ℝ) < (D : ℝ) * (L - a.1.val) := Nat.lt_ceil.mp a.2.isLt
  dsimp [Slot.exponents]
  linarith

/-- The unrounded residual sum is an exact quadratic polynomial. -/
theorem two_mul_sum (endpoint : ℕ) (cutoff : ℝ) :
    2 * (∑ exponent ∈ Finset.range endpoint, (cutoff - (exponent : ℝ))) =
      (endpoint : ℝ) * (2 * cutoff - endpoint + 1) := by
  induction endpoint with
  | zero => simp
  | succ endpoint ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith only [ih]

/-- Integer rounding of the endpoint does not reduce the triangular area. -/
theorem square_div_two_le_sum {cutoff : ℝ} (hcutoff : 0 < cutoff) :
    cutoff ^ 2 / 2 ≤
      ∑ exponent ∈ Finset.range ⌈cutoff⌉₊, (cutoff - (exponent : ℝ)) := by
  have hlower := Nat.le_ceil cutoff
  have hupper := (Nat.ceil_lt_add_one hcutoff.le).le
  have hproduct : 0 ≤ ((⌈cutoff⌉₊ : ℝ) - cutoff) *
      (cutoff + 1 - (⌈cutoff⌉₊ : ℝ)) := mul_nonneg (by linarith) (by linarith)
  have hsum := two_mul_sum ⌈cutoff⌉₊ cutoff
  nlinarith

/-- The positive-part quadratic area is a lower bound for the finite count. -/
theorem count_ge_quadratic (D : ℕ) (cutoff : ℝ) :
    (D : ℝ) * (max cutoff 0) ^ 2 / 2 ≤ count D cutoff := by
  by_cases hcutoff : 0 < cutoff
  · rw [max_eq_left hcutoff.le]
    have harea := mul_le_mul_of_nonneg_left (square_div_two_le_sum hcutoff)
      (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
    calc
      (D : ℝ) * cutoff ^ 2 / 2 ≤
          D * ∑ exponent ∈ Finset.range ⌈cutoff⌉₊, (cutoff - (exponent : ℝ)) := by
            simpa [mul_div_assoc] using harea
      _ = ∑ exponent ∈ Finset.range ⌈cutoff⌉₊, (D : ℝ) * (cutoff - exponent) :=
        Finset.mul_sum ..
      _ ≤ ∑ exponent ∈ Finset.range ⌈cutoff⌉₊,
          (⌈(D : ℝ) * (cutoff - exponent)⌉₊ : ℝ) :=
        Finset.sum_le_sum fun _ _ ↦ Nat.le_ceil _
      _ = count D cutoff := by simp [count]
  · rw [max_eq_right (le_of_not_gt hcutoff)]
    simp

end QuadraticStaircase
