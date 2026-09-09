/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Support counts for symbolic interpolation

The integer budgets below give the non-Cartesian support used in BCHKS25, Lemma 3.1.
For the paper's real strict degree bounds, the budgets are their natural ceilings.
Indices are ordered as `⟨j, (i, h)⟩`: outer Y, middle X, inner Z in `F[Z][X][Y]`.
This module counts unknowns and scalar equations only; it does not assert the numerical
surplus or construct an interpolating polynomial.

## References

- [BCHKS25] Eli Ben-Sasson, Dan Carmon, Ulrich Haböck, Swastik Kopparty, and Shubhangi Saraf.
  On Proximity Gaps for Reed--Solomon Codes. Cryptology ePrint Archive, Paper 2025/2055,
  Lemma 3.1. https://eprint.iacr.org/2025/2055
-/

namespace Polynomial.SymbolicInterpolation

open Finset

/-- Monomials with `i + k*j < dx`, `j < dy`, and `j + h < dz`. -/
def monomialSupport (k dx dy dz : ℕ) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (range dy).sigma fun j => (range (dx - k * j)) ×ˢ (range (dz - j))

/-- The support inequalities expose the semantic X, Y, and Z axes. -/
@[simp] theorem mem_monomialSupport (k dx dy dz i j h : ℕ) :
    ⟨j, (i, h)⟩ ∈ monomialSupport k dx dy dz ↔
      j < dy ∧ i + k * j < dx ∧ j + h < dz := by
  simp only [monomialSupport, mem_sigma, mem_range, mem_product]
  omega

/-- Exact unknown count, including truncated rows when a budget is small. -/
theorem card_monomialSupport (k dx dy dz : ℕ) :
    (monomialSupport k dx dy dz).card =
      ∑ j ∈ range dy, (dx - k * j) * (dz - j) := by
  simp [monomialSupport, card_sigma]

/-- Scalar constraint indices at one interpolation point: Y-Hasse order `s`, X-Hasse
order `r`, and Z-coefficient `d`. The degree budget drops by `s`. -/
def constraintSupport (m dz : ℕ) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (range m).sigma fun s => (range (m - s)) ×ˢ (range (dz - s))

/-- The Hasse order is strictly below the requested multiplicity. -/
@[simp] theorem mem_constraintSupport (m dz r s d : ℕ) :
    ⟨s, (r, d)⟩ ∈ constraintSupport m dz ↔ r + s < m ∧ d + s < dz := by
  simp only [constraintSupport, mem_sigma, mem_range, mem_product]
  omega

/-- Exact per-point scalar equation count. -/
theorem card_constraintSupport (m dz : ℕ) :
    (constraintSupport m dz).card = ∑ s ∈ range m, (dz - s) * (m - s) := by
  simp [constraintSupport, card_sigma, Nat.mul_comm]

/-- Multiplying by the number of points gives the full scalar equation count. -/
theorem card_pointConstraints (n m dz : ℕ) :
    ((range n) ×ˢ constraintSupport m dz).card =
      n * ∑ s ∈ range m, (dz - s) * (m - s) := by
  simp [card_constraintSupport]

private theorem six_mul_sum (a b : ℤ) (m : ℕ) :
    6 * (∑ s ∈ range m, (a - s) * (b - s)) =
      6 * a * b * m - 3 * (a + b) * m * (m - 1) + m * (m - 1) * (2 * m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- The paper's exact equation count without division or truncated subtraction:
`6 E + m³ = 3 dz m (m+1) + m`. The hypothesis ensures every Hasse row has
the untruncated coefficient budget used by the closed formula. -/
theorem six_mul_card_constraintSupport (m dz : ℕ) (hm : m ≤ dz) :
    6 * (constraintSupport m dz).card + m ^ 3 = 3 * dz * m * (m + 1) + m := by
  have hsum := six_mul_sum (dz : ℤ) (m : ℤ) m
  have hcast : ((constraintSupport m dz).card : ℤ) =
      ∑ s ∈ range m, ((dz : ℤ) - s) * ((m : ℤ) - s) := by
    rw [card_constraintSupport, Nat.cast_sum]
    apply sum_congr rfl
    intro s hs
    have hsm : s ≤ m := Nat.le_of_lt (mem_range.mp hs)
    rw [Nat.cast_mul, Nat.cast_sub (hsm.trans hm), Nat.cast_sub hsm]
  have h : (6 : ℤ) * (constraintSupport m dz).card + (m : ℤ) ^ 3 =
      3 * dz * m * (m + 1) + m := by
    rw [hcast]
    nlinarith [hsum]
  exact_mod_cast h

end Polynomial.SymbolicInterpolation
