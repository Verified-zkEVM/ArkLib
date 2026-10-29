/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Basic

/-! # Cyclic product accumulators

A normalized cyclic recurrence equates the two products without cancellation. When denominator
factors are nonzero, prefix products of ratios construct a normalized accumulator.
-/

@[expose] public section

namespace CyclicProduct

open scoped BigOperators

section Monoid

variable {R : Type*} [CommMonoid R]

/-- The prefix invariant of a normalized multiplicative recurrence, without cancellation. -/
theorem prefix_invariant (N Q z : ℕ → R) (n : ℕ) (h0 : z 0 = 1)
    (hstep : ∀ i < n, z (i + 1) * Q i = z i * N i) {i : ℕ} (hi : i ≤ n) :
    z i * (∏ j ∈ Finset.range i, Q j) = ∏ j ∈ Finset.range i, N j := by
  induction i with
  | zero => simp [h0]
  | succ i ih =>
    have hin : i < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi
    have hip : i ≤ n := Nat.le_of_lt hin
    calc
      z (i + 1) * (∏ j ∈ Finset.range (i + 1), Q j) =
          (z (i + 1) * Q i) * (∏ j ∈ Finset.range i, Q j) := by
        rw [Finset.prod_range_succ]
        ac_rfl
      _ = (z i * N i) * (∏ j ∈ Finset.range i, Q j) := by rw [hstep i hin]
      _ = (z i * (∏ j ∈ Finset.range i, Q j)) * N i := by ac_rfl
      _ = (∏ j ∈ Finset.range i, N j) * N i := by rw [ih hip]
      _ = ∏ j ∈ Finset.range (i + 1), N j := (Finset.prod_range_succ N i).symm

/-- A normalized cyclic recurrence equates the products even when factors or accumulator
values vanish. -/
theorem products_eq (N Q z : ℕ → R) (n : ℕ) (h0 : z 0 = 1)
    (hstep : ∀ i < n, z (i + 1) * Q i = z i * N i) (hn : z n = 1) :
    (∏ j ∈ Finset.range n, N j) = ∏ j ∈ Finset.range n, Q j := by
  simpa [hn] using (prefix_invariant N Q z n h0 hstep (Nat.le_refl n)).symm

end Monoid

section Field

variable {F : Type*} [Field F]

/-- The executable prefix product of numerator-to-denominator ratios. -/
def ratioPrefix (N Q : ℕ → F) (i : ℕ) : F :=
  ∏ j ∈ Finset.range i, N j / Q j

/-- The empty prefix is normalized. -/
@[simp]
theorem ratioPrefix_zero (N Q : ℕ → F) : ratioPrefix N Q 0 = 1 := by
  simp [ratioPrefix]

/-- Extending a prefix appends the next ratio. -/
theorem ratioPrefix_succ (N Q : ℕ → F) (i : ℕ) :
    ratioPrefix N Q (i + 1) = ratioPrefix N Q i * (N i / Q i) := by
  exact Finset.prod_range_succ (fun j => N j / Q j) i

/-- A prefix product of ratios is the ratio of prefix products. -/
theorem ratioPrefix_eq_prod_div (N Q : ℕ → F) (i : ℕ) :
    ratioPrefix N Q i =
      (∏ j ∈ Finset.range i, N j) / (∏ j ∈ Finset.range i, Q j) := by
  exact Finset.prod_div_distrib N Q

/-- Nonzero denominator factors give the multiplicative recurrence for honest prefixes. -/
theorem ratioPrefix_recurrence (N Q : ℕ → F) (i : ℕ) (hQ : Q i ≠ 0) :
    ratioPrefix N Q (i + 1) * Q i = ratioPrefix N Q i * N i := by
  rw [ratioPrefix_succ, mul_assoc, div_mul_cancel₀ _ hQ]

/-- Equal total products and nonzero denominator factors close the honest accumulator. -/
theorem ratioPrefix_end (N Q : ℕ → F) (n : ℕ) (hQ : ∀ i < n, Q i ≠ 0)
    (heq : (∏ j ∈ Finset.range n, N j) = ∏ j ∈ Finset.range n, Q j) :
    ratioPrefix N Q n = 1 := by
  rw [ratioPrefix_eq_prod_div, heq]
  exact div_self (Finset.prod_ne_zero_iff.mpr fun i hi => hQ i (Finset.mem_range.mp hi))

end Field

end CyclicProduct
