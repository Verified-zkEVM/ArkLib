/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Finset.WeightedSimplex.Moments

/-!
# Acceptance cases for exact moments of the unit-weight simplex

These cases compare the moment identities with direct enumeration, check budgets zero and one,
show that the mixed moment needs distinct coordinates, use an index type other than `Fin`, and
derive the special cases over `Fin r` with the stars-and-bars binomial.
-/

open Finset

/-- Marking the second of three units in coordinate `true` moves one unit to the new `none`
coordinate and removes the mark, leaving one unit in coordinate `true`. -/
example : natSimplexSplit true (fun b : Bool ↦ if b then 3 else 1) 1 =
    fun k ↦ k.elim 1 (fun b ↦ if b then 1 else 1) := by
  decide

/-- Direct enumeration of the first moment for `σ = Fin 2`, `S = 3`: the ten points have
coordinate-zero total `10`. -/
example : ∑ c ∈ natWeightedSimplex (fun _ : Fin 2 ↦ 1) 3, c 0 = 10 := by
  decide

/-- The same value from the first-moment identity and stars and bars: `3 * x = 3 * 10`. -/
example : ∑ c ∈ natWeightedSimplex (fun _ : Fin 2 ↦ 1) 3, c 0 = 10 := by
  have h := card_add_one_mul_sum_natWeightedSimplex_one_apply (0 : Fin 2) 3
  rw [card_natWeightedSimplex_one] at h
  simp only [Fintype.card_fin] at h
  norm_num [Nat.choose] at h
  omega

/-- The first moment at budget `S + 1` equals a simplex count one dimension higher, here
`#(Δ_{Option Bool} 2) = (2 + 3).choose 3 = 10`. -/
example : ∑ c ∈ natWeightedSimplex (fun _ : Bool ↦ 1) 3, c true = 10 := by
  rw [sum_natWeightedSimplex_one_apply_succ, card_natWeightedSimplex_one]
  decide

/-- Mixed moment on `Bool` at `S = 3`: `3 * 4 * x = 3 * 2 * 10`, so `x = 5`, matching direct
enumeration. -/
example : ∑ c ∈ natWeightedSimplex (fun _ : Bool ↦ 1) 3, c true * c false = 5 := by
  have h := card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_mul_of_ne
    (show true ≠ false by decide) 3
  rw [card_natWeightedSimplex_one] at h
  simp only [Fintype.card_bool] at h
  norm_num [Nat.choose] at h
  omega

example : ∑ c ∈ natWeightedSimplex (fun _ : Bool ↦ 1) 3, c true * c false = 5 := by
  decide

/-- Falling-factorial moment on `Bool` at `S = 3`: `3 * 4 * x = 2 * 3 * 2 * 10`, so `x = 10`. -/
example : ∑ c ∈ natWeightedSimplex (fun _ : Bool ↦ 1) 3, c true * (c true - 1) = 10 := by
  have h := card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_mul_pred true 3
  rw [card_natWeightedSimplex_one] at h
  simp only [Fintype.card_bool] at h
  norm_num [Nat.choose] at h
  omega

example : ∑ c ∈ natWeightedSimplex (fun _ : Bool ↦ 1) 3, c true * (c true - 1) = 10 := by
  decide

/-- At budget one every coordinate is `0` or `1`, so the falling-factorial moment vanishes, as the
identity's factor `S - 1` predicts. -/
example : ∑ c ∈ natWeightedSimplex (fun _ : Fin 3 ↦ 1) 1, c 0 * (c 0 - 1) = 0 := by
  have h := card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_mul_pred (0 : Fin 3) 1
  simp only [Nat.sub_self, mul_zero, zero_mul] at h
  exact (Nat.mul_eq_zero.mp h).resolve_left (by simp)

/-- At budget zero the first moment vanishes. -/
example (i : Fin 4) : ∑ c ∈ natWeightedSimplex (fun _ : Fin 4 ↦ 1) 0, c i = 0 := by
  have h := card_add_one_mul_sum_natWeightedSimplex_one_apply i 0
  simp only [zero_mul] at h
  exact (Nat.mul_eq_zero.mp h).resolve_left (by simp)

/-- The distinctness hypothesis of the mixed moment is necessary: on one coordinate at `S = 1`,
the left side `2 * 3 * 1` is nonzero while `S * (S - 1) * C` is zero. -/
example : ¬ ((Fintype.card Unit + 1) * (Fintype.card Unit + 2) *
    ∑ c ∈ natWeightedSimplex (fun _ : Unit ↦ 1) 1, c () * c () =
      1 * (1 - 1) * (natWeightedSimplex (fun _ : Unit ↦ 1) 1).card) := by
  decide

/-- The first moment over `Fin r`, stated with the stars-and-bars count. -/
example (r S : ℕ) (i : Fin r) :
    (r + 1) * ∑ c ∈ natWeightedSimplex (fun _ : Fin r ↦ 1) S, c i = S * (S + r).choose r := by
  simpa [card_natWeightedSimplex_one] using
    card_add_one_mul_sum_natWeightedSimplex_one_apply i S

/-- The mixed and factorial moments over `Fin r`. -/
example (r S : ℕ) (i j : Fin r) (hij : i ≠ j) :
    (r + 1) * (r + 2) * ∑ c ∈ natWeightedSimplex (fun _ : Fin r ↦ 1) S, c i * c j =
      S * (S - 1) * (S + r).choose r := by
  simpa [card_natWeightedSimplex_one] using
    card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_mul_of_ne hij S

example (r S : ℕ) (i : Fin r) :
    (r + 1) * (r + 2) * ∑ c ∈ natWeightedSimplex (fun _ : Fin r ↦ 1) S, c i * (c i - 1) =
      2 * S * (S - 1) * (S + r).choose r := by
  simpa [card_natWeightedSimplex_one] using
    card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_mul_pred i S

/-- The weighted second moment over `ℤ` for weights `(1, -1)` on `Bool` at `S = 2`: the formula
gives `3 * 4 * x = (0 + 2 * 5 * 2) * 6`, so `x = 10`. -/
example : ∑ c ∈ natWeightedSimplex (fun _ : Bool ↦ 1) 2,
    ((c true : ℤ) - (c false : ℤ)) ^ 2 = 10 := by
  decide

example : ∑ c ∈ natWeightedSimplex (fun _ : Bool ↦ 1) 2,
    ((c true : ℤ) - (c false : ℤ)) ^ 2 = 10 := by
  have h := card_add_one_mul_card_add_two_mul_sum_natWeightedSimplex_one_weighted_sq
    (fun b : Bool ↦ if b then (1 : ℤ) else -1) 2
  rw [card_natWeightedSimplex_one] at h
  simp only [Fintype.card_bool, Fintype.sum_bool] at h
  norm_num [Nat.choose] at h
  simp only [← sub_eq_add_neg] at h
  omega
