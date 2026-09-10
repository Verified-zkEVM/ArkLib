/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Explicit harmonic estimates

Finite rational sums and telescoping midpoint tails bound harmonic power sums uniformly in the
endpoint. The logarithmic estimate is extracted from the monotone Euler–Mascheroni sequence.
These estimates are independent of any coding-theory support or concentration argument.
-/

@[expose] public section

open scoped BigOperators

namespace Real

private theorem reciprocal_square_tail_step (n : ℕ) :
    (1 / (n + 1 : ℝ)) ^ 2 + 2 / (2 * (n + 1 : ℝ) + 1) ≤ 2 / (2 * (n : ℝ) + 1) := by
  have h₁ : (0 : ℝ) < n + 1 := by positivity
  have h₂ : (0 : ℝ) < 2 * (n + 1 : ℝ) + 1 := by positivity
  have h₃ : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  field_simp
  nlinarith

private theorem reciprocal_square_initial :
    (∑ i ∈ Finset.range 12, (1 / (i + 1 : ℝ)) ^ 2) + 2 / 25 < 329 / 200 := by
  norm_num [Finset.sum_range_succ]

/-- A twelve-term rational calculation and a midpoint telescoping tail bound the second
harmonic sum. The tail estimate is valid for every dimension, including zero. -/
theorem reciprocal_square_sum_lt (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / (i + 1 : ℝ)) ^ 2) < 329 / 200 := by
  by_cases hn : 12 ≤ n
  · have hbound : ∀ k, 12 ≤ k →
        (∑ i ∈ Finset.range k, (1 / (i + 1 : ℝ)) ^ 2) + 2 / (2 * (k : ℝ) + 1) ≤
          (∑ i ∈ Finset.range 12, (1 / (i + 1 : ℝ)) ^ 2) + 2 / 25 := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => norm_num
      | succ k hk ih =>
        rw [Finset.sum_range_succ]
        push_cast
        have h := reciprocal_square_tail_step k
        linarith
    have h := hbound n hn
    have hp : (0 : ℝ) < 2 / (2 * (n : ℝ) + 1) := by positivity
    linarith [reciprocal_square_initial]
  · have hsum : (∑ i ∈ Finset.range n, (1 / (i + 1 : ℝ)) ^ 2) ≤
        ∑ i ∈ Finset.range 12, (1 / (i + 1 : ℝ)) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega)) (fun _ _ _ ↦ sq_nonneg _)
    linarith [reciprocal_square_initial]

private theorem reciprocal_cube_tail_step (n : ℕ) :
    (1 / (n + 1 : ℝ)) ^ 3 + 2 / (2 * (n + 1 : ℝ) + 1) ^ 2 ≤
      2 / (2 * (n : ℝ) + 1) ^ 2 := by
  have h₁ : (0 : ℝ) < n + 1 := by positivity
  have h₂ : (0 : ℝ) < 2 * (n + 1 : ℝ) + 1 := by positivity
  have h₃ : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  field_simp
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) ^ 2 by positivity,
    show (0 : ℝ) ≤ (n : ℝ) ^ 3 by positivity]

private theorem reciprocal_cube_initial :
    (∑ i ∈ Finset.range 12, (1 / (i + 1 : ℝ)) ^ 3) + 2 / (25 : ℝ) ^ 2 <
      12021 / 10000 := by
  norm_num [Finset.sum_range_succ]

/-- A twelve-term rational calculation and a midpoint telescoping tail bound the third
harmonic power sum. -/
theorem reciprocal_cube_sum_lt (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / (i + 1 : ℝ)) ^ 3) < 12021 / 10000 := by
  by_cases hn : 12 ≤ n
  · have hbound : ∀ k, 12 ≤ k →
        (∑ i ∈ Finset.range k, (1 / (i + 1 : ℝ)) ^ 3) +
            2 / (2 * (k : ℝ) + 1) ^ 2 ≤
          (∑ i ∈ Finset.range 12, (1 / (i + 1 : ℝ)) ^ 3) + 2 / (25 : ℝ) ^ 2 := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => norm_num
      | succ k hk ih =>
        rw [Finset.sum_range_succ]
        push_cast
        have h := reciprocal_cube_tail_step k
        linarith
    have h := hbound n hn
    have hp : (0 : ℝ) < 2 / (2 * (n : ℝ) + 1) ^ 2 := by positivity
    linarith [reciprocal_cube_initial]
  · have hsum : (∑ i ∈ Finset.range n, (1 / (i + 1 : ℝ)) ^ 3) ≤
        ∑ i ∈ Finset.range 12, (1 / (i + 1 : ℝ)) ^ 3 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega)) (fun _ _ _ ↦ by positivity)
    linarith [reciprocal_cube_initial]

private theorem reciprocal_fourth_tail_step (n : ℕ) :
    (1 / (n + 1 : ℝ)) ^ 4 + 8 / (3 * (2 * (n + 1 : ℝ) + 1) ^ 3) ≤
      8 / (3 * (2 * (n : ℝ) + 1) ^ 3) := by
  have h₁ : (0 : ℝ) < n + 1 := by positivity
  have h₂ : (0 : ℝ) < 2 * (n + 1 : ℝ) + 1 := by positivity
  have h₃ : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  field_simp
  nlinarith [show (0 : ℝ) ≤ (n : ℝ)^3 by positivity,
    show (0 : ℝ) ≤ (n : ℝ)^4 by positivity]

/-- A four-term sum and a midpoint telescoping tail bound every fourth harmonic sum. -/
theorem reciprocal_fourth_sum_lt (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / (i + 1 : ℝ)) ^ 4) < 13 / 12 := by
  have hinit : (∑ i ∈ Finset.range 4, (1 / (i + 1 : ℝ)) ^ 4) +
      8 / (3 * (9 : ℝ)^3) < 13 / 12 := by norm_num [Finset.sum_range_succ]
  by_cases hn : 4 ≤ n
  · have hbound : ∀ k, 4 ≤ k →
        (∑ i ∈ Finset.range k, (1 / (i + 1 : ℝ)) ^ 4) +
          8 / (3 * (2 * (k : ℝ) + 1)^3) ≤
        (∑ i ∈ Finset.range 4, (1 / (i + 1 : ℝ)) ^ 4) + 8 / (3 * (9 : ℝ)^3) := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => norm_num
      | succ k hk ih =>
        rw [Finset.sum_range_succ]
        push_cast
        have h := reciprocal_fourth_tail_step k
        linarith
    have h := hbound n hn
    have hp : (0 : ℝ) < 8 / (3 * (2 * (n : ℝ) + 1)^3) := by positivity
    linarith
  · have hsum : (∑ i ∈ Finset.range n, (1 / (i + 1 : ℝ)) ^ 4) ≤
        ∑ i ∈ Finset.range 4, (1 / (i + 1 : ℝ)) ^ 4 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega)) (fun _ _ _ ↦ by positivity)
    linarith

/-- The first eight terms give the strict lower bound used by finite variance estimates. -/
theorem reciprocal_square_sum_gt {n : ℕ} (hn : 8 ≤ n) :
    (38 / 25 : ℝ) < ∑ i ∈ Finset.range n, (1 / (i + 1 : ℝ))^2 := by
  have hsum : (∑ i ∈ Finset.range 8, (1 / (i + 1 : ℝ))^2) ≤
      ∑ i ∈ Finset.range n, (1 / (i + 1 : ℝ))^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) (fun _ _ _ ↦ sq_nonneg _)
  have h : (38 / 25 : ℝ) < ∑ i ∈ Finset.range 8, (1 / (i + 1 : ℝ))^2 := by
    norm_num [Finset.sum_range_succ]
  exact h.trans_le hsum

/-- The harmonic upper bound used by the paper holds already from index 32. -/
theorem harmonic_le_log_add_three_fifths (n : ℕ) (hn : 32 ≤ n) :
    (harmonic n : ℝ) ≤ Real.log n + 3 / 5 := by
  have hbase : Real.eulerMascheroniSeq' 32 < 3 / 5 := by
    have hlog : Real.log (32 : ℝ) = 5 * Real.log 2 := by
      have h := Real.log_pow (2 : ℝ) 5
      norm_num at h
      exact h
    rw [Real.eulerMascheroniSeq']
    norm_num only [OfNat.ofNat_ne_zero, ↓reduceIte]
    rw [hlog]
    have htwo := Real.log_two_gt_d9
    norm_num [harmonic, Finset.sum_range_succ] at *
    linarith
  have hmono := (Real.strictAnti_eulerMascheroniSeq'.antitone hn).trans_lt hbase
  have hn0 : n ≠ 0 := by omega
  simp only [Real.eulerMascheroniSeq', hn0, ↓reduceIte] at hmono
  linarith

/-- The shifted harmonic index in the prescribed parameters has the required logarithmic bound. -/
theorem harmonic_pred_le_log_add_three_fifths (d : ℕ) (hd : 33 ≤ d) :
    (harmonic (d - 1) : ℝ) ≤ Real.log d + 3 / 5 := by
  have h := Real.harmonic_le_log_add_three_fifths (d - 1) (by omega)
  have hp : (0 : ℝ) < (d - 1 : ℕ) := by exact_mod_cast (by omega : 0 < d - 1)
  have hle : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
  have := Real.log_le_log hp hle
  linarith

private theorem log_ten_le : Real.log 10 ≤ (47 / 20 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 47 / 20) 10
  norm_num [Finset.sum_range_succ] at h
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 10)).mpr
  linarith

/-- The harmonic logarithmic upper bound is at most `sqrt x / 10` above dimension 10000. -/
theorem log_add_three_fifths_le_sqrt_div_ten (x : ℝ) (hx : 10000 ≤ x) :
    Real.log x + 3 / 5 ≤ Real.sqrt x / 10 := by
  have hx0 : 0 < x := by linarith
  have hs : 100 ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) hx0.le]
    norm_num
    exact hx
  have hpos : 0 < Real.sqrt x / 100 := by positivity
  have h := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hx0.le] at h
  have h100 : Real.log 100 ≤ (47 / 10 : ℝ) := by
    have he : (100 : ℝ) = 10 ^ 2 := by norm_num
    rw [he, Real.log_pow]
    nlinarith [log_ten_le]
  linarith

end Real
