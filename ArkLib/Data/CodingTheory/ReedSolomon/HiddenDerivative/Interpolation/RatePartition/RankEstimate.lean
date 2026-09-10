/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Rank
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Lattice.ScaledLattice
public import ArkLib.ToMathlib.Analysis.ExponentialStaircase

/-!
# Finite lattice estimates for the partition rank

The integer simplex sandwich bounds the actual derivative tuple count.
The shift is the sum of all d positive derivative weights.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open scoped BigOperators

/-- The anisotropic tuple count obeys the exact integer volume sandwich. -/
theorem ratePartitionTupleCount_factorial_sandwich (d B : ℕ) :
    B ^ d ≤ ratePartitionTupleCount d B * d.factorial ^ 2 ∧
      ratePartitionTupleCount d B * d.factorial ^ 2 ≤
        (B + (d + 1) * d / 2) ^ d := by
  simpa only [ratePartitionTupleCount, ← scaledExponentCount_eq_weightedHigherJetCount,
    Nat.add_sub_cancel] using scaledExponentCount_factorial_sq_sandwich (d + 1) B

/-- The derivative-tuple count is at most the enlarged simplex volume. -/
theorem ratePartitionTupleCount_le_volume (d B : ℕ) :
    (ratePartitionTupleCount d B : ℝ) ≤
      ((B : ℝ) + (d + 1) * d / 2) ^ d / (d.factorial : ℝ) ^ 2 := by
  have h := (ratePartitionTupleCount_factorial_sandwich d B).2
  have hcast : (ratePartitionTupleCount d B : ℝ) * (d.factorial : ℝ) ^ 2 ≤
      ((B : ℝ) + (((d + 1) * d / 2 : ℕ) : ℝ)) ^ d := by exact_mod_cast h
  have hdiv : (((d + 1) * d / 2 : ℕ) : ℝ) ≤ ((d : ℝ) + 1) * d / 2 := by
    have hh := Nat.div_mul_le_self ((d + 1) * d) 2
    have hh' : (((d + 1) * d / 2 : ℕ) : ℝ) * 2 ≤ ((d : ℝ) + 1) * d := by
      exact_mod_cast hh
    linarith
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (d.factorial : ℝ) ^ 2)).mpr
  exact hcast.trans (pow_le_pow_left₀ (by positivity) (by linarith) d)

/-- A finite rounded rank estimate before exponential majorization. -/
theorem ratePartitionRankBound_le_power_sum (d m W : ℕ) :
    (ratePartitionRankBound d m W : ℝ) ≤
      ∑ s ∈ Finset.range m,
        ((m - s : ℕ) + d : ℝ) / (d + 1) *
          ((W : ℝ) + s + (d + 1) * d / 2) ^ d / (d.factorial : ℝ) ^ 2 := by
  rw [ratePartitionRankBound, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro s hs
  rw [Nat.cast_mul]
  have hc : (((m - s) ⌈/⌉ (d + 1) : ℕ) : ℝ) ≤
      ((m - s : ℕ) + d : ℝ) / (d + 1) := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    have hh := Nat.div_mul_le_self (m - s + d) (d + 1)
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < d + 1)).mpr
    exact_mod_cast (by simpa using hh)
  have ht := ratePartitionTupleCount_le_volume d (W + s)
  push_cast at ht
  calc
    _ ≤ (((m - s : ℕ) + d : ℝ) / (d + 1)) *
        (((W : ℝ) + s + (d + 1) * d / 2) ^ d / (d.factorial : ℝ) ^ 2) :=
      mul_le_mul hc ht (by positivity) (by positivity)
    _ = _ := by ring

/-- Enlargement of a positive simplex radius costs at most an exponential factor. -/
theorem ratePartition_power_enlargement {W x : ℝ} (hW : 0 < W) (hx : 0 ≤ x) (d : ℕ) :
    (W + x) ^ d ≤ W ^ d * Real.exp ((d : ℝ) / W * x) := by
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x / W)) hW.le
  have he' : W + x ≤ W * Real.exp (x / W) := by
    have hcancel : W * (x / W + 1) = W + x := by field_simp; ring
    rwa [hcancel] at he
  calc
    _ ≤ (W * Real.exp (x / W)) ^ d := pow_le_pow_left₀ (by positivity) he' d
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring

/-- The actual rounded rank has the finite exponential bound with no extra fixed loss. -/
theorem ratePartitionRankBound_le_exponential {d m W : ℕ}
    (hd : 0 < d) (hW : 0 < W) :
    (ratePartitionRankBound d m W : ℝ) ≤
      (W : ℝ) ^ d / (d.factorial : ℝ) ^ 2 *
        Real.exp ((d : ℝ) / W * (m + (d + 1) * d / 2)) / (d + 1) *
          ((W : ℝ) ^ 2 / d ^ 2 + (d + 1) * W / d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  let t : ℝ := d / W
  let S : ℝ := (d + 1) * d / 2
  let V : ℝ := (W : ℝ) ^ d / (d.factorial : ℝ) ^ 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hsum := Real.sum_staircase_mul_exp_le m (c := (d : ℝ)) (by positivity) ht
  have hbound : (ratePartitionRankBound d m W : ℝ) ≤
      V * Real.exp (t * S) / (d + 1) *
        (∑ s ∈ Finset.range m, ((m : ℝ) - s + d) * Real.exp (t * s)) := by
    apply (ratePartitionRankBound_le_power_sum d m W).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hsm := (Finset.mem_range.mp hs).le
    have hsm' : (s : ℝ) ≤ m := by exact_mod_cast hsm
    rw [Nat.cast_sub hsm]
    have hp := ratePartition_power_enlargement hW' (by positivity : 0 ≤ (s : ℝ) + S) d
    have hp' := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hp (sq_nonneg (d.factorial : ℝ)))
      (by positivity : 0 ≤ ((m : ℝ) - s + d) / (d + 1))
    dsimp [V, S, t] at hp' ⊢
    rw [mul_add, Real.exp_add] at hp'
    convert hp' using 1 <;> ring
  have hfinal := hbound.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  apply hfinal.trans_eq
  dsimp [V, S, t]
  rw [show (d : ℝ) / W * (m + (d + 1) * d / 2) =
    (d : ℝ) / W * ((d + 1) * d / 2) + (d : ℝ) / W * m by ring,
    Real.exp_add]
  field_simp
  ring

end ReedSolomon.HiddenDerivative
