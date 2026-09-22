/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.FloorTransfer

/-!
# The dimension bound from a moment of the normalized coordinate sum

On the simplex `S = {u ≥ 0 : ∑_i (i + 1) u_i ≤ W}` in `Fin d → ℝ`, write the coordinate sum in
the normalized form `d ∑_i u_i / W`. If `rate W / d * logarithm ≤ level`, then pointwise

```text
(rate W / d) ^ 2 * (max (logarithm - d ∑_i u_i / W) 0) ^ 2 ≤ (max (level - rate ∑_i u_i) 0) ^ 2,
```

and integrating over `S` gives the corresponding bound on the integral of
`PartitionSupport/FloorTransfer.lean`. The volume of `S` is `W ^ d / (d!) ^ 2`
(`MeasureTheory.volume_real_weightedSimplex_succ`), so a lower bound `μ` on the average of the
normalized square over `S` gives

```text
μ / 2 * n * rate * (W / d) ^ 2 * (W ^ d / (d!) ^ 2) < dim
```

for the partition support space at a natural cutoff `L` with `level * n ≤ L`. The factor `1 / 2`
comes from the quadratic staircase bound, and no part of the simplex is discarded.

## Main statements

* `partition_square_rescale`: the pointwise comparison.
* `partition_integral_ge_normalized_moment`: the comparison of integrals over `S`.
* `partitionSupport_dimension_gt_moment`: the dimension bound from a strict lower bound `μ` on the
  average.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient Decoding
  and Smaller Cryptographic Proofs*][DKT26], Section 6.2, (73), and Appendix D.2, in the proof of
  Lemma 6.2
-/

@[expose] public section

open PolynomialDifferential Finset MeasureTheory

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {d D W : ℕ}

/-- The pointwise rescaling. Let `s = rate * radius / degree`. If `s * logarithm ≤ level`, then
`s ^ 2 * (max (logarithm - degree * total / radius) 0) ^ 2 ≤ (max (level - rate * total) 0) ^ 2`.
For positive `rate`, `radius` and `degree`, multiplying `logarithm - degree * total / radius` by
`s` gives `s * logarithm - rate * total`. If one of the three is zero, then `s = 0` and the left
side is zero. The hypothesis `0 ≤ rate` is needed: for `rate = -1`,
`radius = degree = logarithm = 1`, `level = -1` and `total = 0`, the left side is `1` and the right
side is `0`. -/
theorem partition_square_rescale {level rate radius degree logarithm total : ℝ}
    (hrate : 0 ≤ rate) (hradius : 0 ≤ radius) (hdegree : 0 ≤ degree)
    (hlevel : rate * radius / degree * logarithm ≤ level) :
    (rate * radius / degree) ^ 2 * (max (logarithm - degree * total / radius) 0) ^ 2 ≤
      (max (level - rate * total) 0) ^ 2 := by
  have hzero : rate * radius / degree = 0 →
      (rate * radius / degree) ^ 2 * (max (logarithm - degree * total / radius) 0) ^ 2 ≤
        (max (level - rate * total) 0) ^ 2 := fun h => by
    rw [h, zero_pow two_ne_zero, zero_mul]
    positivity
  rcases hrate.eq_or_lt with h | hrate
  · exact hzero (by rw [← h, zero_mul, zero_div])
  rcases hradius.eq_or_lt with h | hradius
  · exact hzero (by rw [← h, mul_zero, zero_div])
  rcases hdegree.eq_or_lt with h | hdegree
  · exact hzero (by rw [← h, div_zero])
  have hscale : 0 < rate * radius / degree := by positivity
  have hid : rate * radius / degree * (logarithm - degree * total / radius) =
      rate * radius / degree * logarithm - rate * total := by field_simp
  rw [← mul_pow, mul_max_of_nonneg _ _ hscale.le, mul_zero, hid]
  exact pow_le_pow_left₀ (by positivity) (max_le_max_right _ (by linarith)) 2

/-- The integral form of `partition_square_rescale` over the simplex
`S = {u ≥ 0 : ∑_i (i + 1) u_i ≤ W}`: for `0 ≤ rate` and `rate * W / d * logarithm ≤ level`,
`(rate * W / d) ^ 2` times the integral over `S` of `(max (logarithm - d ∑_i u_i / W) 0) ^ 2` is
at most the integral over `S` of `(max (level - rate ∑_i u_i) 0) ^ 2`. Both integrands are
continuous and `S` is compact, so no integrability hypothesis is needed. -/
theorem partition_integral_ge_normalized_moment (d W : ℕ) (level rate logarithm : ℝ)
    (hrate : 0 ≤ rate) (hlevel : rate * W / d * logarithm ≤ level) :
    (rate * W / d) ^ 2 *
        ∫ u in Set.weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) W,
          (max (logarithm - (d : ℝ) * (∑ i, u i) / W) 0) ^ 2 ≤
      ∫ u in Set.weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) W,
        (max (level - rate * ∑ i, u i) 0) ^ 2 := by
  have hpos : ∀ i : Fin d, 0 < ((i : ℝ) + 1) := fun i => by positivity
  rw [← integral_const_mul]
  refine setIntegral_mono_on ?_ ?_ (Set.measurableSet_weightedSimplex _ _) fun u _ =>
    partition_square_rescale hrate (Nat.cast_nonneg W) (Nat.cast_nonneg d) hlevel
  · exact ContinuousOn.integrableOn_weightedSimplex hpos (by fun_prop)
  · exact ContinuousOn.integrableOn_weightedSimplex hpos (by fun_prop)

/-- The dimension bound from a moment. Let `S = {u ≥ 0 : ∑_i (i + 1) u_i ≤ W}` in `Fin d → ℝ`,
of volume `W ^ d / (d!) ^ 2`. Suppose `0 < D ≤ rate * n`, `level * n ≤ L`,
`rate * W / d * logarithm ≤ level`, and the average over `S` of
`(max (logarithm - d ∑_i u_i / W) 0) ^ 2` exceeds `μ`. Then
`μ / 2 * n * rate * (W / d) ^ 2 * (W ^ d / (d!) ^ 2)` is strictly less than the dimension of the
partition support space at the natural cutoff `L`.

The hypotheses `0 < d` and `0 < W` make the scale factor positive, which the strict inequality
needs: for `W = 0` the simplex is a null set, the average is `0`, and with `μ = -1`, `L = 0` both
sides are `0`. -/
theorem partitionSupport_dimension_gt_moment (F : Type*) [Field F] {n L : ℕ}
    {rate level logarithm μ : ℝ} (hD : 0 < D) (hd : 0 < d) (hW : 0 < W)
    (hupper : (D : ℝ) ≤ rate * n) (hlevel : level * n ≤ L)
    (hscale : rate * W / d * logarithm ≤ level)
    (hmoment : μ < ⨍ u in Set.weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) W,
      (max (logarithm - (d : ℝ) * (∑ i, u i) / W) 0) ^ 2) :
    μ / 2 * n * rate * ((W : ℝ) / d) ^ 2 * ((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) <
      (Module.finrank F (partitionSupportSpace F D d W (L : ℝ) hD) : ℝ) := by
  set S := Set.weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) W
  set V : ℝ := (W : ℝ) ^ d / (d.factorial : ℝ) ^ 2
  have hrn : 0 < rate * n := (Nat.cast_pos.mpr hD).trans_le hupper
  have hrate : 0 < rate := pos_of_mul_pos_left hrn (Nat.cast_nonneg n)
  have hn : (0 : ℝ) < n := pos_of_mul_pos_right hrn hrate.le
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hWR : (0 : ℝ) < W := Nat.cast_pos.mpr hW
  have hVpos : 0 < V := by positivity
  have hvol : volume.real S = V := volume_real_weightedSimplex_succ d hWR.le
  have hint : ∫ u in S, (max (logarithm - (d : ℝ) * (∑ i, u i) / W) 0) ^ 2 =
      V * ⨍ u in S, (max (logarithm - (d : ℝ) * (∑ i, u i) / W) 0) ^ 2 := by
    rw [setAverage_eq, smul_eq_mul, hvol, ← mul_assoc, mul_inv_cancel₀ hVpos.ne', one_mul]
  have hfactor : 0 < (n : ℝ) / (2 * rate) * (rate * W / d) ^ 2 * V := by positivity
  have hstrict := mul_lt_mul_of_pos_left hmoment hfactor
  have hmono := partition_integral_ge_normalized_moment d W level rate logarithm hrate.le hscale
  rw [hint] at hmono
  have hsource := (mul_le_mul_of_nonneg_left hmono
    (show 0 ≤ (n : ℝ) / (2 * rate) by positivity)).trans
      (partitionSupport_dimension_ge_rate_integral F hD hupper hlevel)
  have hnormalize : (n : ℝ) / (2 * rate) * (rate * W / d) ^ 2 * V * μ =
      μ / 2 * n * rate * ((W : ℝ) / d) ^ 2 * V := by
    field_simp
  rw [hnormalize] at hstrict
  exact hstrict.trans_le (by simpa only [mul_assoc] using hsource)

end ReedSolomon.HiddenDerivative
