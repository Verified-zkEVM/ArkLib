/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Block
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Capacity
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.DimensionInputs
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Endpoints
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Rounding
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Surplus

/-!
# Acceptance cases for weighted-support parameters

Concrete instances exercise the block, capacity, rounding, scalar, dimension and endpoint bounds.
-/

open ReedSolomon ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-! ### Block parameters -/

/-- At `δ = 1 / 4`, `n = 48`, `k = 10` the hypotheses hold with equality in `12 ≤ δ n`
(`⌈δ n⌉₊ = 12` and `10 + 12 ≤ 48`); here `K = max 10 6 = 10` and `D = 9`. -/
example :
    let K := max 10 ⌊(1 / 4 : ℝ) * (48 : ℕ) / 2⌋₊
    let D := K - 1
    (1 / 4 : ℝ) / 3 ≤ (D : ℝ) / (48 : ℕ) ∧ (D : ℝ) / (48 : ℕ) ≤ 1 - 1 / 4 ∧
      (K : ℝ) ≤ (1 - 1 / 4) * (48 : ℕ) := by
  have hc : ⌈(1 / 4 : ℝ) * (48 : ℕ)⌉₊ = 12 := by norm_num
  have h := blockDegree_bounds (δ := 1 / 4) (n := 48) (k := 10) (by norm_num) (by norm_num)
    (by rw [hc]; norm_num)
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The cutoff bound at `δ = 1 / 2`, `n = 10`, `k = 3`: `D = max 3 2 - 1 = 2`,
`g = min 1 ((1 / 2) / (2 / 10)) = 1`, and `D (1 + g) = 4 ≤ 3 + ⌈5⌉₊ = 8`. -/
example : (2 : ℝ) * (1 + rateGap (1 / 2) ((2 : ℝ) / 10)) ≤ 3 + 5 := by
  have hf : ⌊(1 / 2 : ℝ) * (10 : ℕ) / 2⌋₊ = 2 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  have hc : ⌈(1 / 2 : ℝ) * (10 : ℕ)⌉₊ = 5 := by norm_num
  have h := blockDegree_mul_one_add_rateGap_le (1 / 2) 10 3
  dsimp only at h
  rw [hf, hc] at h
  norm_num at h ⊢
  exact h

example :
    let δ : ℝ := 1 / 4
    let d := ⌈Real.exp (xi / δ)⌉₊
    let m := ⌈100 * (d : ℝ) ^ 2 * (harmonic (d - 1) : ℝ)⌉₊
    let n := 8 * m
    let K := max 0 ⌊δ * n / 2⌋₊
    let D := K - 1
    d < D := by
  let δ : ℝ := 1 / 4
  let d := ⌈Real.exp (xi / δ)⌉₊
  let m := ⌈100 * (d : ℝ) ^ 2 * (harmonic (d - 1) : ℝ)⌉₊
  let n := 8 * m
  have hA : 0 + ⌈δ * (n : ℝ)⌉₊ ≤ n := by
    have hceil : ⌈δ * (n : ℝ)⌉₊ ≤ n := Nat.ceil_le.mpr (by
      dsimp [δ]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith)
    simpa using hceil
  exact (prescribedBlockBounds δ n 0 (by norm_num [δ]) (by norm_num [δ]) (by rfl) hA).2.2.1

/-! ### Capacity parameters -/

/-- At `δ = 1 / 8` the order is at least `48000`. -/
example : 48000 ≤ capacityDerivativeOrder (1 / 8) :=
  (capacityDerivativeOrder_lower (by norm_num) (by norm_num)).1

example : 0 < weightedSupportMultiplicity 2 :=
  weightedSupportMultiplicity_pos_iff.mpr (by norm_num)

example :
    let δ : ℝ := 1 / 8
    let m := weightedSupportMultiplicity (capacityDerivativeOrder δ)
    let n := 8 * m
    let K := weightedSupportAmbientDimension δ n 0
    0 < n ∧ capacityDerivativeOrder δ < K - 1 ∧ 0 ≤ K ∧ K ≤ n := by
  let δ : ℝ := 1 / 8
  let m := weightedSupportMultiplicity (capacityDerivativeOrder δ)
  let n := 8 * m
  let K := weightedSupportAmbientDimension δ n 0
  have h := capacity_block_bounds (δ := δ) (n := n) (k := 0) (by norm_num [δ])
    (by norm_num [δ]) (by change 8 * m ≤ 8 * m; exact le_rfl) (by
      have hceil : ⌈δ * (n : ℝ)⌉₊ ≤ n := Nat.ceil_le.mpr (by
        dsimp [δ]
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith)
      simpa using hceil)
  rcases h with ⟨hn, hD, hKlo, hKhi⟩
  exact ⟨hn, hD, hKlo, hKhi⟩

/-! ### Dimension inputs -/

/-- At `d = 3`, `δ = 1 / 4`, `ρ = 1 / 2` and `H = ξ / δ = 54 / 5`: here `g = 1 / 2`,
`a = 19 / 16`, `m = ⌈9720⌉₊`, and the five rounding inputs hold. -/
example :
    let g := rateGap (1 / 4) (1 / 2)
    let a := 1 + theta * g
    let m := ⌈100 * ((3 : ℕ) : ℝ) ^ 2 * (54 / 5)⌉₊
    let W := ⌊a * (3 : ℕ) * m / (54 / 5)⌋₊
    0 < m ∧ 0 < W ∧
      (W : ℝ) * (54 / 5) / (3 : ℕ) ≤ (1 + 3 * g / 8) * m ∧
      (W : ℝ) / (((3 : ℕ) : ℝ) * (g * m)) ≤ 10 / 27 ∧
      (999 / 1000) * (a / (g * (54 / 5))) ^ 2 ≤ ((W : ℝ) / (((3 : ℕ) : ℝ) * (g * m))) ^ 2 :=
  prescribed_dimension_inputs (1 / 4) (1 / 2) (54 / 5) 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) le_rfl (by norm_num [xi])

example :
    let d := ⌈Real.exp (xi / (1 / 4 : ℝ))⌉₊
    48000 ≤ d ∧ xi / (1 / 4 : ℝ) ≤ Real.log d ∧
      xi / (1 / 4 : ℝ) ≤ (harmonic (d - 1) : ℝ) :=
  prescribed_order_lower (1 / 4) (by norm_num) (by norm_num)

/-! ### Endpoint comparison -/

example :
    (543 / 500 : ℝ) < normalizedDimensionRankSurplus (1 / 4) (1 / 4) (54 / 5) (54 / 5) :=
  normalizedDimensionRankSurplus_gt (1 / 4) (1 / 4) (54 / 5) (54 / 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [xi]) (by norm_num [xi])

example :
    (let δ : ℝ := 1 / 4
     let ρ : ℝ := 1 / 2
     let H : ℝ := 54 / 5
     let logd : ℝ := 54 / 5
     xi ^ 2 * Real.exp (theta * xi) ≤
        ρ * (δ / ρ * H / (1 + theta * (δ / ρ))) ^ 2 *
          Real.exp (logd * (theta * (δ / ρ) / (1 + theta * (δ / ρ))))) ∧
      (let δ : ℝ := 1 / 4
       let ρ : ℝ := 1 / 2
       let logd : ℝ := 54 / 5
       Real.exp 1 * (theta * xi / (1 + theta)) ≤
          ρ * Real.exp (logd * (theta * (δ / ρ) / (1 + theta * (δ / ρ))))) := by
  have hb := highRate_baseline_lower (θ := theta) (ξ := xi) (δ := 1 / 4) (ρ := 1 / 2)
    (H := 54 / 5) (logd := 54 / 5) (by norm_num [theta]) (by norm_num [xi]) (by norm_num)
    (by norm_num) (by norm_num [theta]) (by norm_num [xi]) (by norm_num [xi])
  have hv := highRate_variance_lower (θ := theta) (ξ := xi) (δ := 1 / 4) (ρ := 1 / 2)
    (logd := 54 / 5) (by norm_num [theta]) (by norm_num [xi]) (by norm_num) (by norm_num)
    (by norm_num [xi])
  exact ⟨hb, hv⟩

example :
    let δ₀ : ℝ := 1 / 4
    let c : ℝ := 1 / 3
    let ρ : ℝ := 1 / 3
    let H : ℝ := 108 / 5
    let logd : ℝ := 108 / 5
    c * xi ^ 2 / δ₀ * (1 / (1 + theta)) ^ 2 *
        Real.exp (xi / δ₀ * (theta / (1 + theta))) ≤
      ρ * (H / (1 + theta)) ^ 2 * Real.exp (logd * (theta / (1 + theta))) :=
  lowRate_baseline_lower (θ := theta) (ξ := xi) (δ₀ := 1 / 4) (c := 1 / 3) (δ := 1 / 8)
    (ρ := 1 / 3) (H := 108 / 5) (logd := 108 / 5) (by norm_num [theta]) (by norm_num [xi])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [xi]) (by norm_num [xi])

/-! ### Rounding parameters -/

example : (⌊(2 : ℝ) * 2 * 3 / 2⌋₊ : ℝ) * 2 / 2 ≤ 2 * 3 :=
  floorRadius_mul_div_le 2 2 2 3 (by norm_num)

example : (⌊(2 : ℝ) * 2 * 3 / 2⌋₊ : ℝ) / (2 * 1 * 3) ≤ 2 / (1 * 2) :=
  floorRadius_normalized_le 2 1 2 2 3 (by norm_num) (by norm_num) (by norm_num)

example :
    (1 - 1 / 2 : ℝ) ^ 2 * (2 / (1 * 2)) ^ 2 ≤
      ((⌊(2 : ℝ) * 2 * 3 / 2⌋₊ : ℝ) / (2 * 1 * 3)) ^ 2 :=
  floorRadius_sq_ge 2 2 1 2 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example :
  (1 - theta) * 1 * 3 * (1 - 3) ≤
      (3 : ℝ) * (1 + 1) + (2 - 1 : ℕ) - (4 + 0 + Nat.choose 2 2 : ℕ) * 2 / 2 :=
  remainingDegree_lower theta 3 1 2 2 3 0 4 (by omega) (by norm_num [theta]) (by norm_num)
    (by
      symm
      rw [Nat.floor_eq_iff (by norm_num [theta])]
      norm_num [theta]) (by norm_num [theta])

example :
    (3 : ℝ) * (1 + 1) + (2 - 1 : ℕ) - (4 + 0 + Nat.choose 2 2 : ℕ) * 2 / 2 ≤
      (1 - theta) * 1 * 3 * (1 + 2) :=
  remainingDegree_upper theta 2 1 2 2 3 0 4 (by omega) (by norm_num) (by
      symm
      rw [Nat.floor_eq_iff (by norm_num [theta])]
      norm_num [theta]) (by norm_num [theta])

example : ((4 + 0 + Nat.choose 2 2 : ℕ) : ℝ) / 2 ≤ ((1 + theta * 1) * 3 / 2) * (1 + 1) :=
  enlargedRadius_upper theta 1 1 2 2 3 0 4 (by omega) (by omega) (by norm_num [theta]) (by norm_num)
    (by
      symm
      rw [Nat.floor_eq_iff (by norm_num [theta])]
      norm_num [theta]) (by norm_num [theta])

/-! ### Mean and variance bounds -/

example :
    let d : ℕ := 48400
    let H : ℝ := 54 / 5
    let g : ℝ := 1
    let m := ⌈100 * (d : ℝ) ^ 2 * H⌉₊
    let r : ℕ := 1
    let W := ⌊(1 + theta * g) * (d : ℝ) * m / H⌋₊
    (((m : ℝ) * H / d + d.choose 2 * H / d ≤ (2 / 1000) * residualFraction * g * m) ∧
      ((d : ℝ) + H / d ≤ (1 / 1000) * residualFraction * g * m) ∧
      ((m : ℝ) + d.choose 2 ≤ (1 / 1000) * ((1 + theta * g) * d * m / H))) ∧
      (let gap : ℝ := (m : ℝ) * (1 + g) + (d - 1 : ℕ) -
        (W + r + d.choose 2 : ℕ) * H / d
       let variance : ℝ := ((W + r + d.choose 2 : ℕ) : ℝ) ^ 2 / (d * (d + 1))
       0 < gap ∧ gap + variance / (4 * gap) + 1 ≤ g * m * (448 / 625)) := by
  let d : ℕ := 48400
  let H : ℝ := 54 / 5
  let g : ℝ := 1
  let m := ⌈100 * (d : ℝ) ^ 2 * H⌉₊
  let r : ℕ := 1
  let W := ⌊(1 + theta * g) * (d : ℝ) * m / H⌋₊
  have hsize : 100 * (d : ℝ) ^ 2 * H ≤ m := by
    dsimp [m]
    exact Nat.le_ceil _
  have hm2 : 2 ≤ m := by
    norm_num [m, d, H]
  have hm : 0 < m := by omega
  have hd : 48000 ≤ d := by norm_num [d]
  have hr : r < m := by have := hm2; omega
  have hHlower : 54 / 5 ≤ H := by norm_num [H]
  have hHupper : H ≤ (19 / 365) * Real.sqrt d := by
    change (54 / 5 : ℝ) ≤ (19 / 365) * Real.sqrt (48400 : ℝ)
    rw [show (48400 : ℝ) = (220 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 220)]
    norm_num
  have hgH : xi ≤ g * H := by norm_num [xi, g, H]
  have hgm : 270 * d * H ≤ g * m := by
    norm_num [d, H, g] at hsize ⊢
    nlinarith
  have hcenter := centeringErrorBounds d m g H hd hm (by norm_num [g]) (by norm_num [H])
    hHlower hHupper hgH hsize hgm
  have hfiber := prescribedFiberMeanVariance_le d m r W g H 1 hd hm hr (by norm_num [g])
    (by norm_num [H]) hHlower hHupper hgH (by norm_num [theta, xi, g, H]) hsize hgm rfl
    (by norm_num) (by norm_num)
  refine ⟨hcenter, ?_⟩
  dsimp only [g, W] at hfiber
  simpa only [one_mul, mul_one] using hfiber

example :
    0 < (1250 : ℝ) ∧
      (1250 : ℝ) + 1 / (4 * 1250) + 1 ≤ 2000 * (448 / 625 : ℝ) :=
  residualMeanVariance_le 1250 1 2000 (by norm_num)
    (by norm_num [residualFraction, theta]) (by norm_num [residualFraction, theta])
    (by norm_num [xi]) (by norm_num)

/-! ### Scalar parameters -/

/-- At `δ = 1 / 4`, `ρ = 1 / 2`, `θ = 3 / 8` the closed form gives
`(1 + θ g) / g = (1 / 2 + 3 / 32) / (1 / 4) = 19 / 8 ≤ 4 = 1 / δ`. -/
example : (1 + theta * rateGap (1 / 4) (1 / 2)) / rateGap (1 / 4) (1 / 2) = 19 / 8 := by
  rw [one_add_mul_rateGap_div theta (by norm_num) (by norm_num)]
  norm_num [theta]

example : (1 : ℝ) ≤ rateGap (1 / 2) (1 / 2) * 2 :=
  le_rateGap_mul (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-! ### Multiplicative margin identity -/

example :
    let g := rateGap (1 : ℝ) 3
    let a := 1 + theta * g
    let B := g * (448 / 625) * (101 / 100) * (37 / 20) * a ^ 2 / 1 ^ 2 * 2 ^ (1 / a) / 2
    B * normalizedDimensionRankSurplus 1 3 1 (Real.log 2) =
      3 * g ^ 3 / 6 * ((5 / 8 : ℝ) ^ 3 + (4147 / 2160) * (999 / 1000) * (a / (g * 1)) ^ 2) :=
  normalized_surplus_product 1 3 1 2 (by norm_num) (by norm_num [rateGap]) (by norm_num)

/-! ### Positive-rank multiplicative margin -/

example :
    let δ : ℝ := 1 / 4
    let ρ : ℝ := 1 / 4
    let H : ℝ := 54 / 5
    let d : ℝ := Real.exp (54 / 5)
    let g := rateGap δ ρ
    let a := 1 + theta * g
    let s : ℝ := 55 / 432
    let V : ℝ := 1
    let m : ℝ := 1
    let n : ℝ := 1
    let D : ℝ := 1 / 4
    let N := V * D / 6 * (g * m) ^ 3 * ((5 / 8 : ℝ) ^ 3 + (4147 / 2160) * s ^ 2)
    let R := g * (448 / 625) * (101 / 100) * (37 / 20) * a ^ 2 / H ^ 2 *
      d ^ (1 / a) / d
    0 < R ∧ (543 / 500 : ℝ) * n * R < N := by
  let δ : ℝ := 1 / 4
  let ρ : ℝ := 1 / 4
  let H : ℝ := 54 / 5
  let d : ℝ := Real.exp (54 / 5)
  let g := rateGap δ ρ
  let a := 1 + theta * g
  let s : ℝ := 55 / 432
  let V : ℝ := 1
  let m : ℝ := 1
  let n : ℝ := 1
  let D : ℝ := 1 / 4
  let N := V * D / 6 * (g * m) ^ 3 * ((5 / 8 : ℝ) ^ 3 + (4147 / 2160) * s ^ 2)
  let R := g * (448 / 625) * (101 / 100) * (37 / 20) * a ^ 2 / H ^ 2 *
    d ^ (1 / a) / d
  have hmargin := multiplicative_margin_from_bounds δ ρ H d g a s V m n D N R
    (by norm_num [δ]) (by norm_num [δ]) (by norm_num [δ, ρ]) (by norm_num [δ, ρ])
    (by norm_num [δ, H, xi])
    (by simp only [d, Real.log_exp]; norm_num [δ, xi])
    (by positivity) rfl rfl (by norm_num [V]) (by norm_num [m]) (by norm_num [n])
    (by norm_num [D, n, ρ]) (by norm_num [s, a, g, H, δ, ρ, rateGap, theta])
    (by norm_num [N, V, D, m, s, g, rateGap, δ, ρ, theta])
    (by
      norm_num [V, m]
      change (g * (448 / 625) * (101 / 100) * (37 / 20) * a ^ 2 / H ^ 2 *
        d ^ (1 / a) / d) ≤ _
      rw [show H ^ 2 = (2916 / 25 : ℝ) by norm_num [H], one_div])
  constructor
  · dsimp [R, g, a, H, d, δ, ρ, rateGap, theta]
    positivity
  · exact hmargin
