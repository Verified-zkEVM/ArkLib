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

/-- A concrete small-gap block satisfies the prescribed geometric parameter contract. -/
example :
    let δ : ℝ := 1 / 5
    let d := Nat.ceil (Real.exp (xi / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
    let n := 8 * m
    2 * m - 1 < n ∧ d < max 1 (Nat.floor (δ * n / 2)) := by
  let δ : ℝ := 1 / 5
  let d := Nat.ceil (Real.exp (xi / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
  let n := 8 * m
  have hδ : 0 < δ := by norm_num [δ]
  have hδmax : δ < 1 / 4 := by norm_num [δ]
  have ho := prescribed_order_lower δ hδ hδmax.le
  have hH : (0 : ℝ) < (harmonic (d - 1) : ℝ) := by
    have hxi : 0 < xi := by norm_num [xi]
    simpa only [d] using (div_pos hxi hδ).trans_le ho.2.2
  have hdlower : 48000 ≤ d := by simpa only [d] using ho.1
  have hd : 0 < d := by omega
  have hm : 0 < m := by
    dsimp only [m]
    apply Nat.ceil_pos.mpr
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have hblock :
      let d := Nat.ceil (Real.exp (xi / δ))
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
      8 * m ≤ n := by
    dsimp only
    exact Nat.le_refl _
  have hA : capacityAgreementThreshold δ n 1 ≤ n := by
    apply (capacityAgreementThreshold_le_iff_real hδ.le n 1 n).mpr
    have hnR : (n : ℝ) = 8 * m := by norm_num [n]
    rw [hnR]
    dsimp [δ]
    push_cast
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm.ne')
    nlinarith
  obtain ⟨_, _, _, _, hνn, hdK, _, _, _, _⟩ :=
    prescribed_geometric_parameters δ n 1 hδ hδmax hblock hA
  exact ⟨hνn, hdK⟩

/-- At `δ = 1/4`, `n = 8m` and `k = m`, the positive-dimensional block bounds hold. -/
example :
    let δ : ℝ := 1 / 4
    let d := ⌈Real.exp (xi / δ)⌉₊
    let m := ⌈100 * (d : ℝ) ^ 2 * (harmonic (d - 1) : ℝ)⌉₊
    let n := 8 * m
    0 < m ∧ d < weightedSupportAmbientDimension δ n m - 1 := by
  let δ : ℝ := 1 / 4
  let d := ⌈Real.exp (xi / δ)⌉₊
  let m := ⌈100 * (d : ℝ) ^ 2 * (harmonic (d - 1) : ℝ)⌉₊
  let n := 8 * m
  have hm : 0 < m := by
    apply weightedSupportMultiplicity_pos_iff.mpr
    have h := prescribed_order_lower δ (by norm_num [δ]) (by norm_num [δ])
    have hd : 48000 ≤ d := by simpa [d, δ] using h.1
    dsimp [d]
    omega
  have hceil : ⌈δ * (n : ℝ)⌉₊ = 2 * m := by
    rw [show δ * (n : ℝ) = ((2 * m : ℕ) : ℝ) by dsimp [δ, n]; push_cast; ring,
      Nat.ceil_natCast]
  have hA : m + ⌈δ * (n : ℝ)⌉₊ ≤ n := by
    rw [hceil]
    dsimp [n]
    omega
  have hblock : 8 * m ≤ n := by dsimp [n]; omega
  have h := prescribedBlockBounds δ n m (by norm_num [δ]) (by norm_num [δ])
    (by change 8 * m ≤ n; exact hblock) hA
  exact ⟨hm, h.2.2.1⟩

/-! ### Capacity parameters -/

/-- At `δ = 1 / 8` the order is at least `48000`. -/
example : 48000 ≤ capacityDerivativeOrder (1 / 8) :=
  (capacityDerivativeOrder_lower (by norm_num) (by norm_num)).1

/-- At `δ = 1/8`, `n = 8m` and `k = m`, the capacity bounds hold with positive `k`. -/
example :
    let δ : ℝ := 1 / 8
    let m := weightedSupportMultiplicity (capacityDerivativeOrder δ)
    let n := 8 * m
    let K := weightedSupportAmbientDimension δ n m
    0 < m ∧ 0 < n ∧ capacityDerivativeOrder δ < K - 1 ∧ m ≤ K ∧ K ≤ n := by
  let δ : ℝ := 1 / 8
  let m := weightedSupportMultiplicity (capacityDerivativeOrder δ)
  let n := 8 * m
  let K := weightedSupportAmbientDimension δ n m
  have hd : 2 ≤ capacityDerivativeOrder δ := by
    have h := (capacityDerivativeOrder_lower (δ := δ) (by norm_num [δ])
      (by norm_num [δ])).1
    omega
  have hm : 0 < m := weightedSupportMultiplicity_pos_iff.mpr hd
  have hceil : ⌈δ * (n : ℝ)⌉₊ = m := by
    rw [show δ * (n : ℝ) = (m : ℝ) by dsimp [δ, n]; push_cast; ring, Nat.ceil_natCast]
  have hA : m + ⌈δ * (n : ℝ)⌉₊ ≤ n := by
    rw [hceil]
    dsimp [n]
    omega
  have hblock : 8 * m ≤ n := by dsimp [n]; omega
  have h := capacity_block_bounds (δ := δ) (n := n) (k := m)
    (by norm_num [δ]) (by norm_num [δ]) (by change 8 * m ≤ n; exact hblock) hA
  rcases h with ⟨hn, hD, hk, hKhi⟩
  exact ⟨hm, hn, hD, hk, hKhi⟩

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

/-- At `δ = 1/4`, `ρ = 1/2`, the denominator and specialized radius bounds hold. -/
example :
    ((1 / 2 : ℝ) + theta * (1 / 4)) ^ 2 ≤ 1 / 2 ∧
    xi ≤ rateGap (1 / 4) (1 / 2) * (54 / 5) ∧
    (1 / 5 : ℝ) ≤ 10 / 27 := by
  exact ⟨highRate_denominator_sq_le_rate (θ := theta) (δ := 1 / 4) (ρ := 1 / 2)
      (by norm_num) (by norm_num [theta]) (by norm_num [theta]) (by norm_num) (by norm_num),
    xi_le_rateGap_mul (δ := 1 / 4) (ρ := 1 / 2) (H := 54 / 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [xi]),
    normalizedRadius_le_ten_twentySeven (δ := 1 / 4) (ρ := 1 / 2) (H := 54 / 5) (s := 1 / 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [xi])
      (by norm_num [rateGap, theta])⟩

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
