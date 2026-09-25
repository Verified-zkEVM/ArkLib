/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.ProductBounds
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.SharpCountingBound
public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters

/-!
# Product-based scalar bounds for regular power-batched agreement

The intermediate product cutoff gives a scalar cost bound for each regular stage. Uniformizing
over stage orders and summing over a finite family gives one coefficient depending only on the
gap, the stage count, and the degree cap.

## Main statements

* `polynomialCurveProductAgreementConstant` and `polynomialCurveProductStageBound` define the
  aggregate coefficient and order-sensitive stage cost.
* `product_stage_bound` bounds the two incidence contributions at the product cutoff.
* `polynomialCurveProductStageBound_le_uniform` and `product_stages_aggregate` uniformize and sum
  the stage costs.
* `regularPowerBatchedAgreementSharpBound_product_le_stage` and
  `regularPowerBatchedAgreementSharp_product_finiteStage_le` bound one regular stage and a finite
  family of stages.
* `prescribedProductAgreementConstant_pos` proves positivity of the prescribed coefficient.

## References

* [DKT26]
* [DKTZ26]
-/

@[expose] public section

namespace ReedSolomon

open scoped BigOperators
open HiddenDerivative.WeightedSupportParameters

/-- The product-based agreement coefficient, including the terminal height. -/
noncomputable def polynomialCurveProductAgreementConstant (δ : ℝ) (v h d : ℕ) : ℝ :=
  h + 2 ^ d * (v : ℝ) ^ (d + 2) * (1 / δ) ^ d *
    ((h : ℝ) * (d + 1) * (3 * d + 5) / δ + 3)

/-- A product-based scalar stage cost that retains the actual order `r`. -/
noncomputable def polynomialCurveProductStageBound
    (δ : ℝ) (n ℓ v h d r : ℕ) : ℝ :=
  (ℓ : ℝ) * 2 ^ r * (v : ℝ) ^ (r + 1) * (n : ℝ) ^ (r + 1) *
    (1 / δ) ^ r * ((h : ℝ) * (d + 1) * (3 * r + 5) / δ + 3)

/-- The joint and fiber product estimates bound one stage with explicit degree caps. -/
theorem product_stage_bound (δ : ℝ) (n k A d r ℓ v h J b j : ℕ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hd : 0 < d) (hk : 0 < k)
    (hkA : k ≤ A) (hAn : A ≤ n) (hgap : (k : ℝ) + δ * n ≤ A) (hr : r ≤ d)
    (hJ : J ≤ ℓ * h * (3 * r + 5) * 2 ^ r * v ^ (r + 1) * n ^ (r + 1))
    (hb : b ≤ 2 * n * v) (hj : j ≤ v) :
    let L := correlatedProductCutoff d k A
    (J : ℝ) * (((n - L + 1 : ℕ) : ℝ) / (A - L + 1 : ℕ)) *
        (dimensionSensitiveIncidenceProduct n A k 1 r : ℝ) +
      (ℓ : ℝ) * (n - L : ℕ) * j * b ^ r *
        (dimensionSensitiveIncidenceProduct n L k 1 r : ℝ) ≤
      polynomialCurveProductStageBound δ n ℓ v h d r := by
  let L := correlatedProductCutoff d k A
  have hP := evaluation_incidence_product_le δ n k A r hδ hδone hkA hAn hgap
  have hratio := correlatedProductCutoff_jointRatio_le δ n k A d hδ hk hkA hAn hgap
  have hF := (correlatedProductCutoff_fiberProduct_lt_three δ n k A d r
    hδ hδone hd hk hkA hAn hgap hr).le
  have hJR : (J : ℝ) ≤ ℓ * h * (3 * r + 5) * 2 ^ r * v ^ (r + 1) * n ^ (r + 1) := by
    exact_mod_cast hJ
  have hbR : (b : ℝ) ≤ 2 * n * v := by exact_mod_cast hb
  have hjR : (j : ℝ) ≤ v := by exact_mod_cast hj
  have hnL : ((n - L : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n L
  have hP0 : (0 : ℝ) ≤ dimensionSensitiveIncidenceProduct n A k 1 r := by
    exact_mod_cast dimensionSensitiveIncidenceProduct_nonneg n A k 1 r
  have hF0 : (0 : ℝ) ≤ dimensionSensitiveIncidenceProduct n L k 1 r := by
    exact_mod_cast dimensionSensitiveIncidenceProduct_nonneg n L k 1 r
  have hfirst := mul_le_mul (mul_le_mul hJR hratio (by positivity) (by positivity)) hP
    (by positivity) (by positivity)
  have hcoeff : (ℓ : ℝ) * (n - L : ℕ) * j * b ^ r ≤ ℓ * n * v * (2 * n * v) ^ r := by
    gcongr
  have hsecond := mul_le_mul hcoeff hF (by positivity) (by positivity)
  calc
    _ ≤ (ℓ * h * (3 * r + 5) * 2 ^ r * v ^ (r + 1) * n ^ (r + 1)) *
          ((d + 1) / δ) * (1 / δ) ^ r +
        (ℓ * n * v * (2 * n * v) ^ r) * (3 * (1 / δ) ^ r) := add_le_add hfirst hsecond
    _ = _ := by
      unfold polynomialCurveProductStageBound
      simp only [mul_pow, pow_succ]
      ring

/-- Uniformize the stage order after applying the product estimates. -/
theorem polynomialCurveProductStageBound_le_uniform (δ : ℝ) (n ℓ v h d r : ℕ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hn : 0 < n) (hv : 0 < v) (hr : r ≤ d) :
    polynomialCurveProductStageBound δ n ℓ v h d r ≤
      polynomialCurveProductStageBound δ n ℓ v h d d := by
  have hc : (1 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by simpa using hδone)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv
  unfold polynomialCurveProductStageBound
  gcongr
  norm_num

/-- At most `v` stages and the terminal height give the gap-only product coefficient. -/
theorem product_stages_aggregate {ι : Type*} (S : Finset ι) (cost : ι → ℝ)
    (δ : ℝ) (n ℓ v h d : ℕ) (hδ : 0 < δ) (hn : 0 < n)
    (hcard : S.card ≤ v)
    (hstage : ∀ i ∈ S, cost i ≤ polynomialCurveProductStageBound δ n ℓ v h d d) :
    ((ℓ * h : ℕ) : ℝ) + ∑ i ∈ S, cost i ≤
      (ℓ : ℝ) * polynomialCurveProductAgreementConstant δ v h d * (n : ℝ) ^ (d + 1) := by
  let B := polynomialCurveProductStageBound δ n ℓ v h d d
  have hB : 0 ≤ B := by dsimp [B, polynomialCurveProductStageBound]; positivity
  have hsum : ∑ i ∈ S, cost i ≤ (v : ℝ) * B := by
    calc
      _ ≤ ∑ _i ∈ S, B := Finset.sum_le_sum hstage
      _ = (S.card : ℝ) * B := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB
  have hnPow : (1 : ℝ) ≤ (n : ℝ) ^ (d + 1) := one_le_pow₀ (by exact_mod_cast hn)
  have hterminal : ((ℓ * h : ℕ) : ℝ) ≤ (ℓ : ℝ) * h * (n : ℝ) ^ (d + 1) := by
    push_cast
    exact le_mul_of_one_le_right (by positivity) hnPow
  calc
    _ ≤ (ℓ : ℝ) * h * (n : ℝ) ^ (d + 1) + (v : ℝ) * B := add_le_add hterminal hsum
    _ = _ := by
      unfold B polynomialCurveProductStageBound polynomialCurveProductAgreementConstant
      rw [show d + 2 = (d + 1) + 1 by omega, pow_succ]
      ring

/-- The prescribed gap-only coefficient for polynomial-curve agreement. -/
noncomputable def prescribedProductAgreementConstant (δ : ℝ) : ℝ :=
  let d := Nat.ceil (Real.exp (xi / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
  let v := 2 * m - 1
  polynomialCurveProductAgreementConstant δ v (12 * v) d

/-- The prescribed product-based agreement coefficient is strictly positive. -/
theorem prescribedProductAgreementConstant_pos {δ : ℝ} (hδ : 0 < δ)
    (hδquarter : δ < 1 / 4) :
    0 < prescribedProductAgreementConstant δ := by
  let d := Nat.ceil (Real.exp (xi / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
  let v := 2 * m - 1
  have hlower := HiddenDerivative.WeightedSupportParameters.prescribed_order_lower
    δ hδ hδquarter.le
  have hratio : (0 : ℝ) < xi / δ := div_pos xi_pos hδ
  have hH : (0 : ℝ) < (harmonic (d - 1) : ℝ) := hratio.trans_le hlower.2.2
  have hmReal : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) (Nat.le_ceil _)
  have hm : 0 < m := by exact_mod_cast hmReal
  have hv : 0 < v := by dsimp only [v]; omega
  change 0 < polynomialCurveProductAgreementConstant δ v (12 * v) d
  unfold polynomialCurveProductAgreementConstant
  positivity

/-- The product scalar estimate bounds the actual regular-stage budget. -/
theorem regularPowerBatchedAgreementSharpBound_product_le_stage (δ : ℝ)
    (r n K k A ℓ j H v h d τ : ℕ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hd : 0 < d) (hn : 0 < n)
    (hk : 0 < k) (hj : 0 < j) (hh : 0 < h) (hKn : K ≤ n)
    (hjv : j ≤ v) (hH : H ≤ ℓ * h) (hgap : (k : ℝ) + δ * n ≤ A)
    (hAn : A ≤ n) (hr : r ≤ d) (hτ : τ ≤ 2 * K) :
    let L := correlatedProductCutoff d k A
    (regularPowerBatchedAgreementSharpBound r n ℓ K k L A j H (τ := τ) : ℝ) ≤
      polynomialCurveProductStageBound δ n ℓ v h d r := by
  have hkA : k ≤ A := by
    exact_mod_cast
      (show (k : ℝ) ≤ A from le_trans (le_add_of_nonneg_right (by positivity)) hgap)
  have hτn : τ ≤ 2 * n := hτ.trans (Nat.mul_le_mul_left 2 hKn)
  have hJ : regularPowerBatchedInitialMixedDegree r ℓ K j H (τ := τ) ≤
      ℓ * h * (3 * r + 5) * 2 ^ r * v ^ (r + 1) * n ^ (r + 1) := by
    exact regularPowerBatchedInitialMixedDegree_le_uniformCaps r n K ℓ j H v h τ
      hn hτn hj hh hjv hH
  have hb : regularPowerBatchedCutJetDegree K j (τ := τ) ≤ 2 * n * v := by
    have hb' := regularPowerBatchedCutJetDegree_le_two_mul K n j τ hn hτn hj
    exact hb'.trans (Nat.mul_le_mul_left (2 * n) hjv)
  have hbStage := product_stage_bound δ n k A d r ℓ v h
    (regularPowerBatchedInitialMixedDegree r ℓ K j H (τ := τ))
    (regularPowerBatchedCutJetDegree K j (τ := τ)) j
    hδ hδone hd hk hkA hAn hgap hr hJ hb hjv
  simpa only [regularPowerBatchedAgreementSharpBound, Rat.cast_add, Rat.cast_mul,
    Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Nat.cast_mul] using hbStage

/-- Aggregate product-based regular stages under one common height cap. -/
theorem regularPowerBatchedAgreementSharp_product_finiteStage_le
    {ι : Type*} (S : Finset ι) (order jetDegree height : ι → ℕ)
    (δ : ℝ) (n K k A ℓ v h d τ : ℕ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hd : 0 < d) (hn : 0 < n)
    (hk : 0 < k) (hv : 0 < v) (hh : 0 < h) (hKn : K ≤ n)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) (hτ : τ ≤ 2 * K)
    (hcard : S.card ≤ v) (horder : ∀ i ∈ S, order i ≤ d)
    (hjetPos : ∀ i ∈ S, 0 < jetDegree i) (hjet : ∀ i ∈ S, jetDegree i ≤ v)
    (hheight : ∀ i ∈ S, height i ≤ ℓ * h) :
    let L := correlatedProductCutoff d k A
    ((ℓ * h : ℕ) : ℝ) + ∑ i ∈ S,
      (regularPowerBatchedAgreementSharpBound (order i) n ℓ K k L A
        (jetDegree i) (height i) (τ := τ) : ℝ) ≤
      (ℓ : ℝ) * polynomialCurveProductAgreementConstant δ v h d * (n : ℝ) ^ (d + 1) := by
  apply product_stages_aggregate S _ δ n ℓ v h d hδ hn hcard
  intro i hi
  exact (regularPowerBatchedAgreementSharpBound_product_le_stage δ
    (order i) n K k A ℓ (jetDegree i) (height i) v h d τ
      hδ hδone hd hn hk (hjetPos i hi) hh hKn (hjet i hi) (hheight i hi)
      hgap hAn (horder i hi) hτ).trans
    (polynomialCurveProductStageBound_le_uniform δ n ℓ v h d (order i)
      hδ hδone hn hv (horder i hi))

end ReedSolomon
