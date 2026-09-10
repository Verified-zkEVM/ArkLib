/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.ProductBounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.SharpCountingBound
/-!
# Uniformizing the dimension-sensitive MCA budget

The source and fiber contributions retain their incidence products until their scalar
estimates are applied. Only then do we replace each actual stage order by the maximum
order and sum over the separant stages. This gives the prescribed gap-only constant.
-/

@[expose] public section

namespace ReedSolomon
open AffineHilbert

/-- The prescribed product-based MCA coefficient, including the terminal height. -/
noncomputable def polynomialCurveProductMCAConstant (δ : ℝ) (v h d : ℕ) : ℝ :=
  h + 2 ^ d * (v : ℝ) ^ (d + 2) * (1 / δ) ^ d *
    ((h : ℝ) * (d + 1) * (3 * d + 5) / δ + 3)

/-- A scalar stage budget that retains the actual order `r`. -/
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

/-- Uniformize the stage order only after applying the product estimates. -/
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


/-- At most `v` stages and the terminal height give the gap-only MCA coefficient. -/
theorem product_stages_aggregate {ι : Type*} (S : Finset ι) (cost : ι → ℝ)
    (δ : ℝ) (n ℓ v h d : ℕ) (hδ : 0 < δ) (hn : 0 < n)
    (hcard : S.card ≤ v)
    (hstage : ∀ i ∈ S, cost i ≤ polynomialCurveProductStageBound δ n ℓ v h d d) :
    ((ℓ * h : ℕ) : ℝ) + ∑ i ∈ S, cost i ≤
      (ℓ : ℝ) * polynomialCurveProductMCAConstant δ v h d * (n : ℝ) ^ (d + 1) := by
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
      unfold B polynomialCurveProductStageBound polynomialCurveProductMCAConstant
      rw [show d + 2 = (d + 1) + 1 by omega, pow_succ]
      ring
/-- The gap-only scalar used by the prescribed polynomial-curve and line certificates. -/
noncomputable def prescribedMCAConstant (δ : ℝ) : ℝ :=
  let d := Nat.ceil (Real.exp ((27 / 10) / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
  let v := 2 * m - 1
  polynomialCurveProductMCAConstant δ v (12 * v) d

/-- The prescribed small-gap scalar is strictly positive. -/
theorem prescribedMCAConstant_pos {δ : ℝ} (hδ : 0 < δ) (hδquarter : δ < 1 / 4) :
    0 < prescribedMCAConstant δ := by
  let d := Nat.ceil (Real.exp ((27 / 10) / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
  let v := 2 * m - 1
  have hlower := HiddenDerivative.WeightedSupportParameters.prescribed_order_lower δ hδ hδquarter.le
  have hratio : (0 : ℝ) < (27 / 10) / δ := by positivity
  have hH : 0 < harmonicNumber (d - 1) := by
    rw [harmonicNumber_eq_harmonic]
    exact hratio.trans_le hlower.2.2
  have hmReal : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) (Nat.le_ceil _)
  have hm : 0 < m := by exact_mod_cast hmReal
  have hv : 0 < v := by dsimp only [v]; omega
  change 0 < polynomialCurveProductMCAConstant δ v (12 * v) d
  unfold polynomialCurveProductMCAConstant
  positivity

/-- Any certified exponent at most `2K` satisfies the same mixed-degree cap. -/
theorem sourceCurveInitialMixedDegree_le_uniformCaps_of_exponent
    (r n K ℓ j H v h τ : ℕ) (hn : 0 < n) (hKn : K ≤ n) (hj : 0 < j)
    (hh : 0 < h) (hjv : j ≤ v) (hH : H ≤ ℓ * h) (hτ : τ ≤ 2 * K) :
    sourceCurveInitialMixedDegree r ℓ K j H (τ := τ) ≤
      ℓ * h * (3 * r + 5) * 2 ^ r * v ^ (r + 1) * n ^ (r + 1) := by
  apply le_trans ?_ (sourceCurveInitialMixedDegree_le_uniformCaps r n K ℓ j H v h
    hn hKn hj hh hjv hH)
  unfold sourceCurveInitialMixedDegree sourceCurveCutJetDegree sourceCurveCutChallengeDegree
  gcongr

/-- The jet-degree cap also respects the supplied Taylor exponent. -/
theorem sourceCurveCutJetDegree_le_uniformCaps_of_exponent
    (n K j v τ : ℕ) (hn : 0 < n) (hKn : K ≤ n) (hj : 0 < j)
    (hjv : j ≤ v) (hτ : τ ≤ 2 * K) :
    sourceCurveCutJetDegree K j (τ := τ) ≤ 2 * n * v := by
  apply le_trans ?_ ((sourceCurveCutJetDegree_le n K j hn hKn hj).trans
    (Nat.mul_le_mul_left (2 * n) hjv))
  unfold sourceCurveCutJetDegree
  gcongr
/-- Apply the product scalar estimate to the actual regular-stage budget. -/
theorem regularSymbolicCurveMCASharpBound_product_le_stage (δ : ℝ)
    (r n K k A ℓ j H v h d τ : ℕ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hd : 0 < d) (hn : 0 < n)
    (hk : 0 < k) (hj : 0 < j) (hh : 0 < h) (hKn : K ≤ n)
    (hjv : j ≤ v) (hH : H ≤ ℓ * h) (hgap : (k : ℝ) + δ * n ≤ A)
    (hAn : A ≤ n) (hr : r ≤ d) (hτ : τ ≤ 2 * K) :
    let L := correlatedProductCutoff d k A
    (regularSymbolicCurveMCASharpBound r n ℓ K k L A j H (τ := τ) : ℝ) ≤
      polynomialCurveProductStageBound δ n ℓ v h d r := by
  have hkA : k ≤ A := by
    exact_mod_cast (show (k : ℝ) ≤ A from le_trans (le_add_of_nonneg_right (by positivity)) hgap)
  have hb := product_stage_bound δ n k A d r ℓ v h
    (sourceCurveInitialMixedDegree r ℓ K j H (τ := τ))
    (sourceCurveCutJetDegree K j (τ := τ)) j hδ hδone hd hk hkA hAn hgap hr
    (sourceCurveInitialMixedDegree_le_uniformCaps_of_exponent r n K ℓ j H v h τ
      hn hKn hj hh hjv hH hτ)
    (sourceCurveCutJetDegree_le_uniformCaps_of_exponent n K j v τ hn hKn hj hjv hτ) hjv
  simpa only [regularSymbolicCurveMCASharpBound, Rat.cast_add, Rat.cast_mul,
    Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Nat.cast_mul] using hb

/-- Aggregate actual product-based regular stages with a single common height cap. -/
theorem regularSymbolicCurveMCASharp_product_finiteStage_le
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
      (regularSymbolicCurveMCASharpBound (order i) n ℓ K k L A
        (jetDegree i) (height i) (τ := τ) : ℝ) ≤
      (ℓ : ℝ) * polynomialCurveProductMCAConstant δ v h d * (n : ℝ) ^ (d + 1) := by
  apply product_stages_aggregate S _ δ n ℓ v h d hδ hn hcard
  intro i hi
  exact (regularSymbolicCurveMCASharpBound_product_le_stage δ
    (order i) n K k A ℓ (jetDegree i) (height i) v h d τ
      hδ hδone hd hn hk (hjetPos i hi) hh hKn (hjet i hi) (hheight i hi)
      hgap hAn (horder i hi) hτ).trans
    (polynomialCurveProductStageBound_le_uniform δ n ℓ v h d (order i)
      hδ hδone hn hv (horder i hi))

end ReedSolomon
