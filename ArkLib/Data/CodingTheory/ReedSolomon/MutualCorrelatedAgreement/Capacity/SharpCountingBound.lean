/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.ProductBounds
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.Midpoint
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.SharpGeneralEquation
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.Parameters
/-!
# Midpoint scalar budgets for the quarter-gap specialization

This file bounds the dimension-sensitive stage products by midpoint ratios for the retained
quarter-gap specialization. It keeps the actual stage order until finite-stage aggregation.
The prescribed small-gap theorem uses the sharper cutoff and coefficient in `ProductCounting`.
-/

@[expose] public section

namespace ReedSolomon

open scoped BigOperators

/-- The coefficient after midpoint normalization and uniformization over at most
`v` stages of order at most `d`. -/
noncomputable def polynomialCurveSharpMCAConstant (δ : ℝ) (v h d : ℕ) : ℝ :=
  (h : ℝ) + 2 ^ d * (v : ℝ) ^ (d + 2) *
    ((h : ℝ) * (3 * d + 5) * (2 / δ) ^ (d + 1) + (2 / δ) ^ d)

/-- The Taylor denominator degree at any cutoff `K ≤ n` is at most `2*n*v`. -/
theorem sourceCurveCutJetDegree_le (n K v : ℕ)
    (hn : 0 < n) (hKn : K ≤ n) (hv : 0 < v) :
    sourceCurveCutJetDegree K v ≤ 2 * n * v := by
  apply le_trans ?_ (show sourceCurveCutJetDegree n v ≤ 2 * n * v by
    unfold sourceCurveCutJetDegree
    calc
      1 + 2 * n * (v - 1) ≤ 2 * n + 2 * n * (v - 1) := by omega
      _ = 2 * n * (1 + (v - 1)) := by ring
      _ = 2 * n * v := by rw [Nat.add_sub_of_le (Nat.one_le_iff_ne_zero.mpr hv.ne')])
  unfold sourceCurveCutJetDegree
  exact Nat.add_le_add_left (Nat.mul_le_mul_right (v - 1)
    (Nat.mul_le_mul_left 2 hKn)) 1

/-- With source challenge height `ell*h`, the retained challenge-coordinate degree is at most
`3*n*ell*h`. -/
theorem sourceCurveCutChallengeDegree_mul_le (n K ℓ H h : ℕ)
    (hn : 0 < n) (hKn : K ≤ n) (hh : 0 < h) (hH : H ≤ ℓ * h) :
    sourceCurveCutChallengeDegree ℓ K H ≤ 3 * n * ℓ * h := by
  unfold sourceCurveCutChallengeDegree
  have hℓn : ℓ ≤ n * ℓ := Nat.le_mul_of_pos_left ℓ hn
  have hℓnh : ℓ ≤ n * ℓ * h := hℓn.trans (Nat.le_mul_of_pos_right _ hh)
  calc
    ℓ + 2 * K * H ≤ ℓ + 2 * n * (ℓ * h) :=
      Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hKn) hH) ℓ
    _ ≤ n * ℓ * h + 2 * n * (ℓ * h) :=
      Nat.add_le_add_right hℓnh _
    _ = 3 * n * ℓ * h := by ring

/-- The exact mixed degree of a source stage admits the midpoint scalar bound when its
jet degree and challenge height are bounded by the certificate caps. -/
theorem sourceCurveInitialMixedDegree_le_uniformCaps (r n K ℓ j H v h : ℕ)
    (hn : 0 < n) (hKn : K ≤ n) (hj : 0 < j) (hh : 0 < h)
    (hjv : j ≤ v) (hH : H ≤ ℓ * h) :
    sourceCurveInitialMixedDegree r ℓ K j H ≤
      ℓ * h * (3 * r + 5) * 2 ^ r * v ^ (r + 1) * n ^ (r + 1) := by
  let b := sourceCurveCutJetDegree K j
  let a := sourceCurveCutChallengeDegree ℓ K H
  have hb : b ≤ 2 * n * v := (sourceCurveCutJetDegree_le n K j hn hKn hj).trans
    (Nat.mul_le_mul_left (2 * n) hjv)
  have ha : a ≤ 3 * n * ℓ * h :=
    sourceCurveCutChallengeDegree_mul_le n K ℓ H h hn hKn hh hH
  have hbpow : b ^ (r + 1) ≤ (2 * n * v) ^ (r + 1) := Nat.pow_le_pow_left hb _
  have hbpow' : b ^ r ≤ (2 * n * v) ^ r := Nat.pow_le_pow_left hb _
  have hfirst := Nat.mul_le_mul hH hbpow
  have hsecond := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul_left (r + 1) hjv) ha) hbpow'
  unfold sourceCurveInitialMixedDegree
  dsimp only [a, b] at hbpow hbpow' hfirst hsecond ⊢
  calc
    H * sourceCurveCutJetDegree K j ^ (r + 1) +
        (r + 1) * j * sourceCurveCutChallengeDegree ℓ K H *
          sourceCurveCutJetDegree K j ^ r ≤
      ℓ * h * (2 * n * v) ^ (r + 1) +
        ((r + 1) * v * (3 * n * ℓ * h)) * (2 * n * v) ^ r := by
      apply Nat.add_le_add
      · exact hfirst
      · exact hsecond
    _ = ℓ * h * (3 * r + 5) * 2 ^ r * v ^ (r + 1) * n ^ (r + 1) := by
      rw [pow_succ]
      ring

private theorem midpoint_ratio_le_two_div (δ : ℝ) (n N D : ℕ)
    (hδ : 0 < δ) (hn : 0 < n) (hN : N ≤ n)
    (hD : δ * n / 2 ≤ (D : ℝ)) :
    (N : ℝ) / D ≤ 2 / δ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hD
  apply (div_le_iff₀ hDpos).mpr
  have hscale : (0 : ℝ) ≤ 2 / δ := by positivity
  have hm := mul_le_mul_of_nonneg_left hD hscale
  have he : (2 / δ) * (δ * n / 2) = (n : ℝ) := by field_simp
  rw [he] at hm
  exact (show (N : ℝ) ≤ n by exact_mod_cast hN).trans hm

/-- Both midpoint ratios are at most `2/δ`. -/
theorem correlatedMidpoint_ratios_le_two_div (δ : ℝ) (n k A : ℕ)
    (hδ : 0 < δ) (hn : 0 < n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    let L := correlatedMidpoint δ n k
    (((n - L + 1 : ℕ) : ℝ) / ((A - L + 1 : ℕ) : ℝ) ≤ 2 / δ) ∧
      (((n - k + 1 : ℕ) : ℝ) / ((L - k + 1 : ℕ) : ℝ) ≤ 2 / δ) := by
  dsimp only
  let L := correlatedMidpoint δ n k
  have hL := correlatedMidpoint_bounds δ n k A hδ.le hgap hAn
  have hLpos : 0 < L := hk.trans_le hL.1
  have hnL : n - L + 1 ≤ n := by omega
  have hnk : n - k + 1 ≤ n := by
    have hkn : k ≤ n := hL.1.trans (hL.2.1.trans hAn)
    omega
  exact ⟨midpoint_ratio_le_two_div δ n (n - L + 1) (A - L + 1)
      hδ hn hnL hL.2.2.2.1,
    midpoint_ratio_le_two_div δ n (n - k + 1) (L - k + 1)
      hδ hn hnk hL.2.2.2.2⟩

/-- The sharp midpoint-normalized cost of one separant stage, retaining its actual order. -/
noncomputable def polynomialCurveSharpStageBound
    (δ : ℝ) (n ℓ v h r : ℕ) : ℝ :=
  (ℓ : ℝ) * 2 ^ r * (v : ℝ) ^ (r + 1) *
    ((h : ℝ) * (3 * r + 5) * (2 / δ) ^ (r + 1) + (2 / δ) ^ r) *
      (n : ℝ) ^ (r + 1)

/-- The exact arbitrary-order regular-chart budget at the midpoint is bounded by the midpoint
single-stage scalar.  The stage may use any positive jet degree `j ≤ v` and challenge height
`H ≤ ell*h`. -/
theorem regularSymbolicCurveMCASharpBound_midpoint_le_stageBound (δ : ℝ)
    (r n K k A ℓ j H v h : ℕ)
    (hδ : 0 < δ) (hn : 0 < n) (hk : 0 < k) (hj : 0 < j) (hh : 0 < h)
    (hKn : K ≤ n) (hjv : j ≤ v) (hH : H ≤ ℓ * h)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    let L := correlatedMidpoint δ n k
    (regularSymbolicCurveMCASharpBound r n ℓ K k L A j H : ℝ) ≤
      polynomialCurveSharpStageBound δ n ℓ v h r := by
  dsimp only
  let L := correlatedMidpoint δ n k
  have hratios := correlatedMidpoint_ratios_le_two_div δ n k A hδ hn hk hgap hAn
  have hL := correlatedMidpoint_bounds δ n k A hδ.le hgap hAn
  have hkA := hL.1.trans hL.2.1
  have hJ : (sourceCurveInitialMixedDegree r ℓ K j H : ℝ) ≤
      (ℓ : ℝ) * h * (3 * r + 5) * 2 ^ r * v ^ (r + 1) * n ^ (r + 1) := by
    exact_mod_cast sourceCurveInitialMixedDegree_le_uniformCaps r n K ℓ j H v h
      hn hKn hj hh hjv hH
  have hb : (sourceCurveCutJetDegree K j : ℝ) ≤ 2 * n * v := by
    exact_mod_cast (sourceCurveCutJetDegree_le n K j hn hKn hj).trans
      (Nat.mul_le_mul_left (2 * n) hjv)
  have hη : ((n - k + 1 : ℕ) : ℝ) / (A - k + 1 : ℕ) ≤ 2 / δ := by
    apply le_trans ?_ hratios.2
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast (Nat.add_le_add_right (Nat.sub_le_sub_right hL.2.1 k) 1)
  have hPA : (AffineHilbert.dimensionSensitiveIncidenceProduct n A k 1 r : ℝ) ≤
      (2 / δ) ^ r := by
    have hp : (AffineHilbert.dimensionSensitiveIncidenceProduct n A k 1 r : ℝ) ≤
        (((n-k+1 : ℕ) : ℝ) / (A-k+1 : ℕ)) ^ r := by
      simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_natCast] using
        ((Rat.cast_le (K := ℝ)).mpr
          (AffineHilbert.dimensionSensitiveIncidenceProduct_le_first_pow n A k r hkA hAn))
    exact hp.trans (pow_le_pow_left₀ (by positivity) hη r)
  have hPL : (AffineHilbert.dimensionSensitiveIncidenceProduct n L k 1 r : ℝ) ≤
      (2 / δ) ^ r := by
    have hp : (AffineHilbert.dimensionSensitiveIncidenceProduct n L k 1 r : ℝ) ≤
        (((n-k+1 : ℕ) : ℝ) / (L-k+1 : ℕ)) ^ r := by
      simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_natCast] using
        ((Rat.cast_le (K := ℝ)).mpr
          (AffineHilbert.dimensionSensitiveIncidenceProduct_le_first_pow n L k r hL.1 hL.2.2.1))
    exact hp.trans (pow_le_pow_left₀ (by positivity) hratios.2 r)
  have hPA0 : (0 : ℝ) ≤ AffineHilbert.dimensionSensitiveIncidenceProduct n A k 1 r := by
    exact_mod_cast AffineHilbert.dimensionSensitiveIncidenceProduct_nonneg n A k 1 r
  have hPL0 : (0 : ℝ) ≤ AffineHilbert.dimensionSensitiveIncidenceProduct n L k 1 r := by
    exact_mod_cast AffineHilbert.dimensionSensitiveIncidenceProduct_nonneg n L k 1 r
  have hfirst := mul_le_mul (mul_le_mul hJ hratios.1 (by positivity) (by positivity)) hPA
    (by positivity) (by positivity)
  have hnL : ((n - L : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n L
  have hjR : (j : ℝ) ≤ v := by exact_mod_cast hjv
  have hcoeff : (ℓ : ℝ) * (n-L : ℕ) * j * (sourceCurveCutJetDegree K j : ℝ)^r ≤
      ℓ * n * v * (2*n*v)^r := by gcongr
  have hsecond := mul_le_mul hcoeff hPL (by positivity) (by positivity)
  unfold regularSymbolicCurveMCASharpBound
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow,
    Nat.cast_mul]
  calc
    _ ≤ ((ℓ : ℝ) * h * (3*r+5) * 2^r * v^(r+1) * n^(r+1)) *
        (2/δ) * (2/δ)^r + (ℓ*n*v*(2*n*v)^r) * (2/δ)^r := add_le_add hfirst hsecond
    _ = polynomialCurveSharpStageBound δ n ℓ v h r := by
      unfold polynomialCurveSharpStageBound
      simp only [mul_pow, pow_succ]
      ring

/-- The uniform single-stage bound after replacing the actual order by the certificate cap. -/
noncomputable def polynomialCurveSharpUniformStageBound
    (δ : ℝ) (n ℓ v h d : ℕ) : ℝ :=
  (ℓ : ℝ) * 2 ^ d * (v : ℝ) ^ (d + 1) *
    ((h : ℝ) * (3 * d + 5) * (2 / δ) ^ (d + 1) + (2 / δ) ^ d) *
      (n : ℝ) ^ (d + 1)

/-- A stage of order at most `d` is bounded by the uniform midpoint scalar. -/
theorem polynomialCurveSharpStageBound_le_uniform (δ : ℝ) (n ℓ v h r d : ℕ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hn : 0 < n) (hv : 0 < v) (hr : r ≤ d) :
    polynomialCurveSharpStageBound δ n ℓ v h r ≤
      polynomialCurveSharpUniformStageBound δ n ℓ v h d := by
  let c := 2 / δ
  have hc : (1 : ℝ) ≤ c := by
    dsimp only [c]
    apply (le_div_iff₀ hδ).mpr
    linarith
  have hv' : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htwo : (1 : ℝ) ≤ 2 := by norm_num
  have hpowTwo : (2 : ℝ) ^ r ≤ 2 ^ d := pow_le_pow_right₀ htwo hr
  have hpowV : (v : ℝ) ^ (r + 1) ≤ v ^ (d + 1) :=
    pow_le_pow_right₀ hv' (Nat.add_le_add_right hr 1)
  have hpowN : (n : ℝ) ^ (r + 1) ≤ n ^ (d + 1) :=
    pow_le_pow_right₀ hn' (Nat.add_le_add_right hr 1)
  have hpowC : c ^ (r + 1) ≤ c ^ (d + 1) :=
    pow_le_pow_right₀ hc (Nat.add_le_add_right hr 1)
  have hpowC' : c ^ r ≤ c ^ d := pow_le_pow_right₀ hc hr
  have hlinear : (3 * r + 5 : ℝ) ≤ 3 * d + 5 := by
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left 3 hr) 5
  have hmain : (h : ℝ) * (3 * r + 5) * c ^ (r + 1) ≤
      h * (3 * d + 5) * c ^ (d + 1) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hlinear (by positivity)
    · exact hpowC
    · positivity
    · positivity
  have hbracket : (h : ℝ) * (3 * r + 5) * c ^ (r + 1) + c ^ r ≤
      h * (3 * d + 5) * c ^ (d + 1) + c ^ d := add_le_add hmain hpowC'
  have hpref : (ℓ : ℝ) * 2 ^ r * v ^ (r + 1) ≤ ℓ * 2 ^ d * v ^ (d + 1) := by
    calc
      (ℓ : ℝ) * 2 ^ r * v ^ (r + 1) = ℓ * (2 ^ r * v ^ (r + 1)) := by ring
      _ ≤ ℓ * (2 ^ d * v ^ (d + 1)) := mul_le_mul_of_nonneg_left
        (mul_le_mul hpowTwo hpowV (by positivity) (by positivity)) (by positivity)
      _ = (ℓ : ℝ) * 2 ^ d * v ^ (d + 1) := by ring
  unfold polynomialCurveSharpStageBound polynomialCurveSharpUniformStageBound
  dsimp only [c] at hbracket
  exact mul_le_mul (mul_le_mul hpref hbracket (by positivity) (by positivity)) hpowN
    (by positivity) (by positivity)

/-- Aggregate arbitrary positive stage jet degrees and actual orders without losing the exact
midpoint coefficient.  The terminal height and every stage height are bounded by `ell*h`. -/
theorem regularSymbolicCurveMCASharp_finiteStage_uniform_le
    {ι : Type*} (S : Finset ι) (order jetDegree height : ι → ℕ)
    (δ : ℝ) (n K k A ℓ v h d : ℕ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hn : 0 < n) (hk : 0 < k) (hv : 0 < v)
    (hh : 0 < h) (hKn : K ≤ n) (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n)
    (hcard : S.card ≤ v) (horder : ∀ i ∈ S, order i ≤ d)
    (hjetPos : ∀ i ∈ S, 0 < jetDegree i) (hjet : ∀ i ∈ S, jetDegree i ≤ v)
    (hheight : ∀ i ∈ S, height i ≤ ℓ * h) :
    let L := correlatedMidpoint δ n k
    ((ℓ * h : ℕ) : ℝ) + ∑ i ∈ S,
        (regularSymbolicCurveMCASharpBound (order i) n ℓ K k L A
          (jetDegree i) (height i) : ℝ) ≤
      (ℓ : ℝ) * polynomialCurveSharpMCAConstant δ v h d * (n : ℝ) ^ (d + 1) := by
  dsimp only
  let L := correlatedMidpoint δ n k
  let B := polynomialCurveSharpUniformStageBound δ n ℓ v h d
  have hB : 0 ≤ B := by
    dsimp [B, polynomialCurveSharpUniformStageBound]
    positivity
  have hstage (i : ι) (hi : i ∈ S) :
      (regularSymbolicCurveMCASharpBound (order i) n ℓ K k L A
        (jetDegree i) (height i) : ℝ) ≤ B := by
    exact (regularSymbolicCurveMCASharpBound_midpoint_le_stageBound δ
      (order i) n K k A ℓ (jetDegree i) (height i) v h hδ hn hk
        (hjetPos i hi) hh hKn (hjet i hi) (hheight i hi) hgap hAn).trans
      (polynomialCurveSharpStageBound_le_uniform δ n ℓ v h (order i) d
        hδ hδone hn hv (horder i hi))
  have hsum : ∑ i ∈ S,
      (regularSymbolicCurveMCASharpBound (order i) n ℓ K k L A
        (jetDegree i) (height i) : ℝ) ≤ (v : ℝ) * B := by
    calc
      _ ≤ ∑ _i ∈ S, B := Finset.sum_le_sum hstage
      _ = (S.card : ℝ) * B := by simp
      _ ≤ (v : ℝ) * B := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hcard
        · exact hB
  have hnPow : (1 : ℝ) ≤ (n : ℝ) ^ (d + 1) := one_le_pow₀ (by exact_mod_cast hn)
  have hterminal : ((ℓ * h : ℕ) : ℝ) ≤
      (ℓ : ℝ) * h * (n : ℝ) ^ (d + 1) := by
    push_cast
    calc
      (ℓ : ℝ) * h = ℓ * h * 1 := by ring
      _ ≤ ℓ * h * (n : ℝ) ^ (d + 1) :=
        mul_le_mul_of_nonneg_left hnPow (by positivity)
  calc
    _ ≤ (ℓ : ℝ) * h * (n : ℝ) ^ (d + 1) + (v : ℝ) * B :=
      add_le_add hterminal hsum
    _ = (ℓ : ℝ) * polynomialCurveSharpMCAConstant δ v h d *
        (n : ℝ) ^ (d + 1) := by
      unfold B polynomialCurveSharpUniformStageBound polynomialCurveSharpMCAConstant
      ring

/-- Increasing the certified Taylor exponent only increases the explicit mixed-degree budget. -/
theorem regularSymbolicCurveMCASharpBound_mono_exponent
    (r n ℓ K k L A v h τ τ' : ℕ) (hτ : τ ≤ τ') :
    regularSymbolicCurveMCASharpBound r n ℓ K k L A v h (τ := τ) ≤
      regularSymbolicCurveMCASharpBound r n ℓ K k L A v h (τ := τ') := by
  have hPA := AffineHilbert.dimensionSensitiveIncidenceProduct_nonneg n A k 1 r
  have hPL := AffineHilbert.dimensionSensitiveIncidenceProduct_nonneg n L k 1 r
  unfold regularSymbolicCurveMCASharpBound sourceCurveInitialMixedDegree
    sourceCurveCutJetDegree sourceCurveCutChallengeDegree
  gcongr

end ReedSolomon
