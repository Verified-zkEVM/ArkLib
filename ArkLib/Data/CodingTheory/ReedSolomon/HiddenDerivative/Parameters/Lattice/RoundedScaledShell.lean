/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Pratyush Mishra
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Lattice.ScaledShellDiscrete
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


/-!
# The rounded scaled-shell estimate

This file discharges the analytic large-`d` hypotheses left explicit by
`ScaledShellDiscrete`.  The proof is deliberately split in two layers:

* two real inequalities turn elementary bounds for the rounded budgets into
  the cross-multiplied natural-number hypotheses of the discrete theorem;
* filter arguments show that those elementary bounds hold for all sufficiently
  large `d`, for each fixed `0 < θ < 1`.

The definitions and proofs are adapted, with permission, from Kai Zhe
Zheng's `rs-ld-mca` formalization at commit
`9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`. The free-order extension was
contributed through PR 1 by Pratyush Mishra at commit
`b1e346fc39780adb442ed2504a316b32702b97af`; its metadata records Codex as
author and Pratyush Mishra as committer. The project-owner permission
attestation is recorded in `docs/kb/sources/rs-ld-mca/PERMISSION.md`.

The shell exponent is `(5-θ)/(5+θ)`.  This is the exponent compatible with
the subsequent interpolation/rank comparison. A smaller exponent printed in
the source snapshot's draft is not valid throughout `0 < θ < 1`; this note
does not describe the normative current all-rate paper.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon
namespace HiddenDerivative

open Filter Asymptotics

/-- The repaired exponent in the scaled-shell estimate. -/
noncomputable def scaledShellExponent (θ : ℝ) : ℝ :=
  (5 - θ) / (5 + θ)

/-- The natural shell factor used in the discrete cardinality bound. -/
noncomputable def scaledShellFactor (θ : ℝ) (d : ℕ) : ℕ :=
  ⌈(d : ℝ) ^ scaledShellExponent θ⌉₊

/-- The weight budget as a function of the freely chosen derivative order.
It agrees with ArkLib's `interpolationWeightBudget θ d`. -/
noncomputable def scaledShellWeight (θ : ℝ) (d : ℕ) : ℕ :=
  ⌊((1 + θ / 2) * (d : ℝ) * ((d ^ 3 : ℕ) : ℝ)) /
      (1 + Real.log (d : ℝ))⌋₊

/-- The ordinary-degree cutoff, again parametrized by the already chosen
derivative order. -/
noncomputable def scaledShellDegree (θ : ℝ) (d : ℕ) : ℕ :=
  ⌊(1 + 3 * θ / 4) * ((d ^ 3 : ℕ) : ℝ)⌋₊

@[simp]
theorem scaledShellWeight_eq_interpolationWeightBudget (θ : ℝ) (d : ℕ) :
    scaledShellWeight θ d = interpolationWeightBudget θ d := by
  simp [scaledShellWeight, interpolationWeightBudget, multiplicity]

@[simp]
theorem scaledShellDegree_eq_higherJetDegreeBudget (θ : ℝ) (d : ℕ) :
    scaledShellDegree θ d = higherJetDegreeBudget θ d := by
  simp [scaledShellDegree, higherJetDegreeBudget, multiplicity]

private noncomputable def shellA (θ : ℝ) : ℝ := 1 + θ / 2
private noncomputable def shellB (θ : ℝ) : ℝ := 1 + 3 * θ / 4
private noncomputable def shellAInv (θ : ℝ) : ℝ := (shellA θ)⁻¹
private noncomputable def shellGap (θ : ℝ) : ℝ :=
  scaledShellExponent θ - shellAInv θ
private noncomputable def shellGamma₁ (θ : ℝ) : ℝ :=
  shellAInv θ + shellGap θ / 4
private noncomputable def shellGamma₂ (θ : ℝ) : ℝ :=
  shellAInv θ + shellGap θ / 2

/-- A coefficient strictly between the raw ordinary cutoff and the weight
coefficient.  It leaves room for the floor and the `d-1` shift. -/
private noncomputable def shellB₁ (θ : ℝ) : ℝ :=
  shellA θ + 3 * (shellB θ - shellA θ) / 4

/-- A coefficient strictly between `1` and `shellB₁ / shellA`. -/
private noncomputable def shellBadDecay (θ : ℝ) : ℝ :=
  (1 + shellB₁ θ / shellA θ) / 2

private theorem shellA_pos {θ : ℝ} (hθ : 0 < θ) : 0 < shellA θ := by
  unfold shellA
  linarith

private theorem shellB_pos {θ : ℝ} (hθ : 0 < θ) : 0 < shellB θ := by
  unfold shellB
  linarith

private theorem scaledShellExponent_pos {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ < 1) :
    0 < scaledShellExponent θ := by
  unfold scaledShellExponent
  exact div_pos (by linarith) (by linarith)

private theorem shellGap_eq {θ : ℝ} (hθ : 0 < θ) :
    shellGap θ = θ * (1 - θ) / ((5 + θ) * (2 + θ)) := by
  have h5 : 5 + θ ≠ 0 := by linarith
  have h2 : 2 + θ ≠ 0 := by linarith
  unfold shellGap shellAInv shellA scaledShellExponent
  field_simp
  ring

private theorem shellGap_pos {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ < 1) : 0 < shellGap θ := by
  rw [shellGap_eq hθ]
  positivity

private theorem shellGamma₁_pos {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ < 1) : 0 < shellGamma₁ θ := by
  have ha := shellA_pos hθ
  have hg := shellGap_pos hθ hθ₁
  unfold shellGamma₁ shellAInv
  positivity

private theorem shellAInv_lt_gamma₁ {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ < 1) :
    shellAInv θ < shellGamma₁ θ := by
  unfold shellGamma₁
  linarith [shellGap_pos hθ hθ₁]

private theorem shellGamma₁_lt_gamma₂ {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ < 1) :
    shellGamma₁ θ < shellGamma₂ θ := by
  unfold shellGamma₁ shellGamma₂
  linarith [shellGap_pos hθ hθ₁]

private theorem shellGamma₂_lt_exponent {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ < 1) :
    shellGamma₂ θ < scaledShellExponent θ := by
  have hg := shellGap_pos hθ hθ₁
  have heq : scaledShellExponent θ = shellAInv θ + shellGap θ := by
    unfold shellGap
    ring
  rw [heq]
  unfold shellGamma₂
  linarith

private theorem inv_gamma₁_lt_shellA {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ < 1) :
    (shellGamma₁ θ)⁻¹ < shellA θ := by
  have ha := shellA_pos hθ
  have hg := shellGamma₁_pos hθ hθ₁
  rw [inv_lt_comm₀ hg ha]
  simpa [shellAInv] using shellAInv_lt_gamma₁ hθ hθ₁

private theorem shellA_lt_b₁ {θ : ℝ} (hθ : 0 < θ) :
    shellA θ < shellB₁ θ := by
  unfold shellB₁ shellB shellA
  linarith

private theorem shellB₁_lt_b {θ : ℝ} (hθ : 0 < θ) :
    shellB₁ θ < shellB θ := by
  unfold shellB₁ shellB shellA
  linarith

private theorem one_lt_shellBadDecay {θ : ℝ} (hθ : 0 < θ) :
    1 < shellBadDecay θ := by
  have ha := shellA_pos hθ
  have hab := shellA_lt_b₁ hθ
  unfold shellBadDecay
  have : 1 < shellB₁ θ / shellA θ :=
    (lt_div_iff₀ ha).2 (by simpa using hab)
  linarith

/-! ## Two generic real-to-discrete estimates -/

private theorem badTupleEstimate
    {θ : ℝ} (hθ : 0 < θ)
    {d W S : ℕ} (hd : 2 ≤ d)
    (hSW : S + 1 ≤ W)
    (hrS : d - 1 ≤ S + 1)
    (ht : shellB₁ θ * (d : ℝ) ^ 3 ≤
      ((S + 1 - (d - 1) : ℕ) : ℝ))
    (hW : (W : ℝ) ≤
      shellA θ * (d : ℝ) ^ 4 / (1 + Real.log (d : ℝ)))
    (hcoefficient : shellBadDecay θ * shellA θ * (d : ℝ) ≤
      ((d - 1 : ℕ) : ℝ) * shellB₁ θ)
    (hlog : Real.log 2 + Real.log (d : ℝ) ≤
      shellBadDecay θ * (1 + Real.log (d : ℝ))) :
    2 * ((d - 1) *
      (W - (S + 1) + (d - 1)) ^ (d - 1)) ≤ W ^ (d - 1) := by
  let r := d - 1
  let t := S + 1 - r
  have hd0 : 0 < d := by omega
  have hr0 : 0 < r := by omega
  have htW : t ≤ W := by
    dsimp [t, r]
    omega
  have hW0 : 0 < W := lt_of_lt_of_le (by omega : 0 < S + 1) hSW
  have hL0 : 0 < 1 + Real.log (d : ℝ) := by
    have : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd0)
    linarith
  have hraw :
      (W : ℝ) * (1 + Real.log (d : ℝ)) ≤
        shellA θ * (d : ℝ) ^ 4 :=
    (le_div_iff₀ hL0).mp hW
  have hscaled :
      shellBadDecay θ * (W : ℝ) *
          (1 + Real.log (d : ℝ)) ≤
        (r : ℝ) * (t : ℝ) := by
    calc
      shellBadDecay θ * (W : ℝ) *
          (1 + Real.log (d : ℝ)) ≤
          shellBadDecay θ * (shellA θ * (d : ℝ) ^ 4) := by
            have hc : 0 < shellBadDecay θ :=
              (one_lt_shellBadDecay hθ).trans' zero_lt_one
            nlinarith
      _ = (shellBadDecay θ * shellA θ * (d : ℝ)) *
          (d : ℝ) ^ 3 := by ring
      _ ≤ ((r : ℝ) * shellB₁ θ) * (d : ℝ) ^ 3 := by
        gcongr
      _ ≤ (r : ℝ) * (t : ℝ) := by
        dsimp [t, r] at ht ⊢
        nlinarith [ht]
  have hu : shellBadDecay θ * (1 + Real.log (d : ℝ)) ≤
      (r : ℝ) * (t : ℝ) / (W : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hW0)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  have htwo : (2 : ℝ) * (r : ℝ) ≤
      Real.exp ((r : ℝ) * (t : ℝ) / (W : ℝ)) := by
    calc
      (2 : ℝ) * (r : ℝ) ≤ 2 * (d : ℝ) := by
        gcongr
        exact_mod_cast Nat.sub_le d 1
      _ = Real.exp (Real.log (2 * (d : ℝ))) := by
        symm
        apply Real.exp_log
        positivity
      _ = Real.exp (Real.log 2 + Real.log (d : ℝ)) := by
        rw [Real.log_mul (by norm_num) (by exact_mod_cast hd0.ne')]
      _ ≤ Real.exp
          (shellBadDecay θ * (1 + Real.log (d : ℝ))) := by
        exact Real.exp_le_exp.mpr hlog
      _ ≤ Real.exp ((r : ℝ) * (t : ℝ) / (W : ℝ)) :=
        Real.exp_le_exp.mpr hu
  have hdecay :
      (1 - (t : ℝ) / (W : ℝ)) ^ r ≤
        Real.exp (-((r : ℝ) * (t : ℝ) / (W : ℝ))) := by
    have hbase : 0 ≤ 1 - (t : ℝ) / (W : ℝ) := by
      rw [sub_nonneg, div_le_one (by exact_mod_cast hW0)]
      exact_mod_cast htW
    calc
      (1 - (t : ℝ) / (W : ℝ)) ^ r ≤
          (Real.exp (-((t : ℝ) / (W : ℝ)))) ^ r := by
        gcongr
        exact Real.one_sub_le_exp_neg _
      _ = Real.exp (-((r : ℝ) * (t : ℝ) / (W : ℝ))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hexp : (2 : ℝ) * (r : ℝ) *
      Real.exp (-((r : ℝ) * (t : ℝ) / (W : ℝ))) ≤ 1 := by
    calc
      (2 : ℝ) * (r : ℝ) *
          Real.exp (-((r : ℝ) * (t : ℝ) / (W : ℝ))) ≤
          Real.exp ((r : ℝ) * (t : ℝ) / (W : ℝ)) *
            Real.exp (-((r : ℝ) * (t : ℝ) / (W : ℝ))) := by
        gcongr
      _ = 1 := by rw [← Real.exp_add]; ring_nf; simp
  have hbaseEq :
      (((W - t : ℕ) : ℝ)) =
        (W : ℝ) * (1 - (t : ℝ) / (W : ℝ)) := by
    rw [Nat.cast_sub htW]
    field_simp
  have hreal :
      (2 : ℝ) * (r : ℝ) * (((W - t : ℕ) : ℝ) ^ r) ≤
        (W : ℝ) ^ r := by
    rw [hbaseEq, mul_pow]
    calc
      (2 : ℝ) * (r : ℝ) *
          ((W : ℝ) ^ r * (1 - (t : ℝ) / (W : ℝ)) ^ r) ≤
          (2 : ℝ) * (r : ℝ) *
            ((W : ℝ) ^ r *
              Real.exp (-((r : ℝ) * (t : ℝ) / (W : ℝ)))) := by
        gcongr
      _ = (W : ℝ) ^ r *
          ((2 : ℝ) * (r : ℝ) *
            Real.exp (-((r : ℝ) * (t : ℝ) / (W : ℝ)))) := by ring
      _ ≤ (W : ℝ) ^ r * 1 := by gcongr
      _ = (W : ℝ) ^ r := by ring
  have hbaseNat : W - (S + 1) + (d - 1) = W - t := by
    dsimp [t, r]
    omega
  rw [hbaseNat]
  have hnat : 2 * r * (W - t) ^ r ≤ W ^ r := by
    exact_mod_cast hreal
  simpa [r, Nat.mul_assoc] using hnat

private theorem shellRatioEstimate
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1)
    {d W : ℕ} (hd : 2 ≤ d)
    (hWlower : (d : ℝ) ^ 4 ≤
      shellGamma₁ θ * (1 + Real.log (d : ℝ)) * (W : ℝ))
    (hnumerator : shellGamma₁ θ * ((d - 1 : ℕ) : ℝ) *
      (((d ^ 3 + d * (d - 1) / 2 : ℕ) : ℝ)) ≤
        shellGamma₂ θ * (d : ℝ) ^ 4)
    (hlog : Real.log 2 +
        shellGamma₂ θ * (1 + Real.log (d : ℝ)) ≤
      scaledShellExponent θ * Real.log (d : ℝ)) :
    2 * (W + d ^ 3 + d * (d - 1) / 2) ^ (d - 1) ≤
      scaledShellFactor θ d * W ^ (d - 1) := by
  let r := d - 1
  let N := d ^ 3 + d * (d - 1) / 2
  have hd0 : 0 < d := by omega
  have hg1 := shellGamma₁_pos hθ hθ₁
  have hL0 : 0 < 1 + Real.log (d : ℝ) := by
    have : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd0)
    linarith
  have hW0 : 0 < W := by
    by_contra h
    have hWz : W = 0 := Nat.eq_zero_of_not_pos h
    rw [hWz, Nat.cast_zero, mul_zero] at hWlower
    have : 0 < (d : ℝ) ^ 4 := by positivity
    linarith
  have hu : (r : ℝ) * (N : ℝ) / (W : ℝ) ≤
      shellGamma₂ θ * (1 + Real.log (d : ℝ)) := by
    rw [div_le_iff₀ (by exact_mod_cast hW0)]
    have hmain : shellGamma₁ θ * ((r : ℝ) * (N : ℝ)) ≤
        shellGamma₂ θ * (d : ℝ) ^ 4 := by
      simpa [r, N, mul_assoc] using hnumerator
    have hscaled := mul_le_mul_of_nonneg_left hWlower
      (show 0 ≤ shellGamma₂ θ from
        (shellGamma₁_pos hθ hθ₁).le.trans
          (shellGamma₁_lt_gamma₂ hθ hθ₁).le)
    calc
      (r : ℝ) * (N : ℝ) ≤
          (shellGamma₂ θ * (d : ℝ) ^ 4) / shellGamma₁ θ := by
        rw [le_div_iff₀ hg1]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
      _ ≤ shellGamma₂ θ *
          ((1 + Real.log (d : ℝ)) * (W : ℝ)) := by
        rw [div_le_iff₀ hg1]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
      _ = shellGamma₂ θ * (1 + Real.log (d : ℝ)) * (W : ℝ) := by ring
  have hpRatio :
      ((W + N : ℕ) : ℝ) ^ r / (W : ℝ) ^ r ≤
        Real.exp (shellGamma₂ θ * (1 + Real.log (d : ℝ))) := by
    have hbase :
        ((W + N : ℕ) : ℝ) / (W : ℝ) =
          1 + (N : ℝ) / (W : ℝ) := by
      push_cast
      field_simp
    rw [← div_pow, hbase]
    calc
      (1 + (N : ℝ) / (W : ℝ)) ^ r ≤
          (Real.exp ((N : ℝ) / (W : ℝ))) ^ r := by
        gcongr
        simpa [add_comm] using Real.add_one_le_exp ((N : ℝ) / (W : ℝ))
      _ = Real.exp ((r : ℝ) * (N : ℝ) / (W : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ Real.exp (shellGamma₂ θ * (1 + Real.log (d : ℝ))) :=
        Real.exp_le_exp.mpr hu
  have hratioReal :
      (2 : ℝ) * (((W + N : ℕ) : ℝ) ^ r / (W : ℝ) ^ r) ≤
        (d : ℝ) ^ scaledShellExponent θ := by
    calc
      (2 : ℝ) * (((W + N : ℕ) : ℝ) ^ r / (W : ℝ) ^ r) ≤
          2 * Real.exp
            (shellGamma₂ θ * (1 + Real.log (d : ℝ))) := by gcongr
      _ = Real.exp (Real.log 2 +
          shellGamma₂ θ * (1 + Real.log (d : ℝ))) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ Real.exp (scaledShellExponent θ * Real.log (d : ℝ)) :=
        Real.exp_le_exp.mpr hlog
      _ = (d : ℝ) ^ scaledShellExponent θ := by
        rw [Real.rpow_def_of_pos (by exact_mod_cast hd0)]
        congr 1
        ring
  have hceil : (d : ℝ) ^ scaledShellExponent θ ≤
      (scaledShellFactor θ d : ℝ) := by
    exact Nat.le_ceil _
  have hcrossReal :
      (2 : ℝ) * (((W + N : ℕ) : ℝ) ^ r) ≤
        (scaledShellFactor θ d : ℝ) * (W : ℝ) ^ r := by
    have hpow : 0 < (W : ℝ) ^ r := by positivity
    rw [← div_le_iff₀ hpow]
    calc
      (2 : ℝ) * ((W + N : ℕ) : ℝ) ^ r / (W : ℝ) ^ r =
          2 * (((W + N : ℕ) : ℝ) ^ r / (W : ℝ) ^ r) := by ring
      _ ≤ (d : ℝ) ^ scaledShellExponent θ := hratioReal
      _ ≤ (scaledShellFactor θ d : ℝ) := hceil
  dsimp [r, N] at hcrossReal ⊢
  have hnat :
      2 * (W + (d ^ 3 + d * (d - 1) / 2)) ^ (d - 1) ≤
        scaledShellFactor θ d * W ^ (d - 1) := by
    exact_mod_cast hcrossReal
  simpa [Nat.add_assoc] using hnat

/-! ## Eventual rounded estimates -/

private theorem tendsto_one_add_log_div_natCast :
    Tendsto (fun d : ℕ ↦
      (1 + Real.log (d : ℝ)) / (d : ℝ)) atTop (nhds 0) := by
  have hconst : Tendsto (fun x : ℝ ↦ (1 : ℝ) / x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlog : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hsum : Tendsto (fun x : ℝ ↦
      (1 + Real.log x) / x) atTop (nhds 0) := by
    convert hconst.add hlog using 1 <;> simp [add_div]
  exact hsum.comp tendsto_natCast_atTop_atTop

private theorem tendsto_log_natCast_atTop :
    Tendsto (fun d : ℕ ↦ Real.log (d : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-! ## The eventual shell theorem -/

/-- The ceiling used for the natural shell factor costs at most another
factor two. -/
theorem scaledShellFactor_cast_le_two_rpow
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1)
    {d : ℕ} (hd : 1 ≤ d) :
    (scaledShellFactor θ d : ℝ) ≤
      2 * (d : ℝ) ^ scaledShellExponent θ := by
  have hpow : 1 ≤ (d : ℝ) ^ scaledShellExponent θ := by
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    simpa using Real.one_le_rpow hdreal
      (scaledShellExponent_pos hθ hθ₁).le
  have hnonneg : 0 ≤ (d : ℝ) ^ scaledShellExponent θ :=
    Real.rpow_nonneg (by positivity) _
  have hceil : (scaledShellFactor θ d : ℝ) <
      (d : ℝ) ^ scaledShellExponent θ + 1 := by
    exact Nat.ceil_lt_add_one hnonneg
  linarith

set_option maxHeartbeats 500000 in
-- The eventual analytic estimate combines several nonlinear rounded bounds in one proof.
/-- For fixed `0 < θ < 1`, the two explicit hypotheses of
`scaledExponentCount_shell_le_mul_goodScaledExponentCount` hold for all
sufficiently large derivative orders.  This statement is the analytic core
of the repaired shell argument. -/
theorem eventually_scaledShell_discreteHypotheses
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ∀ᶠ d : ℕ in atTop,
      2 * ((d - 1) *
          (scaledShellWeight θ d - (scaledShellDegree θ d + 1) +
            (d - 1)) ^ (d - 1)) ≤
          scaledShellWeight θ d ^ (d - 1) ∧
      2 * (scaledShellWeight θ d + d ^ 3 + d * (d - 1) / 2) ^ (d - 1) ≤
          scaledShellFactor θ d *
            scaledShellWeight θ d ^ (d - 1) := by
  let a := shellA θ
  let b := shellB θ
  let a' := (shellGamma₁ θ)⁻¹
  let b' := shellB₁ θ
  let c := shellBadDecay θ
  let γ₁ := shellGamma₁ θ
  let γ₂ := shellGamma₂ θ
  let β := scaledShellExponent θ
  have ha : 0 < a := shellA_pos hθ
  have hb : 0 < b := shellB_pos hθ
  have hγ₁ : 0 < γ₁ := shellGamma₁_pos hθ hθ₁
  have hγ₂ : 0 < γ₂ :=
    hγ₁.trans (shellGamma₁_lt_gamma₂ hθ hθ₁)
  have ha' : 0 < a' := by dsimp [a']; positivity
  have hc : 1 < c := one_lt_shellBadDecay hθ
  have hfloorGap : 0 < a - a' := by
    dsimp [a, a']
    exact sub_pos.mpr (inv_gamma₁_lt_shellA hθ hθ₁)
  have hdegreeGap : 0 < b - b' := by
    dsimp [b, b']
    exact sub_pos.mpr (shellB₁_lt_b hθ)
  have hdecayGap : 0 < b' - c * a := by
    have hab : 0 < a := ha
    have hba : a < b' := by
      dsimp [a, b']
      exact shellA_lt_b₁ hθ
    dsimp [c, shellBadDecay]
    rw [sub_pos]
    calc
      ((1 + b' / a) / 2) * a = (a + b') / 2 := by
        field_simp [ha.ne']
      _ < b' := by linarith
  have hgammaGap : 0 < γ₂ - γ₁ := by
    exact sub_pos.mpr (shellGamma₁_lt_gamma₂ hθ hθ₁)
  have hexponentGap : 0 < β - γ₂ := by
    exact sub_pos.mpr (shellGamma₂_lt_exponent hθ hθ₁)
  have hsmallFloor : ∀ᶠ d : ℕ in atTop,
      (1 + Real.log (d : ℝ)) / (d : ℝ) < a - a' :=
    tendsto_one_add_log_div_natCast.eventually_lt_const hfloorGap
  have hsmallDegree : ∀ᶠ d : ℕ in atTop,
      (1 + Real.log (d : ℝ)) / (d : ℝ) < a' / (b + 1) := by
    apply tendsto_one_add_log_div_natCast.eventually_lt_const
    positivity
  have hlargeDegree : ∀ᶠ d : ℕ in atTop,
      (b - b')⁻¹ ≤ (d : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hlargeDecay : ∀ᶠ d : ℕ in atTop,
      b' / (b' - c * a) ≤ (d : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hlargeNumerator : ∀ᶠ d : ℕ in atTop,
      γ₁ / (2 * (γ₂ - γ₁)) ≤ (d : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hlargeBadLog : ∀ᶠ d : ℕ in atTop,
      (Real.log 2 - c) / (c - 1) ≤ Real.log (d : ℝ) :=
    tendsto_log_natCast_atTop.eventually (eventually_ge_atTop _)
  have hlargeRatioLog : ∀ᶠ d : ℕ in atTop,
      (Real.log 2 + γ₂) / (β - γ₂) ≤ Real.log (d : ℝ) :=
    tendsto_log_natCast_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (2 : ℕ), hsmallFloor,
      hsmallDegree, hlargeDegree, hlargeDecay, hlargeNumerator,
      hlargeBadLog, hlargeRatioLog] with d hd hsmallFloorD
      hsmallDegreeD hlargeDegreeD hlargeDecayD hlargeNumeratorD
      hlargeBadLogD hlargeRatioLogD
  let W := scaledShellWeight θ d
  let S := scaledShellDegree θ d
  let r := d - 1
  have hd0 : 0 < d := by omega
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd0
  have hdreal1 : 1 ≤ (d : ℝ) := by exact_mod_cast hd0
  have hlognonneg : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hdreal1
  have hL : 0 < 1 + Real.log (d : ℝ) := by linarith
  have hd_le_d4 : (d : ℝ) ≤ (d : ℝ) ^ 4 := by
    calc
      (d : ℝ) = (d : ℝ) ^ 1 := by ring
      _ ≤ (d : ℝ) ^ 4 := pow_le_pow_right₀ hdreal1 (by omega)
  have hfloorLoss : 1 < (a - a') * (d : ℝ) ^ 4 /
      (1 + Real.log (d : ℝ)) := by
    have hsmall' : 1 + Real.log (d : ℝ) < (a - a') * (d : ℝ) :=
      (div_lt_iff₀ hdreal).mp hsmallFloorD
    have hmain : 1 + Real.log (d : ℝ) <
        (a - a') * (d : ℝ) ^ 4 :=
      hsmall'.trans_le (mul_le_mul_of_nonneg_left hd_le_d4 hfloorGap.le)
    exact (lt_div_iff₀ hL).2 (by simpa using hmain)
  have hWstrict : a' * (d : ℝ) ^ 4 /
      (1 + Real.log (d : ℝ)) < (W : ℝ) := by
    have hfloor := Nat.sub_one_lt_floor
      ((a * (d : ℝ) ^ 4) / (1 + Real.log (d : ℝ)))
    have hraw : W = ⌊(a * (d : ℝ) ^ 4) /
        (1 + Real.log (d : ℝ))⌋₊ := by
      dsimp [W, scaledShellWeight, a, shellA]
      congr 1
      push_cast
      ring
    rw [← hraw] at hfloor
    have hcompare : a' * (d : ℝ) ^ 4 /
          (1 + Real.log (d : ℝ)) <
        a * (d : ℝ) ^ 4 / (1 + Real.log (d : ℝ)) - 1 := by
      rw [lt_sub_iff_add_lt]
      calc
        a' * (d : ℝ) ^ 4 / (1 + Real.log (d : ℝ)) + 1 <
            a' * (d : ℝ) ^ 4 / (1 + Real.log (d : ℝ)) +
              (a - a') * (d : ℝ) ^ 4 /
                (1 + Real.log (d : ℝ)) := by linarith
        _ = a * (d : ℝ) ^ 4 /
              (1 + Real.log (d : ℝ)) := by ring
    exact hcompare.trans hfloor
  have hWlower : (d : ℝ) ^ 4 ≤
      γ₁ * (1 + Real.log (d : ℝ)) * (W : ℝ) := by
    have h := hWstrict.le
    have ha'eq : a' * γ₁ = 1 := by
      dsimp [a', γ₁]
      exact inv_mul_cancel₀ hγ₁.ne'
    have := mul_le_mul_of_nonneg_left h (mul_nonneg hγ₁.le hL.le)
    calc
      (d : ℝ) ^ 4 = γ₁ * (1 + Real.log (d : ℝ)) *
          (a' * (d : ℝ) ^ 4 / (1 + Real.log (d : ℝ))) := by
        field_simp [hL.ne']
        nlinarith
      _ ≤ γ₁ * (1 + Real.log (d : ℝ)) * (W : ℝ) := this
  have hWupper : (W : ℝ) ≤
      a * (d : ℝ) ^ 4 / (1 + Real.log (d : ℝ)) := by
    have hrawnonneg : 0 ≤
        a * (d : ℝ) ^ 4 / (1 + Real.log (d : ℝ)) := by positivity
    have h := Nat.floor_le hrawnonneg
    have hraw : W = ⌊(a * (d : ℝ) ^ 4) /
        (1 + Real.log (d : ℝ))⌋₊ := by
      dsimp [W, scaledShellWeight, a, shellA]
      congr 1
      push_cast
      ring
    simpa [hraw] using h
  have hSupper : (S : ℝ) ≤ b * (d : ℝ) ^ 3 := by
    have hrawnonneg : 0 ≤ b * (d : ℝ) ^ 3 := by positivity
    have h := Nat.floor_le hrawnonneg
    have hraw : S = ⌊b * (d : ℝ) ^ 3⌋₊ := by
      dsimp [S, scaledShellDegree, b, shellB]
      congr 1
      push_cast
      rfl
    simpa [hraw] using h
  have hSlower : b * (d : ℝ) ^ 3 < (S : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one (b * (d : ℝ) ^ 3)
    have hraw : S = ⌊b * (d : ℝ) ^ 3⌋₊ := by
      dsimp [S, scaledShellDegree, b, shellB]
      congr 1
      push_cast
      rfl
    simpa [hraw] using h
  have hrS : r ≤ S + 1 := by
    have hb1 : 1 < b := by
      dsimp [b, shellB]
      linarith
    have hdr : (r : ℝ) < b * (d : ℝ) ^ 3 := by
      have hrle : (r : ℝ) ≤ (d : ℝ) := by
        dsimp [r]
        exact_mod_cast Nat.sub_le d 1
      have hdd3 : (d : ℝ) < b * (d : ℝ) ^ 3 := by
        have hd3 : (d : ℝ) ≤ (d : ℝ) ^ 3 := by
          calc
            (d : ℝ) = (d : ℝ) ^ 1 := by ring
            _ ≤ (d : ℝ) ^ 3 := pow_le_pow_right₀ hdreal1 (by omega)
        exact hd3.trans_lt (lt_mul_of_one_lt_left (by positivity) hb1)
      exact hrle.trans_lt hdd3
    exact_mod_cast (hdr.trans hSlower).le
  have htLower : b' * (d : ℝ) ^ 3 ≤
      ((S + 1 - r : ℕ) : ℝ) := by
    rw [Nat.cast_sub hrS]
    have hgapD : 1 ≤ (b - b') * (d : ℝ) := by
      calc
        (1 : ℝ) = (b - b') * (b - b')⁻¹ := by
          rw [mul_inv_cancel₀ hdegreeGap.ne']
        _ ≤ (b - b') * (d : ℝ) :=
          mul_le_mul_of_nonneg_left hlargeDegreeD hdegreeGap.le
    have hrle : (r : ℝ) ≤ (b - b') * (d : ℝ) ^ 3 := by
      have hrled : (r : ℝ) ≤ (d : ℝ) := by
        dsimp [r]
        exact_mod_cast Nat.sub_le d 1
      have hdle : (d : ℝ) ≤ (b - b') * (d : ℝ) ^ 3 := by
        have hmul := mul_le_mul_of_nonneg_right hgapD
          (show 0 ≤ (d : ℝ) ^ 2 by positivity)
        calc
          (d : ℝ) ≤ 1 * (d : ℝ) ^ 2 := by
            simpa using pow_le_pow_right₀ hdreal1 (by omega : 1 ≤ 2)
          _ ≤ ((b - b') * (d : ℝ)) * (d : ℝ) ^ 2 := by gcongr
          _ = (b - b') * (d : ℝ) ^ 3 := by ring
      exact hrled.trans hdle
    push_cast
    linarith
  have hSW : S + 1 ≤ W := by
    have hsmall' : (b + 1) * (1 + Real.log (d : ℝ)) < a' * (d : ℝ) := by
      have hbp : 0 < b + 1 := by positivity
      have := (div_lt_iff₀ hdreal).mp hsmallDegreeD
      have hmul := mul_lt_mul_of_pos_left this hbp
      field_simp [hbp.ne'] at hmul
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    have hcompare : (b + 1) * (d : ℝ) ^ 3 <
        a' * (d : ℝ) ^ 4 / (1 + Real.log (d : ℝ)) := by
      rw [lt_div_iff₀ hL]
      nlinarith
    have hSone : ((S + 1 : ℕ) : ℝ) ≤ (b + 1) * (d : ℝ) ^ 3 := by
      push_cast
      have hd3one : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ hdreal1
      nlinarith
    exact_mod_cast hSone.trans_lt (hcompare.trans hWstrict) |>.le
  have hcoefficient : c * a * (d : ℝ) ≤ (r : ℝ) * b' := by
    have hgapD : b' ≤ (b' - c * a) * (d : ℝ) := by
      calc
        b' = (b' - c * a) * (b' / (b' - c * a)) := by
          field_simp [hdecayGap.ne']
        _ ≤ (b' - c * a) * (d : ℝ) :=
          mul_le_mul_of_nonneg_left hlargeDecayD hdecayGap.le
    have hrcast : (r : ℝ) = (d : ℝ) - 1 := by
      dsimp [r]
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      norm_num
    rw [hrcast]
    nlinarith only [hgapD]
  have hbadLog : Real.log 2 + Real.log (d : ℝ) ≤
      c * (1 + Real.log (d : ℝ)) := by
    have hcgap : 0 < c - 1 := by linarith
    have := (div_le_iff₀ hcgap).mp hlargeBadLogD
    linarith
  have hnumSmall : γ₁ * (1 + 1 / (2 * (d : ℝ))) ≤ γ₂ := by
    have hden : 0 < 2 * (γ₂ - γ₁) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlargeNumeratorD hden.le
    have hbase : γ₁ ≤ 2 * (γ₂ - γ₁) * (d : ℝ) := by
      calc
        γ₁ = (2 * (γ₂ - γ₁)) *
            (γ₁ / (2 * (γ₂ - γ₁))) := by
          field_simp [hden.ne']
        _ ≤ (2 * (γ₂ - γ₁)) * (d : ℝ) := hmul
    have hdiv : γ₁ / (2 * (d : ℝ)) ≤ γ₂ - γ₁ := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * (d : ℝ))]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hbase
    calc
      γ₁ * (1 + 1 / (2 * (d : ℝ))) =
          γ₁ + γ₁ / (2 * (d : ℝ)) := by ring
      _ ≤ γ₁ + (γ₂ - γ₁) := by gcongr
      _ = γ₂ := by ring
  have htri : ((d * (d - 1) / 2 : ℕ) : ℝ) ≤ (d : ℝ) ^ 2 / 2 := by
    calc
      ((d * (d - 1) / 2 : ℕ) : ℝ) ≤
      ((d * (d - 1) : ℕ) : ℝ) / (2 : ℝ) := Nat.cast_div_le
      _ ≤ (d : ℝ) ^ 2 / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        push_cast
        rw [Nat.cast_sub (by omega : 1 ≤ d)]
        nlinarith
  have hnumerator : γ₁ * (r : ℝ) *
      (((d ^ 3 + d * (d - 1) / 2 : ℕ) : ℝ)) ≤
        γ₂ * (d : ℝ) ^ 4 := by
    have hrle : (r : ℝ) ≤ (d : ℝ) := by
      dsimp [r]
      exact_mod_cast Nat.sub_le d 1
    have hN : (((d ^ 3 + d * (d - 1) / 2 : ℕ) : ℝ)) ≤
        (d : ℝ) ^ 3 + (d : ℝ) ^ 2 / 2 := by
      push_cast
      simpa using add_le_add_left htri ((d : ℝ) ^ 3)
    calc
      γ₁ * (r : ℝ) *
          (((d ^ 3 + d * (d - 1) / 2 : ℕ) : ℝ)) ≤
          γ₁ * (d : ℝ) *
            ((d : ℝ) ^ 3 + (d : ℝ) ^ 2 / 2) := by gcongr
      _ = (γ₁ * (1 + 1 / (2 * (d : ℝ)))) * (d : ℝ) ^ 4 := by
        field_simp
      _ ≤ γ₂ * (d : ℝ) ^ 4 := by gcongr
  have hratioLog : Real.log 2 + γ₂ * (1 + Real.log (d : ℝ)) ≤
      β * Real.log (d : ℝ) := by
    have hgap : 0 < β - γ₂ := hexponentGap
    have := (div_le_iff₀ hgap).mp hlargeRatioLogD
    linarith
  constructor
  · exact badTupleEstimate hθ hd hSW hrS htLower hWupper
      hcoefficient hbadLog
  · exact shellRatioEstimate hθ hθ₁ hd hWlower hnumerator hratioLog

/-- An ordinary natural threshold extracted from the eventual theorem. -/
theorem exists_scaledShellThreshold
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      2 * ((d - 1) *
          (scaledShellWeight θ d - (scaledShellDegree θ d + 1) +
            (d - 1)) ^ (d - 1)) ≤
          scaledShellWeight θ d ^ (d - 1) ∧
      2 * (scaledShellWeight θ d + d ^ 3 + d * (d - 1) / 2) ^ (d - 1) ≤
          scaledShellFactor θ d *
            scaledShellWeight θ d ^ (d - 1) :=
  eventually_atTop.mp (eventually_scaledShell_discreteHypotheses hθ hθ₁)

/-- Once the two now-proved rounded inequalities are available, the fully
discrete shell theorem gives the desired comparison of exponent counts. -/
theorem scaledShell_cardinality_bound
    {θ : ℝ} {d : ℕ}
    (hbad :
      2 * ((d - 1) *
          (scaledShellWeight θ d - (scaledShellDegree θ d + 1) +
            (d - 1)) ^ (d - 1)) ≤
        scaledShellWeight θ d ^ (d - 1))
    (hratio :
      2 * (scaledShellWeight θ d + d ^ 3 + d * (d - 1) / 2) ^ (d - 1) ≤
        scaledShellFactor θ d * scaledShellWeight θ d ^ (d - 1)) :
    scaledExponentCount d (scaledShellWeight θ d + d ^ 3) ≤
      scaledShellFactor θ d *
        goodScaledExponentCount d
          (scaledShellWeight θ d) (scaledShellDegree θ d) := by
  exact scaledExponentCount_shell_le_mul_goodScaledExponentCount
    d (scaledShellWeight θ d) (scaledShellDegree θ d) (d ^ 3)
      (scaledShellFactor θ d) hbad hratio

/-- The final scaled-lattice cardinality comparison holds eventually in the
derivative order. -/
theorem eventually_scaledShell_cardinality_bound
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ∀ᶠ d : ℕ in atTop,
      scaledExponentCount d (scaledShellWeight θ d + d ^ 3) ≤
        scaledShellFactor θ d *
          goodScaledExponentCount d
            (scaledShellWeight θ d) (scaledShellDegree θ d) := by
  filter_upwards [eventually_scaledShell_discreteHypotheses hθ hθ₁] with d hd
  exact scaledShell_cardinality_bound hd.1 hd.2

/-- The final free-order scaled-lattice cardinality comparison. Its threshold
depends only on `θ`. -/
theorem exists_scaledShellThreshold_for_freeParameters
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      scaledExponentCount d
          (interpolationWeightBudget θ d + d ^ 3) ≤
        scaledShellFactor θ d *
          goodScaledExponentCount d
            (interpolationWeightBudget θ d)
            (higherJetDegreeBudget θ d) := by
  obtain ⟨d₀, hd₀⟩ := exists_scaledShellThreshold hθ hθ₁
  refine ⟨d₀, fun d hd ↦ ?_⟩
  have h := scaledShell_cardinality_bound (hd₀ d hd).1 (hd₀ d hd).2
  simpa using h

/-- Explicit-exponent form of the ceiling-factor estimate. -/
theorem scaledShellFactor_cast_le_two_rpow_explicit
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1)
    {d : ℕ} (hd : 1 ≤ d) :
    (scaledShellFactor θ d : ℝ) ≤
      2 * (d : ℝ) ^ ((5 - θ) / (5 + θ)) := by
  simpa [scaledShellExponent] using
    scaledShellFactor_cast_le_two_rpow hθ hθ₁ hd

end HiddenDerivative
end ReedSolomon
