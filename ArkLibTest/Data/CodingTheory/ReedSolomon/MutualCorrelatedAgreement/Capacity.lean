/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.Midpoint
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.Parameters
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.SharpCountingBound
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters

/-! # Acceptance case for correlated-agreement capacity bounds -/

open ReedSolomon
open ReedSolomon.HiddenDerivative ReedSolomon.HiddenDerivative.WeightedSupportParameters

example : correlatedMidpoint (1 / 2) 10 2 ≤ 8 ∧
    (1 / 2 : ℝ) * (10 : ℕ) / 2 ≤ ((8 - correlatedMidpoint (1 / 2) 10 2 + 1 : ℕ) : ℝ) := by
  obtain ⟨-, h, -, h', -⟩ := correlatedMidpoint_bounds (1 / 2) 10 2 8 (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨h, h'⟩

example :
    let δ : ℝ := 1 / 5
    let d := Nat.ceil (Real.exp (xi / δ))
    let H : ℝ := harmonic (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let n := 8 * m
    let ν := 2 * m - 1
    let centers : Fin n ↪ ℚ :=
      ⟨fun i => (i : ℚ), fun a b h => by
        apply Fin.ext
        change (a.val : ℚ) = (b.val : ℚ) at h
        exact_mod_cast h⟩
    let f : Fin n → ℚ := fun i => (i : ℚ)
    let g : Fin n → ℚ := fun _ => 0
    Nonempty (SymbolicReceivedCurve.Certificate (agreementThreshold δ n 1) 1 1 ν d
      (12 * ν - 1) centers (fun i => receivedLine (f i) (g i))) := by
  let δ : ℝ := 1 / 5
  let d := Nat.ceil (Real.exp (xi / δ))
  let H : ℝ := harmonic (d - 1)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let n := 8 * m
  let ν := 2 * m - 1
  let centers : Fin n ↪ ℚ :=
    ⟨fun i => (i : ℚ), fun a b h => by
      apply Fin.ext
      change (a.val : ℚ) = (b.val : ℚ) at h
      exact_mod_cast h⟩
  let f : Fin n → ℚ := fun i => (i : ℚ)
  let g : Fin n → ℚ := fun _ => 0
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
      let H : ℝ := harmonic (d - 1)
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      8 * m ≤ n := by
    dsimp only
    exact Nat.le_refl _
  have hA : agreementThreshold δ n 1 ≤ n := by
    apply (agreementThreshold_le_iff_real hδ.le n 1 n).mpr
    have hnR : (n : ℝ) = 8 * m := by norm_num [n]
    rw [hnR]
    dsimp [δ]
    push_cast
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm.ne'
    nlinarith
  have hparams := exists_prescribed_correlated_parameters (F := ℚ) δ n 1 centers f g
    hδ hδmax hblock hA (Or.inl (by simp))
  exact hparams.1

example :
    let L := correlatedMidpoint (1 / 2) 8 1
    (((8 - L + 1 : ℕ) : ℝ) / ((6 - L + 1 : ℕ) : ℝ) ≤ 2 / (1 / 2 : ℝ)) ∧
      (((8 - 1 + 1 : ℕ) : ℝ) / ((L - 1 + 1 : ℕ) : ℝ) ≤ 2 / (1 / 2 : ℝ)) := by
  simpa [correlatedMidpoint] using
    correlatedMidpoint_ratios_le_two_div (δ := 1 / 2) (n := 8) (k := 1) (A := 6)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The midpoint budget bounds a concrete order-one agreement stage. -/
example :
    (regularPowerBatchedAgreementSharpBound 1 8 1 4 1
      (correlatedMidpoint (1 / 2) 8 1) 6 1 1 : ℝ) ≤
      polynomialCurveSharpStageBound (1 / 2) 8 1 1 1 1 := by
  simpa [correlatedMidpoint] using
    regularPowerBatchedAgreementSharpBound_midpoint_le_stageBound
      (δ := 1 / 2) (r := 1) (n := 8) (K := 4) (k := 1) (A := 6)
      (ℓ := 1) (j := 1) (H := 1) (v := 1) (h := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Increasing an order-one stage to its cap preserves the concrete scalar bound. -/
example : polynomialCurveSharpStageBound (1 / 2) 8 1 1 1 1 ≤
    polynomialCurveSharpStageBound (1 / 2) 8 1 1 1 2 := by
  exact polynomialCurveSharpStageBound_le_uniform
    (δ := 1 / 2) (n := 8) (ℓ := 1) (v := 1) (h := 1) (r := 1) (d := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example :
    let L := correlatedMidpoint (1 / 2) 8 1
    (1 : ℝ) + ∑ _i ∈ (Finset.univ : Finset (Fin 1)),
      (regularPowerBatchedAgreementSharpBound 1 8 1 4 1 L 6 1 1 : ℝ) ≤
      polynomialCurveSharpAgreementConstant (1 / 2) 1 1 1 * (8 : ℝ) ^ (1 + 1) := by
  simpa using regularPowerBatchedAgreementSharp_finiteStage_uniform_le
    (S := (Finset.univ : Finset (Fin 1))) (order := fun _ ↦ 1)
    (jetDegree := fun _ ↦ 1) (height := fun _ ↦ 1)
    (δ := 1 / 2) (n := 8) (K := 4) (k := 1) (A := 6) (ℓ := 1) (v := 1) (h := 1) (d := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro i hi; norm_num) (by intro i hi; norm_num) (by intro i hi; norm_num)
    (by intro i hi; norm_num)
