/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.ArbitraryIndex

/-!
# Direct finite Johnson bound for Reed--Solomon codes

This module connects the characteristic-free Johnson recovery theorem to ArkLib's public
arbitrary-index Reed--Solomon code interface. It exposes the stronger exception count used by the
paper before deriving the older BCHKS expression as a compatibility bound.

The code dimension is `k`, so the maximum polynomial degree is `D = k - 1`. At radius `delta`,
the positive Johnson slack is
`eta = 1 - ((k - 1) / n)^(1/2) - delta`. The agreement `sqrt(D/n) + eta` therefore simplifies
exactly to `1 - delta`, including the integer ceiling in the exceptional count.
-/

@[expose] public section

namespace CodingTheory

open scoped NNReal
open CoreDefinitions

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F]

/-- **The direct Johnson MCA bound for a non-full Reed--Solomon code.**

The conclusion uses ArkLib's smaller rounded multiplicity and exact ordinary exceptional count.
It is valid over every finite field, with no characteristic restriction. The separate full-code
boundary theorem handles `k = n`; the strict guard here is exactly what yields `D <= n - 2` for
the Johnson interpolation theorem.
-/
theorem rs_mcaError_le_johnsonE0
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (hk : 1 < k) (hklt : k < Fintype.card ι)
    (hδ :
        (δ : ℝ) <
          1 - ((((k - 1 : ℕ) : ℝ) / Fintype.card ι) ^ ((1 : ℝ) / 2))) :
    mcaError (AffineLineGenerator F) (ReedSolomon.code domain k) (δ : ℝ) ≤
      ENNReal.ofReal
        (let n := Fintype.card ι
         let D := k - 1
         let eta : ℝ :=
           1 - ((((D : ℕ) : ℝ) / n) ^ ((1 : ℝ) / 2)) - δ
         ReedSolomon.HiddenDerivative.johnsonE0 n D ⌈(1 - (δ : ℝ)) * n⌉₊ eta /
           (Fintype.card F : ℝ)) := by
  classical
  let n := Fintype.card ι
  let D := k - 1
  let rho : ℝ := (D : ℝ) / n
  let eta : ℝ := 1 - rho ^ ((1 : ℝ) / 2) - δ
  have hD : 1 ≤ D := by omega
  have hDn : D ≤ n - 2 := by omega
  have heta : 0 < eta := by
    dsimp only [eta, rho, D, n]
    exact sub_pos.mpr hδ
  have hsqrt : √rho = rho ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow rho
  have hagreement :
      ReedSolomon.HiddenDerivative.johnsonAgreement n D eta = 1 - (δ : ℝ) := by
    unfold ReedSolomon.HiddenDerivative.johnsonAgreement
      ReedSolomon.HiddenDerivative.johnsonRhoMinus
    rw [hsqrt]
    dsimp only [eta, rho]
    ring
  have ha : ReedSolomon.HiddenDerivative.johnsonAgreement n D eta ≤ 1 := by
    rw [hagreement]
    have hδnonneg : (0 : ℝ) ≤ δ := by positivity
    linarith
  have hbound :=
    ReedSolomon.johnson_mcaError_le_arbitrary_index domain D eta hD hDn heta ha
  rw [hagreement] at hbound
  have hcode : D + 1 = k := by
    dsimp only [D]
    omega
  rw [hcode] at hbound
  simpa only [n, D, eta, rho, sub_sub_cancel] using hbound

/-- The direct `johnsonE0` result implies the larger BCHKS expression used by the legacy public
catalogue. This theorem handles the non-full-code branch; `k = n` is treated separately because
the code is then the whole ambient space and its MCA error is zero.

The proof makes both rounding representations explicit: `johnsonBCHKS_M` uses the natural-number
ceiling, while the legacy expression prints an integer ceiling coerced to the reals. -/
theorem rs_mcaError_le_bchks_of_lt_card
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (hk : 1 < k) (hklt : k < Fintype.card ι)
    (hδ :
        (δ : ℝ) <
          1 - ((((k - 1 : ℕ) : ℝ) / Fintype.card ι) ^ ((1 : ℝ) / 2))) :
    mcaError (AffineLineGenerator F) (ReedSolomon.code domain k) (δ : ℝ) ≤
      ENNReal.ofReal
        (let n : ℝ := Fintype.card ι
         let ρ : ℝ := (k - 1 : ℕ) / n
         let m : ℝ := max ⌈(ρ ^ ((1 : ℝ) / 2)) /
           (1 - ρ ^ ((1 : ℝ) / 2) - δ)⌉ 3
         ((2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * δ * ρ)
            / (3 * ρ ^ ((3 : ℝ) / 2)) * n
          + (m + 1/2) / ρ ^ ((1 : ℝ) / 2))
           / (Fintype.card F : ℝ)) := by
  classical
  let n := Fintype.card ι
  let D := k - 1
  let rho : ℝ := (D : ℝ) / n
  let eta : ℝ := 1 - rho ^ ((1 : ℝ) / 2) - δ
  let A := ⌈(1 - (δ : ℝ)) * n⌉₊
  have hD : 1 ≤ D := by omega
  have hDn : D ≤ n - 2 := by omega
  have heta : 0 < eta := by
    dsimp only [eta, rho, D, n]
    exact sub_pos.mpr hδ
  have hsqrt : √rho = rho ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow rho
  have hagreement :
      ReedSolomon.HiddenDerivative.johnsonAgreement n D eta = 1 - (δ : ℝ) := by
    unfold ReedSolomon.HiddenDerivative.johnsonAgreement
      ReedSolomon.HiddenDerivative.johnsonRhoMinus
    rw [hsqrt]
    dsimp only [eta, rho]
    ring
  have ha : ReedSolomon.HiddenDerivative.johnsonAgreement n D eta ≤ 1 := by
    rw [hagreement]
    have hδnonneg : (0 : ℝ) ≤ δ := by positivity
    linarith
  have hthreshold :
      ReedSolomon.HiddenDerivative.johnsonAgreement n D eta * n ≤ A := by
    rw [hagreement]
    exact Nat.le_ceil _
  have hAn : A ≤ n := by
    apply Nat.ceil_le.mpr
    have hnnonneg : (0 : ℝ) ≤ n := by positivity
    have hδnonneg : (0 : ℝ) ≤ δ := by positivity
    nlinarith
  have hstrong := rs_mcaError_le_johnsonE0 domain k δ hk hklt hδ
  refine hstrong.trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hE := ReedSolomon.HiddenDerivative.johnsonE0_le_BCHKS
    hD hDn heta ha hthreshold hAn
  have hqnonneg : (0 : ℝ) ≤ Fintype.card F := by positivity
  have hdiv :
      ReedSolomon.HiddenDerivative.johnsonE0 n D A eta / (Fintype.card F : ℝ) ≤
        ReedSolomon.HiddenDerivative.johnsonBCHKS n D eta / (Fintype.card F : ℝ) :=
    div_le_div_of_nonneg_right hE hqnonneg
  have hceilCast :
      (⌈rho ^ ((1 : ℝ) / 2) / eta⌉₊ : ℝ) =
        (⌈rho ^ ((1 : ℝ) / 2) / eta⌉ : ℤ) := by
    rw [natCast_ceil_eq_intCast_ceil]
    positivity
  have hmcast :
      ((max ⌈rho ^ ((1 : ℝ) / 2) / eta⌉₊ 3 : ℕ) : ℝ) =
        max ((⌈rho ^ ((1 : ℝ) / 2) / eta⌉ : ℤ) : ℝ) 3 := by
    rw [Nat.cast_max, hceilCast]
    norm_num
  have hsqrtCube : √rho ^ 3 = rho ^ ((3 : ℝ) / 2) := by
    exact ReedSolomon.HiddenDerivative.johnson_sqrt_cube_eq_rpow_three_halves hD hDn
  unfold ReedSolomon.HiddenDerivative.johnsonBCHKS
    ReedSolomon.HiddenDerivative.johnsonBCHKS_T
    ReedSolomon.HiddenDerivative.johnsonBCHKS_M
    ReedSolomon.HiddenDerivative.johnsonGamma at hdiv
  rw [hagreement] at hdiv
  dsimp only at hdiv
  unfold ReedSolomon.HiddenDerivative.johnsonRhoMinus at hdiv
  change ReedSolomon.HiddenDerivative.johnsonE0 n D A eta /
      (Fintype.card F : ℝ) ≤
    ((2 * ((max ⌈√rho / eta⌉₊ 3 : ℕ) + 1 / 2) ^ 5 +
          3 * ((max ⌈√rho / eta⌉₊ 3 : ℕ) + 1 / 2) * (1 - (1 - (δ : ℝ))) * rho) /
        (3 * √rho ^ 3) * n +
      ((max ⌈√rho / eta⌉₊ 3 : ℕ) + 1 / 2) / √rho) /
      (Fintype.card F : ℝ) at hdiv
  rw [hsqrtCube, hsqrt, hmcast] at hdiv
  simpa only [n, D, rho, eta, A, sub_sub_cancel, Nat.cast_max, Nat.cast_ofNat,
    Int.cast_max, Int.cast_ofNat] using hdiv

end CodingTheory
