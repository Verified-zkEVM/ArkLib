/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.FiniteBounds
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Exact Johnson interpolation counts

This file proves the finite counting inequality behind the order-zero interpolant of [BCHKS25]
with the rounded Johnson parameters of `FiniteBounds`. The ceilings are kept literally. With
`X = ⌈t n √ρ₋⌉₊` (`johnsonXCutoff`), the source monomials `x^i y^j z^k` satisfy `i + D j < X`,
`j ≤ μ` and `k ≤ h`, so a column of `y`-degree `j` contributes `(X - D j)(h + 1 - j)`
coefficients after the interpolant is reduced along the challenge coordinate
(`johnsonSourceSlotCount`). Each of the `n` evaluation points imposes, for every jet grade
`b < m`, `(m - b)(h + 1 - b)` scalar constraints (`johnsonRowSlotCount`).

## Main statements

- `johnsonMu_add_one`, `johnsonH_add_one`: the natural-number cutoffs plus one are the literal
  ceilings `⌈t / √ρ₋⌉₊` and `⌈t² / (3ρ₋)⌉₊`.
- `johnsonMu_le_H`, `johnsonM_le_H_add_one`: the cutoffs are ordered as the counting needs.
- `johnson_D_mul_mu_lt_XCutoff`: the top `y`-slice is nonempty, `D μ < X`.
- `johnsonXCutoff_le_mul_agreement`: `X ≤ m A` whenever `A ≥ (√ρ₋ + η) n`.
- `johnson_interpolation_slot_surplus`: strictly more source coefficients than constraints.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., and Saraf, S., *On Proximity Gaps
  for Reed–Solomon Codes*][BCHKS25], full version, Lemma 3.1
-/
@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

open scoped BigOperators

/-- The strict weighted-degree cutoff `X = ⌈t n √ρ₋⌉₊`, which equals `⌈t √(D n)⌉₊` when
`n > 0`. Source monomials `x^i y^j` satisfy `i + D j < X`. -/
def johnsonXCutoff (n D : ℕ) (eta : ℝ) : ℕ :=
  ⌈johnsonT n D eta * n * √(johnsonRhoMinus n D)⌉₊

/-- The number of source coefficients `∑_{j ≤ μ} (X - D j)(h + 1 - j)` in the strict Johnson
staircase. Natural subtraction truncates; `johnson_D_mul_mu_lt_XCutoff` and `johnsonMu_le_H` show
that it does not truncate at the Johnson parameters. -/
def johnsonSourceSlotCount (X D μ h : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (μ + 1), (X - D * j) * (h + 1 - j)

/-- The number of scalar multiplicity constraints at all `n` points,
`n ∑_{b < m} (m - b)(h + 1 - b)`. -/
def johnsonRowSlotCount (n m h : ℕ) : ℕ :=
  n * ∑ b ∈ Finset.range m, (m - b) * (h + 1 - b)

private theorem sum_linear_product_succ (X D Z : ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), (X - D * i) * (Z - i)) =
      X * (m + 1) * Z - X * ((m : ℝ) * (m + 1) / 2) -
      D * ((m : ℝ) * (m + 1) / 2) * Z +
      D * ((m : ℝ) * (m + 1) * (2 * m + 1) / 6) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem sourceSlotCount_cast {X D μ h : ℕ}
    (hDX : D * μ < X) (hμh : μ ≤ h) :
    (johnsonSourceSlotCount X D μ h : ℝ) =
      (X : ℝ) * (μ + 1) * (h + 1) -
      (X : ℝ) * ((μ : ℝ) * (μ + 1) / 2) -
      (D : ℝ) * ((μ : ℝ) * (μ + 1) / 2) * (h + 1) +
      (D : ℝ) * ((μ : ℝ) * (μ + 1) * (2 * μ + 1) / 6) := by
  rw [johnsonSourceSlotCount]
  push_cast
  calc
    (∑ j ∈ Finset.range (μ + 1),
        ((X - D * j : ℕ) : ℝ) * ((h + 1 - j : ℕ) : ℝ)) =
        ∑ j ∈ Finset.range (μ + 1),
          ((X : ℝ) - D * j) * ((h + 1 : ℝ) - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjμ : j ≤ μ := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [Nat.cast_sub ((Nat.mul_le_mul_left D hjμ).trans (Nat.le_of_lt hDX))]
      rw [Nat.cast_sub (hjμ.trans (hμh.trans (Nat.le_add_right h 1)))]
      push_cast
      ring
    _ = _ := sum_linear_product_succ X D (h + 1) μ

private theorem rowSlotCount_cast {n m h : ℕ} (hmh : m ≤ h + 1) :
    (johnsonRowSlotCount n m h : ℝ) =
      (n : ℝ) * ((m : ℝ) * (m + 1) / 2 * (h + 1) -
        ((m : ℝ) ^ 3 - m) / 6) := by
  rw [johnsonRowSlotCount]
  push_cast
  cases m with
  | zero => simp
  | succ q =>
      calc
        (n : ℝ) * (∑ b ∈ Finset.range (q + 1),
            (((q + 1 - b : ℕ) : ℝ) * ((h + 1 - b : ℕ) : ℝ))) =
            (n : ℝ) * ∑ b ∈ Finset.range (q + 1),
              (((q + 1 : ℕ) : ℝ) - b) * ((h + 1 : ℝ) - b) := by
          congr 1
          apply Finset.sum_congr rfl
          intro b hb
          have hbm : b ≤ q + 1 := Nat.le_of_lt (Finset.mem_range.mp hb)
          rw [Nat.cast_sub hbm, Nat.cast_sub (hbm.trans hmh)]
          push_cast
          ring
        _ = _ := by
          have hs := sum_linear_product_succ ((q + 1 : ℕ) : ℝ) 1 (h + 1) q
          simp only [one_mul] at hs
          rw [hs]
          push_cast
          ring

/-- The candidate cutoff plus one is the literal ceiling `⌈t / √ρ₋⌉₊`. The guards
`1 ≤ D < n` make `ρ₋ > 0`, so the ceiling is at least `1` and the truncated subtraction in
`johnsonMu` is exact. -/
theorem johnsonMu_add_one {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n) :
    johnsonMu n D eta + 1 =
      ⌈johnsonT n D eta / √(johnsonRhoMinus n D)⌉₊ := by
  have hz : 0 < johnsonT n D eta / √(johnsonRhoMinus n D) :=
    div_pos (lt_of_lt_of_le (by norm_num) (johnsonT_ge_seven_halves n D eta))
      (johnsonSqrt_mem_Ioo hD hDn).1
  have hc : 1 ≤ ⌈johnsonT n D eta / √(johnsonRhoMinus n D)⌉₊ :=
    Nat.one_le_ceil_iff.2 hz
  unfold johnsonMu
  omega

/-- The challenge cutoff plus one is the literal ceiling `⌈t² / (3ρ₋)⌉₊`. As for
`johnsonMu_add_one`, the guards `1 ≤ D < n` keep the ceiling positive. -/
theorem johnsonH_add_one {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n) :
    johnsonH n D eta + 1 =
      ⌈johnsonT n D eta ^ 2 / (3 * johnsonRhoMinus n D)⌉₊ := by
  have hz : 0 < johnsonT n D eta ^ 2 / (3 * johnsonRhoMinus n D) := by
    exact div_pos (sq_pos_of_pos (lt_of_lt_of_le (by norm_num)
      (johnsonT_ge_seven_halves n D eta)))
      (mul_pos (by norm_num) (johnsonRhoMinus_pos hD hDn))
  have hc : 1 ≤ ⌈johnsonT n D eta ^ 2 / (3 * johnsonRhoMinus n D)⌉₊ :=
    Nat.one_le_ceil_iff.2 hz
  unfold johnsonH
  omega

/-- The challenge cutoff dominates the candidate cutoff, `μ ≤ h`. In real terms
`t / √ρ₋ ≤ t² / (3ρ₋)` because `t ≥ 7/2 > 3 > 3√ρ₋`; the ceilings preserve the order. -/
theorem johnsonMu_le_H {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n) :
    johnsonMu n D eta ≤ johnsonH n D eta := by
  let x := √(johnsonRhoMinus n D)
  let t := johnsonT n D eta
  have hx := johnsonSqrt_mem_Ioo hD hDn
  have hx0 : 0 < x := by exact hx.1
  have ht := johnsonT_ge_seven_halves n D eta
  have hreal : t / x ≤ t ^ 2 / (3 * johnsonRhoMinus n D) := by
    have hx2 : x ^ 2 = johnsonRhoMinus n D :=
      Real.sq_sqrt (johnsonRhoMinus_pos hD hDn).le
    rw [← hx2]
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    have hgap : 0 ≤ t * (t - 3 * x) := by
      have : 0 < t - 3 * x := by nlinarith [hx.2]
      positivity
    have hbase : 3 * t * x ≤ t ^ 2 := by nlinarith [hgap]
    have hden : 0 < 3 * x ^ 2 := by positivity
    apply (div_le_div_iff₀ hx0 hden).2
    have hmul := mul_le_mul_of_nonneg_right hbase hx0.le
    nlinarith
  have hc := Nat.ceil_mono hreal
  dsimp only [x, t] at hc
  rw [← johnsonMu_add_one hD hDn, ← johnsonH_add_one hD hDn] at hc
  omega

/-- The multiplicity is at most the number of challenge degrees, `m ≤ h + 1`, so every jet
grade `b < m` in `johnsonRowSlotCount` has `h + 1 - b` computed without truncation. -/
theorem johnsonM_le_H_add_one {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n) :
    johnsonM n D eta ≤ johnsonH n D eta + 1 := by
  have hmμ : johnsonM n D eta ≤ johnsonMu n D eta := by
    have hx := johnsonSqrt_mem_Ioo hD hDn
    have ht := johnsonT_ge_seven_halves n D eta
    have hreal : (johnsonM n D eta : ℝ) <
        johnsonT n D eta / √(johnsonRhoMinus n D) := by
      apply (lt_div_iff₀ hx.1).2
      unfold johnsonT
      nlinarith
    have hceil : johnsonM n D eta <
        ⌈johnsonT n D eta / √(johnsonRhoMinus n D)⌉₊ :=
      Nat.lt_ceil.mpr hreal
    rw [← johnsonMu_add_one hD hDn] at hceil
    omega
  exact hmμ.trans (johnsonMu_le_H hD hDn |>.trans (Nat.le_add_right _ 1))

/-- The largest `y`-slice remains strictly inside the weighted-degree cutoff: `D μ < X`, since
`μ < t / √ρ₋` and `D = n ρ₋`. -/
theorem johnson_D_mul_mu_lt_XCutoff {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n) :
    D * johnsonMu n D eta < johnsonXCutoff n D eta := by
  let x := √(johnsonRhoMinus n D)
  let t := johnsonT n D eta
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx := johnsonSqrt_mem_Ioo hD hDn
  have hx2 : x ^ 2 = johnsonRhoMinus n D :=
    Real.sq_sqrt (johnsonRhoMinus_pos hD hDn).le
  have hDreal : (D : ℝ) = n * x ^ 2 := by
    rw [hx2]
    unfold johnsonRhoMinus
    field_simp
  have hμ := johnsonMu_lt (eta := eta) hD hDn
  have hlt : ((D * johnsonMu n D eta : ℕ) : ℝ) < t * n * x := by
    push_cast
    calc
      (D : ℝ) * johnsonMu n D eta < D * (t / x) := by
        exact mul_lt_mul_of_pos_left (by simpa only [x, t] using hμ)
          (by exact_mod_cast hD)
      _ = t * n * x := by rw [hDreal]; field_simp [hx.1.ne']
  have hceil : t * n * x ≤ (johnsonXCutoff n D eta : ℝ) := by
    unfold johnsonXCutoff
    exact Nat.le_ceil _
  have hcast := hlt.trans_le hceil
  exact_mod_cast hcast

/-- The strict weighted-degree cutoff `X` fits below the multiplicity budget supplied by the
agreement threshold: `X ≤ m A` whenever `(√ρ₋ + η) n ≤ A`. This is the rounded form of
`(m + 1/2) √ρ₋ ≤ m (√ρ₋ + η)`, which holds because the ceiling in `johnsonM` gives
`√ρ₋ / 2 ≤ m η` for `η > 0`. No range guard on `D` is needed. -/
theorem johnsonXCutoff_le_mul_agreement {n D A : ℕ} {eta : ℝ}
    (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) :
    johnsonXCutoff n D eta ≤ johnsonM n D eta * A := by
  let x := √(johnsonRhoMinus n D)
  let m := johnsonM n D eta
  have hn : (0 : ℝ) ≤ n := by positivity
  have hgap : x / 2 ≤ (m : ℝ) * eta := by
    simpa only [x, m] using johnson_half_gap n D heta
  have hreal : johnsonT n D eta * n * x ≤ (m * A : ℕ) := by
    have hpoint : johnsonT n D eta * x ≤ (m : ℝ) * johnsonAgreement n D eta := by
      dsimp only [m]
      unfold johnsonT johnsonAgreement
      nlinarith
    calc
      johnsonT n D eta * n * x = n * (johnsonT n D eta * x) := by ring
      _ ≤ n * ((m : ℝ) * johnsonAgreement n D eta) :=
        mul_le_mul_of_nonneg_left hpoint hn
      _ = (m : ℝ) * (johnsonAgreement n D eta * n) := by ring
      _ ≤ (m : ℝ) * A := mul_le_mul_of_nonneg_left hthreshold (by positivity)
      _ = (m * A : ℕ) := by push_cast; ring
  unfold johnsonXCutoff
  exact Nat.ceil_le.mpr hreal

private theorem staircase_closed_form_lower {d X dy y z : ℝ}
    (hd : 0 ≤ d) (hdy : 0 ≤ dy) (hdy_y : dy ≤ y) (hy : 0 ≤ y)
    (hy_lt : y < dy + 1) (hyz : y ≤ z) (hdX : d * dy ≤ X) :
    d * (dy * (dy + 1) / 2 * z - (dy ^ 3 - dy) / 6) ≤
      X * y * z - X * (y * (y - 1) / 2) -
      d * (y * (y - 1) / 2) * z + d * (y * (y - 1) * (2 * y - 1) / 6) := by
  let r := y - dy
  have hr0 : 0 ≤ r := sub_nonneg.mpr hdy_y
  have hr1 : r ≤ 1 := by dsimp only [r]; linarith
  have hbracket : 0 ≤ 3 * z + 1 - 3 * dy - 2 * r := by
    dsimp only [r]
    nlinarith
  have hround : 0 ≤ d * r * (1 - r) * (3 * z + 1 - 3 * dy - 2 * r) / 6 := by
    positivity
  have hcoeff : 0 ≤ y * z - y * (y - 1) / 2 := by
    have hb : 0 ≤ z - (y - 1) / 2 := by nlinarith
    have : 0 ≤ y * (z - (y - 1) / 2) := mul_nonneg hy hb
    nlinarith
  have hxgain : 0 ≤ (X - d * dy) * (y * z - y * (y - 1) / 2) :=
    mul_nonneg (sub_nonneg.mpr hdX) hcoeff
  have hroundId :
      (d * dy * y * z - d * dy * (y * (y - 1) / 2) -
          d * (y * (y - 1) / 2) * z +
          d * (y * (y - 1) * (2 * y - 1) / 6)) -
        d * (dy * (dy + 1) / 2 * z - (dy ^ 3 - dy) / 6) =
          d * r * (1 - r) * (3 * z + 1 - 3 * dy - 2 * r) / 6 := by
    dsimp only [r]
    ring
  have hxgainId :
      (X * y * z - X * (y * (y - 1) / 2)) -
        (d * dy * y * z - d * dy * (y * (y - 1) / 2)) =
          (X - d * dy) * (y * z - y * (y - 1) / 2) := by ring
  nlinarith [hroundId, hxgainId]

/-- At the rounded Johnson cutoffs, the source-slot count strictly exceeds the row-slot count
under the guards `1 ≤ D < n`, which make `ρ₋ ∈ (0, 1)`. -/
theorem johnson_interpolation_slot_surplus {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n) :
    johnsonRowSlotCount n (johnsonM n D eta) (johnsonH n D eta) <
      johnsonSourceSlotCount (johnsonXCutoff n D eta) D
        (johnsonMu n D eta) (johnsonH n D eta) := by
  let x := √(johnsonRhoMinus n D)
  let t := johnsonT n D eta
  let m := johnsonM n D eta
  let μ := johnsonMu n D eta
  let h := johnsonH n D eta
  let Xc := johnsonXCutoff n D eta
  let dy := t / x
  let z := (h + 1 : ℕ)
  change johnsonRowSlotCount n m h < johnsonSourceSlotCount Xc D μ h
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx := johnsonSqrt_mem_Ioo hD hDn
  have hx0 : 0 < x := by exact hx.1
  have hx2 : x ^ 2 = johnsonRhoMinus n D :=
    Real.sq_sqrt (johnsonRhoMinus_pos hD hDn).le
  have ht : 7 / 2 ≤ t := johnsonT_ge_seven_halves n D eta
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hm3 : 3 ≤ m := johnsonM_ge_three n D eta
  have ht_def : t = (m : ℝ) + 1 / 2 := by rfl
  have hDreal : (D : ℝ) = n * x ^ 2 := by
    rw [hx2]
    unfold johnsonRhoMinus
    field_simp
  have hμh : μ ≤ h := johnsonMu_le_H hD hDn
  have hmz : m ≤ z := by exact johnsonM_le_H_add_one hD hDn
  have hDX : D * μ < Xc := johnson_D_mul_mu_lt_XCutoff hD hDn
  have hsource := sourceSlotCount_cast hDX hμh
  have hrow := rowSlotCount_cast (n := n) hmz
  have hdy0 : 0 ≤ dy := (div_pos ht0 hx0).le
  have hdy_y : dy ≤ (μ + 1 : ℕ) := by
    rw [johnsonMu_add_one hD hDn]
    exact Nat.le_ceil _
  have hy_lt : ((μ + 1 : ℕ) : ℝ) < dy + 1 := by
    rw [johnsonMu_add_one hD hDn]
    exact Nat.ceil_lt_add_one hdy0
  have hyzNat : μ + 1 ≤ z := by dsimp only [z]; omega
  have hyz : ((μ + 1 : ℕ) : ℝ) ≤ z := by exact_mod_cast hyzNat
  have hX : (D : ℝ) * dy ≤ Xc := by
    have heq : (D : ℝ) * dy = t * n * x := by
      dsimp only [dy]
      rw [hDreal]
      field_simp [hx0.ne']
    rw [heq]
    unfold Xc johnsonXCutoff
    exact Nat.le_ceil _
  have hsourceLower := staircase_closed_form_lower
    (d := (D : ℝ)) (X := (Xc : ℝ)) (dy := dy)
    (y := ((μ + 1 : ℕ) : ℝ)) (z := (z : ℝ))
    (by positivity) hdy0 hdy_y (by positivity) hy_lt hyz hX
  have hz0 : t ^ 2 / (3 * x ^ 2) ≤ (z : ℝ) := by
    dsimp only [z, h]
    rw [johnsonH_add_one hD hDn, hx2]
    exact Nat.le_ceil _
  have hcoef : 0 < t * x + 1 / 4 := by positivity
  have hmterm : 0 < (m : ℝ) ^ 3 - m := by
    have hmreal : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    nlinarith [sq_nonneg ((m : ℝ) - 1)]
  have hmain :
      (n : ℝ) * ((m : ℝ) * (m + 1) / 2 * (z : ℝ) -
          ((m : ℝ) ^ 3 - m) / 6) <
        (D : ℝ) * (dy * (dy + 1) / 2 * (z : ℝ) - (dy ^ 3 - dy) / 6) := by
    have hcoefId :
        (D : ℝ) * (dy * (dy + 1)) - n * ((m : ℝ) * (m + 1)) =
          n * (t * x + 1 / 4) := by
      dsimp only [dy]
      rw [hDreal, ht_def]
      field_simp [hx0.ne']
      ring
    have hcubicId :
        (D : ℝ) * (dy ^ 3 - dy) - n * ((m : ℝ) ^ 3 - m) =
          n * (t ^ 3 / x - t * x - ((m : ℝ) ^ 3 - m)) := by
      dsimp only [dy]
      rw [hDreal]
      field_simp [hx0.ne']
    have hpositiveAtCutoff :
        0 < 3 * (t * x + 1 / 4) * (t ^ 2 / (3 * x ^ 2)) -
          (t ^ 3 / x - t * x - ((m : ℝ) ^ 3 - m)) := by
      have htail : 0 < t ^ 2 / (4 * x ^ 2) + t * x + ((m : ℝ) ^ 3 - m) := by
        positivity
      field_simp [hx0.ne'] at htail ⊢
      nlinarith
    have hscaled :
        3 * (t * x + 1 / 4) * (t ^ 2 / (3 * x ^ 2)) ≤
          3 * (t * x + 1 / 4) * (z : ℝ) := by gcongr
    have hbracket :
        0 < 3 * (t * x + 1 / 4) * (z : ℝ) -
          (t ^ 3 / x - t * x - ((m : ℝ) ^ 3 - m)) := by
      linarith
    have hdiff :
        (D : ℝ) * (dy * (dy + 1) / 2 * (z : ℝ) - (dy ^ 3 - dy) / 6) -
          (n : ℝ) * ((m : ℝ) * (m + 1) / 2 * (z : ℝ) -
            ((m : ℝ) ^ 3 - m) / 6) =
          (n : ℝ) / 6 * (3 * (t * x + 1 / 4) * (z : ℝ) -
            (t ^ 3 / x - t * x - ((m : ℝ) ^ 3 - m))) := by
      calc
        _ = 1 / 6 *
            (3 * ((D : ℝ) * (dy * (dy + 1)) - n * ((m : ℝ) * (m + 1))) * z -
              ((D : ℝ) * (dy ^ 3 - dy) - n * ((m : ℝ) ^ 3 - m))) := by ring
        _ = _ := by rw [hcoefId, hcubicId]; ring
    rw [← sub_pos, hdiff]
    positivity
  have hsourceLower' :
      (D : ℝ) * (dy * (dy + 1) / 2 * (z : ℝ) - (dy ^ 3 - dy) / 6) ≤
        (johnsonSourceSlotCount Xc D μ h : ℝ) := by
    rw [hsource]
    convert hsourceLower using 1
    all_goals dsimp only [z]; push_cast; ring
  have hcast : (johnsonRowSlotCount n m h : ℝ) <
      (johnsonSourceSlotCount Xc D μ h : ℝ) := by
    rw [hrow]
    have hmain' :
        (n : ℝ) * ((m : ℝ) * (m + 1) / 2 * (h + 1) -
            ((m : ℝ) ^ 3 - m) / 6) <
          (D : ℝ) * (dy * (dy + 1) / 2 * (z : ℝ) - (dy ^ 3 - dy) / 6) := by
      convert hmain using 1
      all_goals dsimp only [z]; push_cast; ring
    exact hmain'.trans_le hsourceLower'
  exact_mod_cast hcast

end
end ReedSolomon.HiddenDerivative
