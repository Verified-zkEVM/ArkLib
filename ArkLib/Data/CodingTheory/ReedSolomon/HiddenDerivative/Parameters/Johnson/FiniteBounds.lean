/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Finite Johnson parameters and their closed numerical bounds

This file contains only the real and natural-number arithmetic used by the characteristic-free
ordinary-agreement theorem.  It records the exact rounded parameter recipe and compares its raw
exception expression with the printed closed bound.  The coding-theoretic transfer is kept in its
owner modules.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

/-- The maximum-degree ratio `D / n`; the physical code rate is `(D + 1) / n`. -/
def johnsonRhoMinus (n D : ℕ) : ℝ :=
  (D : ℝ) / n

/-- The agreement fraction `sqrt(D/n) + eta`. -/
def johnsonAgreement (n D : ℕ) (eta : ℝ) : ℝ :=
  √(johnsonRhoMinus n D) + eta

/-- The rounded Johnson multiplicity. -/
def johnsonM (n D : ℕ) (eta : ℝ) : ℕ :=
  max ⌈√(johnsonRhoMinus n D) / (2 * eta)⌉₊ 3

/-- The half-shifted real multiplicity `m + 1/2`. -/
def johnsonT (n D : ℕ) (eta : ℝ) : ℝ :=
  johnsonM n D eta + 1 / 2

/-- The rounded degree in the candidate-polynomial coordinate. -/
def johnsonMu (n D : ℕ) (eta : ℝ) : ℕ :=
  ⌈johnsonT n D eta / √(johnsonRhoMinus n D)⌉₊ - 1

/-- The rounded challenge-coordinate height. -/
def johnsonH (n D : ℕ) (eta : ℝ) : ℕ :=
  ⌈johnsonT n D eta ^ 2 / (3 * johnsonRhoMinus n D)⌉₊ - 1

/-- The direct incidence ratio `(n-D)/(A-D)`. -/
def johnsonTheta (n D A : ℕ) : ℝ :=
  ((n - D : ℕ) : ℝ) / (A - D : ℕ)

/-- The exact raw characteristic-free ordinary exception expression. -/
def johnsonE0 (n D A : ℕ) (eta : ℝ) : ℝ :=
  let μ := johnsonMu n D eta
  let h := johnsonH n D eta
  (2 * μ - 1 : ℕ) * h + johnsonTheta n D A * (h + μ + 4 * D * μ * h) +
    (n - D - 1 : ℕ) * μ

/-- The sharper raw ordinary exception expression available when `μ ≤ D`. -/
def johnsonESharp (n D A : ℕ) (eta : ℝ) : ℝ :=
  let μ := johnsonMu n D eta
  let h := johnsonH n D eta
  (2 * μ - 1 : ℕ) * h +
    johnsonTheta n D A * (h + μ + (2 * D - 1) * h * (2 * μ - 1)) +
    (n - D - 1 : ℕ) * μ

/-- The multiplicity used in the comparison with the BCHKS Johnson estimate. -/
def johnsonBCHKS_M (n D : ℕ) (eta : ℝ) : ℕ :=
  max ⌈√(johnsonRhoMinus n D) / eta⌉₊ 3

/-- The half-shifted BCHKS comparison multiplicity. -/
def johnsonBCHKS_T (n D : ℕ) (eta : ℝ) : ℝ :=
  johnsonBCHKS_M n D eta + 1 / 2

/-- The nonnegative agreement slack appearing in the BCHKS estimate. -/
def johnsonGamma (n D : ℕ) (eta : ℝ) : ℝ :=
  1 - johnsonAgreement n D eta

/-- The explicit BCHKS exception estimate, written with `sqrt(rhoMinus)^3`. -/
def johnsonBCHKS (n D : ℕ) (eta : ℝ) : ℝ :=
  let rho := johnsonRhoMinus n D
  let tB := johnsonBCHKS_T n D eta
  ((2 * tB ^ 5 + 3 * tB * johnsonGamma n D eta * rho) / (3 * √rho ^ 3)) * n +
    tB / √rho

/-- The degree rate is positive under the finite Johnson guards. -/
theorem johnsonRhoMinus_pos {n D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n - 2) :
    0 < johnsonRhoMinus n D := by
  unfold johnsonRhoMinus
  have hn : 0 < n := by omega
  positivity

/-- The degree rate is strictly below one under the finite Johnson guards. -/
theorem johnsonRhoMinus_lt_one {n D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n - 2) :
    johnsonRhoMinus n D < 1 := by
  unfold johnsonRhoMinus
  have hDn' : D < n := by omega
  exact (div_lt_one (by exact_mod_cast (show 0 < n by omega))).2 (by exact_mod_cast hDn')

/-- The cube of the square root is the printed `rhoMinus^(3/2)` denominator. -/
theorem johnson_sqrt_cube_eq_rpow_three_halves {n D : ℕ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) :
    √(johnsonRhoMinus n D) ^ 3 =
      Real.rpow (johnsonRhoMinus n D) (3 / 2 : ℝ) := by
  symm
  calc
    Real.rpow (johnsonRhoMinus n D) (3 / 2 : ℝ) =
        Real.rpow (√(johnsonRhoMinus n D)) (3 : ℝ) :=
      Real.rpow_div_two_eq_sqrt 3 (johnsonRhoMinus_pos hD hDn).le
    _ = √(johnsonRhoMinus n D) ^ 3 := Real.rpow_natCast _ 3

/-- The square root of the physical degree rate lies strictly between zero and one. -/
theorem johnsonSqrt_mem_Ioo {n D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n - 2) :
    0 < √(johnsonRhoMinus n D) ∧ √(johnsonRhoMinus n D) < 1 := by
  have hrho := johnsonRhoMinus_pos hD hDn
  refine ⟨Real.sqrt_pos.2 hrho, ?_⟩
  simpa only [Real.sqrt_one] using
    Real.sqrt_lt_sqrt hrho.le (johnsonRhoMinus_lt_one hD hDn)

/-- The agreement fraction strictly exceeds the degree rate. -/
theorem johnsonRhoMinus_lt_agreement {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta) :
    johnsonRhoMinus n D < johnsonAgreement n D eta := by
  have hx := johnsonSqrt_mem_Ioo hD hDn
  have hsqrt := Real.sq_sqrt (johnsonRhoMinus_pos hD hDn).le
  unfold johnsonAgreement
  nlinarith [mul_pos hx.1 (sub_pos.2 hx.2)]

/-- The rounded multiplicity is at least three. -/
theorem johnsonM_ge_three (n D : ℕ) (eta : ℝ) : 3 ≤ johnsonM n D eta := by
  unfold johnsonM
  exact le_max_right _ _

/-- Consequently the shifted multiplicity satisfies `t ≥ 7/2`. -/
theorem johnsonT_ge_seven_halves (n D : ℕ) (eta : ℝ) :
    7 / 2 ≤ johnsonT n D eta := by
  have hm : (3 : ℝ) ≤ johnsonM n D eta := by exact_mod_cast johnsonM_ge_three n D eta
  calc
    (7 / 2 : ℝ) = 3 + 1 / 2 := by norm_num
    _ ≤ johnsonM n D eta + 1 / 2 := by
      simpa only [add_comm] using add_le_add_right hm (1 / 2)
    _ = johnsonT n D eta := by rfl

/-- The multiplicity rounding supplies the half-gap inequality used by interpolation. -/
theorem johnson_half_gap {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta) :
    √(johnsonRhoMinus n D) / 2 ≤ johnsonM n D eta * eta := by
  let x := √(johnsonRhoMinus n D)
  have hx : 0 < x := (johnsonSqrt_mem_Ioo hD hDn).1
  have hceil : x / (2 * eta) ≤
      (⌈x / (2 * eta)⌉₊ : ℕ) := Nat.le_ceil _
  have hm : (⌈x / (2 * eta)⌉₊ : ℝ) ≤ johnsonM n D eta := by
    exact_mod_cast (le_max_left ⌈x / (2 * eta)⌉₊ 3)
  have hdiv : x ≤ (johnsonM n D eta : ℝ) * (2 * eta) := by
    have := hceil.trans hm
    apply (div_le_iff₀ (mul_pos (by norm_num) heta)).mp at this
    simpa only [mul_comm] using this
  dsimp only [x] at hdiv ⊢
  nlinarith

/-- The real agreement guard forces the required integer threshold `D+1 ≤ A`. -/
theorem johnson_degree_succ_le_agreement {n D A : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) :
    D + 1 ≤ A := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrho := johnsonRhoMinus_lt_agreement hD hDn heta
  have hDdiv : (D : ℝ) = johnsonRhoMinus n D * n := by
    unfold johnsonRhoMinus
    field_simp
  have hDA : (D : ℝ) < A := by
    rw [hDdiv]
    exact (mul_lt_mul_of_pos_right hrho hn).trans_le hthreshold
  exact_mod_cast hDA

/-- The exact Johnson incidence denominator is positive. -/
theorem johnsonTheta_denominator_pos {n D A : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) :
    0 < A - D := by
  have := johnson_degree_succ_le_agreement hD hDn heta hthreshold
  omega

/-- The candidate-degree rounding retains its strict upper bound. -/
theorem johnsonMu_lt {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) :
    (johnsonMu n D eta : ℝ) < johnsonT n D eta / √(johnsonRhoMinus n D) := by
  let z := johnsonT n D eta / √(johnsonRhoMinus n D)
  have hz : 0 < z := div_pos (by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 2) (johnsonT_ge_seven_halves n D eta))
    (johnsonSqrt_mem_Ioo hD hDn).1
  have hceil : 1 ≤ ⌈z⌉₊ := Nat.one_le_ceil_iff.2 hz
  have hround := Nat.ceil_lt_add_one hz.le
  unfold johnsonMu
  change ((⌈z⌉₊ - 1 : ℕ) : ℝ) < z
  rw [Nat.cast_sub hceil]
  norm_num at hround ⊢
  linarith

/-- The challenge-height rounding retains its strict upper bound. -/
theorem johnsonH_lt {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) :
    (johnsonH n D eta : ℝ) <
      johnsonT n D eta ^ 2 / (3 * johnsonRhoMinus n D) := by
  let z := johnsonT n D eta ^ 2 / (3 * johnsonRhoMinus n D)
  have hz : 0 < z := div_pos (sq_pos_of_pos (lt_of_lt_of_le
    (by norm_num : (0 : ℝ) < 7 / 2) (johnsonT_ge_seven_halves n D eta)))
    (mul_pos (by norm_num) (johnsonRhoMinus_pos hD hDn))
  have hceil : 1 ≤ ⌈z⌉₊ := Nat.one_le_ceil_iff.2 hz
  have hround := Nat.ceil_lt_add_one hz.le
  unfold johnsonH
  change ((⌈z⌉₊ - 1 : ℕ) : ℝ) < z
  rw [Nat.cast_sub hceil]
  norm_num at hround ⊢
  linarith

/-- The rounded candidate-coordinate degree is positive. -/
theorem johnsonMu_pos {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) :
    1 ≤ johnsonMu n D eta := by
  let z := johnsonT n D eta / √(johnsonRhoMinus n D)
  have ht : (1 : ℝ) < johnsonT n D eta :=
    lt_of_lt_of_le (by norm_num) (johnsonT_ge_seven_halves n D eta)
  have hx := johnsonSqrt_mem_Ioo hD hDn
  have hz : (1 : ℝ) < z := by
    dsimp only [z]
    apply (lt_div_iff₀ hx.1).2
    nlinarith
  have hceil : 2 ≤ ⌈z⌉₊ := by
    exact Nat.add_one_le_ceil_iff.2 (by simpa only [Nat.cast_one] using hz)
  unfold johnsonMu
  change 1 ≤ ⌈z⌉₊ - 1
  omega

/-- The rounded challenge height is positive. -/
theorem johnsonH_pos {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) :
    1 ≤ johnsonH n D eta := by
  let z := johnsonT n D eta ^ 2 / (3 * johnsonRhoMinus n D)
  have ht : (3 : ℝ) < johnsonT n D eta ^ 2 := by
    have := johnsonT_ge_seven_halves n D eta
    nlinarith [sq_nonneg (johnsonT n D eta - 7 / 2)]
  have hrho := johnsonRhoMinus_lt_one hD hDn
  have hz : (1 : ℝ) < z := by
    dsimp only [z]
    apply (lt_div_iff₀ (mul_pos (by norm_num) (johnsonRhoMinus_pos hD hDn))).2
    nlinarith
  have hceil : 2 ≤ ⌈z⌉₊ :=
    Nat.add_one_le_ceil_iff.2 (by simpa only [Nat.cast_one] using hz)
  unfold johnsonH
  change 1 ≤ ⌈z⌉₊ - 1
  omega

/-- The reciprocal length satisfies both restrictions used in the closed Johnson comparison. -/
theorem johnson_inv_length_le_min {n D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n - 2) :
    (1 : ℝ) / n ≤ min (√(johnsonRhoMinus n D) ^ 2)
      ((1 - √(johnsonRhoMinus n D) ^ 2) / 2) := by
  let rho := johnsonRhoMinus n D
  let x := √rho
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrho : 0 ≤ rho := (johnsonRhoMinus_pos hD hDn).le
  have hx2 : x ^ 2 = rho := Real.sq_sqrt hrho
  have hrhoEq : rho = (D : ℝ) / n := rfl
  apply le_min
  · rw [hx2, hrhoEq]
    exact (div_le_div_iff_of_pos_right hn).2 (by exact_mod_cast hD)
  · rw [hx2, hrhoEq]
    have hgapNat : 2 ≤ n - D := by omega
    have hgap : (2 : ℝ) ≤ ((n - D : ℕ) : ℝ) := by exact_mod_cast hgapNat
    rw [Nat.cast_sub (show D ≤ n by omega)] at hgap
    have hone : (1 : ℝ) ≤ ((n : ℝ) - D) / 2 := by linarith
    calc
      (1 : ℝ) / n ≤ (((n : ℝ) - D) / 2) / n :=
        (div_le_div_iff_of_pos_right hn).2 hone
      _ = (1 - (D : ℝ) / n) / 2 := by field_simp

/-- The finite threshold guard bounds the incidence ratio by `(1+x)/x`. -/
theorem johnsonTheta_le_sqrt_envelope {n D A : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) :
    johnsonTheta n D A ≤
      (1 + √(johnsonRhoMinus n D)) / √(johnsonRhoMinus n D) := by
  let rho := johnsonRhoMinus n D
  let x := √rho
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx := johnsonSqrt_mem_Ioo hD hDn
  have hx2 : x ^ 2 = rho := Real.sq_sqrt (johnsonRhoMinus_pos hD hDn).le
  have hrhoEq : (D : ℝ) = rho * n := by
    dsimp only [rho]
    unfold johnsonRhoMinus
    field_simp
  have hDA := johnson_degree_succ_le_agreement hD hDn heta hthreshold
  have hnum : ((n - D : ℕ) : ℝ) = n * (1 - x ^ 2) := by
    rw [Nat.cast_sub (show D ≤ n by omega), hx2, hrhoEq]
    ring
  have hden : ((A - D : ℕ) : ℝ) = (A : ℝ) - D := by
    rw [Nat.cast_sub (show D ≤ A by omega)]
  have hxA : x * n < A := by
    unfold johnsonAgreement at hthreshold
    dsimp only [x, rho]
    nlinarith [mul_pos heta hn]
  have hdenLower : n * (x - x ^ 2) ≤ ((A - D : ℕ) : ℝ) := by
    rw [hden, hrhoEq, ← hx2]
    nlinarith
  have hdenPos : (0 : ℝ) < (A - D : ℕ) := by exact_mod_cast (show 0 < A - D by omega)
  unfold johnsonTheta
  rw [hnum]
  change (n : ℝ) * (1 - x ^ 2) / (A - D : ℕ) ≤
    (1 + x) / x
  apply (div_le_iff₀ hdenPos).2
  rw [show (1 + x) / x * ((A - D : ℕ) : ℝ) =
    ((1 + x) * (A - D : ℕ)) / x by ring]
  apply (le_div_iff₀ hx.1).2
  have hmul := mul_le_mul_of_nonneg_left hdenLower (show 0 ≤ 1 + x by positivity)
  nlinarith [show x * (n * (1 - x ^ 2)) =
    (1 + x) * (n * (x - x ^ 2)) by ring]

/-- The normalized upper envelope after inserting `t ≥ 7/2` and the length restrictions. -/
def johnsonNormalizedEnvelope (x : ℝ) : ℝ :=
  4 * (1 + x) / 3 +
    (16 / (21 * x) + 26 / 147) * min (x ^ 2) ((1 - x ^ 2) / 2) +
    4 * x * (1 - x ^ 2) / 49

/-- The normalized expression before replacing `t` by its lower bound and `1/n` by the length
restriction. -/
def johnsonPreEnvelope (x y t : ℝ) : ℝ :=
  4 * (1 + x) / 3 +
    (2 / (3 * x) + (1 + x) / (3 * t * x) + 1 / t ^ 2) * y +
    x * (1 - x ^ 2) / t ^ 2

/-- The pre-envelope is bounded by `johnsonNormalizedEnvelope` under the exact lower bound on
`t` and both length restrictions. -/
theorem johnsonPreEnvelope_le_normalized {x y t : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (ht : 7 / 2 ≤ t)
    (hy : y ≤ min (x ^ 2) ((1 - x ^ 2) / 2)) :
    johnsonPreEnvelope x y t ≤ johnsonNormalizedEnvelope x := by
  let s := min (x ^ 2) ((1 - x ^ 2) / 2)
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hs0 : 0 ≤ s := by
    apply le_min <;> nlinarith [sq_nonneg x]
  have hinv : 1 / t ≤ (2 / 7 : ℝ) := by
    apply (div_le_iff₀ ht0).2
    nlinarith
  have hinvSq : 1 / t ^ 2 ≤ (4 / 49 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos ht0)).2
    nlinarith [sq_nonneg (t - 7 / 2)]
  have hmiddleCoeff :
      2 / (3 * x) + (1 + x) / (3 * t * x) + 1 / t ^ 2 ≤
        16 / (21 * x) + 26 / 147 := by
    have hscaled : (1 + x) / (3 * t * x) ≤ 2 * (1 + x) / (21 * x) := by
      calc
        (1 + x) / (3 * t * x) = (1 + x) / (3 * x) * (1 / t) := by
          field_simp
        _ ≤ (1 + x) / (3 * x) * (2 / 7) := by gcongr
        _ = 2 * (1 + x) / (21 * x) := by ring
    calc
      _ ≤ 2 / (3 * x) + 2 * (1 + x) / (21 * x) + 4 / 49 := by linarith
      _ = 16 / (21 * x) + 26 / 147 := by field_simp; ring
  have hmiddleCoeff0 :
      0 ≤ 2 / (3 * x) + (1 + x) / (3 * t * x) + 1 / t ^ 2 := by positivity
  have hmiddle :
      (2 / (3 * x) + (1 + x) / (3 * t * x) + 1 / t ^ 2) * y ≤
        (16 / (21 * x) + 26 / 147) * s := by
    calc
      _ ≤ (2 / (3 * x) + (1 + x) / (3 * t * x) + 1 / t ^ 2) * s := by
        exact mul_le_mul_of_nonneg_left hy hmiddleCoeff0
      _ ≤ _ := by gcongr
  have hxgap : 0 ≤ x * (1 - x ^ 2) := by
    have : 0 ≤ 1 - x ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hx1) (add_pos_of_pos_of_nonneg hx0 hx0.le)]
    positivity
  have hlast : x * (1 - x ^ 2) / t ^ 2 ≤ 4 * x * (1 - x ^ 2) / 49 := by
    calc
      x * (1 - x ^ 2) / t ^ 2 = x * (1 - x ^ 2) * (1 / t ^ 2) := by ring
      _ ≤ x * (1 - x ^ 2) * (4 / 49) := by gcongr
      _ = 4 * x * (1 - x ^ 2) / 49 := by ring
  unfold johnsonPreEnvelope johnsonNormalizedEnvelope
  dsimp only [s] at hmiddle
  linarith

/-- The exact rounded exception expression is strictly below the pre-envelope after
normalization. -/
theorem johnsonE0_lt_preEnvelope_scale {n D A : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hAn : A ≤ n) :
    johnsonE0 n D A eta <
      ((n : ℝ) * johnsonT n D eta ^ 3 / johnsonRhoMinus n D) *
        johnsonPreEnvelope (√(johnsonRhoMinus n D)) (1 / n) (johnsonT n D eta) := by
  let rho := johnsonRhoMinus n D
  let x := √rho
  let t := johnsonT n D eta
  let μ := johnsonMu n D eta
  let h := johnsonH n D eta
  let theta := johnsonTheta n D A
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrho : 0 < rho := johnsonRhoMinus_pos hD hDn
  have hx := johnsonSqrt_mem_Ioo hD hDn
  have hxne : x ≠ 0 := by
    dsimp only [x]
    exact hx.1.ne'
  have hx2 : x ^ 2 = rho := Real.sq_sqrt hrho.le
  have ht : 7 / 2 ≤ t := johnsonT_ge_seven_halves n D eta
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hμ : (μ : ℝ) < t / x := johnsonMu_lt hD hDn
  have hh : (h : ℝ) < t ^ 2 / (3 * rho) := johnsonH_lt hD hDn
  have hμ0 : (0 : ℝ) < μ := by exact_mod_cast johnsonMu_pos (eta := eta) hD hDn
  have hh0 : (0 : ℝ) < h := by exact_mod_cast johnsonH_pos (eta := eta) hD hDn
  have htheta : theta ≤ (1 + x) / x :=
    johnsonTheta_le_sqrt_envelope hD hDn heta hthreshold
  have hdegreeAgreement := johnson_degree_succ_le_agreement hD hDn heta hthreshold
  have htheta0 : 0 ≤ theta := by
    unfold theta johnsonTheta
    positivity
  have hDEq : (D : ℝ) = n * x ^ 2 := by
    rw [hx2]
    dsimp only [rho]
    unfold johnsonRhoMinus
    field_simp
  have htailEq : ((n - D - 1 : ℕ) : ℝ) = (n : ℝ) * (1 - x ^ 2) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ n - D by omega), Nat.cast_sub (show D ≤ n by omega), hDEq]
    ring
  have hfirst : ((2 * μ - 1 : ℕ) : ℝ) * h < 2 * t ^ 3 / (3 * x ^ 3) := by
    have hcast : ((2 * μ - 1 : ℕ) : ℝ) ≤ 2 * (μ : ℝ) := by
      exact_mod_cast (show 2 * μ - 1 ≤ 2 * μ by omega)
    calc
      ((2 * μ - 1 : ℕ) : ℝ) * h ≤ 2 * (μ : ℝ) * h := by gcongr
      _ < 2 * (t / x) * (t ^ 2 / (3 * rho)) := by gcongr
      _ = 2 * t ^ 3 / (3 * x ^ 3) := by rw [← hx2]; field_simp
  have hthetaHeight : theta * (h : ℝ) < (1 + x) * t ^ 2 / (3 * x ^ 3) := by
    calc
      theta * (h : ℝ) ≤ ((1 + x) / x) * h := by gcongr
      _ < ((1 + x) / x) * (t ^ 2 / (3 * rho)) := by gcongr
      _ = (1 + x) * t ^ 2 / (3 * x ^ 3) := by rw [← hx2]; field_simp
  have hthetaMain : theta * (4 * D * μ * h : ℕ) <
      4 * (1 + x) * n * t ^ 3 / (3 * x ^ 2) := by
    push_cast
    rw [hDEq]
    calc
      theta * (4 * ((n : ℝ) * x ^ 2) * μ * h) ≤
          ((1 + x) / x) * (4 * ((n : ℝ) * x ^ 2) * μ * h) := by gcongr
      _ < ((1 + x) / x) *
          (4 * ((n : ℝ) * x ^ 2) * (t / x) * (t ^ 2 / (3 * rho))) := by gcongr
      _ = 4 * (1 + x) * n * t ^ 3 / (3 * x ^ 2) := by
        rw [← hx2]
        field_simp
  have hcoeff : theta + ((n - D - 1 : ℕ) : ℝ) ≤
      (n : ℝ) * (1 - x ^ 2) + 1 / x := by
    rw [htailEq]
    have hxne : x ≠ 0 := hx.1.ne'
    calc
      theta + ((n : ℝ) * (1 - x ^ 2) - 1) ≤
          (1 + x) / x + ((n : ℝ) * (1 - x ^ 2) - 1) := by linarith
      _ = (n : ℝ) * (1 - x ^ 2) + 1 / x := by field_simp; ring
  have hcoeff0 : 0 ≤ theta + ((n - D - 1 : ℕ) : ℝ) := by positivity
  have hcoeffUpper0 : 0 < (n : ℝ) * (1 - x ^ 2) + 1 / x := by
    have : 0 < 1 - x ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hx.2) (add_pos_of_pos_of_nonneg hx.1 hx.1.le)]
    positivity
  have hlinear : (theta + ((n - D - 1 : ℕ) : ℝ)) * μ <
      (n : ℝ) * t * (1 - x ^ 2) / x + t / x ^ 2 := by
    calc
      (theta + ((n - D - 1 : ℕ) : ℝ)) * μ ≤
          ((n : ℝ) * (1 - x ^ 2) + 1 / x) * μ := by gcongr
      _ < ((n : ℝ) * (1 - x ^ 2) + 1 / x) * (t / x) := by gcongr
      _ = (n : ℝ) * t * (1 - x ^ 2) / x + t / x ^ 2 := by
        field_simp [hxne]
  calc
    johnsonE0 n D A eta =
        ((2 * μ - 1 : ℕ) : ℝ) * h + theta * h + theta * (4 * D * μ * h : ℕ) +
          (theta + ((n - D - 1 : ℕ) : ℝ)) * μ := by
            unfold johnsonE0
            dsimp only [μ, h, theta]
            push_cast
            ring
    _ < 2 * t ^ 3 / (3 * x ^ 3) + (1 + x) * t ^ 2 / (3 * x ^ 3) +
        4 * (1 + x) * n * t ^ 3 / (3 * x ^ 2) +
        ((n : ℝ) * t * (1 - x ^ 2) / x + t / x ^ 2) := by linarith
    _ = ((n : ℝ) * t ^ 3 / rho) * johnsonPreEnvelope x (1 / n) t := by
      unfold johnsonPreEnvelope
      rw [← hx2]
      field_simp [hxne, hn.ne', ht0.ne']
      ring

/-- The normalized envelope is strictly smaller than `8/3` throughout `0 < x < 1`. -/
theorem johnsonNormalizedEnvelope_lt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    johnsonNormalizedEnvelope x < 8 / 3 := by
  let r : ℝ := √(1 / 3 : ℝ)
  have hr0 : 0 < r := Real.sqrt_pos.2 (by norm_num)
  have hr1 : r < 1 := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 : ℝ) / 3 < 1)
  have hr2 : r ^ 2 = (1 / 3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hr3 : r ^ 3 = r / 3 := by
    calc
      r ^ 3 = r * r ^ 2 := by ring
      _ = r / 3 := by rw [hr2]; ring
  by_cases hxr : x ≤ r
  · have hx2r : x ^ 2 ≤ r ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxr) (add_nonneg hx0.le hr0.le)]
    have hmin : min (x ^ 2) ((1 - x ^ 2) / 2) = x ^ 2 := by
      apply min_eq_left
      nlinarith [hr2]
    have hrEndpoint : 0 < 196 - 320 * r - 26 * r ^ 2 + 12 * r ^ 3 := by
      have hsquares : (316 * r) ^ 2 < ((562 : ℝ) / 3) ^ 2 := by
        rw [mul_pow, hr2]
        norm_num
      have hroot : 316 * r < (562 : ℝ) / 3 := by
        nlinarith [sq_nonneg (316 * r + (562 : ℝ) / 3)]
      rw [hr2, hr3]
      nlinarith
    have hbracket :
        0 < 320 + 26 * (x + r) - 12 * (x ^ 2 + x * r + r ^ 2) := by
      have hxxr : x * x ≤ r * x := mul_le_mul_of_nonneg_right hxr hx0.le
      have hxrr : r * x ≤ r * r := mul_le_mul_of_nonneg_left hxr hr0.le
      nlinarith [hr2]
    have hproduct : 0 ≤ (r - x) *
        (320 + 26 * (x + r) - 12 * (x ^ 2 + x * r + r ^ 2)) :=
      mul_nonneg (sub_nonneg.mpr hxr) hbracket.le
    have hpoly : 0 < 196 - 320 * x - 26 * x ^ 2 + 12 * x ^ 3 := by
      nlinarith [show
        (196 - 320 * x - 26 * x ^ 2 + 12 * x ^ 3) -
          (196 - 320 * r - 26 * r ^ 2 + 12 * r ^ 3) =
            (r - x) *
              (320 + 26 * (x + r) - 12 * (x ^ 2 + x * r + r ^ 2)) by ring]
    have hformula :
        8 / 3 - johnsonNormalizedEnvelope x =
          (196 - 320 * x - 26 * x ^ 2 + 12 * x ^ 3) / 147 := by
      unfold johnsonNormalizedEnvelope
      rw [hmin]
      field_simp
      ring
    rw [← sub_pos, hformula]
    exact div_pos hpoly (by norm_num)
  · have hrx : r ≤ x := le_of_not_ge hxr
    have hmin : min (x ^ 2) ((1 - x ^ 2) / 2) = (1 - x ^ 2) / 2 := by
      apply min_eq_right
      nlinarith [mul_nonneg (sub_nonneg.mpr hrx) (add_nonneg hr0.le hx0.le), hr2]
    have hrEndpoint : 0 < -12 * r ^ 3 - 25 * r ^ 2 + 127 * r - 56 := by
      have hsquares : ((193 : ℝ) / 3) ^ 2 < (123 * r) ^ 2 := by
        rw [mul_pow, hr2]
        norm_num
      have hroot : (193 : ℝ) / 3 < 123 * r := by
        nlinarith [sq_nonneg ((193 : ℝ) / 3 + 123 * r)]
      rw [hr2, hr3]
      nlinarith
    have hx2 : x ^ 2 < 1 := by
      nlinarith [mul_pos (sub_pos.mpr hx1) (add_pos_of_pos_of_nonneg hx0 hx0.le)]
    have hxrOne : x * r < 1 := by
      exact mul_lt_one_of_nonneg_of_lt_one_left hx0.le hx1 hr1.le
    have hbracket :
        0 < 127 - 25 * (x + r) - 12 * (x ^ 2 + x * r + r ^ 2) := by
      nlinarith [hr2]
    have hproduct : 0 ≤ (x - r) *
        (127 - 25 * (x + r) - 12 * (x ^ 2 + x * r + r ^ 2)) :=
      mul_nonneg (sub_nonneg.mpr hrx) hbracket.le
    have hpoly : 0 < -12 * x ^ 3 - 25 * x ^ 2 + 127 * x - 56 := by
      nlinarith [show
        (-12 * x ^ 3 - 25 * x ^ 2 + 127 * x - 56) -
          (-12 * r ^ 3 - 25 * r ^ 2 + 127 * r - 56) =
            (x - r) *
              (127 - 25 * (x + r) - 12 * (x ^ 2 + x * r + r ^ 2)) by ring]
    have hformula :
        8 / 3 - johnsonNormalizedEnvelope x =
          (1 - x) * (-12 * x ^ 3 - 25 * x ^ 2 + 127 * x - 56) /
            (147 * x) := by
      unfold johnsonNormalizedEnvelope
      rw [hmin]
      field_simp
      ring
    rw [← sub_pos]
    rw [hformula]
    positivity

/-- The exact rounded Johnson recipe satisfies the printed raw ordinary bound. -/
theorem johnsonE0_lt_closed {n D A : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (_ha : johnsonAgreement n D eta ≤ 1)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hAn : A ≤ n) :
    johnsonE0 n D A eta <
      (8 / 3 : ℝ) * n * johnsonT n D eta ^ 3 / johnsonRhoMinus n D := by
  let rho := johnsonRhoMinus n D
  let x := √rho
  let t := johnsonT n D eta
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrho : 0 < rho := johnsonRhoMinus_pos hD hDn
  have hx := johnsonSqrt_mem_Ioo hD hDn
  have ht : 7 / 2 ≤ t := johnsonT_ge_seven_halves n D eta
  have hscale : 0 < (n : ℝ) * t ^ 3 / rho := by positivity
  have hraw := johnsonE0_lt_preEnvelope_scale hD hDn heta hthreshold hAn
  have hpre : johnsonPreEnvelope x (1 / n) t ≤ johnsonNormalizedEnvelope x :=
    johnsonPreEnvelope_le_normalized hx.1 hx.2 ht (johnson_inv_length_le_min hD hDn)
  have hnormalized : johnsonNormalizedEnvelope x < 8 / 3 :=
    johnsonNormalizedEnvelope_lt hx.1 hx.2
  calc
    johnsonE0 n D A eta <
        ((n : ℝ) * t ^ 3 / rho) * johnsonPreEnvelope x (1 / n) t := hraw
    _ ≤ ((n : ℝ) * t ^ 3 / rho) * johnsonNormalizedEnvelope x := by
      exact mul_le_mul_of_nonneg_left hpre hscale.le
    _ < ((n : ℝ) * t ^ 3 / rho) * (8 / 3) := by
      exact mul_lt_mul_of_pos_left hnormalized hscale
    _ = (8 / 3 : ℝ) * n * t ^ 3 / rho := by ring

/-- The BCHKS comparison multiplicity is at least the multiplicity used in `johnsonE0`. -/
theorem johnsonM_le_BCHKS_M {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta) :
    johnsonM n D eta ≤ johnsonBCHKS_M n D eta := by
  let x := √(johnsonRhoMinus n D)
  have hx : 0 ≤ x := (johnsonSqrt_mem_Ioo hD hDn).1.le
  have hfrac : x / (2 * eta) ≤ x / eta := by
    exact div_le_div_of_nonneg_left hx heta (by linarith)
  have hceil : ⌈x / (2 * eta)⌉₊ ≤ ⌈x / eta⌉₊ := Nat.ceil_mono hfrac
  unfold johnsonM johnsonBCHKS_M
  exact max_le_max hceil le_rfl

/-- The shifted multiplicity used by `johnsonE0` is no larger than the BCHKS one. -/
theorem johnsonT_le_BCHKS_T {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta) :
    johnsonT n D eta ≤ johnsonBCHKS_T n D eta := by
  unfold johnsonT johnsonBCHKS_T
  have hcast : (johnsonM n D eta : ℝ) ≤ johnsonBCHKS_M n D eta := by
    exact_mod_cast johnsonM_le_BCHKS_M hD hDn heta
  linarith

/-- The BCHKS estimate strictly dominates its positive leading quintic term. -/
theorem johnsonBCHKS_leading_lt {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2)
    (ha : johnsonAgreement n D eta ≤ 1) :
    (2 * johnsonBCHKS_T n D eta ^ 5 /
          (3 * √(johnsonRhoMinus n D) ^ 3)) * n <
      johnsonBCHKS n D eta := by
  let rho := johnsonRhoMinus n D
  let x := √rho
  let tB := johnsonBCHKS_T n D eta
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrho : 0 < rho := johnsonRhoMinus_pos hD hDn
  have hx : 0 < x := Real.sqrt_pos.2 hrho
  have htB : 0 < tB := by
    unfold tB johnsonBCHKS_T
    have : (3 : ℝ) ≤ johnsonBCHKS_M n D eta := by
      exact_mod_cast le_max_right ⌈√(johnsonRhoMinus n D) / eta⌉₊ 3
    linarith
  have hgamma : 0 ≤ johnsonGamma n D eta := by
    unfold johnsonGamma
    linarith
  have hden : 0 < 3 * x ^ 3 := by positivity
  have hextra : 0 ≤ 3 * tB * johnsonGamma n D eta * rho := by positivity
  have hquot : 2 * tB ^ 5 / (3 * x ^ 3) ≤
      (2 * tB ^ 5 + 3 * tB * johnsonGamma n D eta * rho) / (3 * x ^ 3) := by
    exact (div_le_div_iff_of_pos_right hden).2 (by linarith)
  unfold johnsonBCHKS
  dsimp only [rho, x, tB]
  calc
    (2 * tB ^ 5 / (3 * x ^ 3)) * n ≤
        ((2 * tB ^ 5 + 3 * tB * johnsonGamma n D eta * rho) / (3 * x ^ 3)) * n := by
      exact mul_le_mul_of_nonneg_right hquot hn.le
    _ < ((2 * tB ^ 5 + 3 * tB * johnsonGamma n D eta * rho) / (3 * x ^ 3)) * n +
        tB / x := by
      have : 0 < tB / x := div_pos htB hx
      linarith

/-- The printed BCHKS comparison bound is positive throughout the Johnson range. -/
theorem johnsonBCHKS_pos {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2)
    (ha : johnsonAgreement n D eta ≤ 1) :
    0 < johnsonBCHKS n D eta := by
  let rho := johnsonRhoMinus n D
  let x := √rho
  let tB := johnsonBCHKS_T n D eta
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrho : 0 < rho := johnsonRhoMinus_pos hD hDn
  have hx : 0 < x := Real.sqrt_pos.2 hrho
  have htB : 0 < tB := by
    unfold tB johnsonBCHKS_T
    have hm : (3 : ℝ) ≤ johnsonBCHKS_M n D eta := by
      exact_mod_cast le_max_right ⌈√(johnsonRhoMinus n D) / eta⌉₊ 3
    linarith
  have hleading0 : 0 < (2 * tB ^ 5 / (3 * x ^ 3)) * n := by positivity
  exact lt_trans hleading0 (johnsonBCHKS_leading_lt hD hDn ha)

/-- For the exact finite recipe, the ordinary bound is less than `16/49` of BCHKS. -/
theorem johnsonE0_div_BCHKS_lt {n D A : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hAn : A ≤ n) :
    johnsonE0 n D A eta / johnsonBCHKS n D eta < 16 / 49 := by
  let rho := johnsonRhoMinus n D
  let x := √rho
  let t := johnsonT n D eta
  let tB := johnsonBCHKS_T n D eta
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrho : 0 < rho := johnsonRhoMinus_pos hD hDn
  have hx := johnsonSqrt_mem_Ioo hD hDn
  have hx1 : x < 1 := by exact hx.2
  have hxne : x ≠ 0 := by
    dsimp only [x]
    exact hx.1.ne'
  have hx2 : x ^ 2 = rho := Real.sq_sqrt hrho.le
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) (johnsonT_ge_seven_halves n D eta)
  have htBLower : 7 / 2 ≤ tB := by
    unfold tB johnsonBCHKS_T
    have hm : (3 : ℝ) ≤ johnsonBCHKS_M n D eta := by
      exact_mod_cast le_max_right ⌈√(johnsonRhoMinus n D) / eta⌉₊ 3
    linarith
  have htB : 0 < tB := lt_of_lt_of_le (by norm_num) htBLower
  have httB : t ≤ tB := johnsonT_le_BCHKS_T hD hDn heta
  have htCube : t ^ 3 ≤ tB ^ 3 := by gcongr
  have hxtCube : x * t ^ 3 < tB ^ 3 := by
    calc
      x * t ^ 3 < 1 * t ^ 3 := by
        exact mul_lt_mul_of_pos_right hx1 (pow_pos ht 3)
      _ ≤ tB ^ 3 := by simpa using htCube
  have h49 : (49 : ℝ) ≤ 4 * tB ^ 2 := by
    nlinarith [sq_nonneg (tB - 7 / 2)]
  have hquintic : 49 * tB ^ 3 ≤ 4 * tB ^ 5 := by
    have hmul := mul_le_mul_of_nonneg_right h49 (pow_nonneg htB.le 3)
    nlinarith [show tB ^ 5 = tB ^ 3 * tB ^ 2 by ring]
  have hkey : 49 * x * t ^ 3 < 4 * tB ^ 5 := by
    nlinarith
  have hnkey : 49 * (n : ℝ) * x * t ^ 3 < 4 * n * tB ^ 5 := by
    nlinarith [mul_pos hn (sub_pos.mpr hkey)]
  have hclosedCompare :
      (8 / 3 : ℝ) * n * t ^ 3 / rho <
        (16 / 49 : ℝ) * ((2 * tB ^ 5 / (3 * x ^ 3)) * n) := by
    rw [← hx2]
    calc
      (8 / 3 : ℝ) * n * t ^ 3 / x ^ 2 =
          ((8 / 3 : ℝ) * n * t ^ 3 * x) / x ^ 3 := by
        field_simp [hxne]
      _ < ((32 / 147 : ℝ) * n * tB ^ 5) / x ^ 3 := by
        exact (div_lt_div_iff_of_pos_right (pow_pos hx.1 3)).2 (by nlinarith)
      _ = (16 / 49 : ℝ) * ((2 * tB ^ 5 / (3 * x ^ 3)) * n) := by
        field_simp [hxne]
        norm_num
  have hE := johnsonE0_lt_closed hD hDn heta ha hthreshold hAn
  have hleading := johnsonBCHKS_leading_lt hD hDn ha
  have hB : 0 < johnsonBCHKS n D eta := johnsonBCHKS_pos hD hDn ha
  apply (div_lt_iff₀ hB).2
  calc
    johnsonE0 n D A eta < (8 / 3 : ℝ) * n * t ^ 3 / rho := hE
    _ < (16 / 49 : ℝ) * ((2 * tB ^ 5 / (3 * x ^ 3)) * n) := hclosedCompare
    _ < (16 / 49 : ℝ) * johnsonBCHKS n D eta := by
      exact mul_lt_mul_of_pos_left hleading (by norm_num)

/-- The exact finite ordinary bound is strictly stronger than the printed BCHKS bound. -/
theorem johnsonE0_lt_BCHKS {n D A : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hAn : A ≤ n) :
    johnsonE0 n D A eta < johnsonBCHKS n D eta := by
  have hB : 0 < johnsonBCHKS n D eta := johnsonBCHKS_pos hD hDn ha
  calc
    johnsonE0 n D A eta < (16 / 49 : ℝ) * johnsonBCHKS n D eta :=
      (div_lt_iff₀ hB).mp (johnsonE0_div_BCHKS_lt hD hDn heta ha hthreshold hAn)
    _ < 1 * johnsonBCHKS n D eta := by
      exact mul_lt_mul_of_pos_right (by norm_num) hB
    _ = johnsonBCHKS n D eta := one_mul _

/-- Non-strict compatibility form of `johnsonE0_lt_BCHKS`. -/
theorem johnsonE0_le_BCHKS {n D A : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hAn : A ≤ n) :
    johnsonE0 n D A eta ≤ johnsonBCHKS n D eta :=
  (johnsonE0_lt_BCHKS hD hDn heta ha hthreshold hAn).le

end

end ReedSolomon.HiddenDerivative
