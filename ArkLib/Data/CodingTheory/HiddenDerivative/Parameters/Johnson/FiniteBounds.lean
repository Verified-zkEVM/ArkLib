/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Algebra.Order.Floor.Semiring
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

The characteristic-free ordinary-agreement theorem for Reed–Solomon codes of length `n` and degree
at most `D` interpolates with parameters chosen from `ρ₋ = D / n` and a slack `η > 0` above the
Johnson radius `√ρ₋`. This file defines the rounded recipe and proves the real and natural-number
inequalities it satisfies. It contains no coding theory.

```text
m  = max ⌈√ρ₋ / (2η)⌉₊ 3        multiplicity                 (johnsonM)
t  = m + 1/2                                                  (johnsonT)
μ  = ⌈t / √ρ₋⌉₊ - 1             candidate degree             (johnsonMu)
h  = ⌈t² / (3ρ₋)⌉₊ - 1          challenge height             (johnsonH)
θ  = (n - D) / (A - D)          incidence ratio              (johnsonTheta)
E₀ = (2μ - 1) h + θ (h + μ + 4Dμh) + (n - D - 1) μ          (johnsonExceptionCount)
```

The basic bounds on `ρ₋`, `μ` and `h` need only `1 ≤ D < n`; the closed bounds on `E₀` also need
`D ≤ n - 2`, through `1 / n ≤ (1 - ρ₋) / 2`.

## Main statements

* `johnsonMu_lt`, `johnsonH_lt`, `johnsonMu_pos`, `johnsonH_pos`: `1 ≤ μ < t / √ρ₋` and
  `1 ≤ h < t² / (3ρ₋)`.
* `johnson_half_gap`: `√ρ₋ / 2 ≤ m η`.
* `johnson_degree_succ_le_agreement`, `johnsonTheta_le_sqrt_envelope`: the threshold
  `(√ρ₋ + η) n ≤ A` gives `D + 1 ≤ A` and `θ ≤ (1 + √ρ₋) / √ρ₋`.
* `johnsonExceptionCount_lt_closed`: `E₀ < (8/3) n t³ / ρ₋`.
* `johnsonExceptionCount_div_comparisonEstimate_lt`,
  `johnsonExceptionCount_lt_comparisonEstimate`: `E₀` is below `16/49` of the exception estimate
  `johnsonComparisonEstimate` of [BCPZZ26].

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed-Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26]
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

/-- The degree ratio `ρ₋ = D / n` of a Reed–Solomon code of length `n` whose messages are
polynomials of degree at most `D`. The code rate is `(D + 1) / n`; the Johnson recipe is stated in
terms of `D / n`. At `n = 0` the value is `0` by the convention `x / 0 = 0`. -/
def johnsonRhoMinus (n D : ℕ) : ℝ :=
  (D : ℝ) / n

/-- The agreement fraction `√(D / n) + η`: the Johnson radius `√ρ₋` plus the slack `η`. -/
def johnsonAgreement (n D : ℕ) (eta : ℝ) : ℝ :=
  √(johnsonRhoMinus n D) + eta

/-- The interpolation multiplicity `m = max ⌈√ρ₋ / (2η)⌉₊ 3`. The ceiling makes
`√ρ₋ / 2 ≤ m η` (`johnson_half_gap`), and the floor `3` makes `m + 1/2 ≥ 7/2`, which the closed
bounds use. -/
def johnsonM (n D : ℕ) (eta : ℝ) : ℕ :=
  max ⌈√(johnsonRhoMinus n D) / (2 * eta)⌉₊ 3

/-- The half-shifted multiplicity `t = m + 1/2`, the real parameter in which the degree and
height recipes and the closed bounds are written. -/
def johnsonT (n D : ℕ) (eta : ℝ) : ℝ :=
  johnsonM n D eta + 1 / 2

/-- The degree bound in the candidate-polynomial coordinate, `μ = ⌈t / √ρ₋⌉₊ - 1`, the largest
natural number strictly below `t / √ρ₋` when that quotient is positive. -/
def johnsonMu (n D : ℕ) (eta : ℝ) : ℕ :=
  ⌈johnsonT n D eta / √(johnsonRhoMinus n D)⌉₊ - 1

/-- The height in the challenge coordinate, `h = ⌈t² / (3ρ₋)⌉₊ - 1`, the largest natural number
strictly below `t² / (3ρ₋)` when that quotient is positive. -/
def johnsonH (n D : ℕ) (eta : ℝ) : ℕ :=
  ⌈johnsonT n D eta ^ 2 / (3 * johnsonRhoMinus n D)⌉₊ - 1

/-- The incidence ratio `θ = (n - D) / (A - D)` for agreement threshold `A`, with natural
subtraction in numerator and denominator. It is `0` when `A ≤ D`; under the Johnson threshold the
denominator is positive (`johnsonTheta_denominator_pos`). -/
def johnsonTheta (n D A : ℕ) : ℝ :=
  ((n - D : ℕ) : ℝ) / (A - D : ℕ)

/-- The raw exception count of the characteristic-free ordinary-agreement argument,
`(2μ - 1) h + θ (h + μ + 4 D μ h) + (n - D - 1) μ`, with `μ = johnsonMu`, `h = johnsonH`,
`θ = johnsonTheta` and natural subtraction in `2μ - 1` and `n - D - 1`. Its closed upper bound is
`johnsonExceptionCount_lt_closed`. -/
def johnsonExceptionCount (n D A : ℕ) (eta : ℝ) : ℝ :=
  let μ := johnsonMu n D eta
  let h := johnsonH n D eta
  (2 * μ - 1 : ℕ) * h + johnsonTheta n D A * (h + μ + 4 * D * μ * h) +
    (n - D - 1 : ℕ) * μ

/-- The sharper raw exception count `(2μ - 1) h + θ (h + μ + (2D - 1) h (2μ - 1)) + (n - D - 1) μ`,
which the ordinary-agreement argument provides when `μ ≤ D`. This file only defines it. -/
def johnsonRefinedExceptionCount (n D A : ℕ) (eta : ℝ) : ℝ :=
  let μ := johnsonMu n D eta
  let h := johnsonH n D eta
  (2 * μ - 1 : ℕ) * h +
    johnsonTheta n D A * (h + μ + (2 * D - 1) * h * (2 * μ - 1)) +
    (n - D - 1 : ℕ) * μ

/-- The multiplicity `max ⌈√ρ₋ / η⌉₊ 3` of the Johnson exception estimate
`johnsonComparisonEstimate`. It differs from `johnsonM` only by the factor `2` in the denominator,
so it is at least `johnsonM` (`johnsonM_le_comparisonMultiplicity`). -/
def johnsonComparisonMultiplicity (n D : ℕ) (eta : ℝ) : ℕ :=
  max ⌈√(johnsonRhoMinus n D) / eta⌉₊ 3

/-- The half-shifted comparison multiplicity `t_B = johnsonComparisonMultiplicity + 1/2`. -/
def johnsonComparisonShift (n D : ℕ) (eta : ℝ) : ℝ :=
  johnsonComparisonMultiplicity n D eta + 1 / 2

/-- The agreement slack `γ = 1 - (√ρ₋ + η)` appearing in `johnsonComparisonEstimate`. It is
nonnegative exactly when the agreement fraction is at most `1`. -/
def johnsonGamma (n D : ℕ) (eta : ℝ) : ℝ :=
  1 - johnsonAgreement n D eta

/-- The Johnson exception estimate
`((2 t_B⁵ + 3 t_B γ ρ₋) / (3 √ρ₋³)) n + t_B / √ρ₋`, written with `√ρ₋ ^ 3`; the equality
`√ρ₋ ^ 3 = ρ₋ ^ (3/2)` is `johnson_sqrt_cube_eq_rpow_three_halves`. -/
def johnsonComparisonEstimate (n D : ℕ) (eta : ℝ) : ℝ :=
  let rho := johnsonRhoMinus n D
  let tB := johnsonComparisonShift n D eta
  ((2 * tB ^ 5 + 3 * tB * johnsonGamma n D eta * rho) / (3 * √rho ^ 3)) * n +
    tB / √rho

/-- `ρ₋ = D / n` is positive when `1 ≤ D < n`. Both bounds are needed: `D = 0` gives `0`, and
`D < n` is used only to make `n` positive. -/
theorem johnsonRhoMinus_pos {n D : ℕ} (hD : 1 ≤ D) (hDn : D < n) :
    0 < johnsonRhoMinus n D := by
  unfold johnsonRhoMinus
  have hn : 0 < n := by omega
  positivity

/-- `ρ₋ = D / n` is strictly below `1` when `1 ≤ D < n`. The bound `D < n` is needed: `D = n`
gives `1`. -/
theorem johnsonRhoMinus_lt_one {n D : ℕ} (hD : 1 ≤ D) (hDn : D < n) :
    johnsonRhoMinus n D < 1 := by
  unfold johnsonRhoMinus
  have hDn' : D < n := by omega
  exact (div_lt_one (by exact_mod_cast (show 0 < n by omega))).2 (by exact_mod_cast hDn')

/-- `√ρ₋ ^ 3 = ρ₋ ^ (3/2)` as a real power. No hypothesis is needed because `ρ₋ ≥ 0`. -/
theorem johnson_sqrt_cube_eq_rpow_three_halves (n D : ℕ) :
    √(johnsonRhoMinus n D) ^ 3 =
      Real.rpow (johnsonRhoMinus n D) (3 / 2 : ℝ) := by
  symm
  calc
    Real.rpow (johnsonRhoMinus n D) (3 / 2 : ℝ) =
        Real.rpow (√(johnsonRhoMinus n D)) (3 : ℝ) :=
      Real.rpow_div_two_eq_sqrt 3 (by unfold johnsonRhoMinus; positivity)
    _ = √(johnsonRhoMinus n D) ^ 3 := Real.rpow_natCast _ 3

/-- `0 < √ρ₋ < 1` when `1 ≤ D < n`. -/
theorem johnsonSqrt_mem_Ioo {n D : ℕ} (hD : 1 ≤ D) (hDn : D < n) :
    0 < √(johnsonRhoMinus n D) ∧ √(johnsonRhoMinus n D) < 1 := by
  have hrho := johnsonRhoMinus_pos hD hDn
  refine ⟨Real.sqrt_pos.2 hrho, ?_⟩
  simpa only [Real.sqrt_one] using
    Real.sqrt_lt_sqrt hrho.le (johnsonRhoMinus_lt_one hD hDn)

/-- The agreement fraction `√ρ₋ + η` strictly exceeds `ρ₋` for `η > 0`, since `ρ₋ < √ρ₋` on
`0 < ρ₋ < 1`. -/
theorem johnsonRhoMinus_lt_agreement {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n) (heta : 0 < eta) :
    johnsonRhoMinus n D < johnsonAgreement n D eta := by
  have hx := johnsonSqrt_mem_Ioo hD hDn
  have hsqrt := Real.sq_sqrt (johnsonRhoMinus_pos hD hDn).le
  unfold johnsonAgreement
  nlinarith [mul_pos hx.1 (sub_pos.2 hx.2)]

/-- The multiplicity `johnsonM` is at least `3`, for all parameters. -/
theorem johnsonM_ge_three (n D : ℕ) (eta : ℝ) : 3 ≤ johnsonM n D eta := by
  unfold johnsonM
  exact le_max_right _ _

/-- The shifted multiplicity satisfies `t ≥ 7/2`, for all parameters. -/
theorem johnsonT_ge_seven_halves (n D : ℕ) (eta : ℝ) :
    7 / 2 ≤ johnsonT n D eta := by
  have hm : (3 : ℝ) ≤ johnsonM n D eta := by exact_mod_cast johnsonM_ge_three n D eta
  calc
    (7 / 2 : ℝ) = 3 + 1 / 2 := by norm_num
    _ ≤ johnsonM n D eta + 1 / 2 := by
      simpa only [add_comm] using add_le_add_right hm (1 / 2)
    _ = johnsonT n D eta := by rfl

/-- The half-gap inequality `√ρ₋ / 2 ≤ m η` used by the interpolation step, from the ceiling in
`johnsonM`. Only `η > 0` is needed; for `η ≤ 0` the ceiling is `0` and the inequality can fail. -/
theorem johnson_half_gap (n D : ℕ) {eta : ℝ} (heta : 0 < eta) :
    √(johnsonRhoMinus n D) / 2 ≤ johnsonM n D eta * eta := by
  let x := √(johnsonRhoMinus n D)
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

/-- If `A ≥ (√ρ₋ + η) n` with `η > 0` and `1 ≤ D < n`, then `D + 1 ≤ A`, because
`D = ρ₋ n < (√ρ₋ + η) n` (`johnsonRhoMinus_lt_agreement`). -/
theorem johnson_degree_succ_le_agreement {n D A : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n) (heta : 0 < eta)
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

/-- Under the Johnson threshold the denominator `A - D` of `johnsonTheta` is positive. -/
theorem johnsonTheta_denominator_pos {n D A : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) :
    0 < A - D := by
  have := johnson_degree_succ_le_agreement hD hDn heta hthreshold
  omega

/-- `μ < t / √ρ₋` when `1 ≤ D < n`. The hypotheses make `√ρ₋` positive; at `D = 0` both sides
are `0`. -/
theorem johnsonMu_lt {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n) :
    (johnsonMu n D eta : ℝ) < johnsonT n D eta / √(johnsonRhoMinus n D) := by
  let z := johnsonT n D eta / √(johnsonRhoMinus n D)
  have hz : 0 < z := div_pos (by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 2) (johnsonT_ge_seven_halves n D eta))
    (johnsonSqrt_mem_Ioo hD hDn).1
  exact Nat.cast_ceil_sub_one_lt hz

/-- `h < t² / (3ρ₋)` when `1 ≤ D < n`. The hypotheses make `ρ₋` positive; at `D = 0` both sides
are `0`. -/
theorem johnsonH_lt {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n) :
    (johnsonH n D eta : ℝ) <
      johnsonT n D eta ^ 2 / (3 * johnsonRhoMinus n D) := by
  let z := johnsonT n D eta ^ 2 / (3 * johnsonRhoMinus n D)
  have hz : 0 < z := div_pos (sq_pos_of_pos (lt_of_lt_of_le
    (by norm_num : (0 : ℝ) < 7 / 2) (johnsonT_ge_seven_halves n D eta)))
    (mul_pos (by norm_num) (johnsonRhoMinus_pos hD hDn))
  exact Nat.cast_ceil_sub_one_lt hz

/-- `1 ≤ μ` when `1 ≤ D < n`, because then `t / √ρ₋ > t > 1`. -/
theorem johnsonMu_pos {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n) :
    1 ≤ johnsonMu n D eta := by
  let z := johnsonT n D eta / √(johnsonRhoMinus n D)
  have ht : (1 : ℝ) < johnsonT n D eta :=
    lt_of_lt_of_le (by norm_num) (johnsonT_ge_seven_halves n D eta)
  have hx := johnsonSqrt_mem_Ioo hD hDn
  have hz : (1 : ℝ) < z := by
    dsimp only [z]
    apply (lt_div_iff₀ hx.1).2
    nlinarith
  exact Nat.one_le_ceil_sub_one hz

/-- `1 ≤ h` when `1 ≤ D < n`, because then `t² / (3ρ₋) > t² / 3 > 1`. -/
theorem johnsonH_pos {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n) :
    1 ≤ johnsonH n D eta := by
  let z := johnsonT n D eta ^ 2 / (3 * johnsonRhoMinus n D)
  have ht : (3 : ℝ) < johnsonT n D eta ^ 2 := by
    exact lt_of_lt_of_le (by norm_num)
      (pow_le_pow_left₀ (by norm_num) (johnsonT_ge_seven_halves n D eta) 2)
  have hrho := johnsonRhoMinus_lt_one hD hDn
  have hz : (1 : ℝ) < z := by
    dsimp only [z]
    apply (lt_div_iff₀ (mul_pos (by norm_num) (johnsonRhoMinus_pos hD hDn))).2
    linarith only [ht, hrho]
  exact Nat.one_le_ceil_sub_one hz

/-- `1 / n ≤ min (√ρ₋²) ((1 - √ρ₋²) / 2)` when `1 ≤ D ≤ n - 2`. The first bound is `1 ≤ D`; the
second is `n - D ≥ 2`, which is where the guard `D ≤ n - 2` (rather than `D < n`) is needed. -/
theorem johnson_inv_length_le_min {n D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n - 2) :
    (1 : ℝ) / n ≤ min (√(johnsonRhoMinus n D) ^ 2)
      ((1 - √(johnsonRhoMinus n D) ^ 2) / 2) := by
  let rho := johnsonRhoMinus n D
  let x := √rho
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrho : 0 ≤ rho := (johnsonRhoMinus_pos hD (by omega)).le
  have hx2 : x ^ 2 = rho := Real.sq_sqrt hrho
  have hrhoEq : rho = (D : ℝ) / n := rfl
  apply le_min
  · rw [hx2, hrhoEq]
    exact (div_le_div_iff_of_pos_right hn).2 (by exact_mod_cast hD)
  · rw [hx2, hrhoEq]
    have hgapNat : 2 ≤ n - D := by omega
    have hgap : (2 : ℝ) ≤ ((n - D : ℕ) : ℝ) := by exact_mod_cast hgapNat
    rw [Nat.cast_sub (show D ≤ n by omega)] at hgap
    have hone : (1 : ℝ) ≤ ((n : ℝ) - D) / 2 := by linarith only [hgap]
    calc
      (1 : ℝ) / n ≤ (((n : ℝ) - D) / 2) / n :=
        (div_le_div_iff_of_pos_right hn).2 hone
      _ = (1 - (D : ℝ) / n) / 2 := by field_simp

/-- Under the Johnson threshold `(√ρ₋ + η) n ≤ A`, the incidence ratio satisfies
`θ ≤ (1 + x) / x` with `x = √ρ₋`: the numerator is `n (1 - x²)` and the denominator is at least
`n (x - x²)`. -/
theorem johnsonTheta_le_sqrt_envelope {n D A : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n) (heta : 0 < eta)
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
    have hthreshold' : (x + eta) * n ≤ (A : ℝ) := by
      simpa only [johnsonAgreement, x, rho] using hthreshold
    calc
      x * n < (x + eta) * n :=
        mul_lt_mul_of_pos_right (lt_add_of_pos_right x heta) hn
      _ ≤ A := hthreshold'
  have hdenLower : n * (x - x ^ 2) ≤ ((A - D : ℕ) : ℝ) := by
    rw [hden, hrhoEq, ← hx2]
    apply (le_sub_iff_add_le).2
    calc
      n * (x - x ^ 2) + x ^ 2 * n = x * n := by ring
      _ ≤ A := hxA.le
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
  calc
    n * (1 - x ^ 2) * x = (1 + x) * (n * (x - x ^ 2)) := by ring
    _ ≤ (1 + x) * ((A - D : ℕ) : ℝ) := hmul

/-- The normalized envelope
`4(1 + x)/3 + (16/(21x) + 26/147) min (x²) ((1 - x²)/2) + 4x(1 - x²)/49`, obtained from
`johnsonPreEnvelope` by inserting `t ≥ 7/2` and `1 / n ≤ min (x²) ((1 - x²)/2)`. -/
def johnsonNormalizedEnvelope (x : ℝ) : ℝ :=
  4 * (1 + x) / 3 +
    (16 / (21 * x) + 26 / 147) * min (x ^ 2) ((1 - x ^ 2) / 2) +
    4 * x * (1 - x ^ 2) / 49

/-- The pre-envelope `4(1 + x)/3 + (2/(3x) + (1 + x)/(3tx) + 1/t²) y + x(1 - x²)/t²`. With
`x = √ρ₋`, `y = 1 / n` and `t = johnsonT`, the scaled value `(n t³ / ρ₋) · johnsonPreEnvelope x y t`
bounds `johnsonExceptionCount` (`johnsonExceptionCount_lt_preEnvelope_scale`). -/
def johnsonPreEnvelope (x y t : ℝ) : ℝ :=
  4 * (1 + x) / 3 +
    (2 / (3 * x) + (1 + x) / (3 * t * x) + 1 / t ^ 2) * y +
    x * (1 - x ^ 2) / t ^ 2

/-- `johnsonPreEnvelope x y t ≤ johnsonNormalizedEnvelope x` for `0 < x < 1`, `t ≥ 7/2` and
`y ≤ min (x²) ((1 - x²)/2)`. The pre-envelope is decreasing in `t` and increasing in `y`, so the
lower bound on `t` and the upper bound on `y` are what the comparison uses. -/
theorem johnsonPreEnvelope_le_normalized {x y t : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (ht : 7 / 2 ≤ t)
    (hy : y ≤ min (x ^ 2) ((1 - x ^ 2) / 2)) :
    johnsonPreEnvelope x y t ≤ johnsonNormalizedEnvelope x := by
  let s := min (x ^ 2) ((1 - x ^ 2) / 2)
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hxSquare : 0 ≤ 1 - x ^ 2 := by
    rw [show (1 : ℝ) - x ^ 2 = (1 - x) * (1 + x) by ring]
    positivity
  have hs0 : 0 ≤ s := by
    apply le_min
    · positivity
    · positivity
  have hinv : 1 / t ≤ (2 / 7 : ℝ) := by
    apply (div_le_iff₀ ht0).2
    calc
      1 = (7 / 2 : ℝ) * (2 / 7) := by norm_num
      _ ≤ t * (2 / 7) := mul_le_mul_of_nonneg_right ht (by norm_num)
      _ = (2 / 7) * t := by ring
  have hinvSq : 1 / t ^ 2 ≤ (4 / 49 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos ht0)).2
    have htSquared : (7 / 2 : ℝ) ^ 2 ≤ t ^ 2 :=
      (sq_le_sq₀ (by norm_num) ht0.le).2 ht
    calc
      1 = (7 / 2 : ℝ) ^ 2 * (4 / 49) := by norm_num
      _ ≤ t ^ 2 * (4 / 49) := mul_le_mul_of_nonneg_right htSquared (by norm_num)
      _ = (4 / 49) * t ^ 2 := by ring
  have hmiddleCoeff :
      2 / (3 * x) + (1 + x) / (3 * t * x) + 1 / t ^ 2 ≤
        16 / (21 * x) + 26 / 147 := by
    have hscaled : (1 + x) / (3 * t * x) ≤ 2 * (1 + x) / (21 * x) := by
      calc
        (1 + x) / (3 * t * x) = (1 + x) / (3 * x) * (1 / t) := by
          field_simp
        _ ≤ (1 + x) / (3 * x) * (2 / 7) := mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 2 * (1 + x) / (21 * x) := by ring
    calc
      _ ≤ 2 / (3 * x) + 2 * (1 + x) / (21 * x) + 4 / 49 :=
        add_le_add (add_le_add le_rfl hscaled) hinvSq
      _ = 16 / (21 * x) + 26 / 147 := by field_simp; ring
  have hmiddleCoeff0 :
      0 ≤ 2 / (3 * x) + (1 + x) / (3 * t * x) + 1 / t ^ 2 := by positivity
  have hmiddle :
      (2 / (3 * x) + (1 + x) / (3 * t * x) + 1 / t ^ 2) * y ≤
        (16 / (21 * x) + 26 / 147) * s := by
    calc
      _ ≤ (2 / (3 * x) + (1 + x) / (3 * t * x) + 1 / t ^ 2) * s := by
        exact mul_le_mul_of_nonneg_left hy hmiddleCoeff0
      _ ≤ _ := mul_le_mul_of_nonneg_right hmiddleCoeff hs0
  have hxgap : 0 ≤ x * (1 - x ^ 2) := by positivity
  have hlast : x * (1 - x ^ 2) / t ^ 2 ≤ 4 * x * (1 - x ^ 2) / 49 := by
    calc
      x * (1 - x ^ 2) / t ^ 2 = x * (1 - x ^ 2) * (1 / t ^ 2) := by ring
      _ ≤ x * (1 - x ^ 2) * (4 / 49) := mul_le_mul_of_nonneg_left hinvSq hxgap
      _ = 4 * x * (1 - x ^ 2) / 49 := by ring
  unfold johnsonPreEnvelope johnsonNormalizedEnvelope
  dsimp only [s] at hmiddle
  exact add_le_add (add_le_add le_rfl hmiddle) hlast

/-- `E₀ < (n t³ / ρ₋) · johnsonPreEnvelope √ρ₋ (1/n) t`, where `E₀ = johnsonExceptionCount`,
under `1 ≤ D < n`, `η > 0` and the Johnson threshold `(√ρ₋ + η) n ≤ A`. Each term of `E₀` is
bounded using `μ < t / √ρ₋`, `h < t² / (3ρ₋)` and `θ ≤ (1 + √ρ₋) / √ρ₋`. -/
theorem johnsonExceptionCount_lt_preEnvelope_scale {n D A : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) :
    johnsonExceptionCount n D A eta <
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
  have htheta0 : 0 ≤ theta := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
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
      ((2 * μ - 1 : ℕ) : ℝ) * h ≤ 2 * (μ : ℝ) * h := mul_le_mul_of_nonneg_right hcast hh0.le
      _ < 2 * (t / x) * (t ^ 2 / (3 * rho)) :=
        mul_lt_mul'' (mul_lt_mul_of_pos_left hμ two_pos) hh (by positivity) hh0.le
      _ = 2 * t ^ 3 / (3 * x ^ 3) := by rw [← hx2]; field_simp
  have hthetaHeight : theta * (h : ℝ) < (1 + x) * t ^ 2 / (3 * x ^ 3) := by
    calc
      theta * (h : ℝ) ≤ ((1 + x) / x) * h := mul_le_mul_of_nonneg_right htheta hh0.le
      _ < ((1 + x) / x) * (t ^ 2 / (3 * rho)) :=
        mul_lt_mul_of_pos_left hh (div_pos (add_pos one_pos hx.1) hx.1)
      _ = (1 + x) * t ^ 2 / (3 * x ^ 3) := by rw [← hx2]; field_simp
  have hthetaMain : theta * (4 * D * μ * h : ℕ) <
      4 * (1 + x) * n * t ^ 3 / (3 * x ^ 2) := by
    have hc4 : 0 < 4 * ((n : ℝ) * x ^ 2) := mul_pos (by norm_num) (mul_pos hn (pow_pos hx.1 2))
    push_cast
    rw [hDEq]
    calc
      theta * (4 * ((n : ℝ) * x ^ 2) * μ * h) ≤
          ((1 + x) / x) * (4 * ((n : ℝ) * x ^ 2) * μ * h) :=
        mul_le_mul_of_nonneg_right htheta (mul_nonneg (mul_nonneg hc4.le hμ0.le) hh0.le)
      _ < ((1 + x) / x) *
          (4 * ((n : ℝ) * x ^ 2) * (t / x) * (t ^ 2 / (3 * rho))) :=
        mul_lt_mul_of_pos_left
          (mul_lt_mul'' (mul_lt_mul_of_pos_left hμ hc4) hh (mul_nonneg hc4.le hμ0.le) hh0.le)
          (div_pos (add_pos one_pos hx.1) hx.1)
      _ = 4 * (1 + x) * n * t ^ 3 / (3 * x ^ 2) := by
        rw [← hx2]
        field_simp
  have hcoeff : theta + ((n - D - 1 : ℕ) : ℝ) ≤
      (n : ℝ) * (1 - x ^ 2) + 1 / x := by
    rw [htailEq]
    have hxne : x ≠ 0 := hx.1.ne'
    calc
      theta + ((n : ℝ) * (1 - x ^ 2) - 1) ≤
          (1 + x) / x + ((n : ℝ) * (1 - x ^ 2) - 1) := add_le_add htheta le_rfl
      _ = (n : ℝ) * (1 - x ^ 2) + 1 / x := by field_simp; ring
  have hcoeff0 : 0 ≤ theta + ((n - D - 1 : ℕ) : ℝ) := add_nonneg htheta0 (Nat.cast_nonneg _)
  have hcoeffUpper0 : 0 < (n : ℝ) * (1 - x ^ 2) + 1 / x := by
    have : 0 < 1 - x ^ 2 := by
      rw [show (1 : ℝ) - x ^ 2 = (1 - x) * (1 + x) by ring]
      exact mul_pos (sub_pos.mpr hx.2) (add_pos one_pos hx.1)
    exact add_pos_of_nonneg_of_pos (mul_nonneg hn.le this.le) (one_div_pos.2 hx.1)
  have hlinear : (theta + ((n - D - 1 : ℕ) : ℝ)) * μ <
      (n : ℝ) * t * (1 - x ^ 2) / x + t / x ^ 2 := by
    calc
      (theta + ((n - D - 1 : ℕ) : ℝ)) * μ ≤
          ((n : ℝ) * (1 - x ^ 2) + 1 / x) * μ := mul_le_mul_of_nonneg_right hcoeff hμ0.le
      _ < ((n : ℝ) * (1 - x ^ 2) + 1 / x) * (t / x) := mul_lt_mul_of_pos_left hμ hcoeffUpper0
      _ = (n : ℝ) * t * (1 - x ^ 2) / x + t / x ^ 2 := by
        field_simp [hxne]
  calc
    johnsonExceptionCount n D A eta =
        ((2 * μ - 1 : ℕ) : ℝ) * h + theta * h + theta * (4 * D * μ * h : ℕ) +
          (theta + ((n - D - 1 : ℕ) : ℝ)) * μ := by
            unfold johnsonExceptionCount
            dsimp only [μ, h, theta]
            push_cast
            ring
    _ < 2 * t ^ 3 / (3 * x ^ 3) + (1 + x) * t ^ 2 / (3 * x ^ 3) +
        4 * (1 + x) * n * t ^ 3 / (3 * x ^ 2) +
        ((n : ℝ) * t * (1 - x ^ 2) / x + t / x ^ 2) :=
      add_lt_add (add_lt_add (add_lt_add hfirst hthetaHeight) hthetaMain) hlinear
    _ = ((n : ℝ) * t ^ 3 / rho) * johnsonPreEnvelope x (1 / n) t := by
      unfold johnsonPreEnvelope
      rw [← hx2]
      field_simp [hxne, hn.ne', ht0.ne']
      ring

/-- `johnsonNormalizedEnvelope x < 8/3` for `0 < x < 1`. The proof splits at `x = 1/√3`, where
the two arguments of the `min` are equal, and reduces each side to a cubic in `x` that is positive
on that side. -/
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
  · have hx2r : x ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hx0.le hxr 2
    have hmin : min (x ^ 2) ((1 - x ^ 2) / 2) = x ^ 2 := by
      apply min_eq_left
      linarith only [hx2r, hr2]
    have hrEndpoint : 0 < 196 - 320 * r - 26 * r ^ 2 + 12 * r ^ 3 := by
      have hsquares : (316 * r) ^ 2 < ((562 : ℝ) / 3) ^ 2 := by
        rw [mul_pow, hr2]
        norm_num
      have hroot : 316 * r < (562 : ℝ) / 3 := lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsquares
      rw [hr2, hr3]
      linarith only [hroot]
    have hbracket :
        0 < 320 + 26 * (x + r) - 12 * (x ^ 2 + x * r + r ^ 2) := by
      have hxxr : x * x ≤ r * x := mul_le_mul_of_nonneg_right hxr hx0.le
      have hxrr : r * x ≤ r * r := mul_le_mul_of_nonneg_left hxr hr0.le
      linarith only [hxxr, hxrr, hr2, hx0, hr0]
    have hproduct : 0 ≤ (r - x) *
        (320 + 26 * (x + r) - 12 * (x ^ 2 + x * r + r ^ 2)) :=
      mul_nonneg (sub_nonneg.mpr hxr) hbracket.le
    have hpoly : 0 < 196 - 320 * x - 26 * x ^ 2 + 12 * x ^ 3 := by
      have hpolyEq : 196 - 320 * x - 26 * x ^ 2 + 12 * x ^ 3 =
          (196 - 320 * r - 26 * r ^ 2 + 12 * r ^ 3) +
            (r - x) * (320 + 26 * (x + r) - 12 * (x ^ 2 + x * r + r ^ 2)) := by
        ring
      rw [hpolyEq]
      exact add_pos_of_pos_of_nonneg hrEndpoint hproduct
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
      linarith only [mul_nonneg (sub_nonneg.mpr hrx) (add_nonneg hr0.le hx0.le), hr2]
    have hrEndpoint : 0 < -12 * r ^ 3 - 25 * r ^ 2 + 127 * r - 56 := by
      have hsquares : ((193 : ℝ) / 3) ^ 2 < (123 * r) ^ 2 := by
        rw [mul_pow, hr2]
        norm_num
      have hroot : (193 : ℝ) / 3 < 123 * r :=
        lt_of_pow_lt_pow_left₀ 2 (mul_pos (by norm_num) hr0).le hsquares
      rw [hr2, hr3]
      linarith only [hroot]
    have hx2 : x ^ 2 < 1 := pow_lt_one₀ hx0.le hx1 two_ne_zero
    have hxrOne : x * r < 1 := by
      exact (mul_le_of_le_one_right hx0.le hr1.le).trans_lt hx1
    have hbracket :
        0 < 127 - 25 * (x + r) - 12 * (x ^ 2 + x * r + r ^ 2) := by
      linarith only [hx2, hxrOne, hr2, hx1, hr1]
    have hproduct : 0 ≤ (x - r) *
        (127 - 25 * (x + r) - 12 * (x ^ 2 + x * r + r ^ 2)) :=
      mul_nonneg (sub_nonneg.mpr hrx) hbracket.le
    have hpoly : 0 < -12 * x ^ 3 - 25 * x ^ 2 + 127 * x - 56 := by
      have hpolyEq : -12 * x ^ 3 - 25 * x ^ 2 + 127 * x - 56 =
          (-12 * r ^ 3 - 25 * r ^ 2 + 127 * r - 56) +
            (x - r) * (127 - 25 * (x + r) - 12 * (x ^ 2 + x * r + r ^ 2)) := by
        ring
      rw [hpolyEq]
      exact add_pos_of_pos_of_nonneg hrEndpoint hproduct
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
    exact div_pos (mul_pos (sub_pos.2 hx1) hpoly) (by positivity)

/-- The closed bound `johnsonExceptionCount < (8/3) n t³ / ρ₋` for `1 ≤ D ≤ n - 2`, `η > 0` and
`(√ρ₋ + η) n ≤ A`. The guard `D ≤ n - 2` enters through `johnson_inv_length_le_min`. -/
theorem johnsonExceptionCount_lt_closed {n D A : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) :
    johnsonExceptionCount n D A eta <
      (8 / 3 : ℝ) * n * johnsonT n D eta ^ 3 / johnsonRhoMinus n D := by
  let rho := johnsonRhoMinus n D
  let x := √rho
  let t := johnsonT n D eta
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrho : 0 < rho := johnsonRhoMinus_pos hD (by omega)
  have hx := johnsonSqrt_mem_Ioo (n := n) hD (by omega)
  have ht : 7 / 2 ≤ t := johnsonT_ge_seven_halves n D eta
  have hscale : 0 < (n : ℝ) * t ^ 3 / rho := by positivity
  have hraw := johnsonExceptionCount_lt_preEnvelope_scale hD (by omega) heta hthreshold
  have hpre : johnsonPreEnvelope x (1 / n) t ≤ johnsonNormalizedEnvelope x :=
    johnsonPreEnvelope_le_normalized hx.1 hx.2 ht (johnson_inv_length_le_min hD hDn)
  have hnormalized : johnsonNormalizedEnvelope x < 8 / 3 :=
    johnsonNormalizedEnvelope_lt hx.1 hx.2
  calc
    johnsonExceptionCount n D A eta <
        ((n : ℝ) * t ^ 3 / rho) * johnsonPreEnvelope x (1 / n) t := hraw
    _ ≤ ((n : ℝ) * t ^ 3 / rho) * johnsonNormalizedEnvelope x := by
      exact mul_le_mul_of_nonneg_left hpre hscale.le
    _ < ((n : ℝ) * t ^ 3 / rho) * (8 / 3) := by
      exact mul_lt_mul_of_pos_left hnormalized hscale
    _ = (8 / 3 : ℝ) * n * t ^ 3 / rho := by ring

/-- `johnsonM ≤ johnsonComparisonMultiplicity` for `η > 0`. For `η < 0` both ceilings are `0`
and the statement still holds, but the proof uses `η > 0` to compare the quotients. -/
theorem johnsonM_le_comparisonMultiplicity (n D : ℕ) {eta : ℝ} (heta : 0 < eta) :
    johnsonM n D eta ≤ johnsonComparisonMultiplicity n D eta := by
  let x := √(johnsonRhoMinus n D)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hfrac : x / (2 * eta) ≤ x / eta := by
    exact div_le_div_of_nonneg_left hx heta (by linarith)
  have hceil : ⌈x / (2 * eta)⌉₊ ≤ ⌈x / eta⌉₊ := Nat.ceil_mono hfrac
  unfold johnsonM johnsonComparisonMultiplicity
  exact max_le_max hceil le_rfl

/-- `johnsonT ≤ johnsonComparisonShift` for `η > 0`. -/
theorem johnsonT_le_comparisonShift (n D : ℕ) {eta : ℝ} (heta : 0 < eta) :
    johnsonT n D eta ≤ johnsonComparisonShift n D eta := by
  unfold johnsonT johnsonComparisonShift
  have hcast : (johnsonM n D eta : ℝ) ≤ johnsonComparisonMultiplicity n D eta := by
    exact_mod_cast johnsonM_le_comparisonMultiplicity n D heta
  linarith

/-- `johnsonComparisonEstimate` strictly exceeds its leading term `(2 t_B⁵ / (3 √ρ₋³)) n` when
`1 ≤ D < n` and the agreement fraction is at most `1`; the last hypothesis makes `γ ≥ 0`. -/
theorem johnsonComparisonEstimate_leading_lt {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n)
    (ha : johnsonAgreement n D eta ≤ 1) :
    (2 * johnsonComparisonShift n D eta ^ 5 /
          (3 * √(johnsonRhoMinus n D) ^ 3)) * n <
      johnsonComparisonEstimate n D eta := by
  let rho := johnsonRhoMinus n D
  let x := √rho
  let tB := johnsonComparisonShift n D eta
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrho : 0 < rho := johnsonRhoMinus_pos hD hDn
  have hx : 0 < x := Real.sqrt_pos.2 hrho
  have htB : 0 < tB := by
    unfold tB johnsonComparisonShift
    have : (3 : ℝ) ≤ johnsonComparisonMultiplicity n D eta := by
      exact_mod_cast le_max_right ⌈√(johnsonRhoMinus n D) / eta⌉₊ 3
    linarith only [this]
  have hgamma : 0 ≤ johnsonGamma n D eta := sub_nonneg.2 ha
  have hden : 0 < 3 * x ^ 3 := by positivity
  have hextra : 0 ≤ 3 * tB * johnsonGamma n D eta * rho := by positivity
  have hquot : 2 * tB ^ 5 / (3 * x ^ 3) ≤
      (2 * tB ^ 5 + 3 * tB * johnsonGamma n D eta * rho) / (3 * x ^ 3) := by
    exact (div_le_div_iff_of_pos_right hden).2 (le_add_of_nonneg_right hextra)
  unfold johnsonComparisonEstimate
  dsimp only [rho, x, tB]
  calc
    (2 * tB ^ 5 / (3 * x ^ 3)) * n ≤
        ((2 * tB ^ 5 + 3 * tB * johnsonGamma n D eta * rho) / (3 * x ^ 3)) * n := by
      exact mul_le_mul_of_nonneg_right hquot hn.le
    _ < ((2 * tB ^ 5 + 3 * tB * johnsonGamma n D eta * rho) / (3 * x ^ 3)) * n +
        tB / x := by
      exact lt_add_of_pos_right _ (div_pos htB hx)

/-- `johnsonComparisonEstimate` is positive when `1 ≤ D < n` and the agreement fraction is at most
`1`. -/
theorem johnsonComparisonEstimate_pos {n D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D < n)
    (ha : johnsonAgreement n D eta ≤ 1) :
    0 < johnsonComparisonEstimate n D eta := by
  let rho := johnsonRhoMinus n D
  let x := √rho
  let tB := johnsonComparisonShift n D eta
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrho : 0 < rho := johnsonRhoMinus_pos hD hDn
  have hx : 0 < x := Real.sqrt_pos.2 hrho
  have htB : 0 < tB := by
    unfold tB johnsonComparisonShift
    have hm : (3 : ℝ) ≤ johnsonComparisonMultiplicity n D eta := by
      exact_mod_cast le_max_right ⌈√(johnsonRhoMinus n D) / eta⌉₊ 3
    linarith only [hm]
  have hleading0 : 0 < (2 * tB ^ 5 / (3 * x ^ 3)) * n := by positivity
  exact lt_trans hleading0 (johnsonComparisonEstimate_leading_lt hD hDn ha)

/-- `johnsonExceptionCount / johnsonComparisonEstimate < 16/49` under `1 ≤ D ≤ n - 2`, `η > 0`,
agreement fraction at most `1`, and `(√ρ₋ + η) n ≤ A`. It combines
`johnsonExceptionCount_lt_closed` with `t ≤ t_B`, `t_B ≥ 7/2` and `√ρ₋ < 1`. -/
theorem johnsonExceptionCount_div_comparisonEstimate_lt {n D A : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) :
    johnsonExceptionCount n D A eta / johnsonComparisonEstimate n D eta < 16 / 49 := by
  let rho := johnsonRhoMinus n D
  let x := √rho
  let t := johnsonT n D eta
  let tB := johnsonComparisonShift n D eta
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrho : 0 < rho := johnsonRhoMinus_pos hD (by omega)
  have hx := johnsonSqrt_mem_Ioo (n := n) hD (by omega)
  have hx1 : x < 1 := by exact hx.2
  have hxne : x ≠ 0 := by
    dsimp only [x]
    exact hx.1.ne'
  have hx2 : x ^ 2 = rho := Real.sq_sqrt hrho.le
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) (johnsonT_ge_seven_halves n D eta)
  have htBLower : 7 / 2 ≤ tB := by
    unfold tB johnsonComparisonShift
    have hm : (3 : ℝ) ≤ johnsonComparisonMultiplicity n D eta := by
      exact_mod_cast le_max_right ⌈√(johnsonRhoMinus n D) / eta⌉₊ 3
    linarith only [hm]
  have htB : 0 < tB := lt_of_lt_of_le (by norm_num) htBLower
  have httB : t ≤ tB := johnsonT_le_comparisonShift n D heta
  have htCube : t ^ 3 ≤ tB ^ 3 := pow_le_pow_left₀ ht.le httB 3
  have hxtCube : x * t ^ 3 < tB ^ 3 := by
    calc
      x * t ^ 3 < 1 * t ^ 3 := by
        exact mul_lt_mul_of_pos_right hx1 (pow_pos ht 3)
      _ ≤ tB ^ 3 := by simpa using htCube
  have h49 : (49 : ℝ) ≤ 4 * tB ^ 2 := by
    have htBSquared : (7 / 2 : ℝ) ^ 2 ≤ tB ^ 2 :=
      (sq_le_sq₀ (by norm_num) htB.le).2 htBLower
    calc
      49 = 4 * ((7 / 2 : ℝ) ^ 2) := by norm_num
      _ ≤ 4 * tB ^ 2 := mul_le_mul_of_nonneg_left htBSquared (by norm_num)
  have hquintic : 49 * tB ^ 3 ≤ 4 * tB ^ 5 := by
    calc
      49 * tB ^ 3 ≤ 4 * tB ^ 2 * tB ^ 3 :=
        mul_le_mul_of_nonneg_right h49 (pow_nonneg htB.le 3)
      _ = 4 * tB ^ 5 := by ring
  have hkey : 49 * x * t ^ 3 < 4 * tB ^ 5 := by
    calc
      49 * x * t ^ 3 = 49 * (x * t ^ 3) := by ring
      _ < 49 * tB ^ 3 := mul_lt_mul_of_pos_left hxtCube (by norm_num)
      _ ≤ 4 * tB ^ 5 := hquintic
  have hnkey : 49 * (n : ℝ) * x * t ^ 3 < 4 * n * tB ^ 5 := by
    calc
      49 * (n : ℝ) * x * t ^ 3 = (n : ℝ) * (49 * x * t ^ 3) := by ring
      _ < (n : ℝ) * (4 * tB ^ 5) := mul_lt_mul_of_pos_left hkey hn
      _ = 4 * n * tB ^ 5 := by ring
  have hclosedCompare :
      (8 / 3 : ℝ) * n * t ^ 3 / rho <
        (16 / 49 : ℝ) * ((2 * tB ^ 5 / (3 * x ^ 3)) * n) := by
    rw [← hx2]
    calc
      (8 / 3 : ℝ) * n * t ^ 3 / x ^ 2 =
          ((8 / 3 : ℝ) * n * t ^ 3 * x) / x ^ 3 := by
        field_simp [hxne]
      _ < ((32 / 147 : ℝ) * n * tB ^ 5) / x ^ 3 := by
        apply (div_lt_div_iff_of_pos_right (pow_pos hx.1 3)).2
        calc
          (8 / 3 : ℝ) * n * t ^ 3 * x = (8 / 147) * (49 * n * x * t ^ 3) := by ring
          _ < (8 / 147) * (4 * n * tB ^ 5) := mul_lt_mul_of_pos_left hnkey (by norm_num)
          _ = (32 / 147 : ℝ) * n * tB ^ 5 := by ring
      _ = (16 / 49 : ℝ) * ((2 * tB ^ 5 / (3 * x ^ 3)) * n) := by
        field_simp [hxne]
        norm_num
  have hE := johnsonExceptionCount_lt_closed hD hDn heta hthreshold
  have hleading := johnsonComparisonEstimate_leading_lt hD (by omega) ha
  have hB : 0 < johnsonComparisonEstimate n D eta := johnsonComparisonEstimate_pos hD (by omega) ha
  apply (div_lt_iff₀ hB).2
  calc
    johnsonExceptionCount n D A eta < (8 / 3 : ℝ) * n * t ^ 3 / rho := hE
    _ < (16 / 49 : ℝ) * ((2 * tB ^ 5 / (3 * x ^ 3)) * n) := hclosedCompare
    _ < (16 / 49 : ℝ) * johnsonComparisonEstimate n D eta := by
      exact mul_lt_mul_of_pos_left hleading (by norm_num)

/-- `johnsonExceptionCount < johnsonComparisonEstimate` under the hypotheses of
`johnsonExceptionCount_div_comparisonEstimate_lt`. -/
theorem johnsonExceptionCount_lt_comparisonEstimate {n D A : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) :
    johnsonExceptionCount n D A eta < johnsonComparisonEstimate n D eta := by
  have hB : 0 < johnsonComparisonEstimate n D eta := johnsonComparisonEstimate_pos hD (by omega) ha
  calc
    johnsonExceptionCount n D A eta < (16 / 49 : ℝ) * johnsonComparisonEstimate n D eta :=
      (div_lt_iff₀ hB).mp
        (johnsonExceptionCount_div_comparisonEstimate_lt hD hDn heta ha hthreshold)
    _ < 1 * johnsonComparisonEstimate n D eta := by
      exact mul_lt_mul_of_pos_right (by norm_num) hB
    _ = johnsonComparisonEstimate n D eta := one_mul _

/-- `johnsonExceptionCount ≤ johnsonComparisonEstimate`, the non-strict form of
`johnsonExceptionCount_lt_comparisonEstimate`. -/
theorem johnsonExceptionCount_le_comparisonEstimate {n D A : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) :
    johnsonExceptionCount n D A eta ≤ johnsonComparisonEstimate n D eta :=
  (johnsonExceptionCount_lt_comparisonEstimate hD hDn heta ha hthreshold).le

end

end ReedSolomon.HiddenDerivative
