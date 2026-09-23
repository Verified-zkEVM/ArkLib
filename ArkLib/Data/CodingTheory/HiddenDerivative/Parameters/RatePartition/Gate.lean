/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The rate-dependent partition gate

The derivative-order partition construction compares a source count with a local rank. In the
limit of large length, their ratio at code rate `R`, agreement fraction `a` and derivative order
`d` is

```text
Γ(R, a, d) = (27/20) · R · (d + 1) / (6d)^(R/a).
```

The construction needs `1 < Γ`. Writing `a = R + δ` and taking logarithms gives the exact identity

```text
(R + δ) log Γ = δ log d - c(R) + δ log(27R/20) + (R + δ) log(1 + 1/d),
c(R) = R log(40 / (9R)),
```

so the derivative order enters only through `δ log d`, and the fixed-rate coefficient `c(R)` is
the price to be paid. For every `ε > 0` and every small enough gap `δ`, the order
`d = ⌈exp((c(R) + ε) / δ)⌉₊` makes `Γ > 1`. The margin `Γ - 1` is not bounded below
uniformly in `δ`; choosing the multiplicity from this strict margin is left to the consumer.

## Main statements

* `rateGamma_pos`, `log_rateGamma`: positivity of `Γ` and its logarithm.
* `complementary_rate_logs`: `log(40/(9R)) + log(27R/20) = log 6`.
* `fixed_rate_log_identity`: the displayed identity for `(R + δ) log Γ`.
* `fixedRateCoefficient_pos`: `0 < c(R)` for `0 < R < 40/9`.
* `exists_small_gap_rate_gate`: the eventual strict gate `1 < Γ(R, R + δ, d)` with `500 ≤ d`.
* `rateGamma_eq_exponential`, `rateGamma_factorization`: equivalent forms of the limiting ratio.
* `rateGamma_ge_one_add_inv_of_factor_six`, `rateGamma_gt_one_of_factor_six`: the factor-six
  threshold and its strict consequence.
* `fixedRatePartitionOrder`, `fixedRatePartitionOrder_ge_500`, `fixedRatePartition_cutoff_eq`:
  the fixed-rate order and its cutoff identity.
* `fixedRateGamma_gt_one`: the strict gate at agreement `R + δ`.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.RatePartition

/-- The limiting source-to-rank ratio `Γ(R, a, d) = (27/20) R (d + 1) / (6d)^(R/a)` of the
derivative-order partition construction at code rate `R`, agreement fraction `a` and derivative
order `d`. At `d = 0` the denominator is `0^(R/a)`, which is `0` when `R/a ≠ 0`, so `Γ = 0`. -/
def rateGamma (rate agreement : ℝ) (order : ℕ) : ℝ :=
  (27 / 20 : ℝ) * rate * (order + 1) / (6 * (order : ℝ)) ^ (rate / agreement)

/-- The fixed-rate coefficient `c(R) = R log(40 / (9R))`. The derivative order has to be at
least `exp((c(R) + ε) / δ)` for the gate to hold at gap `δ`; see `fixed_rate_log_identity`. -/
def fixedRateCoefficient (rate : ℝ) : ℝ := rate * Real.log (40 / (9 * rate))

/-- The partition moment's factor `27/10` halved by the triangular source area gives the
constant `27/20` in `rateGamma`. -/
theorem moment_half_coefficient : (27 / 10 : ℝ) / 2 = 27 / 20 := by norm_num

/-- `Γ(R, a, d) > 0` for `R > 0` and `d > 0`. Both are needed: `Γ` has the sign of `R`, and
`Γ(R, a, 0) = 0` whenever `R/a ≠ 0`. -/
theorem rateGamma_pos {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (horder : 0 < order) : 0 < rateGamma rate agreement order := by
  unfold rateGamma
  positivity

/-- The limiting ratio written as an exponential for positive order. -/
theorem rateGamma_eq_exponential {rate agreement : ℝ} {order : ℕ}
    (horder : 0 < order) :
    rateGamma rate agreement order =
      (27 / 20 : ℝ) * rate * (order + 1) *
        Real.exp (-(rate / agreement * Real.log (6 * (order : ℝ)))) := by
  have hbase : (0 : ℝ) < 6 * order := by positivity
  unfold rateGamma
  rw [Real.rpow_def_of_pos hbase, div_eq_mul_inv, ← Real.exp_neg]
  ring_nf

/-- `log Γ(R, a, d) = log(27R/20) + log(d + 1) - (R/a) log(6d)` for `R ≠ 0` and `d > 0`. The
hypotheses make every factor nonzero; `a` is arbitrary. -/
theorem log_rateGamma {rate agreement : ℝ} {order : ℕ}
    (hrate : rate ≠ 0) (horder : 0 < order) :
    Real.log (rateGamma rate agreement order) = Real.log (27 * rate / 20) +
      Real.log ((order : ℝ) + 1) - rate / agreement * Real.log (6 * (order : ℝ)) := by
  have hbase : (0 : ℝ) < 6 * order := by positivity
  have hfactor : (27 * rate / 20 : ℝ) ≠ 0 := by positivity
  have hsuccessor : (0 : ℝ) < (order : ℝ) + 1 := by positivity
  unfold rateGamma
  rw [show (27 / 20 : ℝ) * rate * (order + 1) =
    (27 * rate / 20) * ((order : ℝ) + 1) by ring]
  rw [Real.log_div (mul_ne_zero hfactor hsuccessor.ne') (Real.rpow_pos_of_pos hbase _).ne',
    Real.log_mul hfactor hsuccessor.ne', Real.log_rpow hbase]

/-- `log(40/(9R)) + log(27R/20) = log 6` for `R ≠ 0`, because the two arguments multiply to `6`.
At `R = 0` both logarithms are `0`. -/
theorem complementary_rate_logs {rate : ℝ} (hrate : rate ≠ 0) :
    Real.log (40 / (9 * rate)) + Real.log (27 * rate / 20) = Real.log 6 := by
  rw [← Real.log_mul (by positivity : (40 / (9 * rate) : ℝ) ≠ 0)
    (by positivity : (27 * rate / 20 : ℝ) ≠ 0)]
  congr 1
  field_simp
  ring

/-- The exact identity
`(R + δ) log Γ(R, R + δ, d) = δ log d - c(R) + δ log(27R/20) + (R + δ) log(1 + 1/d)`.
It separates the term `δ log d`, which grows with the order, from the fixed-rate coefficient
`c(R)`; the last two terms are small for small `δ` and large `d`. The hypothesis `R + δ ≠ 0`
is needed because the left side multiplies `R / (R + δ)` back by `R + δ`; `R ≠ 0` and `d > 0`
are needed for the logarithms to split. -/
theorem fixed_rate_log_identity {rate gap : ℝ} {order : ℕ}
    (hrate : rate ≠ 0) (hsum : rate + gap ≠ 0) (horder : 0 < order) :
    (rate + gap) * Real.log (rateGamma rate (rate + gap) order) =
      gap * Real.log order - fixedRateCoefficient rate + gap * Real.log (27 * rate / 20) +
        (rate + gap) * Real.log (1 + 1 / (order : ℝ)) := by
  have horderReal : (0 : ℝ) < order := by exact_mod_cast horder
  have hsuccessor : Real.log ((order : ℝ) + 1) =
      Real.log order + Real.log (1 + 1 / (order : ℝ)) := by
    rw [← Real.log_mul horderReal.ne' (by positivity : (1 + 1 / (order : ℝ)) ≠ 0)]
    congr 1
    field_simp
  rw [log_rateGamma hrate horder, hsuccessor,
    Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) horderReal.ne']
  unfold fixedRateCoefficient
  rw [← complementary_rate_logs hrate]
  field_simp
  ring

/-- `0 < c(R)` for `0 < R < 40/9`. The upper bound is sharp: `c(40/9) = 0`, and `c(R) < 0` beyond
it. Every code rate `R < 1` is in range. -/
theorem fixedRateCoefficient_pos {rate : ℝ} (hrate : 0 < rate) (hrateBound : rate < 40 / 9) :
    0 < fixedRateCoefficient rate := by
  apply mul_pos hrate
  apply Real.log_pos
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 9 * rate)).mpr
  linarith

/-- The exact factorization
`Γ(R, a, d) = (9R/40) (6d)^((a-R)/a) (1 + 1/d)` for positive `R`, `a` and `d`. -/
theorem rateGamma_factorization {rate agreement : ℝ} {order : ℕ}
    (hagreement : 0 < agreement) (horder : 0 < order) :
    rateGamma rate agreement order =
      (9 * rate / 40) * (6 * (order : ℝ)) ^ ((agreement - rate) / agreement) *
        (1 + 1 / (order : ℝ)) := by
  have horderReal : (0 : ℝ) < order := by exact_mod_cast horder
  have hbase : (0 : ℝ) < 6 * order := by positivity
  rw [rateGamma, show rate / agreement = 1 - (agreement - rate) / agreement by
    field_simp; ring]
  rw [Real.rpow_sub hbase, Real.rpow_one]
  field_simp [hbase.ne', horderReal.ne']
  ring

/-- A factor-six order makes the main factor at least one, retaining the exact successor factor
in `rateGamma`. -/
theorem rateGamma_ge_one_add_inv_of_factor_six {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hgap : rate < agreement) (horder : 0 < order)
    (hbound : (1 / 6 : ℝ) * (40 / (9 * rate)) ^ (agreement / (agreement - rate)) ≤ order) :
    1 + 1 / (order : ℝ) ≤ rateGamma rate agreement order := by
  have hagreement : 0 < agreement := hrate.trans hgap
  have hgap' : 0 < agreement - rate := sub_pos.mpr hgap
  have hexponent : 0 < (agreement - rate) / agreement := by positivity
  have hinverse : agreement / (agreement - rate) * ((agreement - rate) / agreement) = 1 :=
    by field_simp
  have hbase : 40 / (9 * rate) ≤ (6 * (order : ℝ)) ^ ((agreement - rate) / agreement) := by
    have hscaled : (40 / (9 * rate)) ^ (agreement / (agreement - rate)) ≤
        (6 * (order : ℝ)) := by
      nlinarith
    have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤
      (40 / (9 * rate)) ^ (agreement / (agreement - rate))) hscaled hexponent.le
    rw [← Real.rpow_mul (by positivity : 0 ≤ 40 / (9 * rate)), hinverse,
      Real.rpow_one] at hp
    exact hp
  rw [rateGamma_factorization hagreement horder]
  have hfactor : (9 * rate / 40) * (40 / (9 * rate)) = 1 := by field_simp
  have hmain : 1 ≤ (9 * rate / 40) *
      (6 * (order : ℝ)) ^ ((agreement - rate) / agreement) := by
    rw [← hfactor]
    exact mul_le_mul_of_nonneg_left hbase (by positivity)
  calc
    1 + 1 / (order : ℝ) = 1 * (1 + 1 / (order : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hmain (by positivity)

/-- The retained successor factor makes the factor-six limiting gate strict. -/
theorem rateGamma_gt_one_of_factor_six {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hgap : rate < agreement) (horder : 0 < order)
    (hbound : (1 / 6 : ℝ) * (40 / (9 * rate)) ^ (agreement / (agreement - rate)) ≤ order) :
    1 < rateGamma rate agreement order := by
  have horderReal : (0 : ℝ) < order := by exact_mod_cast horder
  exact (lt_add_of_pos_right 1 (one_div_pos.mpr horderReal)).trans_le
    (rateGamma_ge_one_add_inv_of_factor_six hrate hgap horder hbound)

/-- The derivative order
`⌈max(500, (20/(27R)) exp(R log(40/(9R))/δ))⌉₊` selected for a fixed rate
`R` and gap `δ`. -/
def fixedRatePartitionOrder (rate gap : ℝ) : ℕ :=
  ⌈max 500 ((20 / (27 * rate)) * Real.exp (rate * Real.log (40 / (9 * rate)) / gap))⌉₊

/-- The fixed-rate order is at least `500`. -/
theorem fixedRatePartitionOrder_ge_500 (rate gap : ℝ) :
    500 ≤ fixedRatePartitionOrder rate gap := by
  exact_mod_cast (le_max_left (500 : ℝ) _ |>.trans (Nat.le_ceil _))

/-- The exponential cutoff is the factor-six threshold at agreement `R + δ`. -/
theorem fixedRatePartition_cutoff_eq {rate gap : ℝ} (hrate : 0 < rate) (hgap : 0 < gap) :
    (1 / 6 : ℝ) * (40 / (9 * rate)) ^ ((rate + gap) / gap) =
      (20 / (27 * rate)) * Real.exp (rate * Real.log (40 / (9 * rate)) / gap) := by
  have hC : 0 < 40 / (9 * rate) := by positivity
  rw [show (rate + gap) / gap = 1 + rate / gap by field_simp; ring]
  rw [Real.rpow_add hC, Real.rpow_one, Real.rpow_def_of_pos hC]
  field_simp
  ring

/-- The fixed-rate order satisfies the strict limiting gate at agreement `R + δ`. -/
theorem fixedRateGamma_gt_one {rate gap : ℝ} (hrate : 0 < rate) (hgap : 0 < gap) :
    1 < rateGamma rate (rate + gap) (fixedRatePartitionOrder rate gap) := by
  have horder500 := fixedRatePartitionOrder_ge_500 rate gap
  have horder : 0 < fixedRatePartitionOrder rate gap := by omega
  apply rateGamma_gt_one_of_factor_six hrate (by linarith) horder
  rw [show rate + gap - rate = gap by ring]
  rw [fixedRatePartition_cutoff_eq hrate hgap]
  exact (le_max_right (500 : ℝ) _).trans (Nat.le_ceil _)

/-- The eventual strict gate. For a code rate `0 < R < 1` and any `ε > 0` there is a bound `δ₀`
such that every gap `0 < δ < δ₀` satisfies `R + δ < 1`, and the order
`d = ⌈exp((c(R) + ε) / δ)⌉₊` satisfies `500 ≤ d` and `1 < Γ(R, R + δ, d)`.

The bound `R < 1` is needed for the conclusion `R + δ < 1`. The margin `Γ - 1` is only strict,
not uniform in `δ`; a multiplicity has to be chosen from it separately. -/
theorem exists_small_gap_rate_gate {rate epsilon : ℝ}
    (hrate : 0 < rate) (hrateOne : rate < 1) (hepsilon : 0 < epsilon) :
    ∃ gapBound : ℝ, 0 < gapBound ∧ ∀ gap : ℝ, 0 < gap → gap < gapBound →
      let order := ⌈Real.exp ((fixedRateCoefficient rate + epsilon) / gap)⌉₊
      rate + gap < 1 ∧ 500 ≤ order ∧ 1 < rateGamma rate (rate + gap) order := by
  let coefficient := fixedRateCoefficient rate + epsilon
  let logarithm := Real.log (27 * rate / 20)
  have hcoefficient : 0 < coefficient :=
    add_pos (fixedRateCoefficient_pos hrate (by linarith)) hepsilon
  let gapBound := min (1 - rate) (min (coefficient / 500) (epsilon / (|logarithm| + 1)))
  have hgapBound : 0 < gapBound := by
    have : 0 < 1 - rate := by linarith
    dsimp [gapBound]; positivity
  refine ⟨gapBound, hgapBound, ?_⟩
  intro gap hgap hsmall
  have hrateGap : gap < 1 - rate := hsmall.trans_le (min_le_left _ _)
  have hsmall' : gap < min (coefficient / 500) (epsilon / (|logarithm| + 1)) :=
    hsmall.trans_le (min_le_right _ _)
  have horderGap : gap < coefficient / 500 := hsmall'.trans_le (min_le_left _ _)
  have herrorGap : gap < epsilon / (|logarithm| + 1) :=
    hsmall'.trans_le (min_le_right _ _)
  let order := ⌈Real.exp (coefficient / gap)⌉₊
  have horderReal : (500 : ℝ) < order := by
    have hratio : (500 : ℝ) < coefficient / gap := by
      apply (lt_div_iff₀ hgap).mpr
      linarith [(lt_div_iff₀ (by norm_num : (0 : ℝ) < 500)).mp horderGap]
    have hexponential := Real.add_one_le_exp (coefficient / gap)
    have hceil := Nat.le_ceil (Real.exp (coefficient / gap))
    change (500 : ℝ) < ⌈Real.exp (coefficient / gap)⌉₊
    linarith
  have horder : 0 < order :=
    Nat.cast_pos.mp (lt_trans (by norm_num : (0 : ℝ) < 500) horderReal)
  refine ⟨by linarith, ?_, ?_⟩
  · exact (by exact_mod_cast horderReal : 500 < order).le
  · have hlogOrder : coefficient / gap ≤ Real.log order := by
      have := Real.log_le_log (Real.exp_pos (coefficient / gap))
        (Nat.le_ceil (Real.exp (coefficient / gap)))
      simpa only [Real.log_exp] using this
    have hmain : coefficient ≤ gap * Real.log order := by
      have := (div_le_iff₀ hgap).mp hlogOrder
      nlinarith
    have herror : 0 < epsilon + gap * logarithm := by
      have hbound := (lt_div_iff₀ (by positivity : (0 : ℝ) < |logarithm| + 1)).mp herrorGap
      have hlower := mul_le_mul_of_nonneg_left (neg_abs_le logarithm) hgap.le
      nlinarith
    have hcorrection : 0 ≤ (rate + gap) * Real.log (1 + 1 / (order : ℝ)) := by
      apply mul_nonneg (add_pos hrate hgap).le
      exact Real.log_nonneg (le_add_of_nonneg_right (by positivity))
    have hidentity := fixed_rate_log_identity hrate.ne' (add_pos hrate hgap).ne' horder
    have hlogGamma : 0 < Real.log (rateGamma rate (rate + gap) order) := by
      dsimp only [coefficient] at hmain
      dsimp only [logarithm] at herror
      nlinarith
    exact (Real.log_pos_iff (rateGamma_pos hrate horder).le).mp hlogGamma

end ReedSolomon.HiddenDerivative.RatePartition
