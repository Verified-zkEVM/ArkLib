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

The limiting source/rank ratio is
`Gamma(R,a,d) = (27/20) * R * (d+1) / (6*d)^(R/a)`.
Its logarithm isolates the derivative order from the fixed-rate coefficient
`c(R)=R*log(40/(9R))`. Every positive epsilon gives an eventual strict gate at
order `ceil(exp((c(R)+epsilon)/delta))`; this does not assert a fixed finite-loss margin.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative.RatePartition

/-- Limiting source-to-rank ratio for the derivative-order partition construction. -/
def rateGamma (rate agreement : ℝ) (order : ℕ) : ℝ :=
  (27 / 20 : ℝ) * rate * (order + 1) / (6 * (order : ℝ)) ^ (rate / agreement)

/-- The leading fixed-rate coefficient in the exponent of the derivative order. -/
def fixedRateCoefficient (rate : ℝ) : ℝ := rate * Real.log (40 / (9 * rate))

/-- The partition moment's factor `27/10` is divided by two by the triangular source area. -/
theorem moment_half_coefficient : (27 / 10 : ℝ) / 2 = 27 / 20 := by norm_num

/-- The rate ratio is positive at positive rate and derivative order. -/
theorem rateGamma_pos {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (horder : 0 < order) : 0 < rateGamma rate agreement order := by
  unfold rateGamma
  positivity

/-- Taking logarithms keeps the actual rate in the exponent of the denominator. -/
theorem log_rateGamma {rate agreement : ℝ} {order : ℕ}
    (hrate : 0 < rate) (horder : 0 < order) :
    Real.log (rateGamma rate agreement order) = Real.log (27 * rate / 20) +
      Real.log ((order : ℝ) + 1) - rate / agreement * Real.log (6 * (order : ℝ)) := by
  have hbase : (0 : ℝ) < 6 * order := by positivity
  have hfactor : (0 : ℝ) < 27 * rate / 20 := by positivity
  have hsuccessor : (0 : ℝ) < (order : ℝ) + 1 := by positivity
  unfold rateGamma
  rw [show (27 / 20 : ℝ) * rate * (order + 1) =
    (27 * rate / 20) * ((order : ℝ) + 1) by ring]
  rw [Real.log_div (mul_pos hfactor hsuccessor).ne' (Real.rpow_pos_of_pos hbase _).ne',
    Real.log_mul hfactor.ne' hsuccessor.ne', Real.log_rpow hbase]

/-- The two rate-dependent logarithmic constants multiply to six. -/
theorem complementary_rate_logs {rate : ℝ} (hrate : 0 < rate) :
    Real.log (40 / (9 * rate)) + Real.log (27 * rate / 20) = Real.log 6 := by
  rw [← Real.log_mul (by positivity : (40 / (9 * rate) : ℝ) ≠ 0)
    (by positivity : (27 * rate / 20 : ℝ) ≠ 0)]
  congr 1
  field_simp
  ring

/-- The exact fixed-rate identity separates the `delta*log d` term from the rate coefficient. -/
theorem fixed_rate_log_identity {rate gap : ℝ} {order : ℕ}
    (hrate : 0 < rate) (hgap : 0 < gap) (horder : 0 < order) :
    (rate + gap) * Real.log (rateGamma rate (rate + gap) order) =
      gap * Real.log order - fixedRateCoefficient rate + gap * Real.log (27 * rate / 20) +
        (rate + gap) * Real.log (1 + 1 / (order : ℝ)) := by
  have horderReal : (0 : ℝ) < order := by exact_mod_cast horder
  have hsum : rate + gap ≠ 0 := (add_pos hrate hgap).ne'
  have hsuccessor : Real.log ((order : ℝ) + 1) =
      Real.log order + Real.log (1 + 1 / (order : ℝ)) := by
    rw [← Real.log_mul horderReal.ne' (by positivity : (1 + 1 / (order : ℝ)) ≠ 0)]
    congr 1
    field_simp
  rw [log_rateGamma hrate horder, hsuccessor,
    Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) horderReal.ne']
  unfold fixedRateCoefficient
  have hconstants := complementary_rate_logs hrate
  rw [← hconstants]
  field_simp
  ring

/-- The leading coefficient is positive throughout the open rate interval. -/
theorem fixedRateCoefficient_pos {rate : ℝ} (hrate : 0 < rate) (hrateOne : rate < 1) :
    0 < fixedRateCoefficient rate := by
  apply mul_pos hrate
  apply Real.log_pos
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 9 * rate)).mpr
  linarith

/-- Every positive epsilon eventually gives the strict gate at the exact ceiling of the
fixed-rate exponential order. Multiplicity must still be chosen from this strict margin. -/
theorem exists_small_gap_rate_gate {rate epsilon : ℝ}
    (hrate : 0 < rate) (hrateOne : rate < 1) (hepsilon : 0 < epsilon) :
    ∃ gapBound : ℝ, 0 < gapBound ∧ ∀ gap : ℝ, 0 < gap → gap < gapBound →
      let order := ⌈Real.exp ((fixedRateCoefficient rate + epsilon) / gap)⌉₊
      rate + gap < 1 ∧ 500 ≤ order ∧ 1 < rateGamma rate (rate + gap) order := by
  let coefficient := fixedRateCoefficient rate + epsilon
  let logarithm := Real.log (27 * rate / 20)
  have hcoefficient : 0 < coefficient := add_pos (fixedRateCoefficient_pos hrate hrateOne) hepsilon
  let gapBound := min (1 - rate) (min (coefficient / 500) (epsilon / (|logarithm| + 1)))
  have hgapBound : 0 < gapBound := by dsimp [gapBound]; positivity
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
    have hidentity := fixed_rate_log_identity hrate hgap horder
    have hlogGamma : 0 < Real.log (rateGamma rate (rate + gap) order) := by
      dsimp only [coefficient] at hmain
      dsimp only [logarithm] at herror
      nlinarith
    exact (Real.log_pos_iff (rateGamma_pos hrate horder).le).mp hlogGamma

end ReedSolomon.HiddenDerivative.RatePartition
