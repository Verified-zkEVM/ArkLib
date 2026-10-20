/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Pratyush Mishra, Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Basic
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Rounded parameter estimates at a free derivative order

This file proves the inequalities between the rounded parameters of `Parameters/Basic.lean` that
the rectangular dimension bound of `Interpolation/Dimension.lean` consumes, for an arbitrary
derivative order `d`. It has three parts.

* Rounding facts about single parameters: `A = ⌈ε n⌉` and `K = ⌊(1 - θ) ε n⌋` against their real
  targets, and the jet-degree budget `B = ⌈m A / (K - 1)⌉` characterized by
  `B ≤ t ↔ m A ≤ t (K - 1)` when `K ≥ 2`.
* The three slack conditions of the rectangular bound at `H = ⌊θ m / 16⌋` and
  `C = ⌊(1 + 3θ/4) m⌋`: `H ≤ m`, `C + 2H ≤ B`, and `(K - 1)(C + 3H) < m A`. The last one holds
  because `(1 - θ)(1 + 15θ/16) ≤ 1` for `θ ≥ 0`; it fails for some `θ ∈ (-1/3, 0)`.
* Statements for large `d` at fixed `ε` and `θ`: the unrounded box width `θ m / 16` and
  `c d^(2θ / (5 + θ))`, for `c > 0`, tend to infinity. These are pointwise in `(ε, θ)`; they do not
  give an order `d` that works uniformly over rates.

## Main statements

* `agreementThreshold_le_iff`, `le_agreementThreshold`, `ambientDimension_lt_blockLength`,
  `le_ambientDimension_iff`: rounding of `A` and `K`.
* `interpolationDegreeBudget_le_iff`, with the consequences
  `multiplicity_mul_agreementThreshold_le_budget_mul_denominator` and
  `le_interpolationDegreeBudget_of_mul_denominator_le`.
* `boxFamily_weightedBudget_lt`, `interpolationBoxWidth_le_multiplicity`, and
  `freeGlobalDimensionSlacks`: the three slack conditions.
* `half_interpolationBoxWidthTarget_le_cast`: `θ m / 32 ≤ H` once `θ m / 16 ≥ 1`.
* `tendsto_interpolationBoxWidthTarget`, `tendsto_const_mul_rpow_rankSavingExponent`, and
  `eventually_freeOrderElementary`, with the threshold forms
  `exists_orderThreshold_for_boxWidth`, `exists_freeOrderRankThreshold`, and
  `exists_freeOrderElementaryThreshold`.
* `half_rate_le_ambientDimension_sub_one_div` and `freeOrder_rank_comparison`: the rounded rate
  `(K - 1) / n` is at least half of `(1 - θ) ε` once `K ≥ 3`.

Parts of this file are adapted, with permission, from Kai Zhe Zheng's `kz99/rs-ld-mca`
formalization.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26].
* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26]
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

open Filter

variable {ε θ : ℝ} {d n : ℕ}

/-! ### Rounding of single parameters -/

/-- `A ≤ t` exactly when the real target `ε n` is at most `t`. -/
theorem agreementThreshold_le_iff (ε : ℝ) (n t : ℕ) :
    agreementThreshold ε n ≤ t ↔ ε * (n : ℝ) ≤ (t : ℝ) :=
  Nat.ceil_le

/-- The real target `ε n` is at most `A`. -/
theorem le_agreementThreshold (ε : ℝ) (n : ℕ) :
    ε * (n : ℝ) ≤ agreementThreshold ε n :=
  Nat.le_ceil _

/-- A positive fraction of a nonempty block gives a positive agreement threshold. -/
theorem agreementThreshold_pos (hε : 0 < ε) (hn : 0 < n) : 0 < agreementThreshold ε n := by
  rw [agreementThreshold, Nat.ceil_pos]
  positivity

/-- The multiplicity `d³` is positive at positive order. -/
theorem multiplicity_pos (hd : 0 < d) : 0 < multiplicity d :=
  pow_pos hd 3

/-- The ambient dimension is below the block length when `(1 - θ) ε < 1` and the block is
nonempty. Both are needed: at `n = 0` both sides are `0`, and at `ε = 1`, `θ = 0` the dimension
is `n`. -/
theorem ambientDimension_lt_blockLength (h : (1 - θ) * ε < 1) (hn : 0 < n) :
    ambientDimension ε θ n < n := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ambientDimension, Nat.floor_lt' hn.ne']
  simpa using mul_lt_mul_of_pos_right h hnReal

/-- `k ≤ K` exactly when `k ≤ (1 - θ) ε n`, provided `(1 - θ) ε ≥ 0`. Without that, `k = 0`
satisfies the left side and not the right side when `n > 0`. -/
theorem le_ambientDimension_iff {k : ℕ} (h : 0 ≤ (1 - θ) * ε) :
    k ≤ ambientDimension ε θ n ↔ (k : ℝ) ≤ (1 - θ) * ε * (n : ℝ) := by
  rw [ambientDimension, Nat.le_floor_iff (mul_nonneg h (Nat.cast_nonneg n))]

/-- A positive ambient dimension forces `1 ≤ (1 - θ) ε n`. -/
theorem one_le_of_ambientDimension_pos (hK : 0 < ambientDimension ε θ n) :
    1 ≤ (1 - θ) * ε * (n : ℝ) :=
  Nat.floor_pos.mp hK

/-- For `ε ≥ 0`, a positive ambient dimension forces `θ < 1`: for `θ ≥ 1` the target
`(1 - θ) ε n` is at most `0`. -/
theorem lt_one_of_ambientDimension_pos (hε : 0 ≤ ε) (hK : 0 < ambientDimension ε θ n) :
    θ < 1 := by
  have h1 := one_le_of_ambientDimension_pos hK
  by_contra hθ
  have : (1 - θ) * (ε * (n : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith [not_lt.mp hθ])
      (mul_nonneg hε (Nat.cast_nonneg n))
  linarith [mul_assoc (1 - θ) ε (n : ℝ)]

/-- If some order is below the ambient dimension, the block is nonempty: at `n = 0` the ambient
dimension is `0`. -/
theorem blockLength_pos_of_order_lt_ambientDimension (hdK : d < ambientDimension ε θ n) :
    0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ambientDimension] at hdK
  · exact hn

/-- For `0 < d < K` the denominator `K - 1` of the jet-degree budget is positive. -/
theorem interpolationDenominator_pos (hd : 0 < d) (hdK : d < ambientDimension ε θ n) :
    0 < ambientDimension ε θ n - 1 := by
  omega

/-! ### The jet-degree budget -/

/-- The jet-degree budget is the least `t` with `m A ≤ t (K - 1)`. The hypothesis `K - 1 > 0` is
needed: at `K ≤ 1` the budget is `0` while `m A ≤ 0 · (K - 1)` fails whenever `m A > 0`. -/
theorem interpolationDegreeBudget_le_iff (hden : 0 < ambientDimension ε θ n - 1) {t : ℕ} :
    interpolationDegreeBudget d ε θ n ≤ t ↔
      multiplicity d * agreementThreshold ε n ≤ t * (ambientDimension ε θ n - 1) := by
  have hdenReal : (0 : ℝ) < ((ambientDimension ε θ n - 1 : ℕ) : ℝ) := by exact_mod_cast hden
  rw [interpolationDegreeBudget, Nat.ceil_le, div_le_iff₀ hdenReal, ← Nat.cast_mul,
    Nat.cast_le]

/-- Rounding `m A / (K - 1)` up gives `m A ≤ B (K - 1)`, when `K - 1 > 0`. -/
theorem multiplicity_mul_agreementThreshold_le_budget_mul_denominator
    (hden : 0 < ambientDimension ε θ n - 1) :
    multiplicity d * agreementThreshold ε n ≤
      interpolationDegreeBudget d ε θ n * (ambientDimension ε θ n - 1) :=
  (interpolationDegreeBudget_le_iff hden).mp le_rfl

/-- Every `t` with `t (K - 1) ≤ m A` is at most the jet-degree budget, when `K - 1 > 0`. The
hypothesis is needed: at `K - 1 = 0` every `t` satisfies `t (K - 1) ≤ m A`, and the budget is
`0`. -/
theorem le_interpolationDegreeBudget_of_mul_denominator_le
    (hden : 0 < ambientDimension ε θ n - 1) {t : ℕ}
    (ht : t * (ambientDimension ε θ n - 1) ≤ multiplicity d * agreementThreshold ε n) :
    t ≤ interpolationDegreeBudget d ε θ n := by
  by_contra hlt
  have hmul := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge hlt) hden
  have := multiplicity_mul_agreementThreshold_le_budget_mul_denominator (d := d) hden
  omega

/-- The jet-degree budget is positive for `ε > 0` and `0 < d < K`. -/
theorem interpolationDegreeBudget_pos (hε : 0 < ε) (hd : 0 < d)
    (hdK : d < ambientDimension ε θ n) :
    0 < interpolationDegreeBudget d ε θ n := by
  have hden := interpolationDenominator_pos hd hdK
  have hA := agreementThreshold_pos hε (blockLength_pos_of_order_lt_ambientDimension hdK)
  have hmA := Nat.mul_pos (multiplicity_pos hd) hA
  by_contra h
  have h0 : interpolationDegreeBudget d ε θ n ≤ 0 := by omega
  rw [interpolationDegreeBudget_le_iff hden, zero_mul] at h0
  omega

/-! ### The slack conditions of the rectangular bound -/

/-- `C ≤ (1 + 3θ/4) m` for `θ ≥ 0`. -/
theorem higherJetDegreeBudget_cast_le (hθ : 0 ≤ θ) :
    (higherJetDegreeBudget θ d : ℝ) ≤ (1 + 3 * θ / 4) * (multiplicity d : ℝ) :=
  Nat.floor_le (by positivity)

/-- `H ≤ θ m / 16` for `θ ≥ 0`. For `θ < 0` it fails when `m > 0`, since then `H = 0`. -/
theorem interpolationBoxWidth_cast_le (hθ : 0 ≤ θ) :
    (interpolationBoxWidth θ d : ℝ) ≤ θ * (multiplicity d : ℝ) / 16 :=
  Nat.floor_le (by positivity)

/-- `C + 3H ≤ (1 + 15θ/16) m` for `θ ≥ 0`. -/
theorem higherJetDegreeBudget_add_three_boxWidth_cast_le (hθ : 0 ≤ θ) :
    ((higherJetDegreeBudget θ d + 3 * interpolationBoxWidth θ d : ℕ) : ℝ) ≤
      (1 + 15 * θ / 16) * (multiplicity d : ℝ) := by
  push_cast
  have hC := higherJetDegreeBudget_cast_le (d := d) hθ
  have hH := interpolationBoxWidth_cast_le (d := d) hθ
  linarith

/-- The weighted slack of the rectangular bound: `(K - 1)(C + 3H) < m A`. It needs `ε > 0`,
`d > 0`, and `n > 0` so that `m A > 0`, and `θ ≥ 0` so that `(1 - θ)(1 + 15θ/16) ≤ 1`; for
`θ ∈ (-1/3, 0)` this product exceeds `1`, and the tests give a failure at `θ = -1/6`. No upper
bound on `θ` is needed: for `θ ≥ 1` the ambient dimension is `0`. -/
theorem boxFamily_weightedBudget_lt (hε : 0 < ε) (hθ : 0 ≤ θ) (hd : 0 < d) (hn : 0 < n) :
    (ambientDimension ε θ n - 1) *
        (higherJetDegreeBudget θ d + 3 * interpolationBoxWidth θ d) <
      multiplicity d * agreementThreshold ε n := by
  have hmA := Nat.mul_pos (multiplicity_pos hd) (agreementThreshold_pos hε hn)
  rcases Nat.eq_zero_or_pos (ambientDimension ε θ n) with hK | hK
  · rw [hK, Nat.zero_sub, zero_mul]
    exact hmA
  have hx1 := one_le_of_ambientDimension_pos hK
  have hKx : (ambientDimension ε θ n : ℝ) ≤ (1 - θ) * ε * (n : ℝ) :=
    Nat.floor_le (by linarith)
  have hm : (0 : ℝ) < multiplicity d := by exact_mod_cast multiplicity_pos hd
  have hs := higherJetDegreeBudget_add_three_boxWidth_cast_le (d := d) hθ
  have hA := le_agreementThreshold ε n
  have hfactor : (1 - θ) * (1 + 15 * θ / 16) ≤ 1 := by nlinarith
  have hεn : 0 < ε * (n : ℝ) := mul_pos hε (by exact_mod_cast hn)
  have hreal :
      ((ambientDimension ε θ n : ℝ) - 1) *
          ((higherJetDegreeBudget θ d + 3 * interpolationBoxWidth θ d : ℕ) : ℝ) <
        (multiplicity d : ℝ) * (agreementThreshold ε n : ℝ) :=
    calc ((ambientDimension ε θ n : ℝ) - 1) *
          ((higherJetDegreeBudget θ d + 3 * interpolationBoxWidth θ d : ℕ) : ℝ)
        ≤ ((1 - θ) * ε * (n : ℝ) - 1) * ((1 + 15 * θ / 16) * (multiplicity d : ℝ)) :=
          mul_le_mul (by linarith) hs (Nat.cast_nonneg _) (by linarith)
      _ < (1 - θ) * ε * (n : ℝ) * ((1 + 15 * θ / 16) * (multiplicity d : ℝ)) := by
          have : 0 < (1 + 15 * θ / 16) * (multiplicity d : ℝ) := by positivity
          linarith
      _ = ((1 - θ) * (1 + 15 * θ / 16)) * ((multiplicity d : ℝ) * (ε * (n : ℝ))) := by ring
      _ ≤ 1 * ((multiplicity d : ℝ) * (ε * (n : ℝ))) :=
          mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ ≤ (multiplicity d : ℝ) * (agreementThreshold ε n : ℝ) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left hA hm.le
  have hcast : ((ambientDimension ε θ n - 1 : ℕ) : ℝ) = (ambientDimension ε θ n : ℝ) - 1 := by
    rw [Nat.cast_sub hK, Nat.cast_one]
  rw [← hcast] at hreal
  exact_mod_cast hreal

/-- `H ≤ m` when `θ ≤ 16`. For `θ < 0` the width is `0`. The bound `θ ≤ 16` is needed: at
`θ = 32`, `d = 1` the width is `2` and the multiplicity is `1`. -/
theorem interpolationBoxWidth_le_multiplicity (hθ : θ ≤ 16) :
    interpolationBoxWidth θ d ≤ multiplicity d := by
  apply Nat.floor_le_of_le
  have hm : (0 : ℝ) ≤ multiplicity d := Nat.cast_nonneg _
  nlinarith

/-- The three slack conditions consumed by the rectangular dimension bound
`finrank_interpolationSpace_lowerBound`: `H ≤ m`, `C + 2H ≤ B`, and `(K - 1)(C + 3H) ≤ m A`.
The hypotheses are `ε > 0`, `θ ≥ 0`, and `0 < d < K`; the latter gives `n > 0` and `θ < 1`. -/
theorem freeGlobalDimensionSlacks (hε : 0 < ε) (hθ : 0 ≤ θ) (hd : 0 < d)
    (hdK : d < ambientDimension ε θ n) :
    interpolationBoxWidth θ d ≤ multiplicity d ∧
      higherJetDegreeBudget θ d + 2 * interpolationBoxWidth θ d ≤
        interpolationDegreeBudget d ε θ n ∧
      (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudget θ d + 3 * interpolationBoxWidth θ d) ≤
        multiplicity d * agreementThreshold ε n := by
  have hn := blockLength_pos_of_order_lt_ambientDimension hdK
  have hθ1 := lt_one_of_ambientDimension_pos hε.le (by omega : 0 < ambientDimension ε θ n)
  have hweighted := boxFamily_weightedBudget_lt hε hθ hd hn
  refine ⟨interpolationBoxWidth_le_multiplicity (by linarith), ?_, hweighted.le⟩
  apply le_interpolationDegreeBudget_of_mul_denominator_le (interpolationDenominator_pos hd hdK)
  calc (higherJetDegreeBudget θ d + 2 * interpolationBoxWidth θ d) *
          (ambientDimension ε θ n - 1)
      ≤ (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudget θ d + 3 * interpolationBoxWidth θ d) := by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_left _ (by omega)
    _ ≤ multiplicity d * agreementThreshold ε n := hweighted.le

/-- Once the unrounded width `θ m / 16` is at least `1`, rounding down loses less than a factor
of two: `θ m / 32 ≤ H`. The hypothesis is needed: at `θ m / 16 = 1/2` the width is `0`. -/
theorem half_interpolationBoxWidthTarget_le_cast
    (h : 1 ≤ θ * (multiplicity d : ℝ) / 16) :
    θ * (multiplicity d : ℝ) / 32 ≤ (interpolationBoxWidth θ d : ℝ) := by
  have hfloor := Nat.div_two_lt_floor h
  rw [interpolationBoxWidth]
  linarith

/-! ### Large orders -/

/-- For `θ > 0` the unrounded box width `θ d³ / 16` tends to infinity with `d`. -/
theorem tendsto_interpolationBoxWidthTarget (hθ : 0 < θ) :
    Tendsto (fun d : ℕ => θ * (multiplicity d : ℝ) / 16) atTop atTop := by
  have hcube : Tendsto (fun d : ℕ => (d : ℝ) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  simp only [multiplicity, Nat.cast_pow]
  exact (hcube.const_mul_atTop hθ).atTop_div_const (by norm_num)

/-- For `θ > 0` and every real `c`, all large orders have `c ≤ θ m / 16`. -/
theorem exists_orderThreshold_for_boxWidth (hθ : 0 < θ) (c : ℝ) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → c ≤ θ * (multiplicity d : ℝ) / 16 :=
  eventually_atTop.mp ((tendsto_interpolationBoxWidthTarget hθ).eventually_ge_atTop c)

/-- The exponent `2θ / (5 + θ)` of `d` saved by the rank comparison. -/
def rankSavingExponent (θ : ℝ) : ℝ :=
  2 * θ / (5 + θ)

/-- The saved exponent is positive for `θ > 0`. -/
theorem rankSavingExponent_pos (hθ : 0 < θ) : 0 < rankSavingExponent θ := by
  unfold rankSavingExponent
  positivity

/-- For `c > 0` and `θ > 0`, `c d^(2θ / (5 + θ))` tends to infinity with `d`. -/
theorem tendsto_const_mul_rpow_rankSavingExponent {c : ℝ} (hc : 0 < c) (hθ : 0 < θ) :
    Tendsto (fun d : ℕ => c * (d : ℝ) ^ rankSavingExponent θ) atTop atTop :=
  ((tendsto_rpow_atTop (rankSavingExponent_pos hθ)).comp
    tendsto_natCast_atTop_atTop).const_mul_atTop hc

/-- At fixed `ε > 0` and `0 < θ < 1`, all large orders satisfy the scalar rank comparison
`1 < (θ³ / 2¹⁸) ((1 - θ) ε / 2) d^(2θ / (5 + θ))`. The hypotheses make the coefficient positive.
This is pointwise in `(ε, θ)`. -/
theorem eventually_freeOrderRankComparison (hε : 0 < ε) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∀ᶠ d : ℕ in atTop,
      1 < (θ ^ 3 / 262144) * ((1 - θ) * ε / 2) * (d : ℝ) ^ rankSavingExponent θ := by
  have hθ1' : 0 < 1 - θ := by linarith
  exact (tendsto_const_mul_rpow_rankSavingExponent (by positivity) hθ).eventually_gt_atTop 1

/-- The threshold form of `eventually_freeOrderRankComparison`. -/
theorem exists_freeOrderRankThreshold (hε : 0 < ε) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      1 < (θ ^ 3 / 262144) * ((1 - θ) * ε / 2) * (d : ℝ) ^ rankSavingExponent θ :=
  eventually_atTop.mp (eventually_freeOrderRankComparison hε hθ hθ1)

/-- At fixed `ε > 0` and `0 < θ < 1`, all large orders satisfy `d ≥ 2`, `θ m / 16 ≥ 2`, and the
scalar rank comparison. The shell-count condition on `d` is not included here. -/
theorem eventually_freeOrderElementary (hε : 0 < ε) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∀ᶠ d : ℕ in atTop,
      2 ≤ d ∧ 2 ≤ θ * (multiplicity d : ℝ) / 16 ∧
        1 < (θ ^ 3 / 262144) * ((1 - θ) * ε / 2) * (d : ℝ) ^ rankSavingExponent θ :=
  (eventually_ge_atTop 2).and
    (((tendsto_interpolationBoxWidthTarget hθ).eventually_ge_atTop 2).and
      (eventually_freeOrderRankComparison hε hθ hθ1))

/-- The threshold form of `eventually_freeOrderElementary`. -/
theorem exists_freeOrderElementaryThreshold (hε : 0 < ε) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      2 ≤ d ∧ 2 ≤ θ * (multiplicity d : ℝ) / 16 ∧
        1 < (θ ^ 3 / 262144) * ((1 - θ) * ε / 2) * (d : ℝ) ^ rankSavingExponent θ :=
  eventually_atTop.mp (eventually_freeOrderElementary hε hθ hθ1)

/-! ### The rounded rate -/

/-- Once `K ≥ 3`, the rounded rate `(K - 1) / n` is at least half the unrounded rate
`(1 - θ) ε`, because `(1 - θ) ε n < K + 1 ≤ 2 (K - 1)`. The hypothesis is needed: at `K = 2`,
`(1 - θ) ε n` can be close to `3`, and the tests give a failure at `(1 - θ) ε n = 29/10`. -/
theorem half_rate_le_ambientDimension_sub_one_div (hK : 3 ≤ ambientDimension ε θ n) :
    (1 - θ) * ε / 2 ≤ ((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ) := by
  have hn : 0 < n :=
    blockLength_pos_of_order_lt_ambientDimension (ε := ε) (θ := θ) (d := 0) (by omega)
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hnReal]
  have hround : (1 - θ) * ε * (n : ℝ) < (ambientDimension ε θ n : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [Nat.cast_sub (by omega : 1 ≤ ambientDimension ε θ n), Nat.cast_one]
  have hK' : (3 : ℝ) ≤ ambientDimension ε θ n := by exact_mod_cast hK
  nlinarith

/-- The scalar rank comparison at the unrounded rate `(1 - θ) ε` implies it at the rounded rate
`(K - 1) / n`, for `θ ≥ 0` and `K ≥ 3`. -/
theorem freeOrder_rank_comparison (hθ : 0 ≤ θ) (hK : 3 ≤ ambientDimension ε θ n)
    (hlarge : 1 < (θ ^ 3 / 262144) * ((1 - θ) * ε / 2) * (d : ℝ) ^ rankSavingExponent θ) :
    1 < (θ ^ 3 / 262144) * (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
      (d : ℝ) ^ rankSavingExponent θ := by
  have hratio := half_rate_le_ambientDimension_sub_one_div hK
  have hpow : 0 ≤ (d : ℝ) ^ rankSavingExponent θ := Real.rpow_nonneg (Nat.cast_nonneg d) _
  calc 1 < (θ ^ 3 / 262144) * ((1 - θ) * ε / 2) * (d : ℝ) ^ rankSavingExponent θ := hlarge
    _ ≤ (θ ^ 3 / 262144) * (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (d : ℝ) ^ rankSavingExponent θ := by gcongr

end

end ReedSolomon.HiddenDerivative
