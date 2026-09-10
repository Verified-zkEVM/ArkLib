/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Automatic finite parameters for first-order interpolation

This file implements the finite first-order interpolation recipe above the clean rate curve.
The inputs are the physical rate `rho` and requested agreement fraction `a`; every constructed
parameter depends only on this pair.

Write `a₁(rho)` for `automaticFirstOrderThreshold rho`. The recipe uses

* `a₀ = min a ((1 + a₁(rho)) / 2)` to retain the requested agreement guarantee while staying
  uniformly away from agreement one;
* `beta = 3 * (1 - a₀) / (2 * (2 - rho))`, the derivative-degree proportion that optimizes the
  limiting source-minus-rank bracket;
* `S`, the resulting positive normalized surplus;
* `m = ceil(4 / S)`, which makes `m * S ≥ 4` and pays the full `3 * m ^ 2` rounding loss;
* `M = floor(beta * m)`, the cap on the exponent of the hidden derivative variable `Y₁`;
* `mu = ceil(m * a₀ / rho)`, the total-degree cap in the jet variables `Y₀, Y₁`; and
* `h = max 1 (floor(r * mu / (N₀ - r)))`, the symbolic challenge height, where `N₀` is the
  source count and `r` is the exact certified local-rank budget.

The file proves that the normalized implementation of `M` equals the displayed raw floor, that
the finite source-minus-rank surplus remains positive after rounding, and that `h` bounds every
scaled kernel quotient. The coding-theoretic certificate and characteristic transfer remain in
their owner modules.
-/

@[expose] public section

open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

noncomputable section

set_option autoImplicit false

/-! ## Continuous rate and surplus parameters -/

/-- The clean first-order agreement threshold
`a₁(rho) = (3rho + 2 * sqrt(rho(5-rho)(2-rho))) / (8-rho)`. -/
def automaticFirstOrderThreshold (rho : ℝ) : ℝ :=
  (3 * rho + 2 * √(rho * (5 - rho) * (2 - rho))) / (8 - rho)

/-- The uncapped agreement slack `eta₁ = a - a₁(rho)`. -/
def automaticEtaOne (rho a : ℝ) : ℝ :=
  a - automaticFirstOrderThreshold rho

/-- The capped slack `eta₀ = min eta₁ ((1-a₁(rho))/2)`.

The second term keeps the tuned agreement uniformly below one. -/
def automaticEtaZero (rho a : ℝ) : ℝ :=
  min (automaticEtaOne rho a) ((1 - automaticFirstOrderThreshold rho) / 2)

/-- The tuned agreement `a₀ = a₁(rho) + eta₀`.

Equivalently, `a₀ = min a ((1+a₁(rho))/2)`: tuning at `a₀` preserves every agreement guarantee
at `a` while keeping the numerical parameters stable near one. -/
def automaticAgreement (rho a : ℝ) : ℝ :=
  automaticFirstOrderThreshold rho + automaticEtaZero rho a

/-- The derivative-degree proportion `beta = 3(1-a₀)/(2(2-rho))`.

This value maximizes the bracket in the limiting dimension-minus-rank estimate. -/
def automaticBeta (rho a : ℝ) : ℝ :=
  3 * (1 - automaticAgreement rho a) / (2 * (2 - rho))

/-- The source-minus-rank bracket
`a₀²/rho - 1 + 3(1-a₀)²/(4(2-rho))` at the tuned agreement. -/
def automaticGapBracket (rho a : ℝ) : ℝ :=
  automaticAgreement rho a ^ 2 / rho - 1 +
    3 * (1 - automaticAgreement rho a) ^ 2 / (4 * (2 - rho))

/-- The normalized surplus `S = beta/2 * (a₀²/rho - 1 + 3(1-a₀)²/(4(2-rho)))`.

The positivity proof below is the analytic reason that the integer recipe has more source
coefficients than local constraints. -/
def automaticSurplus (rho a : ℝ) : ℝ :=
  automaticBeta rho a * automaticGapBracket rho a / 2

/-- The continuous source density evaluated at `a₀` and `beta`. -/
def automaticSourceDensity (rho a : ℝ) : ℝ :=
  let a₀ := automaticAgreement rho a
  let beta := automaticBeta rho a
  beta * a₀ ^ 2 / (2 * rho) - a₀ * beta ^ 2 / 2 + rho * beta ^ 3 / 6

/-- The cubic envelope `beta/2 - beta²/2 + beta³/3` for the local-rank density. -/
def automaticRankDensityEnvelope (rho a : ℝ) : ℝ :=
  let beta := automaticBeta rho a
  beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3

private def automaticRankRoundingModel (u v : ℝ) : ℝ :=
  (u + v) * ((1 - v) / 2 + v) -
    (2 * ((1 - v) * (2 - v) / 6 -
        (1 - u) * (1 - u - v) * (2 * (1 - u) - v) / 6) +
      (2 * u + 3 * v - 3) *
        ((1 - v) / 2 - (1 - u) * (1 - u - v) / 2) +
      u * (v - 1) * (u + v - 1))

private theorem automaticRankRoundingModel_zero (u : ℝ) :
    automaticRankRoundingModel u 0 = u / 2 - u ^ 2 / 2 + u ^ 3 / 3 := by
  unfold automaticRankRoundingModel
  ring

private theorem automaticRankRoundingModel_le
    {u v beta : ℝ} (hu0 : 0 ≤ u) (hub : u ≤ beta) (hbu : beta ≤ u + v)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (_hb0 : 0 ≤ beta) (hb1 : beta ≤ 3 / 4) :
    automaticRankRoundingModel u v ≤
      beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3 + 3 * v := by
  unfold automaticRankRoundingModel
  have hu34 : u ≤ 3 / 4 := hub.trans hb1
  have hq : 0 ≤ 1 / 2 - (beta + u) / 2 +
      (beta ^ 2 + beta * u + u ^ 2) / 3 := by
    nlinarith [sq_nonneg (beta - u), sq_nonneg (beta + u - 1)]
  have hP : u / 2 - u ^ 2 / 2 + u ^ 3 / 3 ≤
      beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3 := by
    have hdiff :
      (beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3) -
          (u / 2 - u ^ 2 / 2 + u ^ 3 / 3) =
        (beta - u) * (1 / 2 - (beta + u) / 2 +
          (beta ^ 2 + beta * u + u ^ 2) / 3) := by ring
    nlinarith [mul_nonneg (sub_nonneg.mpr hub) hq]
  have hvSq : v ^ 2 ≤ v := by
    nlinarith [mul_nonneg hv0 (sub_nonneg.mpr hv1)]
  have huSq : u ^ 2 ≤ (9 / 16 : ℝ) := by
    have hprod := mul_nonneg (sub_nonneg.mpr hu34)
      (add_nonneg hu0 (by norm_num : (0 : ℝ) ≤ 3 / 4))
    nlinarith
  have huSqV : u ^ 2 * v ≤ (9 / 16 : ℝ) * v :=
    mul_le_mul_of_nonneg_right huSq hv0
  have huVSq : u * v ^ 2 ≤ (3 / 4 : ℝ) * v := by
    calc
      u * v ^ 2 ≤ (3 / 4 : ℝ) * v ^ 2 :=
        mul_le_mul_of_nonneg_right hu34 (sq_nonneg v)
      _ ≤ (3 / 4 : ℝ) * v := mul_le_mul_of_nonneg_left hvSq (by norm_num)
  ring_nf at ⊢
  nlinarith

private def automaticSourceRoundingModel (z u c v : ℝ) : ℝ :=
  (z + v) * u * (u - v) / 2 - u * (u - v) * (2 * u - v) / 6 +
    u * ((z + v) * (c - u) - (c * (c - v) - u * (u - v)) / 2)

private theorem automaticSourceRoundingModel_ge
    {z u c v beta : ℝ}
    (hz1 : 1 ≤ z) (_hb0 : 0 ≤ beta) (hbz : beta ≤ z)
    (hbu : beta ≤ u) (hub : u ≤ beta + v)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hzc : z + v ≤ c) (hcz : c ≤ z + 2 * v) :
    beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6 ≤
      automaticSourceRoundingModel z u c v := by
  have hconcave : automaticSourceRoundingModel z u (z + v) v ≤
      automaticSourceRoundingModel z u c v := by
    have hid : automaticSourceRoundingModel z u c v -
        automaticSourceRoundingModel z u (z + v) v =
          u / 2 * (c - (z + v)) * (z + 2 * v - c) := by
      unfold automaticSourceRoundingModel
      ring
    rw [← sub_nonneg, hid]
    positivity
  have hleft : beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6 ≤
      automaticSourceRoundingModel z u (z + v) v := by
    have hquad : 0 ≤
        (u - z) ^ 2 + (u - z) * (beta - z) + (beta - z) ^ 2 := by
      nlinarith [sq_nonneg ((u - z) + (beta - z)), sq_nonneg (u - z),
        sq_nonneg (beta - z)]
    have hbase : beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6 ≤
        u * z ^ 2 / 2 - z * u ^ 2 / 2 + u ^ 3 / 6 := by
      have hid :
          (u * z ^ 2 / 2 - z * u ^ 2 / 2 + u ^ 3 / 6) -
              (beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6) =
            (u - beta) / 6 *
              ((u - z) ^ 2 + (u - z) * (beta - z) + (beta - z) ^ 2) := by ring
      have hfac : 0 ≤ (u - beta) / 6 :=
        div_nonneg (sub_nonneg.mpr hbu) (by norm_num)
      nlinarith [mul_nonneg hfac hquad]
    have huz : u ≤ z + v := hub.trans (by
      simpa only [add_comm] using add_le_add_right hbz v)
    have hbracket : 0 ≤ z - u / 2 + v / 3 := by nlinarith
    have hround : 0 ≤ v * u * (z - u / 2 + v / 3) := by positivity
    have hid : automaticSourceRoundingModel z u (z + v) v =
        (u * z ^ 2 / 2 - z * u ^ 2 / 2 + u ^ 3 / 6) +
          v * u * (z - u / 2 + v / 3) := by
      unfold automaticSourceRoundingModel
      ring
    rw [hid]
    linarith
  exact hleft.trans hconcave

/-! ## Rounded finite parameters -/

/-- The interpolation multiplicity `m = ceil(4/S)`.

Since `S > 0`, this choice gives `4 ≤ m*S`; the later finite estimate uses that inequality to
absorb all `3*m²` rounding loss. -/
def automaticMultiplicity (rho a : ℝ) : ℕ :=
  ⌈4 / automaticSurplus rho a⌉₊

/-- The paper's derivative cap `Mraw = floor(beta*m)` before normalization. -/
def automaticDerivativeCapRaw (rho a : ℝ) : ℕ :=
  ⌊automaticBeta rho a * automaticMultiplicity rho a⌋₊

/-- The total jet-degree cap `mu = ceil(m*a₀/rho)` in the variables `Y₀, Y₁`. -/
def automaticJetDegree (rho a : ℝ) : ℕ :=
  ⌈automaticMultiplicity rho a * automaticAgreement rho a / rho⌉₊

/-- The normalized hidden-derivative cap `M = min Mraw mu`.

Normalization makes the definition meaningful without hypotheses. In the public parameter range,
`automaticDerivativeCap_eq_raw` proves that this minimum is exactly the paper's `floor(beta*m)`.
-/
def automaticDerivativeCap (rho a : ℝ) : ℕ :=
  min (automaticDerivativeCapRaw rho a) (automaticJetDegree rho a)

/-- The real source lower count `N₀` for fixed `rho`, `a₀`, `m`, `M`, and `mu`. -/
def automaticSourceCountAt (rho a₀ : ℝ) (m M mu : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (mu + 1),
    (min t M + 1 : ℕ) * max (m * a₀ - rho * t) 0

/-- The source count `N₀` specialized to the automatic parameters. -/
def automaticSourceCount (rho a : ℝ) : ℝ :=
  automaticSourceCountAt rho (automaticAgreement rho a) (automaticMultiplicity rho a)
    (automaticDerivativeCap rho a) (automaticJetDegree rho a)

/-- The exact certified local-rank budget `r(m,M)` when every local constraint uses the cap `M`. -/
def automaticRankCountAt (m M : ℕ) : ℕ :=
  ∑ s ∈ Finset.range m,
    ((s + 1) * (M + 1) - (2 * s + 1 - m) * (s + M + 1 - m))

/-- The exact certified local-rank budget `r` specialized to the automatic `m` and `M`. -/
def automaticRankCount (rho a : ℝ) : ℕ :=
  automaticRankCountAt (automaticMultiplicity rho a) (automaticDerivativeCap rho a)

/-- The challenge height `h = max 1 (floor(r*mu/(N₀-r)))`.

The denominator is positive because the finite source count exceeds the certified local-rank budget.
This choice depends only on `rho` and `a`, and uniformly bounds the symbolic kernel quotient.
-/
def automaticChallengeHeight (rho a : ℝ) : ℕ :=
  let r := automaticRankCount rho a
  let mu := automaticJetDegree rho a
  let N₀ := automaticSourceCount rho a
  max 1 ⌊(r : ℝ) * mu / (N₀ - r)⌋₊

/-- A signed real upper count for the certified local-rank budget. -/
def automaticRankCubicUpperCount (m M : ℕ) : ℝ :=
  (∑ s ∈ Finset.range m, ((s + 1 : ℕ) : ℝ) * (M + 1)) -
    ∑ s ∈ Finset.Ico (m - M) m,
      (((2 * s + 1 : ℕ) : ℝ) - m) * (((s + M + 1 : ℕ) : ℝ) - m)

private theorem automatic_rank_correction_le_ambient {m M s : ℕ} (hs : s < m) :
    (2 * s + 1 - m) * (s + M + 1 - m) ≤ (s + 1) * (M + 1) := by
  apply Nat.mul_le_mul <;> omega

/-- The certified all-`M` local-rank budget is bounded by its signed cubic upper count. -/
theorem automaticRankCountAt_le_cubicUpperCount (m M : ℕ) :
    (automaticRankCountAt m M : ℝ) ≤ automaticRankCubicUpperCount m M := by
  rw [automaticRankCountAt, automaticRankCubicUpperCount, Nat.cast_sum]
  have hrank :
      (∑ s ∈ Finset.range m,
          (((s + 1) * (M + 1) -
            (2 * s + 1 - m) * (s + M + 1 - m) : ℕ) : ℝ)) =
        (∑ s ∈ Finset.range m, ((s + 1 : ℕ) : ℝ) * (M + 1)) -
          ∑ s ∈ Finset.range m,
            (((2 * s + 1 - m : ℕ) : ℝ) * ((s + M + 1 - m : ℕ) : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Nat.cast_sub (automatic_rank_correction_le_ambient (Finset.mem_range.mp hs))]
    push_cast
    rfl
  rw [hrank]
  gcongr
  calc
    (∑ s ∈ Finset.Ico (m - M) m,
        (((2 * s + 1 : ℕ) : ℝ) - m) * (((s + M + 1 : ℕ) : ℝ) - m)) ≤
        ∑ s ∈ Finset.Ico (m - M) m,
          (((2 * s + 1 - m : ℕ) : ℝ) * ((s + M + 1 - m : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsecond : m ≤ s + M + 1 := by
        have := (Finset.mem_Ico.mp hs).1
        omega
      by_cases hfirst : m ≤ 2 * s + 1
      · rw [Nat.cast_sub hfirst, Nat.cast_sub hsecond]
      · have hsigned : ((2 * s + 1 : ℕ) : ℝ) - m < 0 := by
          exact sub_neg.mpr (Nat.cast_lt.mpr (by omega))
        have hnonneg : 0 ≤ ((s + M + 1 : ℕ) : ℝ) - m :=
          sub_nonneg.mpr (Nat.cast_le.mpr hsecond)
        exact (mul_nonpos_of_nonpos_of_nonneg hsigned.le hnonneg).trans
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ ≤ ∑ s ∈ Finset.range m,
          (((2 * s + 1 - m : ℕ) : ℝ) * ((s + M + 1 - m : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro s hs
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hs).2
      · intro s _ _
        positivity

private def automaticLinearSum (x : ℝ) : ℝ := x * (x - 1) / 2

private def automaticSquareSum (x : ℝ) : ℝ := x * (x - 1) * (2 * x - 1) / 6

private theorem automatic_sum_range_cast (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ)) = automaticLinearSum n := by
  induction n with
  | zero => simp [automaticLinearSum]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [automaticLinearSum]
      push_cast
      ring

private theorem automatic_sum_range_sq_cast (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) = automaticSquareSum n := by
  induction n with
  | zero => simp [automaticSquareSum]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [automaticSquareSum]
      push_cast
      ring

/-- A polynomial lower sum used to expose the unit-box source estimate. -/
def automaticSourceLowerCount (rho a₀ : ℝ) (m M L : ℕ) : ℝ :=
  ∑ t ∈ Finset.range L, (min t M : ℕ) * (m * a₀ - rho * t)

private theorem automaticSourceLowerCount_normalized_eq_model
    {rho z : ℝ} {m M L : ℕ} (hm : 0 < m) (hML : M ≤ L) :
    automaticSourceLowerCount rho (rho * (z + (m : ℝ)⁻¹)) m M L / (m : ℝ) ^ 3 =
      rho * automaticSourceRoundingModel z ((M : ℝ) / m) ((L : ℝ) / m)
        ((m : ℝ)⁻¹) := by
  have hsplit :
      automaticSourceLowerCount rho (rho * (z + (m : ℝ)⁻¹)) m M L =
        (rho * (z + (m : ℝ)⁻¹)) * m * automaticLinearSum M -
          rho * automaticSquareSum M +
          M * ((rho * (z + (m : ℝ)⁻¹)) * m * (L - M) -
            rho * (automaticLinearSum L - automaticLinearSum M)) := by
    rw [automaticSourceLowerCount, ← Finset.sum_range_add_sum_Ico _ hML]
    have hfirst :
        (∑ t ∈ Finset.range M,
            (min t M : ℕ) * (m * (rho * (z + (m : ℝ)⁻¹)) - rho * t)) =
          (rho * (z + (m : ℝ)⁻¹)) * m * automaticLinearSum M -
            rho * automaticSquareSum M := by
      calc
        _ = ∑ t ∈ Finset.range M,
            ((t : ℝ) * (m * (rho * (z + (m : ℝ)⁻¹)) - rho * t)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [min_eq_left (Finset.mem_range.mp ht).le]
        _ = ∑ t ∈ Finset.range M,
            ((rho * (z + (m : ℝ)⁻¹)) * m * (t : ℝ) -
              rho * (t : ℝ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro t _
          ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            automatic_sum_range_cast, automatic_sum_range_sq_cast]
    have htail :
        (∑ t ∈ Finset.Ico M L,
            (min t M : ℕ) *
              (m * (rho * (z + (m : ℝ)⁻¹)) - rho * t)) =
          M * ((rho * (z + (m : ℝ)⁻¹)) * m * (L - M) -
            rho * (automaticLinearSum L - automaticLinearSum M)) := by
      calc
        _ = ∑ t ∈ Finset.Ico M L,
            ((M : ℝ) * (m * (rho * (z + (m : ℝ)⁻¹)) - rho * t)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [min_eq_right (Finset.mem_Ico.mp ht).1]
        _ = _ := by
          have hsum (n : ℕ) :
              (∑ t ∈ Finset.range n,
                ((m : ℝ) * (rho * (z + (m : ℝ)⁻¹)) - rho * t)) =
                n * (m * (rho * (z + (m : ℝ)⁻¹))) -
                  rho * automaticLinearSum n := by
            induction n with
            | zero => simp [automaticLinearSum]
            | succ n ih =>
                rw [Finset.sum_range_succ, ih]
                simp only [automaticLinearSum]
                push_cast
                ring
          rw [← Finset.mul_sum, Finset.sum_Ico_eq_sub _ hML, hsum, hsum]
          ring
    exact congrArg₂ (fun x y : ℝ ↦ x + y) hfirst htail
  rw [hsplit]
  simp only [automaticLinearSum, automaticSquareSum, automaticSourceRoundingModel]
  field_simp [ne_of_gt (Nat.cast_pos.mpr hm)]

private theorem automatic_shiftedSourceLowerCount_eq
    {rho a₀ : ℝ} {m M L : ℕ} (hm : 0 < m) :
    automaticSourceLowerCount rho (a₀ + rho / m) m (M + 1) (L + 2) =
      ∑ t ∈ Finset.range (L + 1),
        (min t M + 1 : ℕ) * (m * a₀ - rho * t) := by
  rw [automaticSourceLowerCount, Finset.sum_range_succ']
  rw [show min 0 (M + 1) = 0 by omega]
  simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro t _
  rw [show min (t + 1) (M + 1) = min t M + 1 by omega]
  push_cast
  field_simp [ne_of_gt (Nat.cast_pos.mpr hm)]
  ring

private theorem automaticCubicUpperCount_normalized_eq_model {m M : ℕ}
    (hm : 0 < m) (hM : M ≤ m) :
    automaticRankCubicUpperCount m M / (m : ℝ) ^ 3 =
      automaticRankRoundingModel ((M : ℝ) / m) ((m : ℝ)⁻¹) := by
  have hamb (n : ℕ) :
      (∑ s ∈ Finset.range n, ((s + 1 : ℕ) : ℝ) * (M + 1)) =
        (M + 1) * (automaticLinearSum n + n) := by
    calc
      _ = (M + 1 : ℝ) * ((∑ s ∈ Finset.range n, (s : ℝ)) + n) := by
        push_cast
        ring_nf
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        rw [← Finset.sum_mul]
        ring
      _ = _ := by rw [automatic_sum_range_cast]
  have hcorrection (n : ℕ) :
      (∑ s ∈ Finset.range n,
        (((2 * s + 1 : ℕ) : ℝ) - m) * (((s + M + 1 : ℕ) : ℝ) - m)) =
        2 * automaticSquareSum n + (2 * M + 3 - 3 * m) * automaticLinearSum n +
          n * (1 - m) * (M + 1 - m) := by
    calc
      _ = ∑ s ∈ Finset.range n,
          (2 * (s : ℝ) ^ 2 + (2 * M + 3 - 3 * m) * s +
            (1 - m) * (M + 1 - m)) := by
        apply Finset.sum_congr rfl
        intro s _
        push_cast
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, automatic_sum_range_cast,
          automatic_sum_range_sq_cast]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  rw [automaticRankCubicUpperCount,
    Finset.sum_Ico_eq_sub _ (Nat.sub_le m M), hamb, hcorrection, hcorrection]
  rw [Nat.cast_sub hM]
  simp only [automaticLinearSum, automaticSquareSum, automaticRankRoundingModel]
  field_simp [ne_of_gt (Nat.cast_pos.mpr hm)]
  ring

private theorem automatic_radicand_pos {rho : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1) :
    0 < rho * (5 - rho) * (2 - rho) := by
  exact mul_pos (mul_pos hrho (by linarith)) (by linarith)

/-- The clean threshold is the positive root of the surplus bracket. -/
theorem automatic_threshold_bracket_eq_zero {rho : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) :
    automaticFirstOrderThreshold rho ^ 2 / rho - 1 +
      3 * (1 - automaticFirstOrderThreshold rho) ^ 2 / (4 * (2 - rho)) = 0 := by
  have hsquare : (√(rho * (5 - rho) * (2 - rho))) ^ 2 =
      rho * (5 - rho) * (2 - rho) :=
    Real.sq_sqrt (automatic_radicand_pos hrho hrhoOne).le
  unfold automaticFirstOrderThreshold
  field_simp [ne_of_gt hrho, ne_of_gt (show 0 < 2 - rho by linarith),
    ne_of_gt (show 0 < 8 - rho by linarith)]
  nlinarith

/-- The clean first-order threshold lies strictly above the physical rate. -/
theorem rho_lt_automaticFirstOrderThreshold {rho : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) :
    rho < automaticFirstOrderThreshold rho := by
  let s := √(rho * (5 - rho) * (2 - rho))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsquare : s ^ 2 = rho * (5 - rho) * (2 - rho) :=
    Real.sq_sqrt (automatic_radicand_pos hrho hrhoOne).le
  have hfactor :
      s ^ 2 - (rho * (5 - rho) / 2) ^ 2 =
        rho * (5 - rho) * ((1 - rho) * (8 - rho)) / 4 := by
    rw [hsquare]
    ring
  have hfactorPos : 0 < rho * (5 - rho) * ((1 - rho) * (8 - rho)) / 4 := by
    exact div_pos (mul_pos (mul_pos hrho (by linarith))
      (mul_pos (by linarith) (by linarith))) (by norm_num)
  have hauxSq : (rho * (5 - rho) / 2) ^ 2 < s ^ 2 := by linarith
  have haux : rho * (5 - rho) / 2 < s := by
    have hleft : 0 ≤ rho * (5 - rho) / 2 := by
      exact div_nonneg (mul_nonneg hrho.le (by linarith)) (by norm_num)
    nlinarith
  rw [automaticFirstOrderThreshold]
  rw [lt_div_iff₀ (by linarith : 0 < 8 - rho)]
  dsimp only [s] at haux
  nlinarith

/-- The clean first-order threshold is strictly below the Johnson curve `sqrt rho`. -/
theorem automaticFirstOrderThreshold_lt_sqrt {rho : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) :
    automaticFirstOrderThreshold rho < √rho := by
  let x := √rho
  let s := √(rho * (5 - rho) * (2 - rho))
  have hx0 : 0 < x := Real.sqrt_pos.2 hrho
  have hx1 : x < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hrho.le hrhoOne
  have hxSquare : x ^ 2 = rho := Real.sq_sqrt hrho.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsquare : s ^ 2 = rho * (5 - rho) * (2 - rho) :=
    Real.sq_sqrt (automatic_radicand_pos hrho hrhoOne).le
  have hright : 0 < x * (8 - rho) - 3 * rho := by
    dsimp only [x] at hx0 hx1 hxSquare ⊢
    nlinarith [sq_nonneg (x - 1)]
  have hdiff :
      (x * (8 - rho) - 3 * rho) ^ 2 - (2 * s) ^ 2 =
        3 * rho * (1 - x) ^ 2 * (8 - rho) := by
    rw [show (2 * s) ^ 2 = 4 * s ^ 2 by ring, hsquare, ← hxSquare]
    ring
  have hdiffPos : 0 < 3 * rho * (1 - x) ^ 2 * (8 - rho) := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) hrho)
      (sq_pos_of_pos (sub_pos.mpr hx1))) (by linarith)
  have hroot : 2 * s < x * (8 - rho) - 3 * rho := by nlinarith
  rw [automaticFirstOrderThreshold]
  rw [div_lt_iff₀ (by linarith : 0 < 8 - rho)]
  dsimp only [x, s] at hroot ⊢
  nlinarith

/-- The tuned agreement is the paper's value `a₀ = min a ((1+a₁(rho))/2)`. -/
theorem automaticAgreement_eq_min (rho a : ℝ) :
    automaticAgreement rho a = min a ((1 + automaticFirstOrderThreshold rho) / 2) := by
  unfold automaticAgreement automaticEtaZero automaticEtaOne
  rw [← min_add_add_left]
  congr 1 <;> ring

/-- The uncapped agreement gap is positive above the clean threshold. -/
theorem automaticEtaOne_pos {rho a : ℝ}
    (ha : automaticFirstOrderThreshold rho < a) :
    0 < automaticEtaOne rho a := by
  unfold automaticEtaOne
  linarith

/-- The capped gap is positive under the public rate and agreement guards. -/
theorem automaticEtaZero_pos {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) :
    0 < automaticEtaZero rho a := by
  unfold automaticEtaZero
  apply lt_min
  · exact automaticEtaOne_pos ha
  · have := (automaticFirstOrderThreshold_lt_sqrt hrho hrhoOne).trans
        (by simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hrho.le hrhoOne)
    linarith

/-- The capped agreement lies strictly above the clean threshold. -/
theorem automatic_threshold_lt_agreement {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) :
    automaticFirstOrderThreshold rho < automaticAgreement rho a := by
  unfold automaticAgreement
  linarith [automaticEtaZero_pos hrho hrhoOne ha]

/-- The capped agreement is no larger than the caller's agreement. -/
theorem automaticAgreement_le {rho a : ℝ} : automaticAgreement rho a ≤ a := by
  rw [automaticAgreement_eq_min]
  exact min_le_left _ _

/-- The capped agreement remains strictly below one. -/
theorem automaticAgreement_lt_one {rho a : ℝ} (haOne : a < 1) :
    automaticAgreement rho a < 1 :=
  (automaticAgreement_le (rho := rho) (a := a)).trans_lt haOne

/-- The capped agreement remains strictly above the physical rate. -/
theorem rho_lt_automaticAgreement {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) :
    rho < automaticAgreement rho a :=
  (rho_lt_automaticFirstOrderThreshold hrho hrhoOne).trans
    (automatic_threshold_lt_agreement hrho hrhoOne ha)

/-- Above the clean root, the surplus bracket is strictly positive. -/
theorem automaticGapBracket_pos {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) :
    0 < automaticGapBracket rho a := by
  let a₁ := automaticFirstOrderThreshold rho
  let a₀ := automaticAgreement rho a
  have hroot := automatic_threshold_bracket_eq_zero hrho hrhoOne
  have ha₁rho := rho_lt_automaticFirstOrderThreshold hrho hrhoOne
  have ha₀a₁ := automatic_threshold_lt_agreement hrho hrhoOne ha
  have hden : 0 < 4 * (2 - rho) := mul_pos (by norm_num) (by linarith)
  have hcoef : 0 < (a₀ + a₁) / rho +
      3 * (a₀ + a₁ - 2) / (4 * (2 - rho)) := by
    let c := (a₀ + a₁) / rho +
      3 * (a₀ + a₁ - 2) / (4 * (2 - rho))
    let q := rho * (4 * (2 - rho))
    have hq : 0 < q := mul_pos hrho hden
    have hcq : c * q =
        (a₀ + a₁) * (4 * (2 - rho)) +
          3 * (a₀ + a₁ - 2) * rho := by
      dsimp only [c, q]
      field_simp [ne_of_gt hrho, ne_of_gt (show 0 < 2 - rho by linarith)]
    have hrhs : 0 < (a₀ + a₁) * (4 * (2 - rho)) +
        3 * (a₀ + a₁ - 2) * rho := by
      dsimp only [a₀, a₁]
      nlinarith [mul_pos (sub_pos.mpr hrhoOne) (sub_pos.mpr (show rho < 8 by linarith))]
    exact (mul_pos_iff_of_pos_right hq).mp (hcq.symm ▸ hrhs)
  have hdiff :
      (a₀ ^ 2 / rho + 3 * (1 - a₀) ^ 2 / (4 * (2 - rho))) -
          (a₁ ^ 2 / rho + 3 * (1 - a₁) ^ 2 / (4 * (2 - rho))) =
        (a₀ - a₁) * ((a₀ + a₁) / rho +
          3 * (a₀ + a₁ - 2) / (4 * (2 - rho))) := by
    field_simp
    ring
  unfold automaticGapBracket
  dsimp only [a₀, a₁] at hroot ha₀a₁ hcoef hdiff ⊢
  nlinarith

/-- The optimized derivative ratio is positive. -/
theorem automaticBeta_pos {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (_ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    0 < automaticBeta rho a := by
  have ha₀One := automaticAgreement_lt_one (rho := rho) haOne
  unfold automaticBeta
  exact div_pos (mul_pos (by norm_num) (sub_pos.mpr ha₀One))
    (mul_pos (by norm_num) (by linarith))

/-- The optimized derivative ratio is strictly below `3/4`. -/
theorem automaticBeta_lt_three_four {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    automaticBeta rho a < 3 / 4 := by
  have hrhoA := rho_lt_automaticAgreement hrho hrhoOne ha
  have ha₀One := automaticAgreement_lt_one (rho := rho) haOne
  unfold automaticBeta
  rw [div_lt_iff₀ (by nlinarith : 0 < 2 * (2 - rho))]
  nlinarith

/-- The derivative ratio is strictly below the normalized total-degree cutoff. -/
theorem automaticBeta_lt_agreement_div_rate {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    automaticBeta rho a < automaticAgreement rho a / rho := by
  have hrhoA := rho_lt_automaticAgreement hrho hrhoOne ha
  have ha₀One := automaticAgreement_lt_one (rho := rho) haOne
  unfold automaticBeta
  rw [div_lt_div_iff₀ (by nlinarith : 0 < 2 * (2 - rho)) hrho]
  nlinarith

/-- In particular, `3/4` lies below the normalized total-degree cutoff. -/
theorem three_four_lt_automaticAgreement_div_rate {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) :
    3 / 4 < automaticAgreement rho a / rho := by
  have hrhoA := rho_lt_automaticAgreement hrho hrhoOne ha
  apply (lt_div_iff₀ hrho).2
  nlinarith

/-- The normalized surplus `S` is strictly positive. -/
theorem automaticSurplus_pos {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    0 < automaticSurplus rho a := by
  unfold automaticSurplus
  positivity [automaticBeta_pos hrho hrhoOne ha haOne,
    automaticGapBracket_pos hrho hrhoOne ha]

/-- The displayed `S` is exactly the continuous source-minus-rank density gap.

This identity explains the choice of `beta`: substituting the optimizing derivative proportion
turns the difference of the two cubic densities into the explicit surplus formula. -/
theorem automatic_sourceDensity_sub_rankDensityEnvelope {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) :
    automaticSourceDensity rho a - automaticRankDensityEnvelope rho a =
      automaticSurplus rho a := by
  unfold automaticSourceDensity automaticRankDensityEnvelope automaticSurplus
    automaticGapBracket automaticBeta
  field_simp [ne_of_gt hrho, ne_of_gt (show 0 < 2 - rho by linarith)]
  ring

/-- Clearing the positive denominators gives the quadratic polynomial used to identify the root. -/
theorem automaticGapBracket_cleared {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) :
    4 * rho * (2 - rho) * automaticGapBracket rho a =
      (8 - rho) * automaticAgreement rho a ^ 2 -
        6 * rho * automaticAgreement rho a + rho * (4 * rho - 5) := by
  unfold automaticGapBracket
  field_simp [ne_of_gt hrho, ne_of_gt (show 0 < 2 - rho by linarith)]
  ring

/-- The choice `m = ceil(4/S)` gives the exact scaling inequality `4 ≤ m*S`. -/
theorem four_le_automaticMultiplicity_mul_surplus {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    4 ≤ automaticMultiplicity rho a * automaticSurplus rho a := by
  have hS := automaticSurplus_pos hrho hrhoOne ha haOne
  have hceil : 4 / automaticSurplus rho a ≤ (automaticMultiplicity rho a : ℝ) := by
    unfold automaticMultiplicity
    exact Nat.le_ceil _
  exact (div_le_iff₀ hS).mp hceil

/-- The literal multiplicity is positive. -/
theorem automaticMultiplicity_pos {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    0 < automaticMultiplicity rho a := by
  have hS := automaticSurplus_pos hrho hrhoOne ha haOne
  unfold automaticMultiplicity
  exact Nat.ceil_pos.mpr (by positivity)

/-- The raw derivative cap is bounded by the rounded total jet degree. -/
theorem automaticDerivativeCapRaw_le_jetDegree {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    automaticDerivativeCapRaw rho a ≤ automaticJetDegree rho a := by
  let m := automaticMultiplicity rho a
  have hbeta := automaticBeta_lt_agreement_div_rate hrho hrhoOne ha haOne
  have hmul : automaticBeta rho a * m ≤ m * automaticAgreement rho a / rho := by
    have hm : (0 : ℝ) ≤ m := by positivity
    calc
      automaticBeta rho a * m ≤ (automaticAgreement rho a / rho) * m :=
        mul_le_mul_of_nonneg_right hbeta.le hm
      _ = m * automaticAgreement rho a / rho := by ring
  have hfloor : (⌊automaticBeta rho a * m⌋₊ : ℝ) ≤
      m * automaticAgreement rho a / rho := by
    exact (Nat.floor_le (mul_nonneg (automaticBeta_pos hrho hrhoOne ha haOne).le
      (Nat.cast_nonneg m))).trans hmul
  have hceil : m * automaticAgreement rho a / rho ≤
      (⌈m * automaticAgreement rho a / rho⌉₊ : ℝ) := Nat.le_ceil _
  exact_mod_cast hfloor.trans hceil

/-- In the public parameter range, normalization leaves `M = floor(beta*m)` unchanged. -/
theorem automaticDerivativeCap_eq_raw {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    automaticDerivativeCap rho a = automaticDerivativeCapRaw rho a := by
  unfold automaticDerivativeCap
  exact min_eq_left (automaticDerivativeCapRaw_le_jetDegree hrho hrhoOne ha haOne)

/-- The literal automatic source count can therefore be written with `Mraw` directly. -/
theorem automaticSourceCount_eq_raw {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    automaticSourceCount rho a =
      ∑ t ∈ Finset.range (automaticJetDegree rho a + 1),
        (min t (automaticDerivativeCapRaw rho a) + 1 : ℕ) *
          max (automaticMultiplicity rho a * automaticAgreement rho a - rho * t) 0 := by
  unfold automaticSourceCount
  rw [automaticDerivativeCap_eq_raw hrho hrhoOne ha haOne]
  rfl

/-- The literal automatic rank count can therefore be written with `Mraw` directly. -/
theorem automaticRankCount_eq_raw {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    automaticRankCount rho a =
      ∑ s ∈ Finset.range (automaticMultiplicity rho a),
        ((s + 1) * (automaticDerivativeCapRaw rho a + 1) -
          (2 * s + 1 - automaticMultiplicity rho a) *
            (s + automaticDerivativeCapRaw rho a + 1 - automaticMultiplicity rho a)) := by
  unfold automaticRankCount
  rw [automaticDerivativeCap_eq_raw hrho hrhoOne ha haOne]
  rfl

/-- The exact rounded rank loses at most `3m²` from the continuous cubic envelope. -/
theorem automaticRankCount_le_densityEnvelope_add_rounding {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    (automaticRankCount rho a : ℝ) ≤
      automaticMultiplicity rho a ^ 3 * automaticRankDensityEnvelope rho a +
        3 * automaticMultiplicity rho a ^ 2 := by
  let m := automaticMultiplicity rho a
  let beta := automaticBeta rho a
  let M := automaticDerivativeCapRaw rho a
  let u : ℝ := M / m
  let v : ℝ := (m : ℝ)⁻¹
  have hmNat : 0 < m := automaticMultiplicity_pos hrho hrhoOne ha haOne
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hmNat
  have hb0 : 0 < beta := automaticBeta_pos hrho hrhoOne ha haOne
  have hb34 : beta < 3 / 4 := automaticBeta_lt_three_four hrho hrhoOne ha haOne
  have hMReal : (M : ℝ) ≤ beta * m := by
    unfold M automaticDerivativeCapRaw
    exact Nat.floor_le (mul_nonneg hb0.le (Nat.cast_nonneg m))
  have hMlt : beta * m < (M : ℝ) + 1 := by
    unfold M automaticDerivativeCapRaw
    exact Nat.lt_floor_add_one _
  have hMNat : M ≤ m := by
    have hreal : (M : ℝ) ≤ m := by
      calc
        (M : ℝ) ≤ beta * m := hMReal
        _ ≤ (3 / 4 : ℝ) * m := mul_le_mul_of_nonneg_right hb34.le hm.le
        _ ≤ m := by nlinarith
    exact_mod_cast hreal
  have hu0 : 0 ≤ u := by unfold u; positivity
  have hub : u ≤ beta := by
    unfold u
    exact (div_le_iff₀ hm).2 (by simpa [mul_comm] using hMReal)
  have hbu : beta ≤ u + v := by
    unfold u v
    rw [show (M : ℝ) / m + (m : ℝ)⁻¹ = ((M : ℝ) + 1) / m by
      field_simp [ne_of_gt hm]]
    exact (le_div_iff₀ hm).2 (by linarith)
  have hv0 : 0 ≤ v := by unfold v; positivity
  have hv1 : v ≤ 1 := by
    unfold v
    rw [inv_le_one₀ hm]
    exact_mod_cast hmNat
  have hmodel : automaticRankRoundingModel u v ≤
      beta / 2 - beta ^ 2 / 2 + beta ^ 3 / 3 + 3 * v :=
    automaticRankRoundingModel_le hu0 hub hbu hv0 hv1 hb0.le hb34.le
  have hnormalized : automaticRankCubicUpperCount m M / (m : ℝ) ^ 3 ≤
      automaticRankDensityEnvelope rho a + 3 / m := by
    rw [automaticCubicUpperCount_normalized_eq_model hmNat hMNat]
    unfold automaticRankDensityEnvelope
    dsimp only [beta, u, v] at hmodel ⊢
    simpa [div_eq_mul_inv] using hmodel
  have hmCube : 0 < (m : ℝ) ^ 3 := pow_pos hm 3
  have hupper : automaticRankCubicUpperCount m M ≤
      (m : ℝ) ^ 3 * (automaticRankDensityEnvelope rho a + 3 / m) := by
    simpa [mul_comm] using (div_le_iff₀ hmCube).mp hnormalized
  have hscale : (m : ℝ) ^ 3 * (automaticRankDensityEnvelope rho a + 3 / m) =
      (m : ℝ) ^ 3 * automaticRankDensityEnvelope rho a + 3 * (m : ℝ) ^ 2 := by
    field_simp [ne_of_gt hm]
  rw [automaticRankCount_eq_raw hrho hrhoOne ha haOne]
  change (automaticRankCountAt m M : ℝ) ≤ _
  calc
    (automaticRankCountAt m M : ℝ) ≤ automaticRankCubicUpperCount m M :=
      automaticRankCountAt_le_cubicUpperCount m M
    _ ≤ (m : ℝ) ^ 3 * (automaticRankDensityEnvelope rho a + 3 / m) := hupper
    _ = _ := hscale

/-- The rounded source sum dominates its continuous unit-box density without a loss term. -/
theorem automaticSourceDensity_mul_cube_le_sourceCount {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    automaticMultiplicity rho a ^ 3 * automaticSourceDensity rho a ≤
      automaticSourceCount rho a := by
  let a₀ := automaticAgreement rho a
  let beta := automaticBeta rho a
  let m := automaticMultiplicity rho a
  let M := automaticDerivativeCapRaw rho a
  let mu := automaticJetDegree rho a
  let L := ⌊m * a₀ / rho⌋₊
  let z := a₀ / rho
  let u : ℝ := (M + 1 : ℕ) / m
  let c : ℝ := (L + 2 : ℕ) / m
  let v : ℝ := (m : ℝ)⁻¹
  let Q : ℝ := ∑ t ∈ Finset.range (L + 1),
    (min t M + 1 : ℕ) * (m * a₀ - rho * t)
  have hmNat : 0 < m := automaticMultiplicity_pos hrho hrhoOne ha haOne
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hmNat
  have hmCube : 0 < (m : ℝ) ^ 3 := pow_pos hm 3
  have ha₀0 : 0 < a₀ := hrho.trans (rho_lt_automaticAgreement hrho hrhoOne ha)
  have hb0 : 0 < beta := automaticBeta_pos hrho hrhoOne ha haOne
  have hbz : beta < z := by
    dsimp only [beta, z, a₀]
    exact automaticBeta_lt_agreement_div_rate hrho hrhoOne ha haOne
  have hMReal : (M : ℝ) ≤ beta * m := by
    unfold M automaticDerivativeCapRaw
    exact Nat.floor_le (mul_nonneg hb0.le (Nat.cast_nonneg m))
  have hMlt : beta * m < (M : ℝ) + 1 := by
    unfold M automaticDerivativeCapRaw
    exact Nat.lt_floor_add_one _
  have hmulCutoff : beta * m ≤ m * a₀ / rho := by
    have := mul_le_mul_of_nonneg_right hbz.le (Nat.cast_nonneg m)
    dsimp only [z] at this
    calc
      beta * (m : ℝ) ≤ (a₀ / rho) * m := this
      _ = (m : ℝ) * a₀ / rho := by ring
  have hML : M ≤ L := by
    unfold M L automaticDerivativeCapRaw
    exact Nat.floor_le_floor hmulCutoff
  have hcutoff0 : 0 ≤ (m : ℝ) * a₀ / rho := by positivity
  have hLReal : (L : ℝ) ≤ m * a₀ / rho := by
    unfold L
    exact Nat.floor_le hcutoff0
  have hLlt : (m : ℝ) * a₀ / rho < (L : ℝ) + 1 := by
    unfold L
    exact Nat.lt_floor_add_one _
  have hLmu : L ≤ mu := by
    have hceil : (m : ℝ) * a₀ / rho ≤ (⌈m * a₀ / rho⌉₊ : ℝ) := Nat.le_ceil _
    exact_mod_cast hLReal.trans hceil
  have hQle : Q ≤ automaticSourceCount rho a := by
    rw [automaticSourceCount_eq_raw hrho hrhoOne ha haOne]
    change Q ≤ ∑ t ∈ Finset.range (mu + 1),
      (min t M + 1 : ℕ) * max (m * a₀ - rho * t) 0
    dsimp only [Q]
    calc
      (∑ t ∈ Finset.range (L + 1),
          (min t M + 1 : ℕ) * (m * a₀ - rho * t)) =
          ∑ t ∈ Finset.range (L + 1),
            (min t M + 1 : ℕ) * max (m * a₀ - rho * t) 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [max_eq_left]
        have htLt : t < L + 1 := Finset.mem_range.mp ht
        have htLNat : t ≤ L := by omega
        have htL : (t : ℝ) ≤ L := by exact_mod_cast htLNat
        have htCutoff := htL.trans hLReal
        have := mul_le_mul_of_nonneg_left htCutoff hrho.le
        field_simp [ne_of_gt hrho] at this ⊢
        nlinarith
      _ ≤ ∑ t ∈ Finset.range (mu + 1),
            (min t M + 1 : ℕ) * max (m * a₀ - rho * t) 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro t ht
          apply Finset.mem_range.mpr
          have := Finset.mem_range.mp ht
          omega
        · intro t _ _
          positivity
  have hshift : automaticSourceLowerCount rho (a₀ + rho / m) m (M + 1) (L + 2) = Q := by
    exact automatic_shiftedSourceLowerCount_eq hmNat
  have harg : rho * (z + (m : ℝ)⁻¹) = a₀ + rho / m := by
    dsimp only [z]
    field_simp [ne_of_gt hrho, ne_of_gt hm]
  have hnormalized : Q / (m : ℝ) ^ 3 =
      rho * automaticSourceRoundingModel z u c v := by
    have h := automaticSourceLowerCount_normalized_eq_model
      (rho := rho) (z := z) (m := m) (M := M + 1) (L := L + 2) hmNat (by omega)
    rw [harg, hshift] at h
    exact h
  have hz1 : 1 ≤ z := by
    dsimp only [z]
    apply (le_div_iff₀ hrho).2
    simpa only [one_mul] using (rho_lt_automaticAgreement hrho hrhoOne ha).le
  have hbu : beta ≤ u := by
    dsimp only [u]
    exact (le_div_iff₀ hm).2 (by norm_num at hMlt ⊢; linarith)
  have hub : u ≤ beta + v := by
    dsimp only [u, v]
    rw [show beta + (m : ℝ)⁻¹ = (beta * m + 1) / m by
      field_simp [ne_of_gt hm]]
    exact (div_le_div_iff_of_pos_right hm).2 (by norm_num; linarith)
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have hv0 : 0 ≤ v := by dsimp only [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp only [v]
    rw [inv_le_one₀ hm]
    exact_mod_cast hmNat
  have hzc : z + v ≤ c := by
    dsimp only [z, v, c]
    apply (le_div_iff₀ hm).2
    have : (m : ℝ) * (a₀ / rho + (m : ℝ)⁻¹) =
        (m : ℝ) * a₀ / rho + 1 := by field_simp [ne_of_gt hm]
    rw [mul_comm, this]
    push_cast
    linarith
  have hcz : c ≤ z + 2 * v := by
    dsimp only [z, v, c]
    apply (div_le_iff₀ hm).2
    have : (m : ℝ) * (a₀ / rho + 2 * (m : ℝ)⁻¹) =
        (m : ℝ) * a₀ / rho + 2 := by field_simp [ne_of_gt hm]
    rw [mul_comm, this]
    push_cast
    linarith
  have hmodel := automaticSourceRoundingModel_ge hz1 hb0.le hbz.le hbu hub hu0 hv0 hv1 hzc hcz
  have hdensity : automaticSourceDensity rho a =
      rho * (beta * z ^ 2 / 2 - z * beta ^ 2 / 2 + beta ^ 3 / 6) := by
    unfold automaticSourceDensity
    dsimp only [a₀, beta, z]
    field_simp [ne_of_gt hrho]
  have hdensityNorm : automaticSourceDensity rho a ≤ Q / (m : ℝ) ^ 3 := by
    rw [hdensity, hnormalized]
    exact mul_le_mul_of_nonneg_left hmodel hrho.le
  have hdensityQ : (m : ℝ) ^ 3 * automaticSourceDensity rho a ≤ Q := by
    have := (le_div_iff₀ hmCube).mp hdensityNorm
    nlinarith
  exact hdensityQ.trans hQle

/-- The rounded total jet degree is positive. -/
theorem automaticJetDegree_pos {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    0 < automaticJetDegree rho a := by
  unfold automaticJetDegree
  apply Nat.ceil_pos.mpr
  exact div_pos (mul_pos (by exact_mod_cast automaticMultiplicity_pos hrho hrhoOne ha haOne)
    (hrho.trans (rho_lt_automaticAgreement hrho hrhoOne ha))) hrho

/-- The analytic lower margin retained after the `3m²` rounding loss is positive. -/
theorem automatic_rounded_margin_pos {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    0 < (automaticMultiplicity rho a : ℝ) ^ 3 * automaticSurplus rho a / 4 := by
  positivity [automaticMultiplicity_pos hrho hrhoOne ha haOne,
    automaticSurplus_pos hrho hrhoOne ha haOne]

/-- The choice `m = ceil(4/S)` absorbs the complete `3m²` rounding loss. -/
theorem automatic_rounding_loss_bound {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    (automaticMultiplicity rho a : ℝ) ^ 3 * automaticSurplus rho a -
        3 * automaticMultiplicity rho a ^ 2 ≥
      automaticMultiplicity rho a ^ 3 * automaticSurplus rho a / 4 := by
  let m := automaticMultiplicity rho a
  have hm : (0 : ℝ) < m := by exact_mod_cast automaticMultiplicity_pos hrho hrhoOne ha haOne
  have hfour := four_le_automaticMultiplicity_mul_surplus hrho hrhoOne ha haOne
  dsimp only [m] at hm hfour ⊢
  nlinarith [mul_nonneg (sq_nonneg (m : ℝ))
    (sub_nonneg.mpr hfour)]

/-- The finite source-minus-rank gap dominates `m³*S - 3*m²`.

The source lattice sum loses nothing relative to its continuous density lower bound. The rank
estimate can exceed its cubic density by at most `3*m²`; subtracting the two comparisons yields
the displayed finite surplus. -/
theorem automaticFiniteSurplusEstimate {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    automaticMultiplicity rho a ^ 3 * automaticSurplus rho a -
        3 * automaticMultiplicity rho a ^ 2 ≤
      automaticSourceCount rho a - automaticRankCount rho a := by
  -- Compare the rounded source count and certified rank budget with their continuous cubic models.
  have hsource := automaticSourceDensity_mul_cube_le_sourceCount
    hrho hrhoOne ha haOne
  have hrank := automaticRankCount_le_densityEnvelope_add_rounding
    hrho hrhoOne ha haOne
  have hdensity := automatic_sourceDensity_sub_rankDensityEnvelope
    (a := a) hrho hrhoOne
  nlinarith [show
    (automaticMultiplicity rho a : ℝ) ^ 3 * automaticSourceDensity rho a -
        automaticMultiplicity rho a ^ 3 * automaticRankDensityEnvelope rho a =
      automaticMultiplicity rho a ^ 3 * automaticSurplus rho a by
        rw [← hdensity]
        ring]

/-- At least `m³*S/4` remains after the complete finite rounding loss. -/
theorem automaticSurplusQuarter_le_source_sub_rank {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    automaticMultiplicity rho a ^ 3 * automaticSurplus rho a / 4 ≤
      automaticSourceCount rho a - automaticRankCount rho a :=
  (automatic_rounding_loss_bound hrho hrhoOne ha haOne).trans
    (automaticFiniteSurplusEstimate hrho hrhoOne ha haOne)

/-- The automatic source count `N₀` strictly exceeds the certified local-rank budget `r`. -/
theorem automaticRankCount_lt_sourceCount {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    (automaticRankCount rho a : ℝ) < automaticSourceCount rho a := by
  have hquarter := automaticSurplusQuarter_le_source_sub_rank hrho hrhoOne ha haOne
  have hpos := automatic_rounded_margin_pos hrho hrhoOne ha haOne
  linarith

/-- In particular, the denominator in the automatic challenge-height quotient is positive. -/
theorem automaticChallengeDenominator_pos {rho a : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1) :
    0 < automaticSourceCount rho a - automaticRankCount rho a :=
  sub_pos.mpr (automaticRankCount_lt_sourceCount hrho hrhoOne ha haOne)

/-- The automatic challenge height has the paper's formula
`h = max 1 (floor(r*mu/(N₀-r)))`. -/
theorem automaticChallengeHeight_eq (rho a : ℝ) :
    automaticChallengeHeight rho a =
      max 1 ⌊(automaticRankCount rho a : ℝ) * automaticJetDegree rho a /
        (automaticSourceCount rho a - automaticRankCount rho a)⌋₊ := rfl

/-- Tuning at `a₀ ≤ a` preserves every public agreement lower bound. -/
theorem automaticAgreement_mul_le_agreement_mul (rho a : ℝ) (n : ℕ) :
    automaticAgreement rho a * n ≤ a * n := by
  exact mul_le_mul_of_nonneg_right automaticAgreement_le (Nat.cast_nonneg n)

/-- Hence a public agreement count also dominates the capped recipe agreement. -/
theorem automaticAgreement_mul_le_count {rho a : ℝ} {n A : ℕ}
    (hA : a * n ≤ A) :
    automaticAgreement rho a * n ≤ A :=
  (automaticAgreement_mul_le_agreement_mul rho a n).trans hA

/-- With `D=k-1`, the public rate hypothesis supplies the physical degree-rate bound. -/
theorem automatic_degree_le_rate_mul {rho : ℝ} {n k D : ℕ}
    (hD : D = k - 1) (hk : (k : ℝ) ≤ rho * n) :
    (D : ℝ) ≤ rho * n := by
  rw [hD]
  exact (Nat.cast_le.mpr (Nat.sub_le k 1)).trans hk

/-- Each physical-rate source residual is dominated by its public finite-code residual. -/
theorem automatic_source_residual_le_public
    {rho a : ℝ} {n k D A m t : ℕ}
    (hD : D = k - 1) (hk : (k : ℝ) ≤ rho * n) (hA : a * n ≤ A) :
    n * max (m * automaticAgreement rho a - rho * t) 0 ≤
      max (m * A - D * t : ℝ) 0 := by
  have hdegree := automatic_degree_le_rate_mul hD hk
  have hagreement := automaticAgreement_mul_le_count (rho := rho) hA
  by_cases hx : 0 ≤ (m : ℝ) * automaticAgreement rho a - rho * t
  · rw [max_eq_left hx]
    have hbase : (n : ℝ) *
        ((m : ℝ) * automaticAgreement rho a - rho * t) ≤
        (m : ℝ) * A - D * t := by
      have hm : 0 ≤ (m : ℝ) * ((A : ℝ) - automaticAgreement rho a * n) :=
        mul_nonneg (Nat.cast_nonneg m) (sub_nonneg.mpr hagreement)
      have ht : 0 ≤ (t : ℝ) * (rho * n - D) :=
        mul_nonneg (Nat.cast_nonneg t) (sub_nonneg.mpr hdegree)
      nlinarith
    exact hbase.trans (le_max_left _ _)
  · rw [max_eq_right (le_of_not_ge hx)]
    simp only [mul_zero]
    exact le_max_right _ _

/-- The challenge height always retains the paper's floor quotient. -/
theorem automatic_floor_height_le (rho a : ℝ) :
    ⌊(automaticRankCount rho a : ℝ) * automaticJetDegree rho a /
        (automaticSourceCount rho a - automaticRankCount rho a)⌋₊ ≤
      automaticChallengeHeight rho a := by
  unfold automaticChallengeHeight
  exact le_max_right _ _

/-- Generic uniform-height arithmetic used after an actual source/rank surplus is established. -/
theorem scaledKernelHeight_le_of_source_surplus
    {n N r mu : ℕ} {N₀ : ℝ}
    (hn : 0 < n) (hsurplus : (r : ℝ) < N₀) (hN : n * N₀ ≤ N) :
    n * r * mu / (N - n * r) ≤
      max 1 ⌊(r : ℝ) * mu / (N₀ - r)⌋₊ := by
  have hnrNReal : ((n * r : ℕ) : ℝ) < (N : ℕ) := by
    calc
      ((n * r : ℕ) : ℝ) = (n : ℝ) * r := by push_cast; ring
      _ < (n : ℝ) * N₀ := mul_lt_mul_of_pos_left hsurplus (Nat.cast_pos.mpr hn)
      _ ≤ N := hN
  have hnrN : n * r < N := by exact_mod_cast hnrNReal
  have hgap : 0 < N₀ - r := sub_pos.mpr hsurplus
  have hdenLower : (n : ℝ) * (N₀ - r) ≤ ((N - n * r : ℕ) : ℝ) := by
    rw [Nat.cast_sub hnrN.le]
    push_cast
    nlinarith
  have hfrac : (((n * r * mu : ℕ) : ℝ) / ((N - n * r : ℕ) : ℝ)) ≤
      (r : ℝ) * mu / (N₀ - r) := by
    calc
      (((n * r * mu : ℕ) : ℝ) / ((N - n * r : ℕ) : ℝ)) ≤
          ((n : ℝ) * ((r : ℝ) * mu)) / ((n : ℝ) * (N₀ - r)) := by
        push_cast
        rw [show (n : ℝ) * r * mu = (n : ℝ) * (r * mu) by ring]
        exact div_le_div_of_nonneg_left (by positivity)
          (mul_pos (Nat.cast_pos.mpr hn) hgap) hdenLower
      _ = (r : ℝ) * mu / (N₀ - r) := by
        field_simp [ne_of_gt (Nat.cast_pos.mpr hn), ne_of_gt hgap]
  have hcast : ((n * r * mu / (N - n * r) : ℕ) : ℝ) ≤
      (r : ℝ) * mu / (N₀ - r) :=
    (Nat.cast_div_le (m := n * r * mu) (n := N - n * r)).trans hfrac
  have hfloor : n * r * mu / (N - n * r) ≤
      ⌊(r : ℝ) * mu / (N₀ - r)⌋₊ := Nat.le_floor hcast
  exact hfloor.trans (le_max_right _ _)

/-- The finite automatic height uniformly bounds every scaled polynomial-kernel quotient.

The positive gap `N₀-r` supplies a nonzero kernel vector, and the floor in `h` provides the
uniform symbolic challenge-degree bound required by the interpolation certificate. -/
theorem automatic_scaledKernelHeight_le_challengeHeight
    {rho a : ℝ} {n N : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1)
    (hn : 0 < n) (hN : n * automaticSourceCount rho a ≤ N) :
    n * automaticRankCount rho a * automaticJetDegree rho a /
        (N - n * automaticRankCount rho a) ≤ automaticChallengeHeight rho a := by
  rw [automaticChallengeHeight_eq]
  exact scaledKernelHeight_le_of_source_surplus hn
    (automaticRankCount_lt_sourceCount hrho hrhoOne ha haOne) hN

end

end ReedSolomon.HiddenDerivative
