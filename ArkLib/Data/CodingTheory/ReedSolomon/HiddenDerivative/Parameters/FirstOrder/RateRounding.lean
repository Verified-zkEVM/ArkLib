/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.RateBound
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Counting

/-!
# Finite first-order rate parameters

This file records the integer test used after the analytic first-order surplus is positive.  At
multiplicity `m`, the derivative cap is `floor (beta * m)` and the total jet cap is
`ceil (m * a / R)`.  The real number `firstOrderRateSourceCount` is a uniform lower bound for the
actual support dimension divided by the block length; `firstOrderRateRankCount` is the exact
field-independent local-rank budget already used by the interpolation engine.

The distinction between real and executable data is explicit.  Arbitrary real inputs supply an
existence theorem, while `FirstOrderRationalFiniteTest` is a decidable finite check for rational
instances.
-/

@[expose] public section

open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

noncomputable section

/-- The paper's finite source lower sum `N₀`. -/
def firstOrderRateSourceCount (R a : ℝ) (m M mu : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (mu + 1),
    (min t M + 1 : ℕ) * max (m * a - R * t) 0

/-- Exact first-order local-rank sum, valid for every derivative cap `M`. -/
def firstOrderRateRankCount (m M : ℕ) : ℕ :=
  ∑ s ∈ Finset.range m,
    ((s + 1) * (M + 1) - (2 * s + 1 - m) * (s + M + 1 - m))

/-- Rounded derivative cap at multiplicity `m`. -/
def firstOrderRateDerivativeCap (R a : ℝ) (m : ℕ) : ℕ :=
  Nat.floor (firstOrderRateBeta R a * m)

/-- Rounded total jet cap at multiplicity `m`. -/
def firstOrderRateJetDegree (R a : ℝ) (m : ℕ) : ℕ :=
  Nat.ceil (m * a / R)

/-- Finite rank-surplus test for the rounded parameters. -/
def FirstOrderFiniteRateTest (R a : ℝ) (m : ℕ) : Prop :=
  (firstOrderRateRankCount m (firstOrderRateDerivativeCap R a m) : ℝ) <
    firstOrderRateSourceCount R a m (firstOrderRateDerivativeCap R a m)
      (firstOrderRateJetDegree R a m)

/-- Source count normalized by the cubic multiplicity scale.  Its limit is
`firstOrderSourceDensity R a (firstOrderRateBeta R a)`. -/
def firstOrderNormalizedSourceCount (R a : ℝ) (m : ℕ) : ℝ :=
  firstOrderRateSourceCount R a m (firstOrderRateDerivativeCap R a m)
      (firstOrderRateJetDegree R a m) / m ^ 3

/-- Local-rank count normalized by the cubic multiplicity scale.  Its limit is
`firstOrderRankDensity (firstOrderRateBeta R a)`. -/
def firstOrderNormalizedRankCount (R a : ℝ) (m : ℕ) : ℝ :=
  firstOrderRateRankCount m (firstOrderRateDerivativeCap R a m) / m ^ 3

/-- A signed-cubic upper count for the exact local rank.  The correction is allowed to be
negative below contact order `m / 2`; this is what makes one formula dominate both branches. -/
def firstOrderRankCubicUpperCount (m M : ℕ) : ℝ :=
  (∑ s ∈ Finset.range m, ((s + 1 : ℕ) : ℝ) * (M + 1)) -
    ∑ s ∈ Finset.Ico (m - M) m,
      (((2 * s + 1 : ℕ) : ℝ) - m) * (((s + M + 1 : ℕ) : ℝ) - m)

private theorem rank_correction_le_ambient {m M s : ℕ} (hs : s < m) :
    (2 * s + 1 - m) * (s + M + 1 - m) ≤ (s + 1) * (M + 1) := by
  apply Nat.mul_le_mul <;> omega

/-- The exact all-`M` local rank is bounded by the signed cubic envelope count. -/
theorem firstOrderRateRankCount_le_cubicUpperCount (m M : ℕ) :
    (firstOrderRateRankCount m M : ℝ) ≤ firstOrderRankCubicUpperCount m M := by
  rw [firstOrderRateRankCount, firstOrderRankCubicUpperCount, Nat.cast_sum]
  have hrank :
      (∑ x ∈ Finset.range m,
          (((x + 1) * (M + 1) -
            (2 * x + 1 - m) * (x + M + 1 - m) : ℕ) : ℝ)) =
        (∑ x ∈ Finset.range m, ((x + 1 : ℕ) : ℝ) * (M + 1)) -
          ∑ x ∈ Finset.range m,
            (((2 * x + 1 - m : ℕ) : ℝ) * ((x + M + 1 - m : ℕ) : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Nat.cast_sub (rank_correction_le_ambient (Finset.mem_range.mp hx))]
    push_cast
    rfl
  rw [hrank]
  gcongr
  calc
    (∑ x ∈ Finset.Ico (m - M) m,
        (((2 * x + 1 : ℕ) : ℝ) - m) * (((x + M + 1 : ℕ) : ℝ) - m)) ≤
        ∑ x ∈ Finset.Ico (m - M) m,
          (((2 * x + 1 - m : ℕ) : ℝ) * ((x + M + 1 - m : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro x hx
      have hsecond : m ≤ x + M + 1 := by
        have := (Finset.mem_Ico.mp hx).1
        omega
      by_cases hfirst : m ≤ 2 * x + 1
      · rw [Nat.cast_sub hfirst, Nat.cast_sub hsecond]
      · have hsigned : ((2 * x + 1 : ℕ) : ℝ) - m < 0 := by
          exact sub_neg.mpr (Nat.cast_lt.mpr (show 2 * x + 1 < m by omega))
        have hnonneg : 0 ≤ ((x + M + 1 : ℕ) : ℝ) - m := by
          exact sub_nonneg.mpr (Nat.cast_le.mpr hsecond)
        exact (mul_nonpos_of_nonpos_of_nonneg hsigned.le hnonneg).trans
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ ≤ ∑ x ∈ Finset.range m,
          (((2 * x + 1 - m : ℕ) : ℝ) * ((x + M + 1 - m : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
      · intro x _ _
        positivity

private def sumRangeLinear (x : ℝ) : ℝ := x * (x - 1) / 2

private def sumRangeSquare (x : ℝ) : ℝ := x * (x - 1) * (2 * x - 1) / 6

private theorem sum_range_natCast (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ)) = sumRangeLinear n := by
  induction n with
  | zero => simp [sumRangeLinear]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [sumRangeLinear]
      push_cast
      ring

private theorem sum_range_sq_natCast (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) = sumRangeSquare n := by
  induction n with
  | zero => simp [sumRangeSquare]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [sumRangeSquare]
      push_cast
      ring

private theorem cubicUpperCount_eq_formula {m M : ℕ} (hM : M ≤ m) :
    firstOrderRankCubicUpperCount m M =
      (M + 1) * (sumRangeLinear m + m) -
        (2 * (sumRangeSquare m - sumRangeSquare (m - M)) +
          (2 * M + 3 - 3 * m) *
            (sumRangeLinear m - sumRangeLinear (m - M)) +
          (m - (m - M)) * (1 - m) * (M + 1 - m)) := by
  rw [firstOrderRankCubicUpperCount]
  have hIco : Finset.Ico (m - M) m ⊆ Finset.range m := by
    intro x hx
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
  have hamb (n : ℕ) :
      (∑ x ∈ Finset.range n, ((x + 1 : ℕ) : ℝ) * (M + 1)) =
        (M + 1) * (sumRangeLinear n + n) := by
    calc
      _ = (M + 1 : ℝ) * ((∑ x ∈ Finset.range n, (x : ℝ)) + n) := by
        push_cast
        ring_nf
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        rw [← Finset.sum_mul]
        ring
      _ = _ := by rw [sum_range_natCast]
  have hcorrection (n : ℕ) :
      (∑ x ∈ Finset.range n,
        (((2 * x + 1 : ℕ) : ℝ) - m) * (((x + M + 1 : ℕ) : ℝ) - m)) =
        2 * sumRangeSquare n + (2 * M + 3 - 3 * m) * sumRangeLinear n +
          n * (1 - m) * (M + 1 - m) := by
    calc
      _ = ∑ x ∈ Finset.range n,
          (2 * (x : ℝ) ^ 2 + (2 * M + 3 - 3 * m) * x +
            (1 - m) * (M + 1 - m)) := by
        apply Finset.sum_congr rfl
        intro x _
        push_cast
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, sum_range_natCast,
          sum_range_sq_natCast]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  rw [Finset.sum_Ico_eq_sub _ (Nat.sub_le m M)]
  rw [hamb, hcorrection, hcorrection]
  rw [Nat.cast_sub hM]
  simp only [sumRangeLinear, sumRangeSquare]
  ring

/-- Challenge height obtained from the conservative finite source and exact rank counts. -/
def firstOrderRateChallengeDegree (R a : ℝ) (m : ℕ) : ℕ :=
  let r := firstOrderRateRankCount m (firstOrderRateDerivativeCap R a m)
  let N₀ := firstOrderRateSourceCount R a m (firstOrderRateDerivativeCap R a m)
    (firstOrderRateJetDegree R a m)
  max 1 (Nat.floor (r * firstOrderRateJetDegree R a m / (N₀ - r)))

/-- A checked finite choice.  All data depend only on `R` and `a`, before the block length,
field, evaluation set, or received word is chosen. -/
structure FirstOrderFiniteRateParameters (R a : ℝ) where
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  surplus : FirstOrderFiniteRateTest R a multiplicity

namespace FirstOrderFiniteRateParameters

variable {R a : ℝ} (p : FirstOrderFiniteRateParameters R a)

/-- Derivative cap belonging to a checked finite parameter choice. -/
def derivativeCap : ℕ := firstOrderRateDerivativeCap R a p.multiplicity

/-- Total jet cap belonging to a checked finite parameter choice. -/
def jetDegree : ℕ := firstOrderRateJetDegree R a p.multiplicity

/-- Exact local-rank count belonging to a checked finite parameter choice. -/
def rankCount : ℕ := firstOrderRateRankCount p.multiplicity p.derivativeCap

/-- Uniform source lower count belonging to a checked finite parameter choice. -/
def sourceCount : ℝ :=
  firstOrderRateSourceCount R a p.multiplicity p.derivativeCap p.jetDegree

/-- Symbolic challenge-degree bound belonging to a checked finite parameter choice. -/
def challengeDegree : ℕ := firstOrderRateChallengeDegree R a p.multiplicity

theorem sourceCount_gt_rankCount : (p.rankCount : ℝ) < p.sourceCount := p.surplus

end FirstOrderFiniteRateParameters

/-! ## Termination of the multiplicity search from normalized limits -/

/-- Once the normalized finite source and rank sums have their paper limits, strict analytic
surplus makes the search for a finite multiplicity terminate.  This lemma isolates the generic
topological step from the two concrete finite-sum convergence proofs. -/
theorem exists_firstOrderFiniteRateParameters_of_tendsto {R a : ℝ}
    (hsource : Filter.Tendsto (firstOrderNormalizedSourceCount R a) Filter.atTop
      (nhds (firstOrderSourceDensity R a (firstOrderRateBeta R a))))
    (hrank : Filter.Tendsto (firstOrderNormalizedRankCount R a) Filter.atTop
      (nhds (firstOrderRankDensity (firstOrderRateBeta R a))))
    (hsurplus : firstOrderRankDensity (firstOrderRateBeta R a) <
      firstOrderSourceDensity R a (firstOrderRateBeta R a)) :
    Nonempty (FirstOrderFiniteRateParameters R a) := by
  have heventually : ∀ᶠ m in Filter.atTop,
      firstOrderNormalizedRankCount R a m < firstOrderNormalizedSourceCount R a m :=
    Filter.Tendsto.eventually_lt hrank hsource hsurplus
  obtain ⟨m, hm, hmpos⟩ :=
    (heventually.and (Filter.eventually_ge_atTop 1)).exists
  refine ⟨⟨m, hmpos, ?_⟩⟩
  have hscale : (0 : ℝ) < (m : ℝ) ^ 3 := pow_pos (Nat.cast_pos.mpr hmpos) _
  rw [firstOrderNormalizedRankCount, firstOrderNormalizedSourceCount] at hm
  exact (div_lt_div_iff_of_pos_right hscale).mp hm

/-- The analytic first-order surplus reduces automatic parameter existence to the two normalized
finite-sum limits. -/
theorem exists_firstOrderFiniteRateParameters_of_rate_limits {R a : ℝ}
    (hR : 0 < R) (hRa : R < a) (haone : a < 1)
    (hthreshold : firstOrderRateThreshold R < a)
    (hsource : Filter.Tendsto (firstOrderNormalizedSourceCount R a) Filter.atTop
      (nhds (firstOrderSourceDensity R a (firstOrderRateBeta R a))))
    (hrank : Filter.Tendsto (firstOrderNormalizedRankCount R a) Filter.atTop
      (nhds (firstOrderRankDensity (firstOrderRateBeta R a)))) :
    Nonempty (FirstOrderFiniteRateParameters R a) :=
  exists_firstOrderFiniteRateParameters_of_tendsto hsource hrank
    (firstOrderRate_surplus_pos hR hRa haone hthreshold)

/-! ## Identification with the existing local-rank budget -/

private theorem weightedHigherJetCount_one_zero_add (s : ℕ) :
    weightedHigherJetCount 1 (0 + s) = 1 := by
  rw [weightedHigherJetCount, show weightedHigherJetTuples 1 (0 + s) = {default} by
    ext c
    simp only [mem_weightedHigherJetTuples, Finset.mem_singleton]
    constructor
    · intro _
      funext i
      exact Fin.elim0 i
    · intro _
      simp [higherJetTupleWeight]]
  simp

/-- For first order and zero higher-jet budget, the generic certified rank is exactly the
paper's explicit all-`M` rank sum. -/
theorem certifiedEnlargedRankBound_one_eq_firstOrderRateRankCount (m M : ℕ) :
    certifiedEnlargedRankBound 1 m M 0 = firstOrderRateRankCount m M := by
  rw [certifiedEnlargedRankBound, firstOrderRateRankCount]
  apply Finset.sum_congr rfl
  intro s hs
  rw [weightedHigherJetCount_one_zero_add]
  simp only [one_mul]
  unfold certifiedContactRankBudget contactThreshold exhibitedKernelResidualCount
    ambientContactCount exhibitedKernelContactCount
  have hslt : s < m := Finset.mem_range.mp hs
  have hsub : (m - s) ⌈/⌉ 1 = m - s := by simp
  rw [hsub]
  have hfirst : s + 1 - (m - s) = 2 * s + 1 - m := by omega
  have hsecond : M + 1 - (m - s) = s + M + 1 - m := by omega
  rw [hfirst, hsecond]

/-! ## Uniform transfer from rate data to the actual support dimension -/

private theorem rate_source_summand_le_residual {R a : ℝ} {n D A m t b : ℕ}
    (hD : (D : ℝ) ≤ R * n) (hA : a * n ≤ A) :
    n * max (m * a - R * t) 0 ≤ (m * A + b - D * t : ℕ) := by
  by_cases hx : 0 ≤ m * a - R * t
  · rw [max_eq_left hx]
    have hbase : (n : ℝ) * (m * a - R * t) ≤ m * A - D * t := by
      have hm : 0 ≤ (m : ℝ) * ((A : ℝ) - a * n) :=
        mul_nonneg (by positivity) (sub_nonneg.mpr hA)
      have ht : 0 ≤ (t : ℝ) * (R * n - D) :=
        mul_nonneg (by positivity) (sub_nonneg.mpr hD)
      nlinarith
    have hreal : (D * t : ℕ) ≤ (m * A + b : ℕ) := by
      exact_mod_cast (show ((D * t : ℕ) : ℝ) ≤ ((m * A + b : ℕ) : ℝ) by
        push_cast
        nlinarith [hbase])
    have hnat : D * t ≤ m * A + b := hreal
    rw [Nat.cast_sub hnat]
    push_cast
    nlinarith
  · rw [max_eq_right (le_of_not_ge hx)]
    simp only [mul_zero]
    exact Nat.cast_nonneg (α := ℝ) _

/-- Every rate-compatible ambient degree and agreement threshold has actual support dimension at
least `n * N₀`.  This is the key reason that the finite recipe has no hidden lower bound on
`k / n`. -/
theorem firstOrderRateSourceCount_le_dimensionCount {R a : ℝ} {n D A m M mu : ℕ}
    (hD : (D : ℝ) ≤ R * n) (hA : a * n ≤ A) :
    n * firstOrderRateSourceCount R a m M mu ≤
      firstOrderDimensionCount D A m M mu := by
  rw [firstOrderRateSourceCount, firstOrderDimensionCount]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  have hc : min (t : ℝ) (M : ℝ) + 1 = ((min t M + 1 : ℕ) : ℝ) := by
    norm_cast
  rw [hc]
  rw [show (n : ℝ) * ((min t M + 1 : ℕ) * max (m * a - R * t) 0) =
      ∑ _b ∈ Finset.range (min t M + 1),
        (n : ℝ) * max (m * a - R * t) 0 by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring]
  apply Finset.sum_le_sum
  intro b hb
  exact rate_source_summand_le_residual hD hA

/-- The kernel-height quotient is uniform in the block length once `N₀` exceeds the local rank.
This is the arithmetic behind the finite challenge degree in the rate recipe. -/
theorem scaledKernelHeight_le_rateChallengeDegree {n N r mu : ℕ} {N₀ : ℝ}
    (hn : 0 < n) (hsurplus : (r : ℝ) < N₀) (hN : n * N₀ ≤ N) :
    n * r * mu / (N - n * r) ≤
      max 1 (Nat.floor (r * mu / (N₀ - r))) := by
  have hnrNreal : ((n * r : ℕ) : ℝ) < (N : ℕ) := by
    calc
      ((n * r : ℕ) : ℝ) = (n : ℝ) * r := by push_cast; ring
      _ < (n : ℝ) * N₀ := mul_lt_mul_of_pos_left hsurplus (Nat.cast_pos.mpr hn)
      _ ≤ N := hN
  have hnrN : n * r < N := by exact_mod_cast hnrNreal
  have hdenNat : 0 < N - n * r := Nat.sub_pos_of_lt hnrN
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
        apply div_le_div_of_nonneg_left (by positivity)
          (mul_pos (Nat.cast_pos.mpr hn) hgap)
          hdenLower
      _ = (r : ℝ) * mu / (N₀ - r) := by
        field_simp [ne_of_gt (Nat.cast_pos.mpr hn), ne_of_gt hgap]
  have hcast : ((n * r * mu / (N - n * r) : ℕ) : ℝ) ≤
      (r : ℝ) * mu / (N₀ - r) :=
    (Nat.cast_div_le (m := n * r * mu) (n := N - n * r)).trans hfrac
  have hfloor : n * r * mu / (N - n * r) ≤
      Nat.floor ((r : ℝ) * mu / (N₀ - r)) := Nat.le_floor hcast
  exact hfloor.trans (le_max_right _ _)

/-! ## Rational executable interface -/

/-- Rational version of the finite source sum.  It is definitionally finite and decidable. -/
def firstOrderRationalSourceCount (R a : ℚ) (m M mu : ℕ) : ℚ :=
  ∑ t ∈ Finset.range (mu + 1),
    (min t M + 1 : ℕ) * max (m * a - R * t) 0

/-- Decidable rational certificate test corresponding exactly to `FirstOrderFiniteRateTest`. -/
def FirstOrderRationalFiniteTest (R a : ℚ) (m : ℕ) : Prop :=
  let beta : ℚ := 3 * (1 - a) / (2 * (2 - R))
  let M := Nat.floor (beta * m)
  let mu := Nat.ceil (m * a / R)
  (firstOrderRateRankCount m M : ℚ) < firstOrderRationalSourceCount R a m M mu

instance (R a : ℚ) (m : ℕ) : Decidable (FirstOrderRationalFiniteTest R a m) :=
  by unfold FirstOrderRationalFiniteTest; infer_instance

end


end ReedSolomon.HiddenDerivative
