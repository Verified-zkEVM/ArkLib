/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.RateBound
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.RoundedCounts
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Finite first-order rate parameters

At rate `R` and agreement fraction `a`, the rounded first-order recipe chooses a derivative cap
`⌊βm⌋₊` and a total jet-degree cap `⌈ma/R⌉₊`, where `β` is the rate ratio. A finite
parameter certificate records a positive multiplicity at which the source count exceeds the local
rank count. The module also relates the rate source count to the dimension of the interpolation
space and provides a rational, decidable form of the finite test.

## Main statements

* `firstOrderRateDerivativeCap`, `firstOrderRateJetDegree`, and `FirstOrderFiniteRateTest` define
  the rounded caps and the strict finite surplus condition.
* `FirstOrderFiniteRateParameters` packages a positive multiplicity satisfying that condition.
* `firstOrderRateChallengeDegree` defines the challenge-height bound from the finite counts.
* `exists_firstOrderFiniteRateParameters_of_tendsto` derives such a certificate from strict
  surplus between the normalized limits.
* `firstOrderNormalizedSourceCount` and `firstOrderNormalizedRankCount` record the normalized
  counts used by the existence theorem.
* `FirstOrderRationalFiniteTest` gives a decidable rational instance of the finite test.

## References

* [DKT26]
-/

@[expose] public section

open Filter Topology

namespace ReedSolomon.HiddenDerivative

noncomputable section

/-- The rounded first-order derivative cap `⌊β(R, a) m⌋₊`. -/
def firstOrderRateDerivativeCap (rate agreement : ℝ) (m : ℕ) : ℕ :=
  Nat.floor (firstOrderRateBeta rate agreement * m)

/-- The rounded total jet-degree cap `⌈m a / R⌉₊`. -/
def firstOrderRateJetDegree (rate agreement : ℝ) (m : ℕ) : ℕ :=
  Nat.ceil (m * agreement / rate)

/-- The strict finite surplus condition for the rounded first-order parameters. -/
def FirstOrderFiniteRateTest (rate agreement : ℝ) (m : ℕ) : Prop :=
  (firstOrderRankCount m (firstOrderRateDerivativeCap rate agreement m) : ℝ) <
    firstOrderSourceCount rate agreement m (firstOrderRateDerivativeCap rate agreement m)
      (firstOrderRateJetDegree rate agreement m)

/-- The source count divided by the cubic multiplicity scale at the rounded rate parameters. -/
def firstOrderNormalizedSourceCount (rate agreement : ℝ) (m : ℕ) : ℝ :=
  firstOrderSourceCount rate agreement m (firstOrderRateDerivativeCap rate agreement m)
    (firstOrderRateJetDegree rate agreement m) / m ^ 3

/-- The local-rank count divided by the cubic multiplicity scale at the rounded rate parameters. -/
def firstOrderNormalizedRankCount (rate agreement : ℝ) (m : ℕ) : ℝ :=
  firstOrderRankCount m (firstOrderRateDerivativeCap rate agreement m) / m ^ 3

/-- The challenge degree obtained from the rounded source and rank counts. -/
def firstOrderRateChallengeDegree (rate agreement : ℝ) (m : ℕ) : ℕ :=
  let rank := firstOrderRankCount m (firstOrderRateDerivativeCap rate agreement m)
  let count := firstOrderSourceCount rate agreement m
    (firstOrderRateDerivativeCap rate agreement m) (firstOrderRateJetDegree rate agreement m)
  max 1 (Nat.floor (rank * firstOrderRateJetDegree rate agreement m / (count - rank)))

/-- A positive multiplicity whose rounded source count strictly exceeds its local rank count. -/
structure FirstOrderFiniteRateParameters (rate agreement : ℝ) where
  /-- The selected multiplicity. -/
  multiplicity : ℕ
  /-- The selected multiplicity is positive. -/
  multiplicity_pos : 0 < multiplicity
  /-- The source count at this multiplicity strictly exceeds the local rank count. -/
  surplus : FirstOrderFiniteRateTest rate agreement multiplicity

namespace FirstOrderFiniteRateParameters

variable {rate agreement : ℝ} (p : FirstOrderFiniteRateParameters rate agreement)

/-- The derivative cap belonging to a finite rate parameter certificate. -/
def derivativeCap : ℕ := firstOrderRateDerivativeCap rate agreement p.multiplicity

/-- The total jet-degree cap belonging to a finite rate parameter certificate. -/
def jetDegree : ℕ := firstOrderRateJetDegree rate agreement p.multiplicity

/-- The local-rank count belonging to a finite rate parameter certificate. -/
def rankCount : ℕ := firstOrderRankCount p.multiplicity p.derivativeCap

/-- The source count belonging to a finite rate parameter certificate. -/
def sourceCount : ℝ :=
  firstOrderSourceCount rate agreement p.multiplicity p.derivativeCap p.jetDegree

/-- The challenge degree belonging to a finite rate parameter certificate. -/
def challengeDegree : ℕ :=
  firstOrderRateChallengeDegree rate agreement p.multiplicity

/-- The source count strictly exceeds the local-rank count in a finite rate parameter certificate.
-/
theorem sourceCount_gt_rankCount : (p.rankCount : ℝ) < p.sourceCount := p.surplus

end FirstOrderFiniteRateParameters

/-! ## Existence from normalized limits -/

/-- Strict surplus between the normalized limits yields a finite positive multiplicity with
strict finite surplus. -/
theorem exists_firstOrderFiniteRateParameters_of_tendsto {rate agreement : ℝ}
    (hsource : Filter.Tendsto (firstOrderNormalizedSourceCount rate agreement) Filter.atTop
      (nhds (firstOrderSourceDensity rate agreement (firstOrderRateBeta rate agreement))))
    (hrank : Filter.Tendsto (firstOrderNormalizedRankCount rate agreement) Filter.atTop
      (nhds (firstOrderRankDensity (firstOrderRateBeta rate agreement))))
    (hsurplus : firstOrderRankDensity (firstOrderRateBeta rate agreement) <
      firstOrderSourceDensity rate agreement (firstOrderRateBeta rate agreement)) :
    Nonempty (FirstOrderFiniteRateParameters rate agreement) := by
  have heventually : ∀ᶠ m in Filter.atTop,
      firstOrderNormalizedRankCount rate agreement m <
        firstOrderNormalizedSourceCount rate agreement m :=
    Filter.Tendsto.eventually_lt hrank hsource hsurplus
  obtain ⟨m, hm, hmge⟩ :=
    (heventually.and (Filter.eventually_ge_atTop 1)).exists
  have hmpos : 0 < m := by omega
  refine ⟨⟨m, hmpos, ?_⟩⟩
  have hscale : (0 : ℝ) < (m : ℝ) ^ 3 := pow_pos (Nat.cast_pos.mpr hmpos) _
  rw [firstOrderNormalizedRankCount, firstOrderNormalizedSourceCount] at hm
  exact (div_lt_div_iff_of_pos_right hscale).mp hm

/-- Above the first-order rate threshold, strict surplus between the normalized limits gives a
finite positive multiplicity with strict finite surplus. -/
theorem exists_firstOrderFiniteRateParameters_of_rate_limits {rate agreement : ℝ}
    (hrate : 0 < rate) (hrateAgreement : rate < agreement) (hagreement : agreement < 1)
    (hthreshold : firstOrderRateThreshold rate < agreement)
    (hsource : Filter.Tendsto (firstOrderNormalizedSourceCount rate agreement) Filter.atTop
      (nhds (firstOrderSourceDensity rate agreement (firstOrderRateBeta rate agreement))))
    (hrank : Filter.Tendsto (firstOrderNormalizedRankCount rate agreement) Filter.atTop
      (nhds (firstOrderRankDensity (firstOrderRateBeta rate agreement)))) :
    Nonempty (FirstOrderFiniteRateParameters rate agreement) :=
  exists_firstOrderFiniteRateParameters_of_tendsto hsource hrank
    (firstOrderRate_surplus_pos hrate hrateAgreement hagreement hthreshold)

/-! ## Rational finite test -/

/-- The rational first-order source count used by the decidable finite test. -/
def firstOrderRationalSourceCount (rate agreement : ℚ) (m M mu : ℕ) : ℚ :=
  ∑ t ∈ Finset.range (mu + 1),
    (min t M + 1 : ℕ) * max (m * agreement - rate * t) 0

/-- The decidable rational finite surplus test for the rounded first-order parameters. -/
def FirstOrderRationalFiniteTest (rate agreement : ℚ) (m : ℕ) : Prop :=
  let beta : ℚ := 3 * (1 - agreement) / (2 * (2 - rate))
  let derivativeCap := Nat.floor (beta * m)
  let jetDegree := Nat.ceil (m * agreement / rate)
  (firstOrderRankCount m derivativeCap : ℚ) <
    firstOrderRationalSourceCount rate agreement m derivativeCap jetDegree

/-- The rational finite surplus test can be evaluated by computation. -/
instance (rate agreement : ℚ) (m : ℕ) :
    Decidable (FirstOrderRationalFiniteTest rate agreement m) :=
  by unfold FirstOrderRationalFiniteTest; infer_instance

end

end ReedSolomon.HiddenDerivative
