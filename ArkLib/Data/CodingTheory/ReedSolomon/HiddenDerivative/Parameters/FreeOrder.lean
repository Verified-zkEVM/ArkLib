/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Pratyush Mishra
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Positivity

/-!
# Rounded estimates at a free derivative order

The discrete interpolation argument does not require the derivative order to be a prescribed
function of the agreement parameter. This file exposes that fact by proving the rounded budget
estimates for an arbitrary positive order `d`.

The proofs are adapted, with permission, from `rs-ld-mca` commit
`9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`. They exclude the donor's two Kopparty axioms and its
non-executable cost wrapper. The rank-threshold theorem at the end is pointwise in
`(epsilon, theta)`; it is not, by itself, the desired rate-uniform `d(delta)` theorem.
-/

namespace ReedSolomon
namespace HiddenDerivative

noncomputable section

/-- The integer threshold `ceil(epsilon n)` represents the corresponding real inequality. -/
theorem agreementThreshold_le_iff (epsilon : ℝ) (n A : ℕ) :
    agreementThreshold epsilon n ≤ A ↔ epsilon * (n : ℝ) ≤ (A : ℝ) := by
  simp [agreementThreshold]

/-- The real target never exceeds its integer ceiling. -/
theorem le_agreementThreshold (epsilon : ℝ) (n : ℕ) :
    epsilon * (n : ℝ) ≤ agreementThreshold epsilon n := by
  simpa [agreementThreshold] using Nat.le_ceil (epsilon * (n : ℝ))

/-- A positive agreement fraction and nonempty block give a positive threshold. -/
theorem agreementThreshold_pos {epsilon : ℝ} {n : ℕ} (hepsilon : 0 < epsilon)
    (hn : 0 < n) : 0 < agreementThreshold epsilon n := by
  rw [agreementThreshold, Nat.ceil_pos]
  positivity

/-- The free multiplicity is positive at positive derivative order. -/
theorem multiplicity_pos {d : ℕ} (hd : 0 < d) :
    0 < multiplicity d := by
  simp [multiplicity, hd]

/-- The ambient dimension is strictly below the block length in the scoped regime. -/
theorem ambientDimension_lt_blockLength {epsilon theta : ℝ} {n : ℕ}
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon < 1) (htheta : 0 < theta)
    (hthetaOne : theta < 1) (hn : 0 < n) :
    ambientDimension epsilon theta n < n := by
  have hthetaFactor : 0 ≤ 1 - theta := by linarith
  have hfactor : (1 - theta) * epsilon < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_right (by linarith) hepsilon.le hepsilonOne
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [ambientDimension, Nat.floor_lt]
  · simpa using mul_lt_mul_of_pos_right hfactor hnReal
  · positivity

/-- Membership below the rounded ambient dimension is the unrounded real inequality. -/
theorem le_ambientDimension_iff {epsilon theta : ℝ} {n k : ℕ}
    (hepsilon : 0 ≤ epsilon) (htheta : theta ≤ 1) :
    k ≤ ambientDimension epsilon theta n ↔
      (k : ℝ) ≤ (1 - theta) * epsilon * (n : ℝ) := by
  rw [ambientDimension, Nat.le_floor_iff]
  positivity

/-- If the free order is below the ambient dimension, then the block is nonempty. -/
theorem blockLength_pos_of_order_lt_ambientDimension {epsilon theta : ℝ} {d n : ℕ}
    (hdK : d < ambientDimension epsilon theta n) : 0 < n := by
  by_contra hn
  have hnZero : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  simp [ambientDimension] at hdK

/-- The scope hypothesis `d < K`, for positive `d`, makes `K - 1` positive. -/
theorem interpolationDenominator_pos {epsilon theta : ℝ} {d n : ℕ}
    (hd : 0 < d) (hdK : d < ambientDimension epsilon theta n) :
    0 < ambientDimension epsilon theta n - 1 := by
  have hK : 1 < ambientDimension epsilon theta n := lt_of_le_of_lt hd hdK
  omega

/-- The interpolation degree budget is positive in the scoped parameter regime. -/
theorem interpolationDegreeBudget_pos {epsilon theta : ℝ} {d n : ℕ}
    (hepsilon : 0 < epsilon) (hd : 0 < d) (hn : 0 < n)
    (hdK : d < ambientDimension epsilon theta n) :
    0 < interpolationDegreeBudget d epsilon theta n := by
  rw [interpolationDegreeBudget, Nat.ceil_pos]
  apply div_pos
  · exact_mod_cast Nat.mul_pos (multiplicity_pos hd) (agreementThreshold_pos hepsilon hn)
  · exact_mod_cast interpolationDenominator_pos hd hdK

/-- Rounding `mA/(K-1)` upward gives `mA ≤ B(K-1)`. -/
theorem multiplicity_mul_agreementThreshold_le_budget_mul_denominator
    {epsilon theta : ℝ} {d n : ℕ} (hd : 0 < d)
    (hdK : d < ambientDimension epsilon theta n) :
    multiplicity d * agreementThreshold epsilon n ≤
      interpolationDegreeBudget d epsilon theta n *
        (ambientDimension epsilon theta n - 1) := by
  have hdenNat : 0 < ambientDimension epsilon theta n - 1 :=
    interpolationDenominator_pos hd hdK
  have hdenReal : 0 < ((ambientDimension epsilon theta n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hdenNat
  have hceil :
      (((multiplicity d * agreementThreshold epsilon n : ℕ) : ℝ) /
          ((ambientDimension epsilon theta n - 1 : ℕ) : ℝ)) ≤
        (interpolationDegreeBudget d epsilon theta n : ℝ) := by
    simpa [interpolationDegreeBudget] using
      Nat.le_ceil
        (((multiplicity d * agreementThreshold epsilon n : ℕ) : ℝ) /
          ((ambientDimension epsilon theta n - 1 : ℕ) : ℝ))
  have hreal :
      ((multiplicity d * agreementThreshold epsilon n : ℕ) : ℝ) ≤
        (interpolationDegreeBudget d epsilon theta n : ℝ) *
          ((ambientDimension epsilon theta n - 1 : ℕ) : ℝ) :=
    (div_le_iff₀ hdenReal).mp hceil
  exact_mod_cast hreal

/-- A coarse weighted contribution below `mA` lies within the rounded degree budget. -/
theorem le_interpolationDegreeBudget_of_mul_denominator_lt
    {epsilon theta : ℝ} {d n t : ℕ} (hd : 0 < d)
    (hdK : d < ambientDimension epsilon theta n)
    (ht : t * (ambientDimension epsilon theta n - 1) <
      multiplicity d * agreementThreshold epsilon n) :
    t ≤ interpolationDegreeBudget d epsilon theta n := by
  by_contra hnot
  have hBt : interpolationDegreeBudget d epsilon theta n < t := Nat.lt_of_not_ge hnot
  have hden : 0 < ambientDimension epsilon theta n - 1 :=
    interpolationDenominator_pos hd hdK
  have hmul :
      interpolationDegreeBudget d epsilon theta n *
          (ambientDimension epsilon theta n - 1) <
        t * (ambientDimension epsilon theta n - 1) :=
    Nat.mul_lt_mul_of_pos_right hBt hden
  have hbudget :=
    multiplicity_mul_agreementThreshold_le_budget_mul_denominator hd hdK
  exact (not_lt_of_ge hbudget) (hmul.trans ht)

/-- The ordinary higher-jet cutoff is bounded by its unrounded value. -/
theorem higherJetDegreeBudget_cast_le {theta : ℝ} {d : ℕ} (htheta : 0 ≤ theta) :
    (higherJetDegreeBudget theta d : ℝ) ≤
      (1 + 3 * theta / 4) * (multiplicity d : ℝ) := by
  rw [higherJetDegreeBudget]
  apply Nat.floor_le
  positivity

/-- The rectangular width is bounded by its unrounded value. -/
theorem interpolationBoxWidth_cast_le {theta : ℝ} {d : ℕ} (htheta : 0 ≤ theta) :
    (interpolationBoxWidth theta d : ℝ) ≤
      theta * (multiplicity d : ℝ) / 16 := by
  rw [interpolationBoxWidth]
  apply Nat.floor_le
  positivity

/-- The higher-jet cutoff and three box coordinates fit under `(1 + 15 theta / 16)m`. -/
theorem higherJetDegreeBudget_add_three_boxWidth_cast_le {theta : ℝ} {d : ℕ}
    (htheta : 0 ≤ theta) :
    ((higherJetDegreeBudget theta d + 3 * interpolationBoxWidth theta d : ℕ) : ℝ) ≤
      (1 + 15 * theta / 16) * (multiplicity d : ℝ) := by
  push_cast
  have hC := higherJetDegreeBudget_cast_le (d := d) htheta
  have hH := interpolationBoxWidth_cast_le (d := d) htheta
  nlinarith

/-- The rectangular monomials satisfy the strict global weighted-degree budget. -/
theorem boxFamily_weightedBudget_lt {epsilon theta : ℝ} {d n : ℕ}
    (hepsilon : 0 < epsilon) (htheta : 0 < theta) (hthetaOne : theta < 1)
    (hd : 0 < d) (hn : 0 < n) :
    (ambientDimension epsilon theta n - 1) *
        (higherJetDegreeBudget theta d + 3 * interpolationBoxWidth theta d) <
      multiplicity d * agreementThreshold epsilon n := by
  have hfactor : (1 - theta) * (1 + 15 * theta / 16) < 1 := by
    nlinarith [mul_pos htheta (sub_pos.mpr hthetaOne)]
  have hm : 0 < (multiplicity d : ℝ) := by exact_mod_cast multiplicity_pos hd
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hx : 0 ≤ (1 - theta) * epsilon * (n : ℝ) := by positivity
  have hK :
      (ambientDimension epsilon theta n : ℝ) ≤ (1 - theta) * epsilon * (n : ℝ) := by
    simpa [ambientDimension] using Nat.floor_le hx
  have hKSub :
      ((ambientDimension epsilon theta n - 1 : ℕ) : ℝ) ≤
        (1 - theta) * epsilon * (n : ℝ) :=
    (Nat.cast_le.mpr (Nat.sub_le _ _)).trans hK
  have hcut := higherJetDegreeBudget_add_three_boxWidth_cast_le (d := d) htheta.le
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hcut
  have hmain :
      (((ambientDimension epsilon theta n - 1) *
        (higherJetDegreeBudget theta d + 3 * interpolationBoxWidth theta d) : ℕ) : ℝ) <
        (multiplicity d : ℝ) * (epsilon * (n : ℝ)) := by
    push_cast
    calc
      ((ambientDimension epsilon theta n - 1 : ℕ) : ℝ) *
          ((higherJetDegreeBudget theta d : ℝ) + 3 * (interpolationBoxWidth theta d : ℝ)) ≤
          ((ambientDimension epsilon theta n - 1 : ℕ) : ℝ) *
            ((1 + 15 * theta / 16) * (multiplicity d : ℝ)) := by gcongr
      _ ≤ ((1 - theta) * epsilon * (n : ℝ)) *
            ((1 + 15 * theta / 16) * (multiplicity d : ℝ)) := by gcongr
      _ = ((1 - theta) * (1 + 15 * theta / 16)) *
            ((multiplicity d : ℝ) * (epsilon * (n : ℝ))) := by ring
      _ < 1 * ((multiplicity d : ℝ) * (epsilon * (n : ℝ))) := by
        exact mul_lt_mul_of_pos_right hfactor (by positivity)
      _ = (multiplicity d : ℝ) * (epsilon * (n : ℝ)) := by ring
  have hA : epsilon * (n : ℝ) ≤ (agreementThreshold epsilon n : ℝ) :=
    le_agreementThreshold epsilon n
  have hfinal :
      (((ambientDimension epsilon theta n - 1) *
        (higherJetDegreeBudget theta d + 3 * interpolationBoxWidth theta d) : ℕ) : ℝ) <
        ((multiplicity d * agreementThreshold epsilon n : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hmain ⊢
    exact hmain.trans_le (mul_le_mul_of_nonneg_left hA hm.le)
  exact_mod_cast hfinal

/-- The rectangular width is at most the multiplicity. -/
theorem interpolationBoxWidth_le_multiplicity {theta : ℝ} {d : ℕ}
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    interpolationBoxWidth theta d ≤ multiplicity d := by
  have hH := interpolationBoxWidth_cast_le (d := d) htheta.le
  have hm : 0 ≤ (multiplicity d : ℝ) := by positivity
  have hthetaSixteen : theta / 16 ≤ 1 := by linarith
  have hreal : (interpolationBoxWidth theta d : ℝ) ≤ (multiplicity d : ℝ) := by
    calc
      (interpolationBoxWidth theta d : ℝ) ≤
          theta * (multiplicity d : ℝ) / 16 := hH
      _ = (theta / 16) * (multiplicity d : ℝ) := by ring
      _ ≤ 1 * (multiplicity d : ℝ) :=
        mul_le_mul_of_nonneg_right hthetaSixteen hm
      _ = (multiplicity d : ℝ) := one_mul _
  exact_mod_cast hreal

/-- The three exact slack conditions consumed by the rectangular dimension theorem. -/
theorem freeGlobalDimensionSlacks {epsilon theta : ℝ} {d n : ℕ}
    (hepsilon : 0 < epsilon) (htheta : 0 < theta) (hthetaOne : theta < 1)
    (hd : 0 < d) (hn : 0 < n) (hdK : d < ambientDimension epsilon theta n) :
    interpolationBoxWidth theta d ≤ multiplicity d ∧
      higherJetDegreeBudget theta d + 2 * interpolationBoxWidth theta d ≤
        interpolationDegreeBudget d epsilon theta n ∧
      (ambientDimension epsilon theta n - 1) *
          (higherJetDegreeBudget theta d + 3 * interpolationBoxWidth theta d) ≤
        multiplicity d * agreementThreshold epsilon n := by
  have hweighted := boxFamily_weightedBudget_lt hepsilon htheta hthetaOne hd hn
  refine ⟨interpolationBoxWidth_le_multiplicity htheta hthetaOne, ?_, hweighted.le⟩
  apply le_interpolationDegreeBudget_of_mul_denominator_lt hd hdK
  calc
    (higherJetDegreeBudget theta d + 2 * interpolationBoxWidth theta d) *
          (ambientDimension epsilon theta n - 1) =
        (ambientDimension epsilon theta n - 1) *
          (higherJetDegreeBudget theta d + 2 * interpolationBoxWidth theta d) := by ac_rfl
    _ ≤ (ambientDimension epsilon theta n - 1) *
          (higherJetDegreeBudget theta d + 3 * interpolationBoxWidth theta d) := by
      gcongr
      omega
    _ < multiplicity d * agreementThreshold epsilon n := hweighted

/-- If the unrounded width is at least two, taking its floor loses at most a factor of two. -/
theorem half_interpolationBoxWidthTarget_le_cast {theta : ℝ} {d : ℕ}
    (hlarge : 2 ≤ theta * (multiplicity d : ℝ) / 16) :
    theta * (multiplicity d : ℝ) / 32 ≤ (interpolationBoxWidth theta d : ℝ) := by
  have hfloor := Nat.div_two_lt_floor
    (a := theta * (multiplicity d : ℝ) / 16) (by linarith)
  rw [interpolationBoxWidth]
  calc
    theta * (multiplicity d : ℝ) / 32 =
        (theta * (multiplicity d : ℝ) / 16) / 2 := by ring
    _ ≤ (⌊theta * (multiplicity d : ℝ) / 16⌋₊ : ℝ) := hfloor.le

/-- An explicit order threshold making the unrounded box width at least two. -/
theorem exists_orderThreshold_for_boxWidth {theta : ℝ} (htheta : 0 < theta) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → 2 ≤ theta * (multiplicity d : ℝ) / 16 := by
  refine ⟨⌈32 / theta⌉₊, ?_⟩
  intro d hd
  have hthreshold : 0 < ⌈32 / theta⌉₊ := by
    rw [Nat.ceil_pos]
    positivity
  have hdPos : 0 < d := lt_of_lt_of_le hthreshold hd
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast Nat.succ_le_iff.mpr hdPos
  have hceil : 32 / theta ≤ ((⌈32 / theta⌉₊ : ℕ) : ℝ) := Nat.le_ceil (32 / theta)
  have hdReal : 32 / theta ≤ (d : ℝ) := hceil.trans (by exact_mod_cast hd)
  have hlinear : 32 ≤ theta * (d : ℝ) := by
    have := (div_le_iff₀ htheta).mp hdReal
    nlinarith
  have hfactor : 0 ≤ (d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) + 1) := by positivity
  have hcube : (d : ℝ) ≤ (d : ℝ) ^ 3 := by nlinarith [hfactor]
  have hscaled : 32 ≤ theta * (d : ℝ) ^ 3 :=
    hlinear.trans (mul_le_mul_of_nonneg_left hcube htheta.le)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2
  norm_num
  simpa [multiplicity] using hscaled

/-- Positive exponent saved by the donor's rank comparison. -/
def rankSavingExponent (theta : ℝ) : ℝ :=
  2 * theta / (5 + theta)

theorem rankSavingExponent_pos {theta : ℝ} (htheta : 0 < theta) :
    0 < rankSavingExponent theta := by
  unfold rankSavingExponent
  positivity

/-- At fixed positive agreement and slack, every sufficiently large free order satisfies the
scalar rank comparison. This theorem is pointwise in `epsilon` and `theta`. -/
theorem exists_freeOrderRankThreshold {epsilon theta : ℝ} (hepsilon : 0 < epsilon)
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      1 < (theta ^ 3 / 262144) * ((1 - theta) * epsilon / 2) *
        (d : ℝ) ^ rankSavingExponent theta := by
  have hcoefficient : 0 < (theta ^ 3 / 262144) * ((1 - theta) * epsilon / 2) := by
    positivity
  have hpower :
      Filter.Tendsto (fun d : ℕ ↦ (d : ℝ) ^ rankSavingExponent theta)
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (rankSavingExponent_pos htheta)).comp tendsto_natCast_atTop_atTop
  have hproduct :
      Filter.Tendsto
        (fun d : ℕ ↦
          ((theta ^ 3 / 262144) * ((1 - theta) * epsilon / 2)) *
            (d : ℝ) ^ rankSavingExponent theta)
        Filter.atTop Filter.atTop :=
    hpower.const_mul_atTop hcoefficient
  exact Filter.eventually_atTop.mp
    (hproduct.eventually (Filter.eventually_gt_atTop (1 : ℝ)))

/-- The rounded ambient rate is at least half its unrounded target once `2 ≤ d < K`. -/
theorem half_rate_le_ambientDimension_sub_one_div {epsilon theta : ℝ} {d n : ℕ}
    (hd : 2 ≤ d) (hdK : d < ambientDimension epsilon theta n) :
    (1 - theta) * epsilon / 2 ≤
      ((ambientDimension epsilon theta n - 1 : ℕ) : ℝ) / (n : ℝ) := by
  have hn : 0 < n := blockLength_pos_of_order_lt_ambientDimension hdK
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hnReal]
  have hKThree : 3 ≤ ambientDimension epsilon theta n := by omega
  have hKOne : 1 ≤ ambientDimension epsilon theta n := hKThree.trans' (by omega)
  have hround :
      (1 - theta) * epsilon * (n : ℝ) < (ambientDimension epsilon theta n : ℝ) + 1 := by
    simpa [ambientDimension] using
      Nat.lt_floor_add_one ((1 - theta) * epsilon * (n : ℝ))
  rw [Nat.cast_sub hKOne]
  have hKThreeReal : (3 : ℝ) ≤ ambientDimension epsilon theta n := by
    exact_mod_cast hKThree
  nlinarith

/-- Replace the unrounded rate in the scalar comparison by its rounded ambient counterpart. -/
theorem freeOrder_rank_comparison {epsilon theta : ℝ} {d n : ℕ}
    (htheta : 0 < theta) (hd : 2 ≤ d) (hdK : d < ambientDimension epsilon theta n)
    (hlarge :
      1 < (theta ^ 3 / 262144) * ((1 - theta) * epsilon / 2) *
        (d : ℝ) ^ rankSavingExponent theta) :
    1 < (theta ^ 3 / 262144) *
      (((ambientDimension epsilon theta n - 1 : ℕ) : ℝ) / (n : ℝ)) *
      (d : ℝ) ^ rankSavingExponent theta := by
  have hratio := half_rate_le_ambientDimension_sub_one_div hd hdK
  calc
    1 < (theta ^ 3 / 262144) * ((1 - theta) * epsilon / 2) *
        (d : ℝ) ^ rankSavingExponent theta := hlarge
    _ ≤ (theta ^ 3 / 262144) *
        (((ambientDimension epsilon theta n - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (d : ℝ) ^ rankSavingExponent theta := by gcongr

end
end HiddenDerivative
end ReedSolomon
