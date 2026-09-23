/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.MomentSource
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.LocalRank
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.RankBudget
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.FiniteRatio
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.Moment

/-!
# The dimension of the partition support space exceeds a multiple of the local rank

The local constraint map of order `m` on the partition support space has rank at most
`localDerivativeCoordinateBudget d m W` (`finrank_partitionSupportLocalConstraint_le`), and for
`0 < d` and `0 < W` that budget is at most the envelope

```text
E(d, m, W) = (W ^ d / (d!) ^ 2) * exp ((d / W) * (m + (d + 1).choose 2))
               * (1 / ((d + 1) * (d / W) ^ 2) + 1 / (d / W))
```

(`localDerivativeCoordinateBudget_le_geometric`). The moment bound
`partitionSupport_dimension_gt_moment` gives
`μ / 2 * n * rate * (W / d) ^ 2 * (W ^ d / (d!) ^ 2) < dim`. So for every `γ ≥ 0` with
`γ * E(d, m, W) ≤ μ / 2 * rate * (W / d) ^ 2 * (W ^ d / (d!) ^ 2)`, the dimension of the partition
support space exceeds `γ * n` times the coordinate budget, and hence `γ * n` times the rank of the
local constraint map.

For the floor-defined weight budget, the finite partition ratio makes the envelope inequality an
identity when `μ = 27 / 10`. The lower-tail moment bound for `500 ≤ d` then yields the surplus
without an additional moment hypothesis.

## Main statements

* `finrank_partitionSupportLocalConstraint_le_geometric`: the rank of the local constraint map is
  at most `E(d, m, W)`.
* `partitionSupport_surplus`: `γ * n * localDerivativeCoordinateBudget d m W < dim`.
* `partitionSupport_localConstraint_surplus`: the same with the rank of the local constraint map.
* `partitionFiniteRatio_mul_geometricRankEnvelope_eq`: the finite-ratio envelope identity.
* `partitionSupport_finiteRatio_surplus`: the finite partition ratio times the coordinate budget
  is below the dimension under the corresponding second-moment bound.
* `partitionSupport_largeOrder_finiteRatio_surplus`: the same bound for `500 ≤ d`, with the
  second-moment hypothesis discharged by the lower-tail estimate.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient Decoding
  and Smaller Cryptographic Proofs*][DKT26], Section 6.2, Lemma 6.2, and Appendix D.2, (131)
-/

@[expose] public section

open PolynomialDifferential Finset MeasureTheory ReedSolomon.HiddenDerivative.RatePartition

noncomputable section

namespace ReedSolomon.HiddenDerivative

namespace RatePartition

/-- Multiplying the finite ratio by the geometric envelope for the local rank budget cancels the
exponential and rounding terms, leaving `(27 / 20) * rate * (W / d) ^ 2 * (W ^ d / (d!) ^ 2)`. -/
theorem partitionFiniteRatio_mul_geometricRankEnvelope_eq
    {rate agreement : ℝ} {order multiplicity budget : ℕ} (hmultiplicity : 0 < multiplicity)
    (hbudget : partitionWeightBudget rate agreement order multiplicity = budget)
    (hbudget_pos : 0 < budget) :
    partitionFiniteRatio rate agreement order multiplicity *
      ((budget : ℝ) ^ order / (order.factorial : ℝ) ^ 2 *
        Real.exp (((order : ℝ) / budget) * (multiplicity + (order + 1).choose 2)) *
          (1 / (((order : ℝ) + 1) * ((order : ℝ) / budget) ^ 2) +
            1 / ((order : ℝ) / budget))) =
      (27 / 20 : ℝ) * rate * ((budget : ℝ) / order) ^ 2 *
        ((budget : ℝ) ^ order / (order.factorial : ℝ) ^ 2) := by
  subst budget
  rw [partitionFiniteRatio_eq_weightBudget hmultiplicity hbudget_pos]
  have hchoose : ((order + 1).choose 2 : ℝ) =
      ((order : ℝ) + 1) * order / 2 := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  rw [hchoose]
  dsimp only
  rw [Real.exp_neg]
  field_simp

end RatePartition

variable {d D W : ℕ}

/-- For `0 < d` and `0 < W`, the local constraint map of order `m` on the partition support space
has rank at most
`(W ^ d / (d!) ^ 2) * exp ((d / W) * (m + (d + 1).choose 2)) *
(1 / ((d + 1) * (d / W) ^ 2) + 1 / (d / W))` over every field, for every cutoff `L`. -/
theorem finrank_partitionSupportLocalConstraint_le_geometric {F : Type*} [Field F] {m : ℕ}
    {L : ℝ} (hD : 0 < D) (hd : 0 < d) (hW : 0 < W) (center received : F) :
    (Module.finrank F (LinearMap.range
      (partitionSupportLocalConstraint (d := d) (W := W) (L := L) m hD center received)) : ℝ) ≤
      ((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) *
        Real.exp (((d : ℝ) / W) * (m + (d + 1).choose 2)) *
          (1 / (((d : ℝ) + 1) * ((d : ℝ) / W) ^ 2) + 1 / ((d : ℝ) / W)) :=
  (Nat.cast_le.mpr (finrank_partitionSupportLocalConstraint_le hD center received)).trans
    (localDerivativeCoordinateBudget_le_geometric d m W hd hW)

/-- The surplus of the partition support space over the local coordinate budget. Under the
hypotheses of `partitionSupport_dimension_gt_moment`, let `γ ≥ 0` satisfy
`γ * E ≤ μ / 2 * rate * (W / d) ^ 2 * (W ^ d / (d!) ^ 2)`, where `E` is the geometric envelope of
`localDerivativeCoordinateBudget_le_geometric`. Then
`γ * n * localDerivativeCoordinateBudget d m W` is strictly less than the dimension of the
partition support space at the natural cutoff `L`. The hypothesis `0 ≤ γ` is used to multiply the
budget bound by `γ * n`; `m` is arbitrary. -/
theorem partitionSupport_surplus (F : Type*) [Field F] {n L m : ℕ}
    {rate level logarithm μ γ : ℝ} (hD : 0 < D) (hd : 0 < d) (hW : 0 < W)
    (hupper : (D : ℝ) ≤ rate * n) (hlevel : level * n ≤ L)
    (hscale : rate * W / d * logarithm ≤ level)
    (hmoment : μ < ⨍ u in Set.weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) W,
      (max (logarithm - (d : ℝ) * (∑ i, u i) / W) 0) ^ 2)
    (hγ : 0 ≤ γ)
    (henvelope : γ * (((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) *
        Real.exp (((d : ℝ) / W) * (m + (d + 1).choose 2)) *
          (1 / (((d : ℝ) + 1) * ((d : ℝ) / W) ^ 2) + 1 / ((d : ℝ) / W))) ≤
      μ / 2 * rate * ((W : ℝ) / d) ^ 2 * ((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2)) :
    γ * n * localDerivativeCoordinateBudget d m W <
      (Module.finrank F (partitionSupportSpace F D d W (L : ℝ) hD) : ℝ) := by
  have hbudget := mul_le_mul_of_nonneg_left
    (localDerivativeCoordinateBudget_le_geometric d m W hd hW) (mul_nonneg hγ (Nat.cast_nonneg n))
  have hscaled := mul_le_mul_of_nonneg_left henvelope (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hdim := partitionSupport_dimension_gt_moment F hD hd hW hupper hlevel hscale hmoment
  calc γ * n * localDerivativeCoordinateBudget d m W
      ≤ γ * n * (((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) *
          Real.exp (((d : ℝ) / W) * (m + (d + 1).choose 2)) *
            (1 / (((d : ℝ) + 1) * ((d : ℝ) / W) ^ 2) + 1 / ((d : ℝ) / W))) := hbudget
    _ ≤ n * (μ / 2 * rate * ((W : ℝ) / d) ^ 2 * ((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2)) := by
      linarith
    _ = μ / 2 * n * rate * ((W : ℝ) / d) ^ 2 * ((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) := by ring
    _ < _ := hdim

/-- Under the hypotheses of `partitionSupport_surplus`, the dimension of the partition support
space at the natural cutoff `L` exceeds `γ * n` times the rank of the local constraint map of
order `m` at any `(center, received)`. -/
theorem partitionSupport_localConstraint_surplus (F : Type*) [Field F] {n L m : ℕ}
    {rate level logarithm μ γ : ℝ} (hD : 0 < D) (hd : 0 < d) (hW : 0 < W)
    (hupper : (D : ℝ) ≤ rate * n) (hlevel : level * n ≤ L)
    (hscale : rate * W / d * logarithm ≤ level)
    (hmoment : μ < ⨍ u in Set.weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1) W,
      (max (logarithm - (d : ℝ) * (∑ i, u i) / W) 0) ^ 2)
    (hγ : 0 ≤ γ)
    (henvelope : γ * (((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) *
        Real.exp (((d : ℝ) / W) * (m + (d + 1).choose 2)) *
          (1 / (((d : ℝ) + 1) * ((d : ℝ) / W) ^ 2) + 1 / ((d : ℝ) / W))) ≤
      μ / 2 * rate * ((W : ℝ) / d) ^ 2 * ((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2))
    (center received : F) :
    γ * n * Module.finrank F (LinearMap.range
      (partitionSupportLocalConstraint (d := d) (W := W) (L := (L : ℝ)) m hD center received)) <
      (Module.finrank F (partitionSupportSpace F D d W (L : ℝ) hD) : ℝ) := by
  refine lt_of_le_of_lt ?_
    (partitionSupport_surplus F hD hd hW hupper hlevel hscale hmoment hγ henvelope)
  exact mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (finrank_partitionSupportLocalConstraint_le hD center received))
    (mul_nonneg hγ (Nat.cast_nonneg n))

/-- For the floor-defined weight budget and a second moment greater than `27 / 10`, the finite
partition ratio times `n` times `localDerivativeCoordinateBudget` is strictly less than the
dimension of the partition support space at cutoff `m * A`. The hypothesis `0 < n` follows from
`0 < D ≤ rate * n` and `0 < rate`. -/
theorem partitionSupport_finiteRatio_surplus (F : Type*) [Field F] {n m A : ℕ}
    {rate agreement : ℝ} (hD : 0 < D) (hd : 0 < d) (hm : 0 < m) (hrate : 0 < rate)
    (hagreement : 0 < agreement)
    (hW : 0 < partitionWeightBudget rate agreement d m)
    (hupper : (D : ℝ) ≤ rate * n) (hlower : agreement * n ≤ A)
    (hmoment : (27 / 10 : ℝ) <
      ⨍ u in Set.weightedSimplex (fun i : Fin d ↦ (i : ℝ) + 1)
          (partitionWeightBudget rate agreement d m : ℝ),
        (max (Real.log (6 * (d : ℝ)) - (d : ℝ) * (∑ i, u i) /
          partitionWeightBudget rate agreement d m) 0) ^ 2) :
    partitionFiniteRatio rate agreement d m * n *
        localDerivativeCoordinateBudget d m (partitionWeightBudget rate agreement d m) <
      (Module.finrank F (partitionSupportSpace F D d (partitionWeightBudget rate agreement d m)
        ((m * A : ℕ) : ℝ) hD) : ℝ) := by
  let W := partitionWeightBudget rate agreement d m
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hlog : 0 < Real.log (6 * (d : ℝ)) := Real.log_pos (by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  have hfloor : (W : ℝ) ≤
      (m : ℝ) * agreement * d / (rate * Real.log (6 * (d : ℝ))) := by
    dsimp [W, partitionWeightBudget]
    exact Nat.floor_le (by positivity)
  have hcut : Real.log (6 * (d : ℝ)) ≤
      (m : ℝ) * agreement * d / (rate * W) := by
    have hfloor' := (le_div_iff₀ (mul_pos hrate hlog)).mp hfloor
    apply (le_div_iff₀ (mul_pos hrate hW')).mpr
    nlinarith only [hfloor']
  have hcutoff : (m : ℝ) * agreement * n ≤ ((m * A : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlower
      (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    push_cast at h ⊢
    nlinarith
  have hscale : rate * (W : ℝ) / d * Real.log (6 * (d : ℝ)) ≤
      (m : ℝ) * agreement := by
    have h := mul_le_mul_of_nonneg_left hcut
      (show 0 ≤ rate * (W : ℝ) / d by positivity)
    calc
      rate * (W : ℝ) / d * Real.log (6 * (d : ℝ)) ≤
          rate * (W : ℝ) / d * ((m : ℝ) * agreement * d / (rate * W)) := h
      _ = (m : ℝ) * agreement := by field_simp
  have hratio := partitionFiniteRatio_eq_weightBudget hm hW
  have hgamma : 0 < partitionFiniteRatio rate agreement d m := by
    rw [hratio]
    positivity
  have henvelope := RatePartition.partitionFiniteRatio_mul_geometricRankEnvelope_eq
    (order := d) (multiplicity := m) (budget := W) hm rfl hW
  have henvelope_le : partitionFiniteRatio rate agreement d m *
      (((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) *
        Real.exp (((d : ℝ) / W) * (m + (d + 1).choose 2)) *
          (1 / (((d : ℝ) + 1) * ((d : ℝ) / W) ^ 2) + 1 / ((d : ℝ) / W))) ≤
      (27 / 10 : ℝ) / 2 * rate * ((W : ℝ) / d) ^ 2 *
        ((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) := by
    rw [henvelope]
    norm_num
  exact partitionSupport_surplus F hD hd hW hupper hcutoff hscale hmoment hgamma.le
    henvelope_le

/-- For `500 ≤ d`, the finite rate-partition ratio times `n` times the local coordinate budget is
strictly less than the dimension of the partition support space. The cutoff `L` may be any natural
number with `(m * agreement) * n ≤ L`; the weight budget is the finite floor at rate, agreement,
order `d` and multiplicity `m`. -/
theorem partitionSupport_largeOrder_finiteRatio_surplus (F : Type*) [Field F]
    {D d m n L : ℕ} {rate agreement : ℝ} (hD : 0 < D) (hd : 500 ≤ d) (hm : 0 < m)
    (hrate : 0 < rate) (hagreement : 0 < agreement)
    (hbudget : 0 < RatePartition.partitionWeightBudget rate agreement d m)
    (hupper : (D : ℝ) ≤ rate * n) (hlevel : (m : ℝ) * agreement * n ≤ L) :
    RatePartition.partitionFiniteRatio rate agreement d m * n *
      localDerivativeCoordinateBudget d m (RatePartition.partitionWeightBudget rate agreement d m) <
        (Module.finrank F (partitionSupportSpace F D d
          (RatePartition.partitionWeightBudget rate agreement d m) (L : ℝ) hD) : ℝ) := by
  let W := RatePartition.partitionWeightBudget rate agreement d m
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hW : 0 < W := hbudget
  have hWreal : (0 : ℝ) < W := by exact_mod_cast hW
  have hlog : 0 < Real.log (6 * (d : ℝ)) := by
    apply Real.log_pos
    have hdge : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    nlinarith
  have hfloor : (W : ℝ) ≤
      (m : ℝ) * agreement * d / (rate * Real.log (6 * (d : ℝ))) := by
    dsimp only [W, RatePartition.partitionWeightBudget]
    exact Nat.floor_le (by positivity)
  have hmulFloor : (W : ℝ) * (rate * Real.log (6 * (d : ℝ))) ≤
      (m : ℝ) * agreement * d :=
    (le_div_iff₀ (mul_pos hrate hlog)).mp hfloor
  have hscale' : rate * W * Real.log (6 * (d : ℝ)) / d ≤ (m : ℝ) * agreement := by
    apply (div_le_iff₀ hdpos).2
    calc
      rate * W * Real.log (6 * (d : ℝ)) =
          (W : ℝ) * (rate * Real.log (6 * (d : ℝ))) := by ring
      _ ≤ (m : ℝ) * agreement * d := hmulFloor
  have hscale : rate * W / d * Real.log (6 * (d : ℝ)) ≤ (m : ℝ) * agreement := by
    calc
      rate * W / d * Real.log (6 * (d : ℝ)) =
          rate * W * Real.log (6 * (d : ℝ)) / d := by field_simp
      _ ≤ (m : ℝ) * agreement := hscale'
  have hmoment := RatePartition.setAverage_weightedSimplex_succ_lowerTail_sq_gt hd hWreal
  have hγ : 0 ≤ RatePartition.partitionFiniteRatio rate agreement d m := by
    rw [RatePartition.partitionFiniteRatio_eq_weightBudget hm hbudget]
    positivity
  have hEnvelope := RatePartition.partitionFiniteRatio_mul_geometricRankEnvelope_eq
    (order := d) (multiplicity := m) (budget := W) hm rfl hW
  have henvelope : RatePartition.partitionFiniteRatio rate agreement d m *
      (((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) *
        Real.exp (((d : ℝ) / W) * (m + (d + 1).choose 2)) *
          (1 / (((d : ℝ) + 1) * ((d : ℝ) / W) ^ 2) +
            1 / ((d : ℝ) / W))) ≤
      (27 / 10 : ℝ) / 2 * rate * ((W : ℝ) / d) ^ 2 *
        ((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) := by
    rw [hEnvelope]
    norm_num
  simpa only [W] using partitionSupport_surplus F hD (by omega) hW hupper hlevel hscale
    hmoment hγ henvelope

end ReedSolomon.HiddenDerivative
