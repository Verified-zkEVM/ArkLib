/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Block

/-!
# Weighted-support capacity parameters

The weighted-support capacity theorem fixes its numerical parameters from the gap `δ` alone,
before the field, the evaluation points and the received word are chosen:

```text
d = 0                          if 1 / 4 ≤ δ   (order-zero branch)
d = ⌈exp (ξ / δ)⌉₊             if δ < 1 / 4,  ξ = 27 / 10
m = ⌈100 d ^ 2 harmonic (d - 1)⌉₊
K = max k ⌊δ n / 2⌋₊           (ambient dimension, at block length n and message dimension k)
```

The agreement threshold is `A = k + ⌈δ n⌉₊`. This file defines `d`, `m` and `K`, and the
larger-field condition `2 (m A + d - K) ≤ q`, and records the facts about `d` and `m` that follow
from the order bounds in `Parameters/WeightedSupport/ScalarParameters.lean` and the block bounds in
`Parameters/WeightedSupport/Block.lean`.

## Main definitions

* `capacityDerivativeOrder δ`: the order `d` above.
* `weightedSupportMultiplicity d`: the multiplicity `m` as a function of the order.
* `weightedSupportAmbientDimension δ n k`: the ambient dimension `K`.
* `LargeFieldCondition δ n k q d m`: `2 (m A + d - K) ≤ q`.

## Main statements

* `capacityDerivativeOrder_eq_zero`, `capacityDerivativeOrder_eq_ceil`: the two branches.
* `capacityDerivativeOrder_lower`: for `0 < δ < 1 / 4`, `48000 ≤ d`, `ξ / δ ≤ log d` and
  `ξ / δ ≤ harmonic (d - 1)`.
* `weightedSupportMultiplicity_pos_iff`: `0 < m ↔ 2 ≤ d`.
* `capacity_block_bounds`: for `0 < δ < 1 / 4`, `8 m ≤ n` and `k + ⌈δ n⌉₊ ≤ n`, the order is
  below the ambient degree `K - 1` and `k ≤ K ≤ n`.

## References

Ports `Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/WeightedSupport/Capacity.lean`
and `Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/Harmonic.lean` at ArkLib revision
a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `capacityDerivativeOrder`, `capacityDerivativeOrder_eq_zero` and
  `capacityDerivativeOrder_eq_ceil` keep their statements, with the source's literal `27 / 10`
  written as `WeightedSupportParameters.xi`, which is `27 / 10` by definition.
* The source's `harmonicNumber r = ∑ i ∈ range r, 1 / (i + 1)` in `ℝ` is not defined: it is the
  real cast of Mathlib's `harmonic r`, which is what the source's `harmonicNumber_eq_harmonic`
  (the only declaration of `Parameters/Harmonic.lean`) states, and which the earlier
  weighted-support files already use. That file is therefore not ported; the acceptance test
  derives the identity from Mathlib's definition.
* `weightedSupportMultiplicity` takes the order `d` instead of `δ`: the source's
  `weightedSupportMultiplicity δ` is `weightedSupportMultiplicity (capacityDerivativeOrder δ)`.
  The formula agrees with the multiplicity written out in `prescribedBlockBounds` and in
  `Interpolation/WeightedSupport/Margin.lean`.
* `weightedSupportAmbientDimension` keeps its statement.
* `LargeFieldCondition` keeps its statement, with the source's
  `ReedSolomon.agreementThreshold δ n k` written as `k + ⌈δ * n⌉₊`, the form used in
  `Parameters/WeightedSupport/Block.lean`.
* `capacityDerivativeOrder_lower`, `weightedSupportMultiplicity_pos_iff`,
  `le_weightedSupportMultiplicity` and `capacity_block_bounds` are new; they are specializations of
  `prescribed_order_lower` and `prescribedBlockBounds` to the definitions above.

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], weighted-support parameters.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open HiddenDerivative.WeightedSupportParameters

/-- The derivative order of the uniform capacity construction at gap `δ`.

For `1 / 4 ≤ δ` the order is `0`: that branch uses a separate instance-dependent multiplicity and is
not handled by the weighted-support parameters. For `δ < 1 / 4` the order is
`⌈exp (ξ / δ)⌉₊` with `ξ = 27 / 10`, the no-band weighted-support constant. The definition makes
no positivity assumption on `δ`: for `δ ≤ 0` the second branch is still taken, and the order bounds
below assume `0 < δ`. -/
def capacityDerivativeOrder (δ : ℝ) : ℕ :=
  if (1 / 4 : ℝ) ≤ δ then 0 else ⌈Real.exp (xi / δ)⌉₊

/-- The order-zero branch: for `1 / 4 ≤ δ` the derivative order is `0`. -/
@[simp]
theorem capacityDerivativeOrder_eq_zero {δ : ℝ} (hδ : (1 / 4 : ℝ) ≤ δ) :
    capacityDerivativeOrder δ = 0 := by
  exact ite_eq_left hδ

/-- The weighted-support branch: for `δ < 1 / 4` the derivative order is `⌈exp (ξ / δ)⌉₊`. -/
theorem capacityDerivativeOrder_eq_ceil {δ : ℝ} (hδ : δ < 1 / 4) :
    capacityDerivativeOrder δ = ⌈Real.exp (xi / δ)⌉₊ := by
  exact ite_eq_right (not_le_of_gt hδ)

/-- For `0 < δ < 1 / 4`, the derivative order `d` satisfies `48000 ≤ d`, `ξ / δ ≤ log d` and
`ξ / δ ≤ harmonic (d - 1)`. This is `prescribed_order_lower` at the weighted-support branch; the
bound `δ < 1 / 4` is what selects that branch, and `0 < δ` makes `ξ / δ` large. -/
theorem capacityDerivativeOrder_lower {δ : ℝ} (hδ : 0 < δ) (hδmax : δ < 1 / 4) :
    48000 ≤ capacityDerivativeOrder δ ∧ xi / δ ≤ Real.log (capacityDerivativeOrder δ) ∧
      xi / δ ≤ (harmonic (capacityDerivativeOrder δ - 1) : ℝ) := by
  rw [capacityDerivativeOrder_eq_ceil hδmax]
  exact prescribed_order_lower δ hδ hδmax.le

/-- The weighted-support multiplicity `m = ⌈100 d ^ 2 harmonic (d - 1)⌉₊` at derivative order `d`.

The capacity construction uses it at `d = capacityDerivativeOrder δ` with `δ < 1 / 4`. For `d ≤ 1`
the harmonic number `harmonic (d - 1)` is `0`, so `m = 0` (see
`weightedSupportMultiplicity_pos_iff`). -/
def weightedSupportMultiplicity (d : ℕ) : ℕ :=
  ⌈100 * (d : ℝ) ^ 2 * harmonic (d - 1)⌉₊

/-- The unrounded multiplicity is at most `m`. -/
theorem le_weightedSupportMultiplicity (d : ℕ) :
    100 * (d : ℝ) ^ 2 * harmonic (d - 1) ≤ weightedSupportMultiplicity d :=
  Nat.le_ceil _

/-- The multiplicity is positive exactly when `2 ≤ d`: for `d = 0` the factor `d ^ 2` vanishes,
and for `d = 1` the factor `harmonic 0` vanishes. -/
theorem weightedSupportMultiplicity_pos_iff {d : ℕ} :
    0 < weightedSupportMultiplicity d ↔ 2 ≤ d := by
  rw [weightedSupportMultiplicity, Nat.ceil_pos]
  constructor
  · intro h
    by_contra hd
    interval_cases d <;> simp at h
  · intro hd
    have hlog : 0 < Real.log d := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
    have hH : (0 : ℝ) < harmonic (d - 1) := hlog.trans_le (Real.log_le_harmonic_pred d)
    have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity

/-- The ambient dimension `K = max k ⌊δ n / 2⌋₊` of the weighted-support certificate at gap `δ`,
block length `n` and message dimension `k`. Taking the maximum with `k` keeps every message
polynomial inside the ambient space; the second term gives the dimension used for the rate
`(K - 1) / n` in `Parameters/WeightedSupport/Block.lean`. -/
def weightedSupportAmbientDimension (δ : ℝ) (n k : ℕ) : ℕ :=
  max k ⌊δ * n / 2⌋₊

/-- The larger-field condition `2 (m A + d - K) ≤ q`, with `A = k + ⌈δ n⌉₊` and
`K = weightedSupportAmbientDimension δ n k`, under which the weighted-support root count improves
its exponent of `q` from `2 d` to `d`. The natural subtraction is truncated, so the left side is
`2 max 0 (m A + d - K)`. -/
def LargeFieldCondition (δ : ℝ) (n k q d m : ℕ) : Prop :=
  2 * (m * (k + ⌈δ * n⌉₊) + d - weightedSupportAmbientDimension δ n k) ≤ q

/-- The block bounds at the capacity parameters. Let `0 < δ < 1 / 4`,
`d = capacityDerivativeOrder δ`, `m = weightedSupportMultiplicity d` and
`K = weightedSupportAmbientDimension δ n k`. If `8 m ≤ n` and `k + ⌈δ n⌉₊ ≤ n`, then `0 < n`,
`d < K - 1` and `k ≤ K ≤ n`. This is `prescribedBlockBounds` for these definitions. The block
condition `8 m ≤ n` is what makes `δ n` large compared with `d ^ 2`; the threshold condition
`k + ⌈δ n⌉₊ ≤ n` gives `K ≤ n`. -/
theorem capacity_block_bounds {δ : ℝ} {n k : ℕ} (hδ : 0 < δ) (hδmax : δ < 1 / 4)
    (hblock : 8 * weightedSupportMultiplicity (capacityDerivativeOrder δ) ≤ n)
    (hA : k + ⌈δ * n⌉₊ ≤ n) :
    0 < n ∧ capacityDerivativeOrder δ < weightedSupportAmbientDimension δ n k - 1 ∧
      k ≤ weightedSupportAmbientDimension δ n k ∧ weightedSupportAmbientDimension δ n k ≤ n := by
  rw [capacityDerivativeOrder_eq_ceil hδmax] at hblock ⊢
  obtain ⟨hn, -, hdD, -, -, hK, -⟩ := prescribedBlockBounds δ n k hδ hδmax.le hblock hA
  exact ⟨hn, hdD, le_max_left _ _, hK⟩

end ReedSolomon
