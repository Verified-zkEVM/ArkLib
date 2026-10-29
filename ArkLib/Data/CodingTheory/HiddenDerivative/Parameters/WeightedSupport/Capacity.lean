/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Block
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementThreshold

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
* `weightedSupportMultiplicity_pos_iff`: `0 < m ↔ 2 ≤ d`.
* `prescribed_geometric_parameters`: the prescribed order, multiplicity and Taylor cutoff satisfy
  the size and agreement bounds used by geometric list counting.

## References

* [DKT26]
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

/-- The weighted-support multiplicity `m = ⌈100 d ^ 2 harmonic (d - 1)⌉₊` at derivative order `d`.

The capacity construction uses it at `d = capacityDerivativeOrder δ` with `δ < 1 / 4`. For `d ≤ 1`
the harmonic number `harmonic (d - 1)` is `0`, so `m = 0` (see
`weightedSupportMultiplicity_pos_iff`). -/
def weightedSupportMultiplicity (d : ℕ) : ℕ :=
  ⌈100 * (d : ℝ) ^ 2 * harmonic (d - 1)⌉₊

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

/-- The prescribed order and multiplicity give the size and agreement bounds for geometric
list counting. -/
theorem prescribed_geometric_parameters
    (δ : ℝ) (n k : ℕ) (hδ : 0 < δ) (hδmax : δ < 1 / 4)
    (hblock :
      let d := Nat.ceil (Real.exp (xi / δ))
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
      8 * m ≤ n)
    (hA : capacityAgreementThreshold δ n k ≤ n) :
    let A := capacityAgreementThreshold δ n k
    let d := Nat.ceil (Real.exp (xi / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
    let ν := 2 * m - 1
    let K := max k (Nat.floor (δ * n / 2))
    0 < n ∧ 0 < m ∧ 0 < ν ∧ ν ≤ 2 * m ∧ ν < n ∧
      d < K ∧ k ≤ K ∧ K ≤ n ∧ k ≤ A ∧ (k : ℝ) + δ * n ≤ A := by
  let d := Nat.ceil (Real.exp (xi / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
  let ν := 2 * m - 1
  let K := max k (Nat.floor (δ * n / 2))
  let A := capacityAgreementThreshold δ n k
  have hblock' : 8 * m ≤ n := by simpa only [d, m] using hblock
  have hblock'' :
      let d := Nat.ceil (Real.exp (xi / δ))
      let H : ℝ := harmonic (d - 1)
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      8 * m ≤ n := by
    dsimp only
    exact hblock'
  have hA' : k + Nat.ceil (δ * n) ≤ n := by
    simpa only [capacityAgreementThreshold] using hA
  have hb := prescribedBlockBounds δ n k hδ hδmax.le hblock'' hA'
  obtain ⟨hn, hD, hdD, _, _, hKn, _⟩ := hb
  have ho := prescribed_order_lower δ hδ hδmax.le
  have hH : (0 : ℝ) < (harmonic (d - 1) : ℝ) := by
    have hxi : 0 < xi := by norm_num [xi]
    simpa only [d] using (div_pos hxi hδ).trans_le ho.2.2
  have hdlower : 48000 ≤ d := by simpa only [d] using ho.1
  have hd : 0 < d := by omega
  have hmR : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) (Nat.le_ceil _)
  have hm : 0 < m := Nat.cast_pos.mp hmR
  have hν : 0 < ν := by dsimp [ν]; omega
  have hνm : ν ≤ 2 * m := by dsimp [ν]; omega
  have hνn : ν < n := by dsimp [ν]; omega
  have hdK : d < K := by
    have hdD' : d < K - 1 := by simpa only [d, K] using hdD
    omega
  have hkK : k ≤ K := Nat.le_max_left _ _
  have hKn' : K ≤ n := by simpa only [K] using hKn
  have hkA : k ≤ A := by dsimp [A]; exact Nat.le_add_right _ _
  have hgap : (k : ℝ) + δ * n ≤ A :=
    (capacityAgreementThreshold_le_iff_real hδ.le n k _).mp le_rfl
  exact ⟨hn, hm, hν, hνm, hνn, hdK, hkK, hKn', hkA, hgap⟩

end ReedSolomon
