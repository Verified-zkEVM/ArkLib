/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Finset.WeightedSimplex.FloorTransfer
public import ArkLib.ToMathlib.Analysis.Simplex.CenteredMoments
public import ArkLib.ToMathlib.MeasureTheory.Integral.PositivePart

/-!
# Residual sums over a lattice weighted simplex

Let `σ` be a finite index type with `n = Fintype.card σ`, let `w : σ → ℕ` be positive weights, and
let `a : σ → ℝ` be nonnegative coefficients. For a threshold `T`, this file bounds the lattice sum
`∑ c ∈ natWeightedSimplex w W, (max (T - ∑ i, a i * c i) 0 + 1)` by the volume of the continuous
simplex `S = Set.weightedSimplex w (W + ∑ i, w i)` times a mean-variance term.

The proof has three steps.

1. The floor-cell transfer `Finset.sum_natWeightedSimplex_le_setIntegral` bounds the sum by the
   integral over `S` of `max (T + ∑ i, a i - Y u) 0 + 1`, where `Y u = ∑ i, a i * u i`: on the
   unit cell of `c`, `Y` exceeds `∑ i, a i * c i` by at most `∑ i, a i`.
2. The linear form `Y` has average `m = W' * (∑ i, a i / w i) / (n + 1)` on `S`, where
   `W' = W + ∑ i, w i` (`MeasureTheory.setAverage_weightedSimplex_linearForm`).
3. The positive-part bound `MeasureTheory.setIntegral_max_sub_zero_le` gives, for
   `m < c = T + ∑ i, a i`,
   `∫ u in S, max (c - Y u) 0 ≤ vol S * (c - m + ⨍ u in S, (Y u - m) ^ 2 / (4 * (c - m)))`.

The variance is either an arbitrary upper bound `V`
(`Finset.sum_natWeightedSimplex_max_sub_add_one_le_of_setAverage_sq_le`) or the diagonal bound
`W' ^ 2 * (∑ i, (a i / w i) ^ 2) / ((n + 1) * (n + 2))` of
`MeasureTheory.setAverage_weightedSimplex_linearForm_sub_mean_sq_le`
(`Finset.sum_natWeightedSimplex_max_sub_add_one_le`).

Positive weights are needed: with a zero weight the enlarged simplex has infinite volume, so its
`volume.real` is `0`, while the lattice sum is at least `1` because the zero tuple lies in the
lattice simplex. Nonnegative coefficients are needed for the cell comparison in step 1. The
threshold condition `m < c` is the hypothesis of the positive-part bound.

The specializations to the weights `i + 1` and coefficients `1` are in
`ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.RankIntegral`.

## Main statements

* `Finset.sum_natWeightedSimplex_max_sub_add_one_le_of_setAverage_sq_le`: the bound with an
  arbitrary variance bound `V`.
* `Finset.sum_natWeightedSimplex_max_sub_add_one_le`: the bound with the variance discharged.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Finset

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {w : σ → ℕ}

/-- The residual sum over the lattice weighted simplex with an arbitrary variance bound. Let
`W' = W + ∑ i, w i`, let `S = Set.weightedSimplex w W'`, let `n = Fintype.card σ`, let
`m = W' * (∑ i, a i / w i) / (n + 1)` be the average of `∑ i, a i * u i` on `S`, and let
`c = T + ∑ i, a i`. If `m < c` and `V` bounds the variance `⨍ u in S, (∑ i, a i * u i - m) ^ 2`,
then
`∑ c ∈ natWeightedSimplex w W, (max (T - ∑ i, a i * c i) 0 + 1) ≤
  vol S * (c - m + V / (4 * (c - m)) + 1)`.

Positive weights make `S` compact with finite positive volume; with a zero weight the volume of
`S` is infinite and `volume.real S = 0`, while the left side is at least `1`. Nonnegative
coefficients give the cell comparison `∑ i, a i * u i ≤ ∑ i, a i * c i + ∑ i, a i`. The condition
`m < c` is needed by the positive-part bound. -/
theorem sum_natWeightedSimplex_max_sub_add_one_le_of_setAverage_sq_le (hw : ∀ i, w i ≠ 0)
    (W : ℕ) {a : σ → ℝ} (ha : ∀ i, 0 ≤ a i) {T V : ℝ}
    (hc : ((W : ℝ) + ∑ i, (w i : ℝ)) * (∑ i, a i / w i) / (Fintype.card σ + 1) <
      T + ∑ i, a i)
    (hV : ⨍ u in Set.weightedSimplex (fun i ↦ (w i : ℝ)) ((W : ℝ) + ∑ i, (w i : ℝ)),
        (∑ i, a i * u i -
          ((W : ℝ) + ∑ i, (w i : ℝ)) * (∑ i, a i / w i) / (Fintype.card σ + 1)) ^ 2 ≤ V) :
    ∑ c ∈ natWeightedSimplex w W, (max (T - ∑ i, a i * (c i : ℝ)) 0 + 1) ≤
      volume.real (Set.weightedSimplex (fun i ↦ (w i : ℝ)) ((W : ℝ) + ∑ i, (w i : ℝ))) *
        (T + ∑ i, a i -
            ((W : ℝ) + ∑ i, (w i : ℝ)) * (∑ i, a i / w i) / (Fintype.card σ + 1) +
          V / (4 * (T + ∑ i, a i -
            ((W : ℝ) + ∑ i, (w i : ℝ)) * (∑ i, a i / w i) / (Fintype.card σ + 1))) + 1) := by
  set W' : ℝ := (W : ℝ) + ∑ i, (w i : ℝ) with hW'
  set S := Set.weightedSimplex (fun i ↦ (w i : ℝ)) W' with hS
  set m : ℝ := W' * (∑ i, a i / w i) / (Fintype.card σ + 1) with hm
  set c : ℝ := T + ∑ i, a i with hcdef
  have hwpos : ∀ i, 0 < (w i : ℝ) := fun i ↦ Nat.cast_pos.2 (Nat.pos_of_ne_zero (hw i))
  have hI : ∀ f : (σ → ℝ) → ℝ, Continuous f → IntegrableOn f S :=
    fun f hf ↦ hf.continuousOn.integrableOn_weightedSimplex hwpos
  have hfin : volume S ≠ ⊤ := (volume_weightedSimplex_lt_top hwpos W').ne
  -- Step 1: the floor-cell transfer.
  have htransfer : ∑ c ∈ natWeightedSimplex w W, (max (T - ∑ i, a i * (c i : ℝ)) 0 + 1) ≤
      ∫ u in S, (max (c - ∑ i, a i * u i) 0 + 1) :=
    sum_natWeightedSimplex_le_setIntegral W (hI _ (by fun_prop)) (fun _ _ ↦ by positivity)
      fun z _ u hu ↦ by
        have h := sum_mul_le_sum_mul_add_sum_of_mem_natFloorCell ha hu
        exact add_le_add_left (max_le_max_right 0 (by linarith)) 1
  -- Step 2: the mean of the linear form.
  have hmean : ⨍ u in S, ∑ i, a i * u i = m := by
    rcases (show (0 : ℝ) ≤ W' by positivity).eq_or_lt with h0 | hpos
    · have hσ : IsEmpty σ := by
        refine ⟨fun i ↦ ?_⟩
        have hle : (w i : ℝ) ≤ ∑ j, (w j : ℝ) :=
          single_le_sum (fun j _ ↦ (hwpos j).le) (mem_univ i)
        have : (W : ℝ) ≥ 0 := by positivity
        linarith [hwpos i]
      simp [hm, ← h0]
    · exact setAverage_weightedSimplex_linearForm hwpos a hpos
  -- Step 3: the positive-part bound.
  have hpp := setIntegral_max_sub_zero_le (fun u ↦ ∑ i, a i * u i)
    (hI _ (by fun_prop)) hmean (hI _ (by fun_prop)) hc
  have hvar : (⨍ u in S, (∑ i, a i * u i - m) ^ 2) / (4 * (c - m)) ≤ V / (4 * (c - m)) :=
    div_le_div_of_nonneg_right hV (by linarith)
  rw [integral_add (hI _ (by fun_prop)) (integrableOn_const hfin), setIntegral_const,
    smul_eq_mul, mul_one] at htransfer
  calc _ ≤ _ := htransfer
    _ ≤ volume.real S * (c - m + (⨍ u in S, (∑ i, a i * u i - m) ^ 2) / (4 * (c - m))) +
        volume.real S := by gcongr
    _ ≤ volume.real S * (c - m + V / (4 * (c - m))) + volume.real S := by
        gcongr
    _ = _ := by ring

/-- The residual sum over the lattice weighted simplex with the variance discharged. With
`W' = W + ∑ i, w i`, `S = Set.weightedSimplex w W'`, `n = Fintype.card σ`,
`m = W' * (∑ i, a i / w i) / (n + 1)` and `c = T + ∑ i, a i`, if `m < c` then
`∑ c ∈ natWeightedSimplex w W, (max (T - ∑ i, a i * c i) 0 + 1) ≤
  vol S * (c - m + (W' ^ 2 * (∑ i, (a i / w i) ^ 2) / ((n + 1) * (n + 2))) / (4 * (c - m)) + 1)`.
This is `sum_natWeightedSimplex_max_sub_add_one_le_of_setAverage_sq_le` with the variance bound
`MeasureTheory.setAverage_weightedSimplex_linearForm_sub_mean_sq_le`; the hypotheses play the same
roles. -/
theorem sum_natWeightedSimplex_max_sub_add_one_le (hw : ∀ i, w i ≠ 0) (W : ℕ) {a : σ → ℝ}
    (ha : ∀ i, 0 ≤ a i) {T : ℝ}
    (hc : ((W : ℝ) + ∑ i, (w i : ℝ)) * (∑ i, a i / w i) / (Fintype.card σ + 1) <
      T + ∑ i, a i) :
    ∑ c ∈ natWeightedSimplex w W, (max (T - ∑ i, a i * (c i : ℝ)) 0 + 1) ≤
      volume.real (Set.weightedSimplex (fun i ↦ (w i : ℝ)) ((W : ℝ) + ∑ i, (w i : ℝ))) *
        (T + ∑ i, a i -
            ((W : ℝ) + ∑ i, (w i : ℝ)) * (∑ i, a i / w i) / (Fintype.card σ + 1) +
          (((W : ℝ) + ∑ i, (w i : ℝ)) ^ 2 * (∑ i, (a i / w i) ^ 2) /
              ((Fintype.card σ + 1) * (Fintype.card σ + 2))) /
            (4 * (T + ∑ i, a i -
              ((W : ℝ) + ∑ i, (w i : ℝ)) * (∑ i, a i / w i) / (Fintype.card σ + 1))) + 1) :=
  sum_natWeightedSimplex_max_sub_add_one_le_of_setAverage_sq_le hw W ha hc
    (setAverage_weightedSimplex_linearForm_sub_mean_sq_le
      (fun i ↦ Nat.cast_pos.2 (Nat.pos_of_ne_zero (hw i))) a _)

end Finset
