/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Finset.WeightedSimplex
public import ArkLib.ToMathlib.Analysis.Simplex.WeightedVolume
public import ArkLib.ToMathlib.MeasureTheory.Integral.NatFloorCells

/-!
# Floor-cell transfers between discrete and continuous weighted simplices

Let `σ` be a finite index type and `w : σ → ℕ` a weight vector. This file compares sums over the
lattice points of `Finset.natWeightedSimplex w W` with integrals over the continuous weighted
simplex `Set.weightedSimplex (fun i ↦ (w i : ℝ)) W`. Each lattice point `c` is charged for its
unit cell `MeasureTheory.natFloorCell c = ∏ i, [c i, c i + 1)`.

* **Flooring.** For positive weights, the coordinatewise natural floor of a point of the
  continuous simplex of budget `W` is a lattice point of budget `⌊W⌋₊`. Consequently the continuous
  simplex is covered by the cells of these lattice points, and an integral over any measurable
  part `T` of it is at most the sum of the cellwise upper bounds
  (`Finset.setIntegral_le_sum_natWeightedSimplex`).
* **Enlargement.** The cell of a lattice point of budget `W` lies in the continuous simplex of
  budget `W + ∑ i, w i`, for any weights. Consequently a sum of cellwise lower bounds is at most
  the integral of a function that is nonnegative on the enlarged simplex
  (`Finset.sum_natWeightedSimplex_le_setIntegral`).

With the constant function `1` these give the counting sandwich
`vol (weightedSimplex w W) ≤ #(natWeightedSimplex w W) ≤ vol (weightedSimplex w (W + ∑ i, w i))`
for positive weights; the acceptance tests derive it. Together with
`MeasureTheory.volume_real_weightedSimplex`, the right inequality recovers
`Finset.card_natWeightedSimplex_le`, which is why the counting forms are not stated separately.

Positive weights are needed for flooring: a zero weight leaves its coordinate unbounded in the
continuous simplex, while `natWeightedSimplex` still bounds every coordinate by the budget. The
enlargement needs no hypothesis on the weights. With a zero weight, however, the enlarged simplex
has infinite volume, so the constant function `1` is not integrable on it, and the right half of
the counting sandwich fails: for one coordinate of weight zero and budget zero, the lattice simplex
has one point while the enlarged simplex has infinite volume, whose `volume.real` is zero.

## Main statements

* `Finset.natFloor_mem_natWeightedSimplex`: flooring maps the continuous simplex of budget `W`
  into the lattice simplex of budget `⌊W⌋₊`.
* `Finset.natFloorCell_subset_weightedSimplex`: the cell of a lattice point lies in the enlarged
  continuous simplex.
* `Finset.setIntegral_le_sum_natWeightedSimplex`: integrals over the continuous simplex are
  bounded above by lattice sums.
* `Finset.sum_natWeightedSimplex_le_setIntegral`: lattice sums are bounded above by integrals over
  the enlarged continuous simplex.

## References

Generalizes, from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, the generic parts of
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`:

* `WeightedSupportParameters.floor_higher_mem` (`FloorTransfer.lean`) becomes
  `natFloor_mem_natWeightedSimplex`, for any finite index type, positive natural weights, and a
  real budget, instead of `Fin (d - 1)` with weights `i + 1` and a natural budget.
* The covering and cell argument of `WeightedSupportParameters.weighted_floor_integral`
  (`FloorTransfer.lean`) becomes `setIntegral_le_sum_natWeightedSimplex`, with an arbitrary
  integrand and cellwise bound in place of the cubic positive part.
* `floorCell_subset_weightedSimplex` (`CubeTransfer.lean`) becomes
  `natFloorCell_subset_weightedSimplex`, and the cell argument of
  `weighted_residual_sum_le_integral` becomes `sum_natWeightedSimplex_le_setIntegral`, with an
  arbitrary integrand and cellwise bound in place of the residual.

The source-shaped cubic and residual statements are thin specializations in
`ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.FloorTransfer`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Finset

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {w : σ → ℕ}

/-- For positive weights, flooring every coordinate of a point of the continuous weighted simplex
of budget `W` gives a lattice point of budget `⌊W⌋₊`. Positivity is needed because a zero-weight
coordinate is unbounded in the continuous simplex but bounded by the budget in the lattice
simplex. -/
theorem natFloor_mem_natWeightedSimplex (hw : ∀ i, w i ≠ 0) {W : ℝ} {x : σ → ℝ}
    (hx : x ∈ Set.weightedSimplex (fun i ↦ (w i : ℝ)) W) :
    (fun i ↦ ⌊x i⌋₊) ∈ natWeightedSimplex w ⌊W⌋₊ := by
  obtain ⟨hx0, hxW⟩ := Set.mem_weightedSimplex.mp hx
  rw [mem_natWeightedSimplex hw]
  apply Nat.le_floor
  have h := sum_mul_le_sum_mul_of_mem_natFloorCell (a := fun i ↦ (w i : ℝ))
    (fun i ↦ Nat.cast_nonneg _) (mem_natFloorCell_natFloor hx0)
  push_cast
  exact h.trans hxW

/-- The unit cell of a lattice point of budget `W` lies in the continuous weighted simplex of
budget `W + ∑ i, w i`: moving from the lower corner across the cell raises the weighted sum by less
than the total weight. This holds for all weights. -/
theorem natFloorCell_subset_weightedSimplex {W : ℕ} {c : σ → ℕ}
    (hc : c ∈ natWeightedSimplex w W) :
    natFloorCell c ⊆ Set.weightedSimplex (fun i ↦ (w i : ℝ)) ((W : ℝ) + ∑ i, (w i : ℝ)) := by
  intro x hx
  refine ⟨nonneg_of_mem_natFloorCell hx, ?_⟩
  have hcW : ∑ i, (w i : ℝ) * (c i : ℝ) ≤ W := by
    exact_mod_cast weightedSum_le_of_mem_natWeightedSimplex hc
  have h := sum_mul_le_sum_mul_add_sum_of_mem_natFloorCell (a := fun i ↦ (w i : ℝ))
    (fun i ↦ Nat.cast_nonneg _) hx
  linarith

/-- An integral over a measurable part `T` of the continuous weighted simplex is at most a sum over
the lattice simplex, when the integrand is bounded at each point by a nonnegative quantity that
depends only on the coordinatewise floor of the point. The cells of the lattice points cover `T`
and have volume one.

Positive weights are needed for the cover (`natFloor_mem_natWeightedSimplex`). The bound `g c`
must be nonnegative because `T` may meet a cell in a set of volume less than one. -/
theorem setIntegral_le_sum_natWeightedSimplex (hw : ∀ i, w i ≠ 0) {W : ℝ} {T : Set (σ → ℝ)}
    (hT : MeasurableSet T) (hTW : T ⊆ Set.weightedSimplex (fun i ↦ (w i : ℝ)) W)
    {f : (σ → ℝ) → ℝ} {g : (σ → ℕ) → ℝ} (hf : IntegrableOn f T)
    (hg : ∀ c ∈ natWeightedSimplex w ⌊W⌋₊, 0 ≤ g c)
    (hfg : ∀ x ∈ T, f x ≤ g fun i ↦ ⌊x i⌋₊) :
    ∫ x in T, f x ≤ ∑ c ∈ natWeightedSimplex w ⌊W⌋₊, g c := by
  set s := natWeightedSimplex w ⌊W⌋₊
  have hcover : T = ⋃ c ∈ s, T ∩ natFloorCell c := by
    ext x
    constructor
    · intro hx
      have hx0 := (Set.mem_weightedSimplex.mp (hTW hx)).1
      exact Set.mem_biUnion (natFloor_mem_natWeightedSimplex hw (hTW hx))
        ⟨hx, mem_natFloorCell_natFloor hx0⟩
    · intro hx
      obtain ⟨c, -, hxc⟩ := Set.mem_iUnion₂.mp hx
      exact hxc.1
  calc
    ∫ x in T, f x = ∫ x in ⋃ c ∈ s, T ∩ natFloorCell c, f x := by rw [← hcover]
    _ ≤ ∑ c ∈ s, g c := by
      refine setIntegral_biUnion_le_sum s (fun c ↦ T ∩ natFloorCell c) f g
        (fun c _ ↦ hT.inter (measurableSet_natFloorCell c))
        (fun c _ d _ hcd ↦ (pairwise_disjoint_natFloorCell hcd).mono
          Set.inter_subset_right Set.inter_subset_right)
        (fun c _ ↦ hf.mono_set Set.inter_subset_left)
        (fun c _ ↦ (measure_mono Set.inter_subset_right).trans_eq (volume_natFloorCell c))
        hg fun c _ x hx ↦ ?_
      have hfloor : (fun i ↦ ⌊x i⌋₊) = c :=
        funext ((mem_natFloorCell_iff_natFloor_eq (nonneg_of_mem_natFloorCell hx.2)).mp hx.2)
      simpa [hfloor] using hfg x hx.1

/-- A sum over the lattice simplex of budget `W` is at most the integral over the continuous
simplex of budget `W + ∑ i, w i`, when each term is bounded by the integrand on the cell of its
lattice point. The integrand must be nonnegative on the enlarged simplex, which is not covered by
the cells. No hypothesis on the weights is needed. With a zero weight the enlarged simplex has
infinite volume, so a constant integrand such as the counting function `1` is not integrable
there. -/
theorem sum_natWeightedSimplex_le_setIntegral (W : ℕ) {f : (σ → ℝ) → ℝ} {g : (σ → ℕ) → ℝ}
    (hf : IntegrableOn f
      (Set.weightedSimplex (fun i ↦ (w i : ℝ)) ((W : ℝ) + ∑ i, (w i : ℝ))))
    (hf0 : ∀ x ∈ Set.weightedSimplex (fun i ↦ (w i : ℝ)) ((W : ℝ) + ∑ i, (w i : ℝ)), 0 ≤ f x)
    (hgf : ∀ c ∈ natWeightedSimplex w W, ∀ x ∈ natFloorCell c, g c ≤ f x) :
    ∑ c ∈ natWeightedSimplex w W, g c ≤
      ∫ x in Set.weightedSimplex (fun i ↦ (w i : ℝ)) ((W : ℝ) + ∑ i, (w i : ℝ)), f x :=
  sum_le_setIntegral_of_measure_eq_one _ natFloorCell _ f g
    (fun c _ ↦ measurableSet_natFloorCell c)
    (fun _ _ _ _ hcd ↦ pairwise_disjoint_natFloorCell hcd)
    (fun c _ ↦ volume_natFloorCell c)
    (fun _ hc ↦ natFloorCell_subset_weightedSimplex hc)
    (Set.measurableSet_weightedSimplex _ _) hf hf0 hgf

end Finset
