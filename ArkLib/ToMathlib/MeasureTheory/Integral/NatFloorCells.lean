/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Natural floor cells and finite cell comparisons

For a natural vector `c : ι → ℕ`, `MeasureTheory.natFloorCell c` is the half-open unit box
`∏ i, [c i, c i + 1)` in `ι → ℝ`. On nonnegative vectors, `x` lies in the cell of `c` exactly when
`⌊x i⌋₊ = c i` for every `i`. Distinct cells are disjoint and each has volume one. These are the
facts needed to compare a sum over a finite set of lattice points with an integral: each lattice
point is charged for its own cell.

The comparison itself is stated for an arbitrary measure space and an arbitrary finite family of
pairwise disjoint measurable cells.

* If every cell has measure at most one and `f ≤ w i` on cell `i`, with `0 ≤ w i`, then the integral
  of `f` over the union of the cells is at most `∑ i, w i`
  (`MeasureTheory.setIntegral_biUnion_le_sum`).
* If every cell has measure exactly one, lies in a measurable set `S` on which `f` is nonnegative,
  and `w i ≤ f` on cell `i`, then `∑ i, w i` is at most the integral of `f` over `S`
  (`MeasureTheory.sum_le_setIntegral_of_measure_eq_one`).

The nonnegativity of `w i` in the first statement is needed because a cell may have measure less
than one: a constant `f = w i < 0` on a cell of measure `1 / 2` integrates to `w i / 2 > w i`.

## Main statements

* `MeasureTheory.natFloorCell`, `MeasureTheory.mem_natFloorCell`,
  `MeasureTheory.measurableSet_natFloorCell`, `MeasureTheory.volume_natFloorCell`.
* `MeasureTheory.mem_natFloorCell_iff_natFloor_eq`, `MeasureTheory.mem_natFloorCell_natFloor`:
  the cell of a nonnegative vector is indexed by its coordinatewise natural floor.
* `MeasureTheory.pairwise_disjoint_natFloorCell`: distinct cells are disjoint.
* `MeasureTheory.sum_mul_le_sum_mul_of_mem_natFloorCell`,
  `MeasureTheory.sum_mul_le_sum_mul_add_sum_of_mem_natFloorCell`: a nonnegative linear form
  varies across a cell by at most the sum of its coefficients.
* `MeasureTheory.setIntegral_biUnion_le_sum` and
  `MeasureTheory.sum_le_setIntegral_of_measure_eq_one`: the two finite cell comparisons.

## References

Ports, from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,

* `integral_biUnion_le_sum_of_cell_measure_le_one` and `sum_le_integral_of_unit_cells` from
  `ArkLib/ToMathlib/MeasureTheory/Integral/FiniteCells.lean`, as
  `setIntegral_biUnion_le_sum` and `sum_le_setIntegral_of_measure_eq_one`. The first now assumes
  the one-sided bound `f x ≤ w i` instead of `‖f x‖ ≤ w i`, so `f` may be arbitrarily negative.
  The second assumes `0 ≤ f` only on `S`, together with measurability of `S`, instead of on the
  whole space.
* `natFloorCell`, `measurableSet_natFloorCell`, `volume_natFloorCell`, `mem_natFloorCell_iff`, and
  `disjoint_natFloorCell` from `ArkLib/ToMathlib/MeasureTheory/Integral/NaturalFloorCells.lean`.
  Disjointness is stated as `Pairwise (Disjoint on natFloorCell)`.
* The first half of `sum_natFloor_bounds` from the same file, in the weighted cell form
  `sum_mul_le_sum_mul_of_mem_natFloorCell`; its second half becomes
  `sum_mul_le_sum_mul_add_sum_of_mem_natFloorCell` with coefficients.

`bounded_region_eq_union_natFloorCells` and `integral_bounded_region_le_natFloor_sum` are not
ported: the weighted-simplex transfers in `ArkLib.Data.Finset.WeightedSimplex.FloorTransfer` index
the cells by the lattice points of the simplex directly.
-/

@[expose] public section

open Function Set
open scoped BigOperators

namespace MeasureTheory

section Cells

variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Integrating over finitely many disjoint cells, each of measure at most one, gives at most the
sum of the cellwise upper bounds. The bounds must be nonnegative because a cell may have measure
less than one; the function itself may take any sign. -/
theorem setIntegral_biUnion_le_sum (s : Finset ι) (cell : ι → Set X) (f : X → ℝ) (w : ι → ℝ)
    (hmeas : ∀ i ∈ s, MeasurableSet (cell i))
    (hdisj : (s : Set ι).PairwiseDisjoint cell)
    (hint : ∀ i ∈ s, IntegrableOn f (cell i) μ)
    (hvol : ∀ i ∈ s, μ (cell i) ≤ 1)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hbound : ∀ i ∈ s, ∀ x ∈ cell i, f x ≤ w i) :
    ∫ x in ⋃ i ∈ s, cell i, f x ∂μ ≤ ∑ i ∈ s, w i := by
  rw [integral_biUnion_finset s hmeas hdisj hint]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hfin : μ (cell i) ≠ ⊤ := ((hvol i hi).trans_lt ENNReal.one_lt_top).ne
  have hv : μ.real (cell i) ≤ 1 := by
    simpa [Measure.real] using ENNReal.toReal_mono ENNReal.one_ne_top (hvol i hi)
  calc
    ∫ x in cell i, f x ∂μ ≤ ∫ _x in cell i, w i ∂μ :=
      setIntegral_mono_on (hint i hi) (integrableOn_const hfin) (hmeas i hi) (hbound i hi)
    _ = μ.real (cell i) * w i := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ 1 * w i := mul_le_mul_of_nonneg_right hv (hw i hi)
    _ = w i := one_mul _

/-- Finitely many disjoint cells of measure one inside `S` transfer cellwise lower bounds to the
integral over `S`. The function must be nonnegative on `S`, since the part of `S` outside the cells
also contributes to the integral; the bounds `w i` may take any sign. -/
theorem sum_le_setIntegral_of_measure_eq_one (s : Finset ι) (cell : ι → Set X) (S : Set X)
    (f : X → ℝ) (w : ι → ℝ)
    (hmeas : ∀ i ∈ s, MeasurableSet (cell i))
    (hdisj : (s : Set ι).PairwiseDisjoint cell)
    (hvol : ∀ i ∈ s, μ (cell i) = 1)
    (hsub : ∀ i ∈ s, cell i ⊆ S)
    (hS : MeasurableSet S) (hint : IntegrableOn f S μ) (hf : ∀ x ∈ S, 0 ≤ f x)
    (hbound : ∀ i ∈ s, ∀ x ∈ cell i, w i ≤ f x) :
    ∑ i ∈ s, w i ≤ ∫ x in S, f x ∂μ := by
  have hintCell : ∀ i ∈ s, IntegrableOn f (cell i) μ :=
    fun i hi ↦ hint.mono_set (hsub i hi)
  calc
    ∑ i ∈ s, w i ≤ ∑ i ∈ s, ∫ x in cell i, f x ∂μ := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      have hfin : μ (cell i) ≠ ⊤ := by simp [hvol i hi]
      have h := setIntegral_mono_on (integrableOn_const hfin) (hintCell i hi) (hmeas i hi)
        (hbound i hi)
      simpa [Measure.real, hvol i hi] using h
    _ = ∫ x in ⋃ i ∈ s, cell i, f x ∂μ := (integral_biUnion_finset s hmeas hdisj hintCell).symm
    _ ≤ ∫ x in S, f x ∂μ := by
      refine setIntegral_mono_set hint (ae_restrict_of_forall_mem hS hf) ?_
      exact Filter.Eventually.of_forall (Set.iUnion₂_subset hsub)

end Cells

section NatFloorCell

variable {ι : Type*}

/-- The half-open unit box `∏ i, [c i, c i + 1)` whose lower corner is the natural vector `c`. -/
def natFloorCell (c : ι → ℕ) : Set (ι → ℝ) :=
  Set.univ.pi fun i ↦ Ico (c i : ℝ) ((c i : ℝ) + 1)

/-- Membership in a natural floor cell, unfolded coordinatewise. -/
@[simp]
theorem mem_natFloorCell {c : ι → ℕ} {x : ι → ℝ} :
    x ∈ natFloorCell c ↔ ∀ i, (c i : ℝ) ≤ x i ∧ x i < (c i : ℝ) + 1 := by
  simp [natFloorCell]

/-- Natural floor cells are measurable products of intervals over a countable index type. -/
theorem measurableSet_natFloorCell [Countable ι] (c : ι → ℕ) :
    MeasurableSet (natFloorCell c) :=
  MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Ico

/-- Every natural floor cell has volume one, including the one-point space over an empty
index type. -/
theorem volume_natFloorCell [Fintype ι] (c : ι → ℕ) : volume (natFloorCell c) = 1 := by
  simp [natFloorCell, volume_pi_pi]

/-- A nonnegative vector lies in the cell of `c` exactly when its coordinatewise natural floor is
`c`. Nonnegativity is needed: `⌊x i⌋₊ = 0` for every negative `x i`, while the cell of `0` contains
no vector with a negative coordinate. -/
theorem mem_natFloorCell_iff_natFloor_eq {c : ι → ℕ} {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    x ∈ natFloorCell c ↔ ∀ i, ⌊x i⌋₊ = c i := by
  rw [mem_natFloorCell]
  exact forall_congr' fun i ↦ (Nat.floor_eq_iff (hx i)).symm

/-- A nonnegative vector lies in the cell indexed by its coordinatewise natural floor. -/
theorem mem_natFloorCell_natFloor {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    x ∈ natFloorCell (fun i ↦ ⌊x i⌋₊) :=
  (mem_natFloorCell_iff_natFloor_eq hx).mpr fun _ ↦ rfl

/-- Every point of a natural floor cell has nonnegative coordinates. -/
theorem nonneg_of_mem_natFloorCell {c : ι → ℕ} {x : ι → ℝ} (hx : x ∈ natFloorCell c) (i : ι) :
    0 ≤ x i :=
  (Nat.cast_nonneg (c i)).trans (mem_natFloorCell.mp hx i).1

/-- Distinct natural floor cells are disjoint: a point of a cell determines its index as its
coordinatewise natural floor. -/
theorem pairwise_disjoint_natFloorCell : Pairwise (Disjoint on (natFloorCell (ι := ι))) := by
  intro c d hcd
  rw [Function.onFun, Set.disjoint_left]
  intro x hxc hxd
  have hx := nonneg_of_mem_natFloorCell hxc
  have hc := (mem_natFloorCell_iff_natFloor_eq hx).mp hxc
  have hd := (mem_natFloorCell_iff_natFloor_eq hx).mp hxd
  exact hcd (funext fun i ↦ (hc i).symm.trans (hd i))

variable [Fintype ι]

/-- On the cell of `c`, a linear form with nonnegative coefficients is at least its value at the
lower corner `c`. -/
theorem sum_mul_le_sum_mul_of_mem_natFloorCell {c : ι → ℕ} {x : ι → ℝ} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hx : x ∈ natFloorCell c) :
    ∑ i, a i * (c i : ℝ) ≤ ∑ i, a i * x i :=
  Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (mem_natFloorCell.mp hx i).1 (ha i)

/-- On the cell of `c`, a linear form with nonnegative coefficients exceeds its value at the lower
corner by at most the sum of its coefficients. -/
theorem sum_mul_le_sum_mul_add_sum_of_mem_natFloorCell {c : ι → ℕ} {x : ι → ℝ} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hx : x ∈ natFloorCell c) :
    ∑ i, a i * x i ≤ ∑ i, a i * (c i : ℝ) + ∑ i, a i := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have h := mul_le_mul_of_nonneg_left (mem_natFloorCell.mp hx i).2.le (ha i)
  linarith

end NatFloorCell

end MeasureTheory
