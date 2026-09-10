/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.MeasureTheory.Integral.FiniteCells
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
/-!
# Finite natural flooring cells

The half-open unit boxes indexed by natural vectors have volume one and are pairwise disjoint.
A bounded nonnegative region is the union of its intersections with finitely many such boxes.
Integrating cellwise bounds therefore gives a finite sum without counting any cell more than
once. This is the geometric comparison used by weighted lattice counts.
-/

@[expose] public section

open Set

namespace MeasureTheory

noncomputable section
variable {ι : Type*}
/-- The half-open unit box whose lower corner is the natural vector `c`. -/
def natFloorCell (c : ι → ℕ) : Set (ι → ℝ) :=
  Set.pi Set.univ fun i ↦ Ico (c i : ℝ) ((c i : ℝ) + 1)

/-- Natural flooring cells are measurable finite products of intervals. -/
lemma measurableSet_natFloorCell [Countable ι] (c : ι → ℕ) : MeasurableSet (natFloorCell c) := by
  exact MeasurableSet.pi Set.countable_univ (fun _ _ ↦ measurableSet_Ico)

/-- Every flooring cell has volume one, including the empty-coordinate product. -/
lemma volume_natFloorCell [Fintype ι] (c : ι → ℕ) : volume (natFloorCell c) = 1 := by
  simp [natFloorCell, volume_pi_pi]

/-- For nonnegative coordinates, the cell index is exactly the coordinatewise natural floor. -/
lemma mem_natFloorCell_iff {c : ι → ℕ} {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    x ∈ natFloorCell c ↔ ∀ i, ⌊x i⌋₊ = c i := by
  simp only [natFloorCell, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ico]
  exact forall_congr' fun i ↦ (Nat.floor_eq_iff (hx i)).symm

/-- Distinct natural vectors give disjoint cells. -/
lemma disjoint_natFloorCell {c d : ι → ℕ} (h : c ≠ d) :
    Disjoint (natFloorCell c) (natFloorCell d) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hnonneg : ∀ i, 0 ≤ x i := fun i ↦ (Nat.cast_nonneg (c i)).trans (hx i trivial).1
  have hc := (mem_natFloorCell_iff hnonneg).mp hx
  have hd := (mem_natFloorCell_iff hnonneg).mp hy
  exact h (funext fun i ↦ (hc i).symm.trans (hd i))

/-- A bounded nonnegative region is covered exactly by its finitely indexed flooring cells. -/
lemma bounded_region_eq_union_natFloorCells {N : ℕ} (S : Set (ι → ℝ))
    (hnonneg : ∀ x ∈ S, ∀ i, 0 ≤ x i)
    (hbounded : ∀ x ∈ S, ∀ i, x i < N + 1) :
    S = ⋃ c : ι → Fin (N + 1), S ∩ natFloorCell (fun i ↦ (c i).val) := by
  ext x
  constructor
  · intro hx
    let c : ι → Fin (N + 1) := fun i ↦ ⟨⌊x i⌋₊, by
      apply (Nat.floor_lt (hnonneg x hx i)).mpr
      exact_mod_cast hbounded x hx i⟩
    apply Set.mem_iUnion.mpr
    refine ⟨c, hx, (mem_natFloorCell_iff (hnonneg x hx)).mpr ?_⟩
    intro i
    rfl
  · intro hx
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hx
    exact hc.1


/-- Integrating over a bounded region cannot exceed a finite sum of cellwise bounds.
Intersecting each cell with the region can only decrease its volume. -/
lemma integral_bounded_region_le_natFloor_sum [Fintype ι] [DecidableEq ι] {N : ℕ}
    (S : Set (ι → ℝ)) (hS : MeasurableSet S) (f : (ι → ℝ) → ℝ)
    (w : (ι → Fin (N + 1)) → ℝ)
    (hnonneg : ∀ x ∈ S, ∀ i, 0 ≤ x i)
    (hbounded : ∀ x ∈ S, ∀ i, x i < N + 1)
    (hint : IntegrableOn f S volume)
    (hw : ∀ c, 0 ≤ w c)
    (hbound : ∀ c, ∀ x ∈ S ∩ natFloorCell (fun i ↦ (c i).val), ‖f x‖ ≤ w c) :
    (∫ x in S, f x) ≤ ∑ c, w c := by
  classical
  let cells := fun c : ι → Fin (N + 1) ↦ S ∩ natFloorCell (fun i ↦ (c i).val)
  have hmeas : ∀ c, MeasurableSet (cells c) := fun c ↦ hS.inter (measurableSet_natFloorCell _)
  have hdisj : Pairwise (fun c d ↦ Disjoint (cells c) (cells d)) := by
    intro c d hcd
    apply Disjoint.mono Set.inter_subset_right Set.inter_subset_right
    apply disjoint_natFloorCell
    intro he
    apply hcd
    funext i
    exact Fin.ext (congrFun he i)
  have hvol : ∀ c, volume (cells c) ≤ 1 := by
    intro c
    exact (measure_mono Set.inter_subset_right).trans_eq (volume_natFloorCell _)
  have h := integral_biUnion_le_sum_of_cell_measure_le_one Finset.univ cells f w
    (fun c _ ↦ hmeas c) (fun c _ d _ hcd ↦ hdisj hcd)
    (fun c _ ↦ hint.mono_set Set.inter_subset_left) (fun c _ ↦ hvol c)
    (fun c _ ↦ hw c) (fun c _ ↦ hbound c)
  simpa only [cells, Finset.mem_univ, iUnion_true,
    ← bounded_region_eq_union_natFloorCells S hnonneg hbounded] using h

end
/-- Flooring nonnegative coordinates loses at most one per coordinate in their sum. -/
theorem sum_natFloor_bounds {ι : Type*} [Fintype ι] (u : ι → ℝ)
    (hu : ∀ i, 0 ≤ u i) :
    (∑ i, (Nat.floor (u i) : ℝ)) ≤ ∑ i, u i ∧
      (∑ i, u i) - Fintype.card ι ≤ ∑ i, (Nat.floor (u i) : ℝ) := by
  constructor
  · exact Finset.sum_le_sum fun i hi ↦ Nat.floor_le (hu i)
  · have h := Finset.sum_le_sum (s := Finset.univ)
      (fun i hi ↦ (Nat.lt_floor_add_one (u i)).le)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] at h
    linarith


end MeasureTheory
