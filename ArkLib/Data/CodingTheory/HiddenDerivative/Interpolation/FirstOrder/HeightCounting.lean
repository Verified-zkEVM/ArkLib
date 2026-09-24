/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Dimension
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.SourceColumn
public import ArkLib.ToMathlib.BigOperators.LinearBudget

/-!
# Height counts for first-order interpolation

The first-order support columns each provide `h + 1 - y₀` coefficient slots at height `h`.
Reindexing by total jet degree `t` and first-jet exponent `b` gives the executable sum
`∑_{t ≤ μ} ∑_{b ≤ min t M} (m A + b - D t) (h + 1 - (t - b))`. A canonical height from the
total `Y₀`-weight makes this slot count strictly exceed any row budget below the support size.
The support also enumerates as distinct symbolic source columns for the interpolation API.

## Main statements

* `firstOrderColumnSlotCount_eq_heightSlotCount` identifies the support sum and its executable
  nested sum.
* `firstOrder_rowTotal_mul_height_lt_columnSlotCount` and
  `firstOrder_rowTotal_mul_height_lt_heightSlotCount` give a strict slot surplus.
* `firstOrderColumns` enumerates the first-order support as distinct symbolic source columns.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential
open Finset
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {D A m M μ h rowTotal : ℕ}

/-- The total number of polynomial coefficient slots at height `h` over first-order support. -/
def firstOrderColumnSlotCount (D A m M μ h : ℕ) : ℕ :=
  Finset.sum (firstOrderExponents D A m M μ) fun u ↦ h + 1 - u (some 0)

/-- The executable nested sum for the first-order column slots at height `h`. -/
def firstOrderHeightSlotCount (D A m M μ h : ℕ) : ℕ :=
  Finset.sum (Finset.range (μ + 1)) fun t ↦
    Finset.sum (Finset.range (min t M + 1)) fun b ↦
      (m * A + b - D * t) * (h + 1 - (t - b))

/-- The sum of `Y₀` exponents over first-order support columns. -/
def firstOrderY₀Weight (D A m M μ : ℕ) : ℕ :=
  Finset.sum (firstOrderExponents D A m M μ) fun u ↦ u (some 0)

/-- Every first-order support column has `Y₀` exponent at most the total-jet cap. -/
theorem firstOrder_y₀_le_μ {u : JetVariable 1 →₀ ℕ}
    (hu : u ∈ firstOrderExponents D A m M μ) : u (some 0) ≤ μ := by
  calc
    u (some 0) = u.some 0 := rfl
    _ ≤ Finsupp.degree u.some := Finsupp.le_degree 0 u.some
    _ = totalJetDegree u := (totalJetDegree_eq_degree_some u).symm
    _ ≤ μ := (mem_firstOrderExponents.mp hu).2.1

/-- The support slot count and total `Y₀`-weight form a rectangle above the total-jet cap. -/
theorem firstOrderColumnSlotCount_add_y₀Weight (hμ : μ ≤ h) :
    firstOrderColumnSlotCount D A m M μ h + firstOrderY₀Weight D A m M μ =
      (firstOrderExponents D A m M μ).card * (h + 1) := by
  simpa [firstOrderColumnSlotCount, firstOrderY₀Weight] using
    (Finset.sum_tsub_add_sum_eq_card_mul (firstOrderExponents D A m M μ)
      (fun u ↦ u (some 0)) h
      (fun u hu => (firstOrder_y₀_le_μ hu).trans
        (hμ.trans (Nat.le_add_right h 1))))

/-- The canonical height from the dimension surplus and total `Y₀`-weight. -/
def firstOrderCertificateHeight (D A m M μ rowTotal : ℕ) : ℕ :=
  Finset.slotSurplusHeight (firstOrderExponents D A m M μ)
    (fun u ↦ u (some 0)) μ rowTotal

/-- A row budget below the support size has strictly fewer rows than first-order coefficient slots
at the canonical height. -/
theorem firstOrder_rowTotal_mul_height_lt_columnSlotCount
    (hrank : rowTotal < (firstOrderExponents D A m M μ).card) :
    rowTotal * (firstOrderCertificateHeight D A m M μ rowTotal + 1) <
      firstOrderColumnSlotCount D A m M μ
        (firstOrderCertificateHeight D A m M μ rowTotal) := by
  simpa [firstOrderCertificateHeight, firstOrderColumnSlotCount] using
    (Finset.rows_mul_slotSurplusHeight_add_one_lt_sum_tsub
      (firstOrderExponents D A m M μ) (fun u ↦ u (some 0)) μ rowTotal hrank
      (fun u hu => firstOrder_y₀_le_μ hu))

/-- The dimension-coordinate sum counts the same height slots as `firstOrderHeightSlotCount`. -/
theorem sum_firstOrderDimensionCoordinates_height (D A m M μ h : ℕ) :
    (Finset.univ.sum fun q : ↑(firstOrderDimensionCoordinates D A m M μ) ↦
      h + 1 - (q.1.1.1 - q.1.1.2)) = firstOrderHeightSlotCount D A m M μ h := by
  classical
  let f : (Σ _ : (Σ _ : ℕ, ℕ), ℕ) → ℕ :=
    fun q ↦ h + 1 - (q.1.1 - q.1.2)
  have hsum : (Finset.univ.sum fun q : ↑(firstOrderDimensionCoordinates D A m M μ) ↦
      f q.1) = (firstOrderDimensionCoordinates D A m M μ).sum f := by
    rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach]
  rw [hsum, firstOrderDimensionCoordinates, Finset.sum_sigma, Finset.sum_sigma]
  simp [firstOrderHeightSlotCount, Finset.sum_const, Finset.card_range]

/-- The support-side slot sum is the executable first-order height sum. -/
theorem firstOrderColumnSlotCount_eq_heightSlotCount (hD : 0 < D) :
    firstOrderColumnSlotCount D A m M μ h = firstOrderHeightSlotCount D A m M μ h := by
  rw [firstOrderColumnSlotCount, ← Finset.sum_attach]
  let e := firstOrderCoordinatesEquiv (D := D) (A := A) (m := m) (M := M) (μ := μ) hD
  calc
    (Finset.univ.sum fun u : ↑(firstOrderExponents D A m M μ) ↦ h + 1 - u.1 (some 0)) =
        Finset.univ.sum fun q : ↑(firstOrderDimensionCoordinates D A m M μ) ↦
          h + 1 - (q.1.1.1 - q.1.1.2) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro u _
      congr 1
      rw [firstOrderCoordinatesEquiv_y₀ hD]
    _ = firstOrderHeightSlotCount D A m M μ h :=
      sum_firstOrderDimensionCoordinates_height D A m M μ h

/-- The support-side height inequality in its executable nested-sum form. -/
theorem firstOrder_rowTotal_mul_height_lt_heightSlotCount (hD : 0 < D)
    (hrank : rowTotal < (firstOrderExponents D A m M μ).card) :
    rowTotal * (firstOrderCertificateHeight D A m M μ rowTotal + 1) <
      firstOrderHeightSlotCount D A m M μ
        (firstOrderCertificateHeight D A m M μ rowTotal) := by
  rw [← firstOrderColumnSlotCount_eq_heightSlotCount hD]
  exact firstOrder_rowTotal_mul_height_lt_columnSlotCount hrank

/-- Enumerate every first-order support exponent as a symbolic source column. -/
def firstOrderColumns :
    Fin (Fintype.card ↑(firstOrderExponents D A m M μ)) → SourceColumn 1 :=
  SourceColumn.enumerate (firstOrderExponents D A m M μ)

/-- The exponent of each enumerated column is its indexed first-order support exponent. -/
@[simp]
theorem firstOrderColumns_exponent
    (j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ))) :
    (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent =
      ((Fintype.equivFin ↑(firstOrderExponents D A m M μ)).symm j).1 := by
  exact SourceColumn.exponent_enumerate _ _

/-- Distinct indices enumerate distinct first-order source columns. -/
theorem firstOrderColumns_injective :
    Function.Injective (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) := by
  exact SourceColumn.enumerate_injective _

/-- Each enumerated column has an eligible first-order exponent. -/
theorem firstOrderColumns_eligible
    (j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ))) :
    (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent ∈
      firstOrderExponents D A m M μ := by
  exact SourceColumn.exponent_enumerate_mem _ _

end

end ReedSolomon.HiddenDerivative
