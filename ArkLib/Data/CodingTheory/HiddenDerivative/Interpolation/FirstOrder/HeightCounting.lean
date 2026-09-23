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
* `firstOrderCoordinatesEquiv` reindexes support exponents by dimension coordinates, and
  `firstOrderCoordinatesEquiv_y₀` identifies the `Y₀` coordinate.
* `firstOrder_rowTotal_mul_height_lt_columnSlotCount` and
  `firstOrder_rowTotal_mul_height_lt_heightSlotCount` give a strict slot surplus.
* `firstOrderColumns` enumerates the first-order support as distinct symbolic source columns.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26]
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

/-- The exponent vector corresponding to a first-order dimension coordinate triple. -/
def firstOrderCoordinateExponent
    (q : Σ _ : (Σ _ : ℕ, ℕ), ℕ) : JetVariable 1 →₀ ℕ :=
  Finsupp.single none q.2 + Finsupp.single (some 0) (q.1.1 - q.1.2) +
    Finsupp.single (some 1) q.1.2

/-- The `Y₀` exponent corresponding to a dimension coordinate is `t - b`. -/
theorem firstOrderCoordinateExponent_y₀
    (q : Σ _ : (Σ _ : ℕ, ℕ), ℕ) :
    firstOrderCoordinateExponent q (some 0) = q.1.1 - q.1.2 := by
  simp [firstOrderCoordinateExponent]

/-- The finite first-order support is indexed by the dimension coordinate triples. -/
def firstOrderCoordinatesEquiv (hD : 0 < D) :
    (↑(firstOrderExponents D A m M μ)) ≃
      (↑(firstOrderDimensionCoordinates D A m M μ)) := by
  refine
    { toFun := fun u ↦ ⟨⟨⟨u.1 (some 0) + u.1 (some 1), u.1 (some 1)⟩, u.1 none⟩, ?_⟩
      invFun := fun q ↦ ⟨firstOrderCoordinateExponent q.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hu := (mem_firstOrderExponents_iff_coordinates.mp u.2)
    rw [firstOrderWeight_lt_iff_lt_residual hD] at hu
    simp only [firstOrderDimensionCoordinates, Finset.mem_sigma, Finset.mem_range]
    omega
  · have hq := q.2
    simp only [firstOrderDimensionCoordinates, Finset.mem_sigma, Finset.mem_range] at hq
    rcases hq with ⟨⟨ht, hb⟩, hx⟩
    have hbt : q.1.1.2 ≤ q.1.1.1 := by omega
    have ht' : q.1.1.1 ≤ μ := by omega
    have hb' : q.1.1.2 ≤ M := by omega
    have hx' : q.1.2 < m * A + q.1.1.2 - D * q.1.1.1 := by omega
    have hweight : q.1.2 + D * (q.1.1.1 - q.1.1.2) +
        (D - 1) * q.1.1.2 < m * A := by
      rw [firstOrderWeight_lt_iff_lt_residual hD]
      simpa [Nat.sub_add_cancel hbt] using hx'
    rw [mem_firstOrderExponents_iff_coordinates]
    simpa [firstOrderCoordinateExponent] using
      (show q.1.1.2 ≤ M ∧
        (q.1.1.1 - q.1.1.2) + q.1.1.2 ≤ μ ∧
          q.1.2 + D * (q.1.1.1 - q.1.1.2) + (D - 1) * q.1.1.2 < m * A from
        ⟨hb', by omega, hweight⟩)
  · intro u
    apply Subtype.ext
    apply Finsupp.ext
    intro v
    rcases v with _ | j
    · simp [firstOrderCoordinateExponent]
    · fin_cases j <;> simp [firstOrderCoordinateExponent]
  · intro q
    apply Subtype.ext
    have hq := q.2
    simp only [firstOrderDimensionCoordinates, Finset.mem_sigma, Finset.mem_range] at hq
    have hbt : q.1.1.2 ≤ q.1.1.1 := by omega
    simp [firstOrderCoordinateExponent, Nat.sub_add_cancel hbt]

/-- The support exponent's `Y₀` coordinate is its total-jet degree minus its `Y₁` exponent.
The hypothesis `0 < D` is needed to index every support exponent by a dimension coordinate. -/
theorem firstOrderCoordinatesEquiv_y₀ (hD : 0 < D)
    (u : ↑(firstOrderExponents D A m M μ)) :
    u.1 (some 0) =
      (firstOrderCoordinatesEquiv hD u).1.1.1 -
        (firstOrderCoordinatesEquiv hD u).1.1.2 := by
  simp [firstOrderCoordinatesEquiv]

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
  fun j ↦
    let u := ((Fintype.equivFin ↑(firstOrderExponents D A m M μ)).symm j).1
    { x := u none
      y₀ := u (some 0)
      higher := fun k ↦ u (some k.succ) }

/-- The exponent of each enumerated column is its indexed first-order support exponent. -/
@[simp]
theorem firstOrderColumns_exponent
    (j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ))) :
    (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent =
      ((Fintype.equivFin ↑(firstOrderExponents D A m M μ)).symm j).1 := by
  apply Finsupp.ext
  intro v
  rcases v with _ | i
  · simp [firstOrderColumns]
  · fin_cases i <;> simp [firstOrderColumns, SourceColumn.exponent]

/-- Distinct indices enumerate distinct first-order source columns. -/
theorem firstOrderColumns_injective :
    Function.Injective (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) := by
  intro i j hij
  have hExp : ((Fintype.equivFin ↑(firstOrderExponents D A m M μ)).symm i).1 =
      ((Fintype.equivFin ↑(firstOrderExponents D A m M μ)).symm j).1 := by
    rw [← firstOrderColumns_exponent i, ← firstOrderColumns_exponent j]
    exact congrArg SourceColumn.exponent hij
  have hEq : (Fintype.equivFin ↑(firstOrderExponents D A m M μ)).symm i =
      (Fintype.equivFin ↑(firstOrderExponents D A m M μ)).symm j := Subtype.ext hExp
  exact (Fintype.equivFin ↑(firstOrderExponents D A m M μ)).symm.injective hEq

/-- Each enumerated column has an eligible first-order exponent. -/
theorem firstOrderColumns_eligible
    (j : Fin (Fintype.card ↑(firstOrderExponents D A m M μ))) :
    (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ) j).exponent ∈
      firstOrderExponents D A m M μ := by
  rw [firstOrderColumns_exponent]
  exact ((Fintype.equivFin ↑(firstOrderExponents D A m M μ)).symm j).2

end

end ReedSolomon.HiddenDerivative
