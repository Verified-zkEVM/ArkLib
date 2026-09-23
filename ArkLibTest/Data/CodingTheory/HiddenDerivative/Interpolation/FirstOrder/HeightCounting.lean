/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.HeightCounting
import Mathlib.Tactic.NormNum

/-!
# First-order height-count acceptance tests

The examples compute the nested height sum, check the support-coordinate reindexing, and apply the
canonical strict surplus to a concrete first-order support. The `D = 0` case shows that the
coordinate count can include tuples that do not satisfy the first-order support condition.
-/

open ReedSolomon.HiddenDerivative
open PolynomialDifferential
open scoped BigOperators

/-- At `(D,A,m,M,μ,h) = (2,3,1,0,1,1)`, the first-order height sum is seven. -/
example : firstOrderHeightSlotCount 2 3 1 0 1 1 = 7 := by decide

/-- At positive degree, the support-side slot count agrees with the executable nested sum. -/
example : firstOrderColumnSlotCount 2 3 1 0 1 1 = 7 := by
  rw [firstOrderColumnSlotCount_eq_heightSlotCount (D := 2) (A := 3) (m := 1) (M := 0)
    (μ := 1) (h := 1) (by omega)]
  decide

/-- Coordinate triples of the same parameters contribute the same seven height slots. -/
example :
    (Finset.univ.sum fun q : ↑(firstOrderDimensionCoordinates 2 3 1 0 1) ↦
      2 - (q.1.1.1 - q.1.1.2)) = 7 := by
  rw [sum_firstOrderDimensionCoordinates_height]
  decide

/-- At height one, the four-column support has seven slots, so one row gives `2 < 7`. -/
example : firstOrderCertificateHeight 2 3 1 0 1 1 = 1 ∧
    firstOrderHeightSlotCount 2 3 1 0 1
        (firstOrderCertificateHeight 2 3 1 0 1 1) = 7 ∧ 2 < 7 := by
  have hcard : (firstOrderExponents 2 3 1 0 1).card = 4 := by
    rw [card_firstOrderExponents (D := 2) (A := 3) (m := 1) (M := 0) (μ := 1) (by omega)]
    decide
  have hweight :
      (firstOrderExponents 2 3 1 0 1).sum (fun u ↦ u (some 0)) = 1 := by
    have hD : 0 < 2 := by omega
    let e := firstOrderCoordinatesEquiv (D := 2) (A := 3) (m := 1) (M := 0) (μ := 1) hD
    rw [← Finset.sum_attach]
    calc
      (Finset.univ.sum fun u : ↑(firstOrderExponents 2 3 1 0 1) ↦ u.1 (some 0)) =
          (Finset.univ.sum fun q : ↑(firstOrderDimensionCoordinates 2 3 1 0 1) ↦
            q.1.1.1 - q.1.1.2) := by
        rw [← e.sum_comp]
        apply Finset.sum_congr rfl
        intro u _
        rw [firstOrderCoordinatesEquiv_y₀ hD]
      _ = 1 := by decide
  have hheight : firstOrderCertificateHeight 2 3 1 0 1 1 = 1 := by
    change max 1 ((firstOrderExponents 2 3 1 0 1).sum (fun u ↦ u (some 0)) /
      ((firstOrderExponents 2 3 1 0 1).card - 1)) = 1
    rw [hweight, hcard]
    decide
  have hslots : firstOrderHeightSlotCount 2 3 1 0 1
      (firstOrderCertificateHeight 2 3 1 0 1 1) = 7 := by
    rw [hheight]
    decide
  refine ⟨hheight, hslots, ?_⟩
  have hsurplus :=
    firstOrder_rowTotal_mul_height_lt_heightSlotCount (D := 2) (A := 3) (m := 1)
      (M := 0) (μ := 1) (rowTotal := 1) (by omega) (by omega)
  rw [hslots, hheight] at hsurplus
  change 2 < 7 at hsurplus
  exact hsurplus

/-- For `D = 0`, the support is empty while the coordinate formula counts two slots. -/
example : firstOrderColumnSlotCount 0 0 1 1 1 1 = 0 ∧
    firstOrderHeightSlotCount 0 0 1 1 1 1 = 2 := by
  have hempty : firstOrderExponents 0 0 1 1 1 = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro u hu
    have hw := (mem_firstOrderExponents_iff_coordinates.mp hu).2.2
    norm_num at hw
  constructor
  · simp [firstOrderColumnSlotCount, hempty]
  · decide

/-- The complete finite support supplies distinct eligible `SourceColumn`s. -/
example :
    Function.Injective (firstOrderColumns (D := 2) (A := 3) (m := 1) (M := 0) (μ := 1)) ∧
      ∀ j, (firstOrderColumns (D := 2) (A := 3) (m := 1) (M := 0) (μ := 1) j).exponent ∈
        firstOrderExponents 2 3 1 0 1 :=
  ⟨firstOrderColumns_injective, firstOrderColumns_eligible⟩

/-- At `(D,A,m,M,μ) = (2,1,3,0,1)`, total degree zero contributes three exponents and total
degree one contributes one, for four dimension coordinates. -/
example : firstOrderDimensionCount 2 1 3 0 1 = 4 := by
  decide

/-- The finite first-order support has four elements, matching its dimension-coordinate count. -/
example : Fintype.card ↑(firstOrderExponents 2 1 3 0 1) = 4 := by
  calc
    Fintype.card ↑(firstOrderExponents 2 1 3 0 1) =
        (firstOrderExponents 2 1 3 0 1).card := Fintype.card_coe _
    _ = firstOrderDimensionCount 2 1 3 0 1 :=
      card_firstOrderExponents (D := 2) (A := 1) (m := 3) (M := 0) (μ := 1) (by omega)
    _ = 4 := by decide

/-- Exponent images of the four enumerated columns cover exactly the concrete support. -/
example :
    SourceColumn.exponent '' Set.range
      (firstOrderColumns (D := 2) (A := 1) (m := 3) (M := 0) (μ := 1)) =
      (firstOrderExponents 2 1 3 0 1 : Set (JetVariable 1 →₀ ℕ)) := by
  ext u
  constructor
  · rintro ⟨c, ⟨j, rfl⟩, hu⟩
    rw [← hu]
    exact firstOrderColumns_eligible j
  · intro hu
    obtain ⟨j, hj⟩ :=
      (Fintype.equivFin ↑(firstOrderExponents 2 1 3 0 1)).symm.surjective ⟨u, hu⟩
    refine ⟨firstOrderColumns j, ⟨j, rfl⟩, ?_⟩
    simpa only [firstOrderColumns_exponent] using congrArg Subtype.val hj
