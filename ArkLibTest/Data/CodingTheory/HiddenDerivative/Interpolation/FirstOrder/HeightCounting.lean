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

/-- With one row, the canonical height gives a strict surplus for the four-column support. -/
example :
    1 * (firstOrderCertificateHeight 2 3 1 0 1 1 + 1) <
      firstOrderHeightSlotCount 2 3 1 0 1
        (firstOrderCertificateHeight 2 3 1 0 1 1) := by
  have hcard : (firstOrderExponents 2 3 1 0 1).card = 4 := by
    rw [card_firstOrderExponents (D := 2) (A := 3) (m := 1) (M := 0) (μ := 1) (by omega)]
    decide
  apply firstOrder_rowTotal_mul_height_lt_heightSlotCount (D := 2) (A := 3) (m := 1)
    (M := 0) (μ := 1) (rowTotal := 1) (by omega)
  omega

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
