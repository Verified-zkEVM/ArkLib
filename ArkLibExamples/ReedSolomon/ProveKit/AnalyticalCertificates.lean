/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKit.AnalyticalParameters
import Mathlib.Tactic.NormNum

/-!
# Arithmetic certificates for the analytical ProveKit supports

This file recomputes the exact sharp squarefree expressions selected by the manuscript checker.
It records the interpolation dimensions, local-rank upper bounds, shifted heights, characteristic
guards, exact rational estimates, and their integer ceilings.

The declarations here are deliberately arithmetic certificates, not semantic list-decoding or
agreement theorems. The separate `AnalyticalSemantics` module connects the unchanged configurations
to the reusable squarefree list and MCA theorems, preserving the independent list/MCA supports.
-/

namespace ArkLibExamples.ReedSolomon.ProveKit

/-- Data used by the sharp squarefree one-chart arithmetic. -/
structure SharpFirstOrderData where
  n : ℕ
  k : ℕ
  agreement : ℕ
  support : FirstOrderSupport
  sourceDimension : ℕ
  localRankUpper : ℕ
  height : ℕ
  deriving DecidableEq, Repr

namespace SharpFirstOrderData

/-- Actual message-degree bound `D = k - 1`. -/
def messageDegree (d : SharpFirstOrderData) : ℕ := d.k - 1

/-- The first-order Taylor weight `2D - 1`. -/
def taylorWeight (d : SharpFirstOrderData) : ℕ := 2 * d.messageDegree - 1

/-- Total degree of the regular one-chart image. -/
def regularTotalDegree (d : SharpFirstOrderData) : ℕ :=
  1 + d.taylorWeight * (d.support.jetDegree - 1)

/-- Derivative-variable degree of the regular one-chart image. -/
def regularDerivativeDegree (d : SharpFirstOrderData) : ℕ :=
  min d.regularTotalDegree
    (d.taylorWeight * (d.support.derivativeCap - 1) + d.messageDegree)

/-- Generic-fiber degree of the regular one-chart contribution. -/
def regularFiberDegree (d : SharpFirstOrderData) : ℕ :=
  d.support.jetDegree * d.regularDerivativeDegree +
    d.support.derivativeCap * (d.regularTotalDegree - d.regularDerivativeDegree)

/-- Ordinary-variable envelope of the content-resultant singular contribution. -/
def ordinaryDegree (d : SharpFirstOrderData) : ℕ :=
  max d.support.jetDegree
    ((2 * d.support.derivativeCap - 1) * d.support.jetDegree -
      d.support.derivativeCap ^ 2)

/-- Challenge-degree envelope of the content-resultant singular contribution. -/
def ordinaryHeight (d : SharpFirstOrderData) : ℕ :=
  (2 * d.support.derivativeCap - 1) * d.height

/-- Joint-degree envelope of the regular one-chart contribution. -/
def regularJointDegree (d : SharpFirstOrderData) : ℕ :=
  d.height * (2 * d.regularTotalDegree * d.regularDerivativeDegree -
      d.regularDerivativeDegree ^ 2) +
    2 * (1 + d.taylorWeight * d.height) * d.regularFiberDegree

/-- Joint-degree envelope of the ordinary content-resultant contribution. -/
def ordinaryJointDegree (d : SharpFirstOrderData) : ℕ :=
  d.ordinaryHeight + d.ordinaryDegree +
    4 * d.messageDegree * d.ordinaryDegree * d.ordinaryHeight

/-- The rational shortening factor `(n-D)/(A-D)`. -/
def shorteningFactor (d : SharpFirstOrderData) : ℚ :=
  (d.n - d.messageDegree : ℕ) / (d.agreement - d.messageDegree : ℕ)

/-- Sharp squarefree list expression for one support. -/
def sharpListBound (d : SharpFirstOrderData) : ℚ :=
  d.shorteningFactor * d.regularFiberDegree + d.ordinaryDegree

/-- Sharp squarefree line-MCA expression at a fixed descent threshold. -/
def sharpMcaBound (d : SharpFirstOrderData) (threshold : ℕ) : ℚ :=
  (2 * d.ordinaryDegree - 1) * d.ordinaryHeight +
    d.shorteningFactor * d.ordinaryJointDegree +
    (d.n - d.messageDegree - 1) * d.ordinaryDegree +
    ((d.n - threshold + 1 : ℕ) / (d.agreement - threshold + 1 : ℕ)) *
      d.shorteningFactor * d.regularJointDegree +
    (d.n - threshold : ℕ) *
      ((d.n - d.messageDegree : ℕ) / (threshold - d.messageDegree : ℕ)) *
      d.regularFiberDegree

/-- The characteristic guard selected by the squarefree formulas. -/
def characteristicGuard (d : SharpFirstOrderData) : ℕ :=
  max d.messageDegree d.support.derivativeCap

/-- The source coefficient space strictly exceeds the aggregate local-rank bound. -/
def HasInterpolationSurplus (d : SharpFirstOrderData) : Prop :=
  d.n * d.localRankUpper < d.sourceDimension

end SharpFirstOrderData

/-- Passport fifth-row support used for the MCA exceptional count. -/
def passportOuterAnalyticalMcaData : SharpFirstOrderData where
  n := 16384
  k := 16
  agreement := 394
  support := passportOuterAnalyticalMcaSupport 4
  sourceDimension := 1097099030
  localRankUpper := 66185
  height := 43116

/-- Passport fifth-row support used for the scalar list size. -/
def passportOuterAnalyticalListData : SharpFirstOrderData where
  n := 16384
  k := 16
  agreement := 394
  support := passportOuterAnalyticalListSupport 4
  sourceDimension := 845055981
  localRankUpper := 51562
  height := 1483758

/-- Goldilocks first-row support used for the MCA exceptional count. -/
def goldilocksLookupAnalyticalMcaData : SharpFirstOrderData where
  n := 4096
  k := 1024
  agreement := 1933
  support := goldilocksLookupAnalyticalMcaSupport 0
  sourceDimension := 571856054
  localRankUpper := 139105
  height := 6809

/-- Goldilocks first-row support used for the scalar list size. -/
def goldilocksLookupAnalyticalListData : SharpFirstOrderData where
  n := 4096
  k := 1024
  agreement := 1933
  support := goldilocksLookupAnalyticalListSupport 0
  sourceDimension := 166303690
  localRankUpper := 40600
  height := 441221

theorem passportOuterAnalyticalMca_surplus :
    passportOuterAnalyticalMcaData.HasInterpolationSurplus := by
  norm_num [SharpFirstOrderData.HasInterpolationSurplus, passportOuterAnalyticalMcaData]

theorem passportOuterAnalyticalList_surplus :
    passportOuterAnalyticalListData.HasInterpolationSurplus := by
  norm_num [SharpFirstOrderData.HasInterpolationSurplus, passportOuterAnalyticalListData]

theorem goldilocksLookupAnalyticalMca_surplus :
    goldilocksLookupAnalyticalMcaData.HasInterpolationSurplus := by
  norm_num [SharpFirstOrderData.HasInterpolationSurplus, goldilocksLookupAnalyticalMcaData]

theorem goldilocksLookupAnalyticalList_surplus :
    goldilocksLookupAnalyticalListData.HasInterpolationSurplus := by
  norm_num [SharpFirstOrderData.HasInterpolationSurplus, goldilocksLookupAnalyticalListData]

theorem passportOuterAnalyticalMca_characteristicGuard :
    passportOuterAnalyticalMcaData.characteristicGuard = 60 := by
  have hs := passportOuterAnalytical_supports.1
  norm_num [SharpFirstOrderData.characteristicGuard, SharpFirstOrderData.messageDegree,
    passportOuterAnalyticalMcaData, hs]

theorem passportOuterAnalyticalList_characteristicGuard :
    passportOuterAnalyticalListData.characteristicGuard = 53 := by
  have hs := passportOuterAnalytical_supports.2
  norm_num [SharpFirstOrderData.characteristicGuard, SharpFirstOrderData.messageDegree,
    passportOuterAnalyticalListData, hs]

theorem goldilocksLookupAnalyticalMca_characteristicGuard :
    goldilocksLookupAnalyticalMcaData.characteristicGuard = 1023 := by
  have hs := goldilocksLookupAnalytical_supports.1
  norm_num [SharpFirstOrderData.characteristicGuard, SharpFirstOrderData.messageDegree,
    goldilocksLookupAnalyticalMcaData, hs]

theorem goldilocksLookupAnalyticalList_characteristicGuard :
    goldilocksLookupAnalyticalListData.characteristicGuard = 1023 := by
  have hs := goldilocksLookupAnalytical_supports.2
  norm_num [SharpFirstOrderData.characteristicGuard, SharpFirstOrderData.messageDegree,
    goldilocksLookupAnalyticalListData, hs]

/-- Exact Passport fifth-row MCA bound at the selected threshold 19. -/
theorem passportOuterAnalyticalMca_exact :
    passportOuterAnalyticalMcaData.sharpMcaBound 19 =
      (718222660229194099738 : ℚ) / 17813 := by
  have hs := passportOuterAnalytical_supports.1
  norm_num [SharpFirstOrderData.sharpMcaBound, SharpFirstOrderData.shorteningFactor,
    SharpFirstOrderData.ordinaryJointDegree, SharpFirstOrderData.regularJointDegree,
    SharpFirstOrderData.ordinaryHeight, SharpFirstOrderData.ordinaryDegree,
    SharpFirstOrderData.regularFiberDegree, SharpFirstOrderData.regularDerivativeDegree,
    SharpFirstOrderData.regularTotalDegree, SharpFirstOrderData.taylorWeight,
    SharpFirstOrderData.messageDegree, passportOuterAnalyticalMcaData,
    hs]

/-- The Passport MCA integer is the exact ceiling of the sharp rational expression. -/
theorem passportOuterAnalyticalMca_ceiling :
    (40320140359804305 : ℚ) < passportOuterAnalyticalMcaData.sharpMcaBound 19 ∧
      passportOuterAnalyticalMcaData.sharpMcaBound 19 ≤ 40320140359804306 := by
  rw [passportOuterAnalyticalMca_exact]
  norm_num

/-- Exact Passport fifth-row list expression from its independent list support. -/
theorem passportOuterAnalyticalList_exact :
    passportOuterAnalyticalListData.sharpListBound =
      (68382703067 : ℚ) / 379 := by
  have hs := passportOuterAnalytical_supports.2
  norm_num [SharpFirstOrderData.sharpListBound, SharpFirstOrderData.shorteningFactor,
    SharpFirstOrderData.ordinaryDegree, SharpFirstOrderData.regularFiberDegree,
    SharpFirstOrderData.regularDerivativeDegree, SharpFirstOrderData.regularTotalDegree,
    SharpFirstOrderData.taylorWeight, SharpFirstOrderData.messageDegree,
    passportOuterAnalyticalListData, hs]

/-- The Passport list integer is the exact ceiling of its sharp rational expression. -/
theorem passportOuterAnalyticalList_ceiling :
    (180429295 : ℚ) < passportOuterAnalyticalListData.sharpListBound ∧
      passportOuterAnalyticalListData.sharpListBound ≤ 180429296 := by
  rw [passportOuterAnalyticalList_exact]
  norm_num

/-- Exact Goldilocks first-row MCA bound at the selected threshold 1028. -/
theorem goldilocksLookupAnalyticalMca_exact :
    goldilocksLookupAnalyticalMcaData.sharpMcaBound 1028 =
      (246683662443910870239 : ℚ) / 19630 := by
  have hs := goldilocksLookupAnalytical_supports.1
  norm_num [SharpFirstOrderData.sharpMcaBound, SharpFirstOrderData.shorteningFactor,
    SharpFirstOrderData.ordinaryJointDegree, SharpFirstOrderData.regularJointDegree,
    SharpFirstOrderData.ordinaryHeight, SharpFirstOrderData.ordinaryDegree,
    SharpFirstOrderData.regularFiberDegree, SharpFirstOrderData.regularDerivativeDegree,
    SharpFirstOrderData.regularTotalDegree, SharpFirstOrderData.taylorWeight,
    SharpFirstOrderData.messageDegree, goldilocksLookupAnalyticalMcaData,
    hs]

/-- The Goldilocks MCA integer is the exact ceiling of the sharp rational expression. -/
theorem goldilocksLookupAnalyticalMca_ceiling :
    (12566666451549203 : ℚ) < goldilocksLookupAnalyticalMcaData.sharpMcaBound 1028 ∧
      goldilocksLookupAnalyticalMcaData.sharpMcaBound 1028 ≤ 12566666451549204 := by
  rw [goldilocksLookupAnalyticalMca_exact]
  norm_num

/-- Exact Goldilocks first-row list expression from its independent list support. -/
theorem goldilocksLookupAnalyticalList_exact :
    goldilocksLookupAnalyticalListData.sharpListBound =
      (2581881416 : ℚ) / 65 := by
  have hs := goldilocksLookupAnalytical_supports.2
  norm_num [SharpFirstOrderData.sharpListBound, SharpFirstOrderData.shorteningFactor,
    SharpFirstOrderData.ordinaryDegree, SharpFirstOrderData.regularFiberDegree,
    SharpFirstOrderData.regularDerivativeDegree, SharpFirstOrderData.regularTotalDegree,
    SharpFirstOrderData.taylorWeight, SharpFirstOrderData.messageDegree,
    goldilocksLookupAnalyticalListData, hs]

/-- The Goldilocks list integer is the exact ceiling of its sharp rational expression. -/
theorem goldilocksLookupAnalyticalList_ceiling :
    (39721252 : ℚ) < goldilocksLookupAnalyticalListData.sharpListBound ∧
      goldilocksLookupAnalyticalListData.sharpListBound ≤ 39721253 := by
  rw [goldilocksLookupAnalyticalList_exact]
  norm_num

end ArkLibExamples.ReedSolomon.ProveKit
