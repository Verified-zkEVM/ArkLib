/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLibExamples.ReedSolomon.CurveProfile
import ArkLibExamples.ReedSolomon.Fields

/-!
# Parameters of the compressed ZisK final STARK

These are the eight positive-degree curves for `vadcop_final_compressed` in the
September 7, 2026 artifact audit: four inner opening groups, the outer combination,
and three folds. The fifth inner group is a singleton and needs no interpolation.
The proposed change reduces 54 queries to 53 and preserves the existing 22-bit hook.
-/
namespace ArkLibExamples.ReedSolomon.ZisK
open CurveProfile

/-- Inner degrees in increasing outer powers order: opening points `2, 1, 0, -1, -2`.
This reverses the opening-point order traversed by the outer Horner evaluation. -/
def innerDegree : Fin 5 → ℕ := ![0, 24, 103, 2, 1]

/-- Exact finite supports and challenge heights for the five batching and three fold curves. -/
def profiles : Fin 8 → LineProfile := ![
  { n := 524288, k := 32768, agreement := 131069, multiplicity := 6,
    firstDerivativeCap := 3, totalJetCap := 21, batchingDegree := 1,
    supportDimension := 34340426, localRank := 62,
    columnY₀Weight := 241990210, height := 105, heightSlots := 3398094946 },
  { n := 524288, k := 32768, agreement := 131069, multiplicity := 6,
    firstDerivativeCap := 3, totalJetCap := 21, batchingDegree := 2,
    supportDimension := 34340426, localRank := 62,
    columnY₀Weight := 241990210, height := 211, heightSlots := 7038180102 },
  { n := 524288, k := 32768, agreement := 131069, multiplicity := 6,
    firstDerivativeCap := 3, totalJetCap := 21, batchingDegree := 103,
    supportDimension := 34340426, localRank := 62,
    columnY₀Weight := 241990210, height := 10909, heightSlots := 374412057450 },
  { n := 524288, k := 32768, agreement := 131069, multiplicity := 6,
    firstDerivativeCap := 3, totalJetCap := 21, batchingDegree := 24,
    supportDimension := 34340426, localRank := 62,
    columnY₀Weight := 241990210, height := 2542, heightSlots := 87085713108 },
  { n := 524288, k := 32768, agreement := 131069, multiplicity := 6,
    firstDerivativeCap := 3, totalJetCap := 21, batchingDegree := 4,
    supportDimension := 34340426, localRank := 62,
    columnY₀Weight := 241990210, height := 423, heightSlots := 14318350414 },
  { n := 65536, k := 4096, agreement := 16384, multiplicity := 6,
    firstDerivativeCap := 3, totalJetCap := 21, batchingDegree := 7,
    supportDimension := 4293646, localRank := 62,
    columnY₀Weight := 30261926, height := 738, heightSlots := 3142742468 },
  { n := 8192, k := 512, agreement := 2048, multiplicity := 6,
    firstDerivativeCap := 3, totalJetCap := 21, batchingDegree := 7,
    supportDimension := 537614, localRank := 62,
    columnY₀Weight := 3794086, height := 718, heightSlots := 382750380 },
  { n := 1024, k := 64, agreement := 256, multiplicity := 5,
    firstDerivativeCap := 2, totalJetCap := 19, batchingDegree := 7,
    supportDimension := 37168, localRank := 35,
    columnY₀Weight := 227414, height := 971, heightSlots := 35899882 }
 ]

/-- Splits used in the exact exceptional-fiber estimates. -/
def splits : Fin 8 → ℕ := ![39863, 39847, 39835, 39835, 39840, 4981, 623, 75]

/-- Integer ceilings, subsequently proved to bound actual exceptional sets. -/
def exceptionalCounts : Fin 8 → ℕ := ![
  42856230830712318, 86096673661637490, 4450305636508366542,
  1037001715557082149, 172577519297966305, 4701453548397283,
  71138720230254, 796551213271]

/-- Cardinality of the actual cubic Goldilocks challenge field. -/
def fieldSize : ℕ := 6277101731002175853884774869567645561244584131361410908161

/-- The concrete finite field has the advertised number of elements. -/
theorem fieldSize_eq : Fintype.card ConcreteFields.GoldilocksCubic = fieldSize := by
  rw [ConcreteFields.goldilocksCubic_card]
  rfl

/-- Each exact support satisfies the shifted curve-constructor inequalities. -/
theorem profiles_verified (i : Fin 8) : (profiles i).CurveVerification := by
  fin_cases i <;> decide +kernel

end ArkLibExamples.ReedSolomon.ZisK
