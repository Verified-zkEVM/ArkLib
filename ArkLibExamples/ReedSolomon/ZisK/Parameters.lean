/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Profile
import ArkLibExamples.ReedSolomon.Fields
/-!
# Parameters of the compressed ZisK final STARK

These are the eight positive-degree curves for `vadcop_final_compressed` in the
September 10, 2026 artifact audit: four inner opening groups, the outer combination,
and three folds. The fifth inner group is a singleton and needs no interpolation.
The proposed change reduces 54 queries to 51 and preserves the existing 22-bit hook.
-/
namespace ArkLibExamples.ReedSolomon.ZisK
open _root_.ReedSolomon.CurveProfile

/-- Inner degrees in increasing outer powers order: opening points `2, 1, 0, -1, -2`.
This reverses the opening-point order traversed by the outer Horner evaluation. -/
def innerDegree : Fin 5 → ℕ := ![0, 24, 103, 2, 1]

/-- Exact finite supports and challenge heights for the five batching and three fold curves. -/
def profiles : Fin 8 → LineProfile := ![
  { n := 524288, k := 32768, agreement := 124136, multiplicity := 10,
    firstDerivativeCap := 6, totalJetCap := 37, batchingDegree := 1,
    supportDimension := 144034345, localRank := 265,
    columnY₀Weight := 1637940367, height := 249, heightSlots := 34370645883 },
  { n := 524288, k := 32768, agreement := 124136, multiplicity := 10,
    firstDerivativeCap := 6, totalJetCap := 37, batchingDegree := 2,
    supportDimension := 144034345, localRank := 265,
    columnY₀Weight := 1637940367, height := 498, heightSlots := 70235197788 },
  { n := 524288, k := 32768, agreement := 124136, multiplicity := 10,
    firstDerivativeCap := 6, totalJetCap := 37, batchingDegree := 103,
    supportDimension := 144034345, localRank := 265,
    columnY₀Weight := 1637940367, height := 25648, heightSlots := 3692698974538 },
  { n := 524288, k := 32768, agreement := 124136, multiplicity := 10,
    firstDerivativeCap := 6, totalJetCap := 37, batchingDegree := 24,
    supportDimension := 144034345, localRank := 265,
    columnY₀Weight := 1637940367, height := 5976, heightSlots := 859255339698 },
  { n := 524288, k := 32768, agreement := 124136, multiplicity := 10,
    firstDerivativeCap := 6, totalJetCap := 37, batchingDegree := 4,
    supportDimension := 144034345, localRank := 265,
    columnY₀Weight := 1637940367, height := 996, heightSlots := 141964301598 },
  { n := 65536, k := 4096, agreement := 15517, multiplicity := 10,
    firstDerivativeCap := 6, totalJetCap := 37, batchingDegree := 7,
    supportDimension := 18009187, localRank := 265,
    columnY₀Weight := 204847461, height := 1731, heightSlots := 30987064423 },
  { n := 8192, k := 512, agreement := 1940, multiplicity := 10,
    firstDerivativeCap := 6, totalJetCap := 37, batchingDegree := 7,
    supportDimension := 2256961, localRank := 265,
    columnY₀Weight := 25726519, height := 1625, heightSlots := 3644092067 },
  { n := 1024, k := 64, agreement := 243, multiplicity := 10,
    firstDerivativeCap := 6, totalJetCap := 37, batchingDegree := 7,
    supportDimension := 288239, localRank := 265,
    columnY₀Weight := 3341625, height := 1096, heightSlots := 312856558 }
 ]

/-- Splits used in the exact exceptional-fiber estimates. -/
def splits : Fin 8 → ℕ := ![36978, 36978, 36978, 36978, 36978, 4623, 579, 74]

/-- Integer ceilings, subsequently proved to bound actual exceptional sets. -/
def exceptionalCounts : Fin 8 → ℕ := ![
  38067076574628351, 76134153149256701, 3921055981081409424,
  913609837791080406, 152268306298513401, 4133214248655057,
  60416130086406, 616878212719]

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
