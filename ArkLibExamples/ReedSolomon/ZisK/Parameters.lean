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
September 7, 2026 artifact audit: four inner opening groups, the outer combination,
and three folds. The fifth inner group is a singleton and needs no interpolation.
The proposed change reduces 54 queries to 52 and preserves the existing 22-bit hook.
-/
namespace ArkLibExamples.ReedSolomon.ZisK
open _root_.ReedSolomon.CurveProfile

/-- Inner degrees in increasing outer powers order: opening points `2, 1, 0, -1, -2`.
This reverses the opening-point order traversed by the outer Horner evaluation. -/
def innerDegree : Fin 5 → ℕ := ![0, 24, 103, 2, 1]

/-- Exact finite supports and challenge heights for the five batching and three fold curves. -/
def profiles : Fin 8 → LineProfile := ![
  { n := 524288, k := 32768, agreement := 127623, multiplicity := 7,
    firstDerivativeCap := 3, totalJetCap := 26, batchingDegree := 1,
    supportDimension := 45249170, localRank := 84,
    columnY₀Weight := 374580524, height := 244, heightSlots := 10711466126 },
  { n := 524288, k := 32768, agreement := 127623, multiplicity := 7,
    firstDerivativeCap := 3, totalJetCap := 26, batchingDegree := 2,
    supportDimension := 45249170, localRank := 84,
    columnY₀Weight := 374580524, height := 488, heightSlots := 21752263606 },
  { n := 524288, k := 32768, agreement := 127623, multiplicity := 7,
    firstDerivativeCap := 3, totalJetCap := 26, batchingDegree := 103,
    supportDimension := 45249170, localRank := 84,
    columnY₀Weight := 374580524, height := 25179, heightSlots := 1138999520076 },
  { n := 524288, k := 32768, agreement := 127623, multiplicity := 7,
    firstDerivativeCap := 3, totalJetCap := 26, batchingDegree := 24,
    supportDimension := 45249170, localRank := 84,
    columnY₀Weight := 374580524, height := 5867, heightSlots := 265147549036 },
  { n := 524288, k := 32768, agreement := 127623, multiplicity := 7,
    firstDerivativeCap := 3, totalJetCap := 26, batchingDegree := 4,
    supportDimension := 45249170, localRank := 84,
    columnY₀Weight := 374580524, height := 977, heightSlots := 43879107736 },
  { n := 65536, k := 4096, agreement := 15953, multiplicity := 7,
    firstDerivativeCap := 3, totalJetCap := 26, batchingDegree := 7,
    supportDimension := 5657590, localRank := 84,
    columnY₀Weight := 46845060, height := 1696, heightSlots := 9554085170 },
  { n := 8192, k := 512, agreement := 1995, multiplicity := 7,
    firstDerivativeCap := 3, totalJetCap := 26, batchingDegree := 7,
    supportDimension := 709178, localRank := 84,
    columnY₀Weight := 5884700, height := 1547, heightSlots := 1091922844 },
  { n := 1024, k := 64, agreement := 250, multiplicity := 7,
    firstDerivativeCap := 3, totalJetCap := 26, batchingDegree := 7,
    supportDimension := 90448, localRank := 84,
    columnY₀Weight := 762464, height := 965, heightSlots := 86610304 }
 ]

/-- Splits used in the exact exceptional-fiber estimates. -/
def splits : Fin 8 → ℕ := ![37354, 37354, 37350, 37350, 37352, 4671, 586, 75]

/-- Integer ceilings, subsequently proved to bound actual exceptional sets. -/
def exceptionalCounts : Fin 8 → ℕ := ![
  21656247800604350, 43312495601208700, 2234600611179264784,
  520687776177624473, 86710249098918186, 2350811912435207,
  33384690056931, 314563552828]

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
