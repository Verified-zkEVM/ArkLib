/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKit
import ArkLibExamples.ReedSolomon.CurveProfile

/-!
# ProveKit shifted first-order interpolation certificates

Both application rows use the canonical finite first-order support and the same shifted graded
row engine. The BN254 row is the line case `ℓ = 1`; it uses agreement 492831, support
`(384,168,688)`, and height 867623, which is the least height passing the shifted surplus for
that support. The revised cubic Goldilocks row uses agreement 508263, support `(16,7,30)`, and
height 339.
-/

open PolynomialDifferential Polynomial
open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit

open CurveProfile
open ReedSolomon.HiddenDerivative.SymbolicWeightedSupportInterpolation

set_option maxRecDepth 4096

/-- A finite interval sum used to split the large BN254 arithmetic check into kernel-reducible
pieces. -/
private def sumChunk (f : ℕ → ℕ) (start length : ℕ) : ℕ :=
  ∑ i ∈ Finset.range length, f (start + i)

private theorem sumChunk_add (f : ℕ → ℕ) (start a b : ℕ) :
    sumChunk f start (a + b) = sumChunk f start a + sumChunk f (start + a) b := by
  simp only [sumChunk, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.add_assoc]

private theorem shiftedRowSlotBound_eq_sumChunk
    (D A m M μ n ℓ h : ℕ) :
    firstOrderCurveShiftedRowSlotBound D A m M μ n ℓ h =
      sumChunk (fun t ↦ n * firstOrderGradedRankBound D A m M t *
        (h + 1 - ℓ * t)) 0 (μ + 1) := by
  simp [firstOrderCurveShiftedRowSlotBound, sumChunk]

private theorem shiftedHeightSlotCount_eq_sumChunk
    (D A m M μ ℓ h : ℕ) :
    firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h =
      sumChunk (fun t ↦ ∑ b ∈ Finset.range (min t M + 1),
        (m * A + b - D * t) * (h + 1 - ℓ * t)) 0 (μ + 1) := by
  simp [firstOrderCurveShiftedHeightSlotCount, sumChunk]

/-- The degree-`t` shifted row contribution for the BN254 support. -/
private def bn254ShiftedRowTerm (t : ℕ) : ℕ :=
  1048576 * firstOrderGradedRankBound 262143 492831 384 168 t *
    (867623 + 1 - 1 * t)

/-- The degree-`t` shifted source contribution for the BN254 support. -/
private def bn254ShiftedSourceTerm (t : ℕ) : ℕ :=
  ∑ b ∈ Finset.range (min t 168 + 1),
    (384 * 492831 + b - 262143 * t) * (867623 + 1 - 1 * t)

private theorem bn254_shifted_row_slots_eq_sumChunk :
    firstOrderCurveShiftedRowSlotBound 262143 492831 384 168 688 1048576 1 867623 =
      sumChunk bn254ShiftedRowTerm 0 689 := by
  rw [shiftedRowSlotBound_eq_sumChunk]
  rfl

private theorem bn254_shifted_source_slots_eq_sumChunk :
    firstOrderCurveShiftedHeightSlotCount 262143 492831 384 168 688 1 867623 =
      sumChunk bn254ShiftedSourceTerm 0 689 := by
  rw [shiftedHeightSlotCount_eq_sumChunk]
  rfl

private theorem bn254_shifted_row_chunk_zero :
    sumChunk bn254ShiftedRowTerm 0 128 = 2248098769163780096 := by decide

private theorem bn254_shifted_row_chunk_one :
    sumChunk bn254ShiftedRowTerm 128 128 = 3611399677655646208 := by decide

private theorem bn254_shifted_row_chunk_two :
    sumChunk bn254ShiftedRowTerm 256 128 = 1626439830172860416 := by decide

private theorem bn254_shifted_row_chunk_three :
    sumChunk bn254ShiftedRowTerm 384 128 = 363584364132433920 := by decide

private theorem bn254_shifted_row_chunk_four :
    sumChunk bn254ShiftedRowTerm 512 128 = 5409873770577920 := by decide

private theorem bn254_shifted_row_chunk_five :
    sumChunk bn254ShiftedRowTerm 640 49 = 0 := by decide

private theorem bn254_shifted_source_chunk_zero :
    sumChunk bn254ShiftedSourceTerm 0 128 = 1196498687857102304 := by decide

private theorem bn254_shifted_source_chunk_one :
    sumChunk bn254ShiftedSourceTerm 128 128 = 2500797754813413914 := by decide

private theorem bn254_shifted_source_chunk_two :
    sumChunk bn254ShiftedSourceTerm 256 128 = 1979208535621442112 := by decide

private theorem bn254_shifted_source_chunk_three :
    sumChunk bn254ShiftedSourceTerm 384 128 = 1349479233439291968 := by decide

private theorem bn254_shifted_source_chunk_four :
    sumChunk bn254ShiftedSourceTerm 512 128 = 719935748013398592 := by decide

private theorem bn254_shifted_source_chunk_five :
    sumChunk bn254ShiftedSourceTerm 640 49 = 109012555294875960 := by decide

private theorem bn254_shifted_row_slots :
    firstOrderCurveShiftedRowSlotBound 262143 492831 384 168 688 1048576 1 867623 =
      7854932514895298560 := by
  rw [bn254_shifted_row_slots_eq_sumChunk]
  rw [show 689 = 128 + 561 by norm_num, sumChunk_add,
    show 561 = 128 + 433 by norm_num, sumChunk_add,
    show 433 = 128 + 305 by norm_num, sumChunk_add,
    show 305 = 128 + 177 by norm_num, sumChunk_add,
    show 177 = 128 + 49 by norm_num, sumChunk_add,
    bn254_shifted_row_chunk_zero, bn254_shifted_row_chunk_one,
    bn254_shifted_row_chunk_two, bn254_shifted_row_chunk_three,
    bn254_shifted_row_chunk_four, bn254_shifted_row_chunk_five]

private theorem bn254_shifted_source_slots :
    firstOrderCurveShiftedHeightSlotCount 262143 492831 384 168 688 1 867623 =
      7854932515039524850 := by
  rw [bn254_shifted_source_slots_eq_sumChunk]
  rw [show 689 = 128 + 561 by norm_num, sumChunk_add,
    show 561 = 128 + 433 by norm_num, sumChunk_add,
    show 433 = 128 + 305 by norm_num, sumChunk_add,
    show 305 = 128 + 177 by norm_num, sumChunk_add,
    show 177 = 128 + 49 by norm_num, sumChunk_add,
    bn254_shifted_source_chunk_zero, bn254_shifted_source_chunk_one,
    bn254_shifted_source_chunk_two, bn254_shifted_source_chunk_three,
    bn254_shifted_source_chunk_four, bn254_shifted_source_chunk_five]

/-- Height 867623 passes the shifted line surplus for the BN254 support. -/
theorem bn254_interpolation_height :
    firstOrderCurveShiftedRowSlotBound 262143 492831 384 168 688 1048576 1 867623 <
      firstOrderCurveShiftedHeightSlotCount 262143 492831 384 168 688 1 867623 := by
  rw [bn254_shifted_row_slots, bn254_shifted_source_slots]
  norm_num

/-- The full primitive BN254 line certificate produced by the shifted engine. -/
theorem bn254_exists_symbolicCertificate {F : Type*} [Field F]
    (centers : Fin 1048576 ↪ F) (f g : Fin 1048576 → F) :
    Nonempty (FirstOrderSymbolicCertificate 262143 492831 384 168 688 262144 867623
      centers f g (firstOrderColumns
        (D := 262143) (A := 492831) (m := 384) (M := 168) (μ := 688))) := by
  exact exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    (by norm_num) (by norm_num) (by norm_num) centers f g bn254_interpolation_height

/-- Revised cubic Goldilocks interpolation row. -/
def goldilocksCubic113Profile : LineProfile where
  n := 1048576
  k := 262144
  agreement := 508263
  multiplicity := 16
  firstDerivativeCap := 7
  totalJetCap := 30
  batchingDegree := 1
  supportDimension := 828594536
  localRank := 780
  columnY₀Weight := 7427747152
  height := 339
  heightSlots := 274294395088

/-- Lean checks the exact shifted row/source surplus at height 339. -/
theorem goldilocksCubic113_verified : goldilocksCubic113Profile.CurveVerification := by
  decide

/-- The executable shifted row/source surplus used by the scalar Goldilocks list theorem. -/
theorem goldilocksCubic113_interpolation_height :
    firstOrderCurveShiftedRowSlotBound 262143 508263 16 7 30 1048576 1 339 <
      firstOrderCurveShiftedHeightSlotCount 262143 508263 16 7 30 1 339 := by
  simpa [goldilocksCubic113Profile, LineProfile.D, LineProfile.shiftedRowSlots,
    LineProfile.shiftedHeightSlots] using goldilocksCubic113_verified.2.2.2.1

/-- The revised Goldilocks row constructs its actual primitive height-339 curve certificate. -/
theorem goldilocksCubic113_exists_curveCertificate {F : Type*} [Field F]
    (centers : Fin goldilocksCubic113Profile.n ↪ F)
    (w : Fin goldilocksCubic113Profile.n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ goldilocksCubic113Profile.batchingDegree) :
    Nonempty (FirstOrderCurveCertificate goldilocksCubic113Profile.D
      goldilocksCubic113Profile.agreement goldilocksCubic113Profile.multiplicity
      goldilocksCubic113Profile.firstDerivativeCap goldilocksCubic113Profile.totalJetCap
      goldilocksCubic113Profile.k goldilocksCubic113Profile.height centers w
      goldilocksCubic113Profile.columns) :=
  goldilocksCubic113_verified.exists_certificate centers w hw

end ArkLibExamples.ReedSolomon.ProveKit
