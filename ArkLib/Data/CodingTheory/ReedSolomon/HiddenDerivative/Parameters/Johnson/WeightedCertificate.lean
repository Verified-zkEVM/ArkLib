/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Johnson.FiniteBounds
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Exact weighted finite Johnson certificates

This file records the integer arithmetic behind the tuned ordinary Johnson interpolation
certificate.  For multiplicity `m`, agreement count `A`, candidate-degree cap `D`, and jet cutoff
`B`, the source slices have widths `m * A - D * j`.  The local rows stop at
`u = min B (m - 1)`.  Their zeroth and first moments are

`N = sum_j (mA-Dj)`, `W = sum_j j(mA-Dj)`,
`R = sum_b (m-b)`, and `T = sum_b b(m-b)`.

The difference `W - n*T` is deliberately represented in `Int`: it may be negative for a valid
small certificate.  When `N > n*R`, the paper's height

`max B (floor ((W-n*T)/(N-n*R)))`

is therefore exact at both positive and negative moments.  All definitions remain total at zero;
the mathematical certificate predicate records the positive multiplicity, jet, cutoff, and slope
guards separately.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open scoped BigOperators

/-- Largest active local-row grade.  It is zero when `m = 0`. -/
def johnsonWeightedU (m B : ℕ) : ℕ :=
  min B (m - 1)

/-- Zeroth moment of the strict source widths `m*A-D*j`, for `0 ≤ j ≤ B`. -/
def johnsonWeightedN (D A m B : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (B + 1), (m * A - D * j)

/-- First moment of the strict source widths `m*A-D*j`, for `0 ≤ j ≤ B`. -/
def johnsonWeightedW (D A m B : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (B + 1), j * (m * A - D * j)

/-- Zeroth moment of the active triangular local rows. -/
def johnsonWeightedR (m B : ℕ) : ℕ :=
  ∑ b ∈ Finset.range (johnsonWeightedU m B + 1), (m - b)

/-- First moment of the active triangular local rows. -/
def johnsonWeightedT (m B : ℕ) : ℕ :=
  ∑ b ∈ Finset.range (johnsonWeightedU m B + 1), b * (m - b)

/-- Exact coefficient surplus `N-nR`.  The certificate requires it to be positive. -/
def johnsonWeightedSlope (n D A m B : ℕ) : ℤ :=
  (johnsonWeightedN D A m B : ℤ) -
    (n : ℤ) * (johnsonWeightedR m B : ℤ)

/-- Exact weighted moment `W-nT`, retained in `Int` so negative moments are not truncated. -/
def johnsonWeightedMoment (n D A m B : ℕ) : ℤ :=
  (johnsonWeightedW D A m B : ℤ) -
    (n : ℤ) * (johnsonWeightedT m B : ℤ)

/-- The paper's integer height before conversion back to a natural challenge degree. -/
def johnsonWeightedHeightInt (n D A m B : ℕ) : ℤ :=
  max (B : ℤ) (johnsonWeightedMoment n D A m B / johnsonWeightedSlope n D A m B)

/-- Natural challenge height attached to the exact integer floor. -/
def johnsonWeightedHeight (n D A m B : ℕ) : ℕ :=
  (johnsonWeightedHeightInt n D A m B).toNat

/-- Literal number of source coefficient slots at challenge height `H`. -/
def johnsonWeightedSourceSlots (D A m B H : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (B + 1), (m * A - D * j) * (H + 1 - j)

/-- Literal upper bound on the scalar local-row count at `n` evaluation positions. -/
def johnsonWeightedRowSlots (n m B H : ℕ) : ℕ :=
  n * ∑ b ∈ Finset.range (johnsonWeightedU m B + 1),
    (m - b) * (H + 1 - b)

/-- The exact sharper ordinary transfer expression for chosen jet degree `B` and height `H`. -/
def johnsonWeightedSharpException (n D A B H : ℕ) : ℚ :=
  ((2 * B - 1) * H : ℕ) +
    (((n - D : ℕ) : ℚ) / (A - D : ℕ)) *
      (H + B + (2 * D - 1) * H * (2 * B - 1) : ℕ) +
    ((n - D - 1) * B : ℕ)

/-- The integer consequence printed in the finite table. -/
def johnsonWeightedSharpExceptionFloor (n D A B H : ℕ) : ℤ :=
  ⌊johnsonWeightedSharpException n D A B H⌋

/-- The exact floor of the classical pairwise Johnson quotient used in the table's list column. -/
def johnsonPairwiseListFloor (n D A : ℕ) : ℕ :=
  n * (A - D) / (A * A - n * D)

/-- The finite arithmetic hypotheses for a weighted ordinary Johnson certificate. -/
def IsJohnsonWeightedCertificate (n D A m B H : ℕ) : Prop :=
  1 ≤ m ∧ 1 ≤ B ∧ D * B < m * A ∧
    n * johnsonWeightedR m B < johnsonWeightedN D A m B ∧
    H = johnsonWeightedHeight n D A m B

/-- The integer height is always nonnegative because it is at least the natural cutoff `B`. -/
theorem johnsonWeightedHeightInt_nonneg (n D A m B : ℕ) :
    0 ≤ johnsonWeightedHeightInt n D A m B := by
  unfold johnsonWeightedHeightInt
  exact le_trans (Int.natCast_nonneg B) (le_max_left _ _)

/-- Converting the chosen integer height to `Nat` loses no information. -/
@[simp] theorem johnsonWeightedHeight_cast (n D A m B : ℕ) :
    (johnsonWeightedHeight n D A m B : ℤ) = johnsonWeightedHeightInt n D A m B := by
  unfold johnsonWeightedHeight
  exact Int.toNat_of_nonneg (johnsonWeightedHeightInt_nonneg n D A m B)

/-- The selected challenge height retains the required lower bound `H ≥ B`. -/
theorem johnsonWeightedHeight_ge (n D A m B : ℕ) :
    B ≤ johnsonWeightedHeight n D A m B := by
  have h : (B : ℤ) ≤ (johnsonWeightedHeight n D A m B : ℤ) := by
    rw [johnsonWeightedHeight_cast]
    exact le_max_left _ _
  exact_mod_cast h

/-- Positive coefficient surplus is exactly positivity of the integer denominator. -/
theorem johnsonWeightedSlope_pos {n D A m B : ℕ}
    (hN : n * johnsonWeightedR m B < johnsonWeightedN D A m B) :
    0 < johnsonWeightedSlope n D A m B := by
  unfold johnsonWeightedSlope
  omega

/-- The floor height gives the strict scalar-slot surplus required for a nonzero kernel. -/
theorem johnsonWeightedHeight_strict {n D A m B : ℕ}
    (hN : n * johnsonWeightedR m B < johnsonWeightedN D A m B) :
    johnsonWeightedMoment n D A m B <
      ((johnsonWeightedHeight n D A m B + 1 : ℕ) : ℤ) *
        johnsonWeightedSlope n D A m B := by
  let q := johnsonWeightedMoment n D A m B / johnsonWeightedSlope n D A m B
  have hslope : 0 < johnsonWeightedSlope n D A m B := johnsonWeightedSlope_pos hN
  have hq : q ≤ (johnsonWeightedHeight n D A m B : ℤ) := by
    rw [johnsonWeightedHeight_cast]
    exact le_max_right _ _
  have hmul : q * johnsonWeightedSlope n D A m B ≤
      (johnsonWeightedHeight n D A m B : ℤ) * johnsonWeightedSlope n D A m B :=
    mul_le_mul_of_nonneg_right hq hslope.le
  have hrem := Int.emod_lt_of_pos (johnsonWeightedMoment n D A m B) hslope
  have hdecomp := Int.emod_add_mul_ediv
    (johnsonWeightedMoment n D A m B) (johnsonWeightedSlope n D A m B)
  dsimp only [q] at hmul
  rw [Int.natCast_add, Int.natCast_one]
  nlinarith

/-- Expanded form of the strict slot-surplus inequality printed in the paper. -/
theorem johnsonWeightedHeight_strict_expanded {n D A m B : ℕ}
    (hN : n * johnsonWeightedR m B < johnsonWeightedN D A m B) :
    (johnsonWeightedW D A m B : ℤ) - (n : ℤ) * johnsonWeightedT m B <
      ((johnsonWeightedHeight n D A m B + 1 : ℕ) : ℤ) *
        ((johnsonWeightedN D A m B : ℤ) - (n : ℤ) * johnsonWeightedR m B) := by
  simpa only [johnsonWeightedMoment, johnsonWeightedSlope] using
    johnsonWeightedHeight_strict (n := n) (D := D) (A := A) (m := m) (B := B) hN

/-- The strict weighted cutoff makes every selected source width positive. -/
theorem johnsonWeighted_slice_pos {D A m B j : ℕ} (hj : j ≤ B)
    (hcutoff : D * B < m * A) :
    0 < m * A - D * j := by
  apply Nat.sub_pos_of_lt
  exact (Nat.mul_le_mul_left D hj).trans_lt hcutoff

/-- The paper's quotient guard is equivalent to the strict weighted cutoff when `D > 0`. -/
theorem johnsonWeighted_cutoff_iff_le_div {D A m B : ℕ} (hD : 0 < D)
    (hbudget : 0 < m * A) :
    D * B < m * A ↔ B ≤ (m * A - 1) / D := by
  constructor
  · intro h
    apply (Nat.le_div_iff_mul_le hD).2
    rw [Nat.mul_comm]
    omega
  · intro h
    have h' := (Nat.le_div_iff_mul_le hD).1 h
    rw [Nat.mul_comm] at h'
    omega

/-- The literal source-slot sum is the rectangle `(H+1)N` minus its first moment `W`.
The additive form remains exact in `Nat` and therefore also covers zero-width boundary slices. -/
theorem johnsonWeightedSourceSlots_add_W {D A m B H : ℕ} (hBH : B ≤ H) :
    johnsonWeightedSourceSlots D A m B H + johnsonWeightedW D A m B =
      (H + 1) * johnsonWeightedN D A m B := by
  unfold johnsonWeightedSourceSlots johnsonWeightedW johnsonWeightedN
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjB : j ≤ B := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hjH : j ≤ H + 1 := hjB.trans (hBH.trans (Nat.le_add_right H 1))
  rw [mul_comm j (m * A - D * j), ← Nat.mul_add, Nat.sub_add_cancel hjH]
  ring

/-- The literal scalar-row sum is the rectangle `n(H+1)R` minus `nT`. -/
theorem johnsonWeightedRowSlots_add_nT {n m B H : ℕ}
    (huH : johnsonWeightedU m B ≤ H) :
    johnsonWeightedRowSlots n m B H + n * johnsonWeightedT m B =
      n * (H + 1) * johnsonWeightedR m B := by
  unfold johnsonWeightedRowSlots johnsonWeightedT johnsonWeightedR
  rw [← Nat.mul_add]
  rw [Nat.mul_assoc]
  apply congrArg (n * ·)
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hbu : b ≤ johnsonWeightedU m B :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hb)
  have hbH : b ≤ H + 1 := hbu.trans (huH.trans (Nat.le_add_right H 1))
  rw [mul_comm b (m - b), ← Nat.mul_add, Nat.sub_add_cancel hbH]
  ring

/-- Every arithmetic certificate has strictly more source slots than scalar rows. -/
theorem IsJohnsonWeightedCertificate.rowSlots_lt_sourceSlots
    {n D A m B H : ℕ} (hcert : IsJohnsonWeightedCertificate n D A m B H) :
    johnsonWeightedRowSlots n m B H < johnsonWeightedSourceSlots D A m B H := by
  obtain ⟨_hm, _hB, _hcutoff, hN, hheight⟩ := hcert
  have hBH : B ≤ H := by
    rw [hheight]
    exact johnsonWeightedHeight_ge n D A m B
  have huH : johnsonWeightedU m B ≤ H :=
    (min_le_left B (m - 1)).trans hBH
  have hsource := johnsonWeightedSourceSlots_add_W (D := D) (A := A)
    (m := m) (B := B) hBH
  have hrows := johnsonWeightedRowSlots_add_nT (n := n) (m := m) (B := B) huH
  have hstrict := johnsonWeightedHeight_strict (n := n) (D := D) (A := A)
    (m := m) (B := B) hN
  rw [← hheight] at hstrict
  unfold johnsonWeightedMoment johnsonWeightedSlope at hstrict
  have hstrictNat :
      johnsonWeightedW D A m B + n * (H + 1) * johnsonWeightedR m B <
        (H + 1) * johnsonWeightedN D A m B + n * johnsonWeightedT m B := by
    exact_mod_cast (show
      (johnsonWeightedW D A m B : ℤ) +
          (n : ℤ) * (H + 1) * johnsonWeightedR m B <
      (H + 1 : ℕ) * johnsonWeightedN D A m B +
          (n : ℤ) * johnsonWeightedT m B by
      push_cast
      simp only [Int.natCast_add, Int.natCast_one] at hstrict
      ring_nf at hstrict ⊢
      linarith)
  omega

/-- A certificate packages the paper's strict expanded scalar-surplus inequality at its stated
height, rather than only at the computed height hidden inside the definition. -/
theorem IsJohnsonWeightedCertificate.strict_scalar_surplus
    {n D A m B H : ℕ} (hcert : IsJohnsonWeightedCertificate n D A m B H) :
    (johnsonWeightedW D A m B : ℤ) - (n : ℤ) * johnsonWeightedT m B <
      ((H + 1 : ℕ) : ℤ) *
        ((johnsonWeightedN D A m B : ℤ) - (n : ℤ) * johnsonWeightedR m B) := by
  rw [hcert.2.2.2.2]
  exact johnsonWeightedHeight_strict_expanded hcert.2.2.2.1

/-- At `B=0`, the source moments reduce to the single zeroth slice. -/
@[simp] theorem johnsonWeightedN_zero_B (D A m : ℕ) :
    johnsonWeightedN D A m 0 = m * A := by
  simp [johnsonWeightedN]

@[simp] theorem johnsonWeightedW_zero_B (D A m : ℕ) :
    johnsonWeightedW D A m 0 = 0 := by
  simp [johnsonWeightedW]

/-- At zero multiplicity the active row moments vanish, including the truncated `m-1` endpoint. -/
@[simp] theorem johnsonWeightedR_zero_m (B : ℕ) : johnsonWeightedR 0 B = 0 := by
  simp [johnsonWeightedR, johnsonWeightedU]

@[simp] theorem johnsonWeightedT_zero_m (B : ℕ) : johnsonWeightedT 0 B = 0 := by
  simp [johnsonWeightedT, johnsonWeightedU]

/-- All source widths vanish at zero multiplicity, even when `D`, `A`, or `B` is zero. -/
@[simp] theorem johnsonWeightedN_zero_m (D A B : ℕ) :
    johnsonWeightedN D A 0 B = 0 := by
  simp [johnsonWeightedN]

@[simp] theorem johnsonWeightedW_zero_m (D A B : ℕ) :
    johnsonWeightedW D A 0 B = 0 := by
  simp [johnsonWeightedW]

/-- The total height function chooses its explicit lower cutoff when every count is zero. -/
@[simp] theorem johnsonWeightedHeight_zero_m (n D A B : ℕ) :
    johnsonWeightedHeight n D A 0 B = B := by
  simp [johnsonWeightedHeight, johnsonWeightedHeightInt, johnsonWeightedSlope,
    johnsonWeightedMoment]

/-- The first reviewed agreement count is the exact ceiling at gap `1/100`. -/
theorem johnsonWeightedAgreementCeil_rate_one_sixteenth :
    ⌈(√((4095 : ℝ) / 65536) + 1 / 100) * 65536⌉₊ = 17038 := by
  let x := √((4095 : ℝ) / 65536)
  change ⌈(x + 1 / 100) * 65536⌉₊ = 17038
  rw [Nat.ceil_eq_iff (by norm_num : (17038 : ℕ) ≠ 0)]
  have hx2 : x ^ 2 = (4095 : ℝ) / 65536 := by
    exact Real.sq_sqrt (by positivity)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  constructor <;> norm_num at ⊢ <;> nlinarith

/-- The second reviewed agreement count is the exact ceiling at gap `1/100`. -/
theorem johnsonWeightedAgreementCeil_rate_one_fourth :
    ⌈(√((16383 : ℝ) / 65536) + 1 / 100) * 65536⌉₊ = 33423 := by
  let x := √((16383 : ℝ) / 65536)
  change ⌈(x + 1 / 100) * 65536⌉₊ = 33423
  rw [Nat.ceil_eq_iff (by norm_num : (33423 : ℕ) ≠ 0)]
  have hx2 : x ^ 2 = (16383 : ℝ) / 65536 := by
    exact Real.sq_sqrt (by positivity)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  constructor <;> norm_num at ⊢ <;> nlinarith

/-- The third reviewed agreement count is the exact ceiling at gap `1/100`. -/
theorem johnsonWeightedAgreementCeil_rate_one_half :
    ⌈(√((32767 : ℝ) / 65536) + 1 / 100) * 65536⌉₊ = 46996 := by
  let x := √((32767 : ℝ) / 65536)
  change ⌈(x + 1 / 100) * 65536⌉₊ = 46996
  rw [Nat.ceil_eq_iff (by norm_num : (46996 : ℕ) ≠ 0)]
  have hx2 : x ^ 2 = (32767 : ℝ) / 65536 := by
    exact Real.sq_sqrt (by positivity)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  constructor <;> norm_num at ⊢ <;> nlinarith

/-- The reviewed `k/n = 1/16`, `eta = 0.01` table row is an exact weighted certificate. -/
theorem johnsonWeightedCertificate_rate_one_sixteenth :
    IsJohnsonWeightedCertificate 65536 4095 17038 14 57 568 ∧
      57 ≤ (14 * 17038 - 1) / 4095 ∧ 57 ≤ 4095 ∧
      johnsonWeightedU 14 57 = 13 ∧
      johnsonWeightedN 4095 17038 14 57 = 7065821 ∧
      johnsonWeightedW 4095 17038 14 57 = 134813721 ∧
      johnsonWeightedR 14 57 = 105 ∧
      johnsonWeightedT 14 57 = 455 ∧
      johnsonWeightedSlope 65536 4095 17038 14 57 = 184541 ∧
      johnsonWeightedMoment 65536 4095 17038 14 57 = 104994841 ∧
      johnsonWeightedSourceSlots 4095 17038 14 57 568 = 3885638428 ∧
      johnsonWeightedRowSlots 65536 14 57 568 = 3885629440 ∧
      johnsonPairwiseListFloor 65536 4095 17038 = 38 ∧
      johnsonWeightedSharpExceptionFloor 65536 4095 17038 57 568 = 2498629121 := by
  norm_num [IsJohnsonWeightedCertificate, johnsonWeightedHeight,
    johnsonWeightedHeightInt, johnsonWeightedSlope, johnsonWeightedMoment,
    johnsonWeightedSourceSlots, johnsonWeightedRowSlots, johnsonPairwiseListFloor,
    johnsonWeightedSharpExceptionFloor,
    johnsonWeightedSharpException, johnsonWeightedN, johnsonWeightedW, johnsonWeightedR,
    johnsonWeightedT, johnsonWeightedU, Finset.sum_range_succ, Int.toNat_of_nonneg]
  all_goals decide

/-- The reviewed `k/n = 1/4`, `eta = 0.01` table row is an exact weighted certificate. -/
theorem johnsonWeightedCertificate_rate_one_fourth :
    IsJohnsonWeightedCertificate 65536 16383 33423 18 36 504 ∧
      36 ≤ (18 * 33423 - 1) / 16383 ∧ 36 ≤ 16383 ∧
      johnsonWeightedU 18 36 = 17 ∧
      johnsonWeightedN 16383 33423 18 36 = 11348640 ∧
      johnsonWeightedW 16383 33423 18 36 = 135172026 ∧
      johnsonWeightedR 18 36 = 171 ∧
      johnsonWeightedT 18 36 = 969 ∧
      johnsonWeightedSlope 65536 16383 33423 18 36 = 141984 ∧
      johnsonWeightedMoment 65536 16383 33423 18 36 = 71667642 ∧
      johnsonWeightedSourceSlots 16383 33423 18 36 504 = 5595891174 ∧
      johnsonWeightedRowSlots 65536 18 36 504 = 5595856896 ∧
      johnsonPairwiseListFloor 65536 16383 33423 = 25 ∧
      johnsonWeightedSharpExceptionFloor 65536 16383 33423 36 504 = 3383852708 := by
  norm_num [IsJohnsonWeightedCertificate, johnsonWeightedHeight,
    johnsonWeightedHeightInt, johnsonWeightedSlope, johnsonWeightedMoment,
    johnsonWeightedSourceSlots, johnsonWeightedRowSlots, johnsonPairwiseListFloor,
    johnsonWeightedSharpExceptionFloor, johnsonWeightedSharpException, johnsonWeightedN,
    johnsonWeightedW, johnsonWeightedR, johnsonWeightedT, johnsonWeightedU,
    Finset.sum_range_succ, Int.toNat_of_nonneg]
  all_goals decide

/-- The reviewed `k/n = 1/2`, `eta = 0.01` table row is an exact weighted certificate. -/
theorem johnsonWeightedCertificate_rate_one_half :
    IsJohnsonWeightedCertificate 65536 32767 46996 15 21 234 ∧
      21 ≤ (15 * 46996 - 1) / 32767 ∧ 21 ≤ 32767 ∧
      johnsonWeightedU 15 21 = 14 ∧
      johnsonWeightedN 32767 46996 15 21 = 7939503 ∧
      johnsonWeightedW 32767 46996 15 21 = 54349603 ∧
      johnsonWeightedR 15 21 = 120 ∧
      johnsonWeightedT 15 21 = 560 ∧
      johnsonWeightedSlope 65536 32767 46996 15 21 = 75183 ∧
      johnsonWeightedMoment 65536 32767 46996 15 21 = 17649443 ∧
      johnsonWeightedSourceSlots 32767 46996 15 21 234 = 1811433602 ∧
      johnsonWeightedRowSlots 65536 15 21 234 = 1811415040 ∧
      johnsonPairwiseListFloor 65536 32767 46996 = 15 ∧
      johnsonWeightedSharpExceptionFloor 65536 32767 46996 21 234 = 1448631664 := by
  norm_num [IsJohnsonWeightedCertificate, johnsonWeightedHeight,
    johnsonWeightedHeightInt, johnsonWeightedSlope, johnsonWeightedMoment,
    johnsonWeightedSourceSlots, johnsonWeightedRowSlots, johnsonPairwiseListFloor,
    johnsonWeightedSharpExceptionFloor, johnsonWeightedSharpException, johnsonWeightedN,
    johnsonWeightedW, johnsonWeightedR, johnsonWeightedT, johnsonWeightedU,
    Finset.sum_range_succ, Int.toNat_of_nonneg]
  all_goals decide

end ReedSolomon.HiddenDerivative
