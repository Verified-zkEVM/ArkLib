/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Exact weighted finite Johnson certificates

This file records the integer arithmetic behind the weighted ordinary Johnson interpolation
certificate, a refinement of the rounded recipe in
`ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.FiniteBounds`. For length `n`,
degree cap `D`, agreement count `A`, multiplicity `m` and jet cutoff `B`, the source slices have
widths `m A - D j` for `0 ≤ j ≤ B`, and the local rows stop at grade `u = min B (m - 1)`. Their
zeroth and first moments are

```text
N = ∑_{j ≤ B} (m A - D j)        W = ∑_{j ≤ B} j (m A - D j)
R = ∑_{b ≤ u} (m - b)            T = ∑_{b ≤ u} b (m - b)
```

The moment `W - n T` is kept in `ℤ` because it can be negative for a valid certificate. When
`N > n R`, the challenge height is `H = max B ⌊(W - n T) / (N - n R)⌋`, computed with integer
floor division, so it is exact for moments of either sign. At height `H` the source has
`∑_j (m A - D j)(H + 1 - j)` coefficient slots and the local rows impose at most
`n ∑_b (m - b)(H + 1 - b)` scalar conditions; the certificate guarantees strictly more slots than
conditions, which is what the interpolation step needs for a nonzero kernel element.

All definitions are total (natural subtraction truncates, integer division by zero is zero);
`IsJohnsonWeightedCertificate` records the positivity, cutoff and slope guards separately.

## Main statements

* `johnsonWeightedHeight_ge`, `johnsonWeightedHeight_strict`: `B ≤ H` and
  `W - n T < (H + 1)(N - n R)` whenever `n R < N`.
* `johnsonWeightedSourceSlots_add_W`, `johnsonWeightedRowSlots_add_nT`: the slot and row sums
  are the rectangles `(H + 1) N` and `n (H + 1) R` minus their first moments.
* `IsJohnsonWeightedCertificate.rowSlots_lt_sourceSlots`: every certificate has strictly more
  source slots than scalar rows.
* `IsJohnsonWeightedCertificate.strict_scalar_surplus`: the strict expanded scalar-surplus
  inequality at the certificate's stated height.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open scoped BigOperators

/-- The largest active local-row grade `u = min B (m - 1)`. Rows of grade `b ≥ m` impose no
condition, and rows above the jet cutoff `B` are not used. It is `0` when `m = 0`. -/
def johnsonWeightedU (m B : ℕ) : ℕ :=
  min B (m - 1)

/-- The zeroth moment `N = ∑_{j ≤ B} (m A - D j)` of the source widths. Natural subtraction
truncates a width at `0`; under the certificate cutoff `D B < m A` no width truncates. -/
def johnsonWeightedN (D A m B : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (B + 1), (m * A - D * j)

/-- The first moment `W = ∑_{j ≤ B} j (m A - D j)` of the source widths. -/
def johnsonWeightedW (D A m B : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (B + 1), j * (m * A - D * j)

/-- The zeroth moment `R = ∑_{b ≤ u} (m - b)` of the active local rows, `u = min B (m - 1)`. -/
def johnsonWeightedR (m B : ℕ) : ℕ :=
  ∑ b ∈ Finset.range (johnsonWeightedU m B + 1), (m - b)

/-- The first moment `T = ∑_{b ≤ u} b (m - b)` of the active local rows. -/
def johnsonWeightedT (m B : ℕ) : ℕ :=
  ∑ b ∈ Finset.range (johnsonWeightedU m B + 1), b * (m - b)

/-- The coefficient surplus `N - n R` in `ℤ`. The certificate requires it to be positive; it is
the divisor in the height formula. -/
def johnsonWeightedSlope (n D A m B : ℕ) : ℤ :=
  (johnsonWeightedN D A m B : ℤ) -
    (n : ℤ) * (johnsonWeightedR m B : ℤ)

/-- The weighted moment `W - n T` in `ℤ`, so that a negative moment is not truncated to `0`. -/
def johnsonWeightedMoment (n D A m B : ℕ) : ℤ :=
  (johnsonWeightedW D A m B : ℤ) -
    (n : ℤ) * (johnsonWeightedT m B : ℤ)

/-- The integer height `max B ⌊(W - n T) / (N - n R)⌋`, with `Int` floor division. When the
slope is `0` the quotient is `0` and the height is `B`. -/
def johnsonWeightedHeightInt (n D A m B : ℕ) : ℤ :=
  max (B : ℤ) (johnsonWeightedMoment n D A m B / johnsonWeightedSlope n D A m B)

/-- The challenge height as a natural number. `johnsonWeightedHeight_cast` shows the conversion
from `ℤ` loses nothing. -/
def johnsonWeightedHeight (n D A m B : ℕ) : ℕ :=
  (johnsonWeightedHeightInt n D A m B).toNat

/-- The number `∑_{j ≤ B} (m A - D j)(H + 1 - j)` of source coefficient slots at height `H`. -/
def johnsonWeightedSourceSlots (D A m B H : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (B + 1), (m * A - D * j) * (H + 1 - j)

/-- The upper bound `n ∑_{b ≤ u} (m - b)(H + 1 - b)` on the number of scalar local-row
conditions over `n` evaluation positions. -/
def johnsonWeightedRowSlots (n m B H : ℕ) : ℕ :=
  n * ∑ b ∈ Finset.range (johnsonWeightedU m B + 1),
    (m - b) * (H + 1 - b)

/-- The sharper ordinary transfer bound
`(2B - 1) H + ((n - D)/(A - D)) (H + B + (2D - 1) H (2B - 1)) + (n - D - 1) B` in `ℚ`, for jet
degree `B` and height `H`. The natural subtractions are exact when `1 ≤ B`, `1 ≤ D < A` and
`D < n`. -/
def johnsonWeightedRefinedExceptionCount (n D A B H : ℕ) : ℚ :=
  ((2 * B - 1) * H : ℕ) +
    (((n - D : ℕ) : ℚ) / (A - D : ℕ)) *
      (H + B + (2 * D - 1) * H * (2 * B - 1) : ℕ) +
    ((n - D - 1) * B : ℕ)

/-- The floor `⌊johnsonWeightedRefinedExceptionCount n D A B H⌋` in `ℤ`. -/
def johnsonWeightedRefinedExceptionCountFloor (n D A B H : ℕ) : ℤ :=
  ⌊johnsonWeightedRefinedExceptionCount n D A B H⌋

/-- The floor `⌊n (A - D) / (A² - n D)⌋` of the classical pairwise Johnson list bound. It is
meaningful when `A² > n D`. -/
def johnsonPairwiseListFloor (n D A : ℕ) : ℕ :=
  n * (A - D) / (A * A - n * D)

/-- The arithmetic conditions of a weighted ordinary Johnson certificate: positive multiplicity
and jet cutoff, the strict cutoff `D B < m A` (every source width is positive), positive slope
`n R < N`, and `H` equal to the computed height. -/
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

/-- The natural-number slope condition `n R < N` makes the integer slope `N - n R` positive. -/
theorem johnsonWeightedSlope_pos {n D A m B : ℕ}
    (hN : n * johnsonWeightedR m B < johnsonWeightedN D A m B) :
    0 < johnsonWeightedSlope n D A m B := by
  unfold johnsonWeightedSlope
  omega

/-- The height satisfies `W - n T < (H + 1)(N - n R)`. The hypothesis `n R < N` is needed: at a
zero slope the right side is `0`, while `W - n T` can be `0` (for example at `m = 0`). -/
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

/-- The strict slot-surplus inequality `W - n T < (H + 1)(N - n R)` with the moment and slope
written out. -/
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

/-- For `D > 0` and `m A > 0`, the strict cutoff `D B < m A` is equivalent to the quotient guard
`B ≤ ⌊(m A - 1) / D⌋`. -/
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

/-- A certificate satisfies the strict expanded scalar-surplus inequality at its stated height. -/
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

/-- At `B = 0` the first source moment is `0`. -/
@[simp] theorem johnsonWeightedW_zero_B (D A m : ℕ) :
    johnsonWeightedW D A m 0 = 0 := by
  simp [johnsonWeightedW]

/-- At zero multiplicity the active row moments vanish, including the truncated `m-1` endpoint. -/
@[simp] theorem johnsonWeightedR_zero_m (B : ℕ) : johnsonWeightedR 0 B = 0 := by
  simp [johnsonWeightedR, johnsonWeightedU]

/-- At `m = 0` the first row moment is `0`. -/
@[simp] theorem johnsonWeightedT_zero_m (B : ℕ) : johnsonWeightedT 0 B = 0 := by
  simp [johnsonWeightedT, johnsonWeightedU]

/-- All source widths vanish at zero multiplicity, even when `D`, `A`, or `B` is zero. -/
@[simp] theorem johnsonWeightedN_zero_m (D A B : ℕ) :
    johnsonWeightedN D A 0 B = 0 := by
  simp [johnsonWeightedN]

/-- At `m = 0` the first source moment is `0`. -/
@[simp] theorem johnsonWeightedW_zero_m (D A B : ℕ) :
    johnsonWeightedW D A 0 B = 0 := by
  simp [johnsonWeightedW]

/-- The total height function chooses its explicit lower cutoff when every count is zero. -/
@[simp] theorem johnsonWeightedHeight_zero_m (n D A B : ℕ) :
    johnsonWeightedHeight n D A 0 B = B := by
  simp [johnsonWeightedHeight, johnsonWeightedHeightInt, johnsonWeightedSlope,
    johnsonWeightedMoment]

end ReedSolomon.HiddenDerivative
