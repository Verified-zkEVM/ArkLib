/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Polynomial.DerivativeResultantDegree

/-!
# Exact degree envelopes for first-order squarefree counting

The first-order counting argument retains the root-independent content and multiplies it by the
resultant of the positive-root squarefree product and its derivative.  If `B` bounds the total
jet degree and `M` bounds the positive root-variable degree, the exact ordinary-variable envelope
is

`max B ((2 * M - 1) * B - M ^ 2)`.

This file isolates the natural-number arithmetic, including the zero and linear root-degree
branches where truncated subtraction matters.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

/-- The exact ordinary-variable degree envelope for the content-resultant product. -/
def ordinaryDegreeEnvelope (B M : ℕ) : ℕ :=
  max B ((2 * M - 1) * B - M ^ 2)

@[simp]
theorem ordinaryDegreeEnvelope_zero (B : ℕ) : ordinaryDegreeEnvelope B 0 = B := by
  simp [ordinaryDegreeEnvelope]

theorem ordinaryDegreeEnvelope_ge_total (B M : ℕ) :
    B ≤ ordinaryDegreeEnvelope B M :=
  Nat.le_max_left _ _

theorem ordinaryDegreeEnvelope_ge_resultant (B M : ℕ) :
    (2 * M - 1) * B - M ^ 2 ≤ ordinaryDegreeEnvelope B M :=
  Nat.le_max_right _ _

/-- The content plus a sharp derivative-resultant degree fits the exact manuscript envelope.

The hypotheses are deliberately stated in the additive form produced by the determinant proof,
so no information is lost to an intermediate truncated subtraction. -/
theorem content_add_resultantDegree_le
    {B M bU j r d : ℕ}
    (hr : 0 < r) (hrj : r ≤ j) (hrM : r ≤ M) (hMB : M ≤ B)
    (hbudget : bU + j ≤ B)
    (hresultant : d + r ^ 2 ≤ (2 * r - 1) * j) :
    bU + d ≤ ordinaryDegreeEnvelope B M := by
  by_cases hr_one : r = 1
  · subst r
    apply (ordinaryDegreeEnvelope_ge_total B M).trans'
    norm_num at hresultant
    omega
  · have hr_two : 2 ≤ r := by omega
    have hMpos : 0 < M := hr.trans_le hrM
    have htwor : 2 * r - 1 + 1 = 2 * r := Nat.sub_add_cancel (by omega)
    have htwoM : 2 * M - 1 + 1 = 2 * M := Nat.sub_add_cancel (by omega)
    have hMsq : M ^ 2 ≤ (2 * M - 1) * B := by
      nlinarith
    have hMsub : ((2 * M - 1) * B - M ^ 2) + M ^ 2 = (2 * M - 1) * B :=
      Nat.sub_add_cancel hMsq
    apply (ordinaryDegreeEnvelope_ge_resultant B M).trans'
    nlinarith

/-- A simpler bound used by inverse-`eta` corollaries. -/
theorem ordinaryDegreeEnvelope_le (B M : ℕ) :
    ordinaryDegreeEnvelope B M ≤ B + 2 * B * M := by
  rw [ordinaryDegreeEnvelope]
  apply max_le
  · omega
  · calc
      (2 * M - 1) * B - M ^ 2 ≤ (2 * M - 1) * B := Nat.sub_le _ _
      _ ≤ 2 * M * B := Nat.mul_le_mul_right B (Nat.sub_le _ _)
      _ ≤ B + 2 * B * M := by nlinarith

/-- The exact challenge-degree envelope for the derivative resultant. -/
def resultantChallengeEnvelope (H M : ℕ) : ℕ :=
  (2 * M - 1) * H

@[simp]
theorem resultantChallengeEnvelope_zero (H : ℕ) :
    resultantChallengeEnvelope H 0 = 0 := by
  simp [resultantChallengeEnvelope]

theorem resultantChallengeEnvelope_mono
    {H M h r : ℕ} (hh : h ≤ H) (hr : r ≤ M) :
    resultantChallengeEnvelope h r ≤ resultantChallengeEnvelope H M := by
  rw [resultantChallengeEnvelope, resultantChallengeEnvelope]
  exact Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hr) 1) hh

/-- Retaining the root-independent content does not add another challenge-height term: its
height and the positive-product height already share the source budget. -/
theorem content_add_resultantChallenge_le
    {H M hU hV r d : ℕ} (hr : 0 < r) (hrM : r ≤ M)
    (hbudget : hU + hV ≤ H) (hresultant : d ≤ (2 * r - 1) * hV) :
    hU + d ≤ resultantChallengeEnvelope H M := by
  have hone : 1 ≤ 2 * r - 1 := by omega
  calc
    hU + d ≤ hU + (2 * r - 1) * hV := Nat.add_le_add_left hresultant _
    _ ≤ (2 * r - 1) * hU + (2 * r - 1) * hV := by
      exact Nat.add_le_add_right (by simpa using Nat.mul_le_mul_right hU hone) _
    _ = (2 * r - 1) * (hU + hV) := by rw [Nat.mul_add]
    _ ≤ (2 * M - 1) * H :=
      Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hrM) 1) hbudget
    _ = resultantChallengeEnvelope H M := rfl

theorem resultantChallengeEnvelope_le (H M : ℕ) :
    resultantChallengeEnvelope H M ≤ 2 * H * M := by
  rw [resultantChallengeEnvelope]
  calc
    (2 * M - 1) * H ≤ 2 * M * H := Nat.mul_le_mul_right H (Nat.sub_le _ _)
    _ = 2 * H * M := by ac_rfl

end ReedSolomon.FirstOrder.Squarefree
