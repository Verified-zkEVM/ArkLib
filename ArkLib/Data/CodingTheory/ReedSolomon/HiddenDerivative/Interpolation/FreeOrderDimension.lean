/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Pratyush Mishra, Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.DimensionBridge
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Global.Dimension
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FreeOrder
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
/-!
# Free-order interpolation dimension comparison

This file connects the exact finite count used by the hidden-derivative interpolation space to
the coarse numerical estimates in the source all-rate argument.  In particular, it bounds the
residual dimension certified by the exhibited local kernel; it does not identify that budget with
the rank of either the enlarged or the actual local constraint map.

The scalar comparison is adapted, with permission, from Kai Zhe Zheng's `rs-ld-mca`
formalization at commit `9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`.  The free-order extension
was contributed through PR 1 by Pratyush Mishra.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon
namespace HiddenDerivative

noncomputable section

open scoped BigOperators

/-- The weighted higher-jet simplex count is monotone in its weight budget. -/
theorem weightedHigherJetCount_mono (d : ℕ) {W W' : ℕ} (hWW' : W ≤ W') :
    weightedHigherJetCount d W ≤ weightedHigherJetCount d W' := by
  apply Finset.card_le_card
  intro c hc
  rw [mem_weightedHigherJetTuples] at hc ⊢
  exact hc.trans hWW'

/-- Removing a square of side lengths reduced by `h` from an ambient rectangle leaves at most
the two boundary strips of total size `h * (a + b)`. -/
private theorem rectangleResidual_le (a b h : ℕ) :
    a * b - (a - h) * (b - h) ≤ h * (a + b) := by
  by_cases ha : h ≤ a
  · by_cases hb : h ≤ b
    · have ha' : a - h + h = a := Nat.sub_add_cancel ha
      have hb' : b - h + h = b := Nat.sub_add_cancel hb
      have hexpand :
          a * b = (a - h) * (b - h) +
            ((a - h) * h + h * (b - h) + h * h) := by
        calc
          a * b = (a - h + h) * (b - h + h) := by rw [ha', hb']
          _ = _ := by ring
      rw [hexpand, Nat.add_sub_cancel_left]
      calc
        (a - h) * h + h * (b - h) + h * h ≤
            (a - h) * h + h * (b - h) + h * h + h * h := by omega
        _ = h * ((a - h + h) + (b - h + h)) := by ring
        _ = h * (a + b) := by rw [ha', hb']
    · have hb' : b ≤ h := Nat.le_of_not_ge hb
      rw [Nat.sub_eq_zero_of_le hb', mul_zero, Nat.sub_zero]
      calc
        a * b ≤ a * h := Nat.mul_le_mul_left a hb'
        _ ≤ h * (a + b) := by
          rw [mul_comm a h]
          exact Nat.mul_le_mul_left h (Nat.le_add_right a b)
  · have ha' : a ≤ h := Nat.le_of_not_ge ha
    rw [Nat.sub_eq_zero_of_le ha', zero_mul, Nat.sub_zero]
    calc
      a * b ≤ h * b := Nat.mul_le_mul_right b ha'
      _ ≤ h * (a + b) := Nat.mul_le_mul_left h (Nat.le_add_left b a)

/-- The canonical contact threshold is at most `d²` when `m = d³`. -/
private theorem contactThreshold_cube_le_sq {d r : ℕ} (hd : 0 < d) (hr : r < d ^ 3) :
    contactThreshold d (d ^ 3) r ≤ d ^ 2 := by
  rw [contactThreshold, ceilDiv_le_iff_le_mul hd]
  have : d ^ 3 = d * d ^ 2 := by ring
  omega

/-- At multiplicity and first-jet cap `d³`, each residual contact rectangle has size at most
`4 d⁵`. -/
private theorem certifiedContactRankBudget_cube_le {d r : ℕ} (hd : 0 < d)
    (hr : r < d ^ 3) :
    certifiedContactRankBudget d (d ^ 3) (d ^ 3) r ≤ 4 * d ^ 5 := by
  let h := contactThreshold d (d ^ 3) r
  have hh : h ≤ d ^ 2 := contactThreshold_cube_le_sq hd hr
  have hrOne : r + 1 ≤ d ^ 3 := by omega
  calc
    certifiedContactRankBudget d (d ^ 3) (d ^ 3) r =
        (r + 1) * (d ^ 3 + 1) -
          (r + 1 - h) * (d ^ 3 + 1 - h) := by
      rfl
    _ ≤ h * ((r + 1) + (d ^ 3 + 1)) := rectangleResidual_le _ _ _
    _ ≤ d ^ 2 * (2 * (d ^ 3 + 1)) := by
      apply Nat.mul_le_mul hh
      omega
    _ ≤ 4 * d ^ 5 := by
      have hone : 1 ≤ d ^ 3 := Nat.one_le_pow 3 d hd
      have hsum : 2 * (d ^ 3 + 1) ≤ 4 * d ^ 3 := by omega
      calc
        d ^ 2 * (2 * (d ^ 3 + 1)) ≤ d ^ 2 * (4 * d ^ 3) := by
          exact Nat.mul_le_mul_left (d ^ 2) hsum
        _ = 4 * d ^ 5 := by ring

/-- The exhibited-kernel residual sum has the source's coarse `4 d⁸` upper bound. -/
theorem certifiedEnlargedRankBound_le_four_mul_d_pow_eight {d W : ℕ} (hd : 0 < d) :
    certifiedEnlargedRankBound d (d ^ 3) (d ^ 3) W ≤
      4 * d ^ 8 * weightedHigherJetCount d (W + d ^ 3) := by
  rw [certifiedEnlargedRankBound]
  calc
    (∑ r ∈ Finset.range (d ^ 3),
        weightedHigherJetCount d (W + r) *
          certifiedContactRankBudget d (d ^ 3) (d ^ 3) r) ≤
        ∑ _r ∈ Finset.range (d ^ 3),
          weightedHigherJetCount d (W + d ^ 3) * (4 * d ^ 5) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Nat.mul_le_mul
      · apply weightedHigherJetCount_mono
        have : r < d ^ 3 := Finset.mem_range.mp hr
        omega
      · exact certifiedContactRankBudget_cube_le hd (Finset.mem_range.mp hr)
    _ = 4 * d ^ 8 * weightedHigherJetCount d (W + d ^ 3) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp only [Nat.cast_id]
      ring

/-- Exponent in the source's shell ratio. -/
def shellExponent (theta : ℝ) : ℝ :=
  (5 - theta) / (5 + theta)

theorem shellExponent_add_rankSavingExponent {theta : ℝ} (htheta : 0 < theta) :
    shellExponent theta + rankSavingExponent theta = 1 := by
  unfold shellExponent rankSavingExponent
  field_simp [ne_of_gt (by linarith : 0 < 5 + theta)]
  ring

/-- Convert the source's real shell and width estimates into the strict natural-number rectangle
comparison. -/
theorem rankShellBound_lt_interpolationBox {theta : ℝ} {d K H R n : ℕ}
    (htheta : 0 < theta) (hd : 0 < d) (hn : 0 < n)
    (hH : theta * (d ^ 3 : ℕ) / 32 ≤ (H : ℝ))
    (hR : (R : ℝ) ≤ 2 * (d : ℝ) ^ shellExponent theta)
    (hcompare :
      1 < (theta ^ 3 / 262144) *
        (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (d : ℝ) ^ rankSavingExponent theta) :
    n * (4 * d ^ 8 * R) < (K - 1) * H ^ 3 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpowShell : 0 < (d : ℝ) ^ shellExponent theta :=
    Real.rpow_pos_of_pos hdR _
  have hmultPos :
      0 < 8 * (n : ℝ) * (d : ℝ) ^ 8 *
        (d : ℝ) ^ shellExponent theta := by positivity
  have hscaled := mul_lt_mul_of_pos_left hcompare hmultPos
  have hpowers :
      (d : ℝ) ^ shellExponent theta *
          (d : ℝ) ^ rankSavingExponent theta = (d : ℝ) := by
    rw [← Real.rpow_add hdR,
      shellExponent_add_rankSavingExponent htheta, Real.rpow_one]
  have hmiddle :
      8 * (n : ℝ) * (d : ℝ) ^ 8 *
          (d : ℝ) ^ shellExponent theta <
        ((K - 1 : ℕ) : ℝ) *
          (theta * ((d : ℝ) ^ 3) / 32) ^ 3 := by
    calc
      8 * (n : ℝ) * (d : ℝ) ^ 8 *
          (d : ℝ) ^ shellExponent theta =
          (8 * (n : ℝ) * (d : ℝ) ^ 8 *
            (d : ℝ) ^ shellExponent theta) * 1 := by ring
      _ < (8 * (n : ℝ) * (d : ℝ) ^ 8 *
            (d : ℝ) ^ shellExponent theta) *
          ((theta ^ 3 / 262144) *
            (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
            (d : ℝ) ^ rankSavingExponent theta) := hscaled
      _ = ((K - 1 : ℕ) : ℝ) *
          (theta * ((d : ℝ) ^ 3) / 32) ^ 3 := by
        calc
          8 * (n : ℝ) * (d : ℝ) ^ 8 *
                (d : ℝ) ^ shellExponent theta *
              ((theta ^ 3 / 262144) *
                (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
                (d : ℝ) ^ rankSavingExponent theta) =
              (8 * (n : ℝ) * (theta ^ 3 / 262144) *
                (((K - 1 : ℕ) : ℝ) / (n : ℝ)) * (d : ℝ) ^ 8) *
                ((d : ℝ) ^ shellExponent theta *
                  (d : ℝ) ^ rankSavingExponent theta) := by ring
          _ = (8 * (n : ℝ) * (theta ^ 3 / 262144) *
                (((K - 1 : ℕ) : ℝ) / (n : ℝ)) * (d : ℝ) ^ 8) *
                (d : ℝ) := by rw [hpowers]
          _ = ((K - 1 : ℕ) : ℝ) *
              (theta * ((d : ℝ) ^ 3) / 32) ^ 3 := by
            field_simp
            ring
  have hleft :
      ((n * (4 * d ^ 8 * R) : ℕ) : ℝ) ≤
        8 * (n : ℝ) * (d : ℝ) ^ 8 *
          (d : ℝ) ^ shellExponent theta := by
    push_cast
    calc
      (n : ℝ) * (4 * (d : ℝ) ^ 8 * (R : ℝ)) ≤
          (n : ℝ) *
            (4 * (d : ℝ) ^ 8 *
              (2 * (d : ℝ) ^ shellExponent theta)) := by gcongr
      _ = 8 * (n : ℝ) * (d : ℝ) ^ 8 *
          (d : ℝ) ^ shellExponent theta := by ring
  have hright :
      ((K - 1 : ℕ) : ℝ) *
          (theta * ((d : ℝ) ^ 3) / 32) ^ 3 ≤
        (((K - 1) * H ^ 3 : ℕ) : ℝ) := by
    push_cast
    gcongr
    simpa only [Nat.cast_pow] using hH
  have hfinal :
      ((n * (4 * d ^ 8 * R) : ℕ) : ℝ) <
        (((K - 1) * H ^ 3 : ℕ) : ℝ) :=
    hleft.trans_lt (hmiddle.trans_le hright)
  exact_mod_cast hfinal

/-- A shell estimate and the strict scalar rectangle comparison imply that the exact finite
interpolation space has dimension larger than `n` certified local-rank budgets. -/
theorem n_mul_certifiedEnlargedRankBound_lt_finrank_exactInterpolationSpace
    {F : Type*} [Field F] {d A K B W C H R n : ℕ}
    (hd : 0 < d) (hdK : d < K - 1)
    (hH : H ≤ d ^ 3) (hdegree : C + 2 * H ≤ B)
    (hweighted : (K - 1) * (C + 3 * H) ≤ d ^ 3 * A)
    (hshell : weightedHigherJetCount d (W + d ^ 3) ≤
      R * (goodHigherExponents d W C).card)
    (harithmetic : n * (4 * d ^ 8 * R) < (K - 1) * H ^ 3) :
    n * certifiedEnlargedRankBound d (d ^ 3) (d ^ 3) W <
      Module.finrank F
        (exactInterpolationSpace F (K - 1) A d (d ^ 3) (d ^ 3) W hdK) := by
  have hlocal := certifiedEnlargedRankBound_le_four_mul_d_pow_eight (W := W) hd
  have hgood : 0 < (goodHigherExponents d W C).card := by
    rw [Finset.card_pos]
    refine ⟨0, ?_⟩
    rw [mem_goodHigherExponents]
    exact ⟨by simp [higherJetWeight], by simp [higherJetDegree]⟩
  have hK : K - 1 + 1 = K := by omega
  have hglobal := finrank_interpolationSpace_lowerBound
    (F := F) (d := d) (m := d ^ 3) (A := A) (K := K) (B := B)
    (W := W) (C := C) (H := H) hd hH hdegree hweighted
  have hembed := finrank_interpolationSpace_le_exactInterpolationSpace
    (F := F) (D := K - 1) (A := A) (d := d) (m := d ^ 3)
    (W := W) (B := B) (C := C) hdK
  rw [hK] at hembed
  calc
    n * certifiedEnlargedRankBound d (d ^ 3) (d ^ 3) W ≤
        n * (4 * d ^ 8 * weightedHigherJetCount d (W + d ^ 3)) :=
      Nat.mul_le_mul_left n hlocal
    _ ≤ n * (4 * d ^ 8 * (R * (goodHigherExponents d W C).card)) := by
      gcongr
    _ = (n * (4 * d ^ 8 * R)) * (goodHigherExponents d W C).card := by ring
    _ < ((K - 1) * H ^ 3) * (goodHigherExponents d W C).card :=
      Nat.mul_lt_mul_of_pos_right harithmetic hgood
    _ = (goodHigherExponents d W C).card * (K - 1) * H ^ 3 := by ring
    _ ≤ Module.finrank F (interpolationSpace F d (d ^ 3) A K B W C) := hglobal
    _ ≤ Module.finrank F
        (exactInterpolationSpace F (K - 1) A d (d ^ 3) (d ^ 3) W hdK) := hembed

/-- The source shell and scalar hypotheses imply the exact finite-dimensional inequality consumed
by interpolation-kernel extraction. -/
theorem localRankBound_lt_interpolationSpace_of_shell_bounds
    {F : Type*} [Field F] {theta : ℝ} {d A K B W C H R n : ℕ}
    (htheta : 0 < theta) (hd : 0 < d) (hn : 0 < n) (hdK : d < K - 1)
    (hHle : H ≤ d ^ 3) (hdegree : C + 2 * H ≤ B)
    (hweighted : (K - 1) * (C + 3 * H) ≤ d ^ 3 * A)
    (hH : theta * (d ^ 3 : ℕ) / 32 ≤ (H : ℝ))
    (hR : (R : ℝ) ≤ 2 * (d : ℝ) ^ shellExponent theta)
    (hcompare :
      1 < (theta ^ 3 / 262144) *
        (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (d : ℝ) ^ rankSavingExponent theta)
    (hshell : weightedHigherJetCount d (W + d ^ 3) ≤
      R * (goodHigherExponents d W C).card) :
    n * certifiedEnlargedRankBound d (d ^ 3) (d ^ 3) W <
      Module.finrank F
        (exactInterpolationSpace F (K - 1) A d (d ^ 3) (d ^ 3) W hdK) := by
  apply n_mul_certifiedEnlargedRankBound_lt_finrank_exactInterpolationSpace
    hd hdK hHle hdegree hweighted hshell
  exact rankShellBound_lt_interpolationBox htheta hd hn hH hR hcompare

end
end HiddenDerivative
end ReedSolomon
