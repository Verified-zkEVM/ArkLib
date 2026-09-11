/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Profile

/-!
# Finite-length first-order parameter envelopes

This file isolates the elementary estimates behind the finite-length slack
`eta + 1 / n`.  It deliberately keeps the interpolation parameters as exact natural numbers:
ceilings, floors, zero caps, and truncated differences are not replaced by real-valued proxies.

The list envelope is the public squarefree product/resultant expression.  The line envelope is
the finite expression from the first-order factorwise argument, written with the exact natural
budgets `b = B * (2 * M + 1)` and `h = H * (2 * M + 1)`.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder

open ReedSolomon.HiddenDerivative
open ReedSolomon.FirstOrder.Squarefree

noncomputable section

set_option autoImplicit false

/-- The finite-length slack used by the first-order rate theorem. -/
def finiteLengthSlack (eta : ℝ) (n : ℕ) : ℝ := eta + 1 / (n : ℝ)

theorem finiteLengthSlack_pos {eta : ℝ} {n : ℕ} (heta : 0 < eta) (hn : 0 < n) :
    0 < finiteLengthSlack eta n := by
  unfold finiteLengthSlack
  positivity

theorem eta_le_finiteLengthSlack {eta : ℝ} {n : ℕ} (hn : 0 < n) :
    eta ≤ finiteLengthSlack eta n := by
  unfold finiteLengthSlack
  exact le_add_of_nonneg_right (by positivity)

/-- The one-degree saving gives the exact absorption inequality `1/s ≤ n`. -/
theorem finiteLengthSlack_inv_le_length {eta : ℝ} {n : ℕ}
    (heta : 0 ≤ eta) (hn : 0 < n) :
    1 / finiteLengthSlack eta n ≤ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < finiteLengthSlack eta n := by
    unfold finiteLengthSlack
    positivity
  rw [div_le_iff₀ hs]
  unfold finiteLengthSlack
  have hone : (n : ℝ) * (1 / (n : ℝ)) = 1 := by
    field_simp
  calc
    1 = (n : ℝ) * (1 / (n : ℝ)) := hone.symm
    _ ≤ (n : ℝ) * (eta + 1 / (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hn'.le
      linarith

/-- Replacing the finite-length slack by `eta` only weakens an inverse-power bound. -/
theorem div_finiteLengthSlack_sq_le_div_eta_sq
    {C eta : ℝ} {n : ℕ} (hC : 0 ≤ C) (heta : 0 < eta) (hn : 0 < n) :
    C / finiteLengthSlack eta n ^ 2 ≤ C / eta ^ 2 := by
  have hs := eta_le_finiteLengthSlack (eta := eta) hn
  have hspos := finiteLengthSlack_pos heta hn
  exact div_le_div_of_nonneg_left hC (sq_pos_of_pos heta)
    (pow_le_pow_left₀ heta.le hs 2)

/-- Replacing the finite-length slack by `eta` only weakens a fourth-power bound. -/
theorem div_finiteLengthSlack_four_le_div_eta_four
    {C eta : ℝ} {n : ℕ} (hC : 0 ≤ C) (heta : 0 < eta) (hn : 0 < n) :
    C / finiteLengthSlack eta n ^ 4 ≤ C / eta ^ 4 := by
  have hs := eta_le_finiteLengthSlack (eta := eta) hn
  exact div_le_div_of_nonneg_left hC (pow_pos heta 4)
    (pow_le_pow_left₀ heta.le hs 4)

/-- A common inverse-finite-slack cap gives the squarefree list envelope
`O(n / (eta + 1/n)^2)`. -/
theorem squarefreeListExpression_le_finiteLength
    {C eta lambda : ℝ} {n D B M : ℕ}
    (hC : 1 ≤ C) (heta : 0 < eta) (hn : 1 ≤ n)
    (hsOne : finiteLengthSlack eta n ≤ 1)
    (hD : 1 ≤ D) (hDn : D ≤ n) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hlambda0 : 0 ≤ lambda) (hlambda : lambda ≤ C)
    (hB : (B : ℝ) ≤ C / finiteLengthSlack eta n) :
    (firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) : ℝ) * lambda +
        ordinaryDegreeEnvelope B M ≤
      7 * C ^ 3 * n / finiteLengthSlack eta n ^ 2 := by
  let s := finiteLengthSlack eta n
  let q := 1 / s
  have hs : 0 < s := finiteLengthSlack_pos heta (by omega)
  have hq : 1 ≤ q := by
    dsimp only [q]
    exact (one_le_div hs).2 hsOne
  have hB' : (B : ℝ) ≤ C * q := by
    dsimp only [q, s]
    simpa only [div_eq_mul_inv, one_mul] using hB
  have hstageNat :
      firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) ≤ 4 * D * B * M := by
    have hsharp := firstOrderCurveFiberStageOne_le_hybridEnvelope hD hM hMB
    apply hsharp.trans
    have hsub : 2 * B - M ≤ 2 * B := Nat.sub_le _ _
    calc
      2 * D * M * (2 * B - M) ≤ 2 * D * M * (2 * B) :=
        Nat.mul_le_mul_left _ hsub
      _ = 4 * D * B * M := by ring
  have hstage :
      (firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) : ℝ) ≤
        4 * D * B * M := by
    exact_mod_cast hstageNat
  have htail : (ordinaryDegreeEnvelope B M : ℝ) ≤ B + 2 * B * M := by
    exact_mod_cast ordinaryDegreeEnvelope_le B M
  have hM' : (M : ℝ) ≤ C * q := (Nat.cast_le.mpr hMB).trans hB'
  have hD' : (D : ℝ) ≤ n := by exact_mod_cast hDn
  have hraw :
      (firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) : ℝ) * lambda +
          ordinaryDegreeEnvelope B M ≤
        4 * (D : ℝ) * B * M * lambda + 2 * (B : ℝ) * M + B := by
    have hproduct := mul_le_mul_of_nonneg_right hstage hlambda0
    linarith
  have hrough :
      4 * (D : ℝ) * B * M * lambda + 2 * (B : ℝ) * M + B ≤
        4 * (n : ℝ) * (C * q) * (C * q) * C +
          2 * (C * q) * (C * q) + C * q := by
    gcongr
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hx : 1 ≤ C * q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hq)]
  have hCN : 1 ≤ C * (n : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hN)]
  have htwo : (C * q) * (C * q) ≤ C ^ 3 * n * q ^ 2 := by
    have hnonneg : 0 ≤ (C * q) ^ 2 := sq_nonneg _
    have hmul : (C * q) ^ 2 ≤ (C * q) ^ 2 * (C * n) := by
      nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hCN)]
    nlinarith [hmul]
  have hone : C * q ≤ C ^ 3 * n * q ^ 2 := by
    have hsquare : C * q ≤ (C * q) ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hC0 hq0) (sub_nonneg.mpr hx)]
    exact hsquare.trans (by simpa only [pow_two] using htwo)
  have hbound :
      (firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) : ℝ) * lambda +
          ordinaryDegreeEnvelope B M ≤ 7 * C ^ 3 * n * q ^ 2 := by
    calc
      (firstOrderCurveFiberStageOne (D + 1) B M (2 * D - 1) : ℝ) * lambda +
          ordinaryDegreeEnvelope B M ≤
        4 * (D : ℝ) * B * M * lambda + 2 * (B : ℝ) * M + B := hraw
      _ ≤ 4 * (n : ℝ) * (C * q) * (C * q) * C +
          2 * (C * q) * (C * q) + C * q := hrough
      _ = 4 * (C ^ 3 * n * q ^ 2) + 2 * ((C * q) * (C * q)) + C * q := by ring
      _ ≤ 4 * (C ^ 3 * n * q ^ 2) + 2 * (C ^ 3 * n * q ^ 2) +
          C ^ 3 * n * q ^ 2 := by gcongr
      _ = 7 * C ^ 3 * n * q ^ 2 := by ring
  dsimp only [q, s] at hbound ⊢
  field_simp [ne_of_gt hs] at hbound ⊢
  nlinarith

/-- Exact finite first-order line-MCA expression.  The natural subtractions preserve the
small-length and full-agreement boundary behavior of the semantic counting theorem. -/
def finiteLengthMCAEnvelope
    (lambda : ℝ) (n D B M H : ℕ) : ℝ :=
  let b := B * (2 * M + 1)
  let h := H * (2 * M + 1)
  (((2 * b - 1 : ℕ) : ℝ) * h +
      lambda * (h + b + 4 * D * b * h) +
      ((n - D - 1 : ℕ) : ℝ) * b) +
    (48 * (D : ℝ) ^ 2 * H + 16 * D) * lambda ^ 2 * B * M +
    8 * D * ((n - D - 1 : ℕ) : ℝ) * lambda * B * M

set_option maxHeartbeats 800000 in
-- The exact natural-number envelope expands into several high-degree ordered-ring estimates.
/-- If the exact jet and challenge-height parameters have their expected inverse-slack sizes,
the factorwise line expression is fourth power in inverse slack. -/
theorem finiteLengthMCAEnvelope_le_rateEnvelope
    {C q lambda : ℝ} {n D B M H : ℕ}
    (hC : 1 ≤ C) (hq : 1 ≤ q) (hn : 1 ≤ n) (hqN : q ≤ n)
    (hDn : D ≤ n) (hlambda0 : 0 ≤ lambda) (hlambda : lambda ≤ C)
    (hB : (B : ℝ) ≤ C * q) (hM : (M : ℝ) ≤ C * q)
    (hH : (H : ℝ) ≤ C * q ^ 2) :
    finiteLengthMCAEnvelope lambda n D B M H ≤ 140 * C ^ 6 * n ^ 2 * q ^ 4 := by
  let x := C * q
  let b : ℝ := B * (2 * M + 1)
  let h : ℝ := H * (2 * M + 1)
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hx1 : 1 ≤ x := by
    dsimp only [x]
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hq)]
  have htwoM : 2 * (M : ℝ) + 1 ≤ 3 * x := by
    have := hM
    dsimp only [x] at hx1 ⊢
    nlinarith
  have hb : b ≤ 3 * x ^ 2 := by
    dsimp only [b]
    calc
      (B : ℝ) * (2 * M + 1) ≤ x * (3 * x) := by gcongr
      _ = 3 * x ^ 2 := by ring
  have hh : h ≤ 3 * C ^ 2 * q ^ 3 := by
    dsimp only [h]
    calc
      (H : ℝ) * (2 * M + 1) ≤ (C * q ^ 2) * (3 * x) := by gcongr
      _ = 3 * C ^ 2 * q ^ 3 := by dsimp only [x]; ring
  have hD : (D : ℝ) ≤ n := by exact_mod_cast hDn
  have htail : ((n - D - 1 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast Nat.sub_le n (D + 1)
  have hqN' : q ≤ (n : ℝ) := by exact_mod_cast hqN
  have hb0 : 0 ≤ b := by positivity
  have hh0 : 0 ≤ h := by positivity
  have hB0 : (0 : ℝ) ≤ B := by positivity
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hH0 : (0 : ℝ) ≤ H := by positivity
  have htwoB : (((2 * (B * (2 * M + 1)) - 1 : ℕ) : ℝ)) ≤ 2 * b := by
    calc
      (((2 * (B * (2 * M + 1)) - 1 : ℕ) : ℝ)) ≤
          ((2 * (B * (2 * M + 1)) : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_le (2 * (B * (2 * M + 1))) 1
      _ = 2 * b := by simp [b]
  have hraw : finiteLengthMCAEnvelope lambda n D B M H ≤
      2 * b * h + C * (h + b + 4 * n * b * h) + n * b +
        (48 * n ^ 2 * (C * q ^ 2) + 16 * n) * C ^ 2 *
          (C * q) * (C * q) +
        8 * n * n * C * (C * q) * (C * q) := by
    have hfirst : (((2 * (B * (2 * M + 1)) - 1 : ℕ) : ℝ)) * h ≤ 2 * b * h := by
      gcongr
    have hmiddle :
        lambda * (h + b + 4 * (D : ℝ) * b * h) ≤
          C * (h + b + 4 * n * b * h) := by
      gcongr
    have htailTerm : ((n - D - 1 : ℕ) : ℝ) * b ≤ (n : ℝ) * b := by
      gcongr
    have hregular :
        (48 * (D : ℝ) ^ 2 * H + 16 * D) * lambda ^ 2 * B * M ≤
          (48 * (n : ℝ) ^ 2 * (C * q ^ 2) + 16 * n) * C ^ 2 *
            (C * q) * (C * q) := by
      gcongr
    have hlast :
        8 * (D : ℝ) * ((n - D - 1 : ℕ) : ℝ) * lambda * B * M ≤
          8 * (n : ℝ) * n * C * (C * q) * (C * q) := by
      gcongr
    unfold finiteLengthMCAEnvelope
    dsimp only
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    nlinarith
  let Z := C ^ 6 * (n : ℝ) ^ 2 * q ^ 4
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hC3C6 : C ^ 3 ≤ C ^ 6 := by
    calc
      C ^ 3 = C ^ 3 * 1 := by ring
      _ ≤ C ^ 3 * C ^ 3 := by gcongr; exact one_le_pow₀ hC
      _ = C ^ 6 := by ring
  have hC2C6 : C ^ 2 ≤ C ^ 6 := by
    calc
      C ^ 2 = C ^ 2 * 1 := by ring
      _ ≤ C ^ 2 * C ^ 4 := by gcongr; exact one_le_pow₀ hC
      _ = C ^ 6 := by ring
  have hC4C6 : C ^ 4 ≤ C ^ 6 := by
    calc
      C ^ 4 = C ^ 4 * 1 := by ring
      _ ≤ C ^ 4 * C ^ 2 := by gcongr; exact one_le_pow₀ hC
      _ = C ^ 6 := by ring
  have hC5C6 : C ^ 5 ≤ C ^ 6 := by
    calc
      C ^ 5 = C ^ 5 * 1 := by ring
      _ ≤ C ^ 5 * C := by gcongr
      _ = C ^ 6 := by ring
  have hnN2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    calc
      (n : ℝ) = (n : ℝ) * 1 := by ring
      _ ≤ (n : ℝ) * n := by gcongr
      _ = (n : ℝ) ^ 2 := by ring
  have hq2q4 : q ^ 2 ≤ q ^ 4 := by
    calc
      q ^ 2 = q ^ 2 * 1 := by ring
      _ ≤ q ^ 2 * q ^ 2 := by gcongr; exact one_le_pow₀ hq
      _ = q ^ 4 := by ring
  have hq3q4 : q ^ 3 ≤ q ^ 4 := by
    calc
      q ^ 3 = q ^ 3 * 1 := by ring
      _ ≤ q ^ 3 * q := by gcongr
      _ = q ^ 4 := by ring
  have hq5 : q ^ 5 ≤ (n : ℝ) * q ^ 4 := by
    calc
      q ^ 5 = q * q ^ 4 := by ring
      _ ≤ (n : ℝ) * q ^ 4 := by gcongr
  have hb' : b ≤ 3 * C ^ 2 * q ^ 2 := by
    calc
      b ≤ 3 * x ^ 2 := hb
      _ = 3 * C ^ 2 * q ^ 2 := by dsimp only [x]; ring
  have hbh : b * h ≤ 9 * C ^ 4 * q ^ 5 := by
    calc
      b * h ≤ (3 * C ^ 2 * q ^ 2) * (3 * C ^ 2 * q ^ 3) := by gcongr
      _ = 9 * C ^ 4 * q ^ 5 := by ring
  have hbhZ : b * h ≤ 9 * Z := by
    apply hbh.trans
    dsimp only [Z]
    have hqpow : q ^ 5 ≤ (n : ℝ) * q ^ 4 := by
      calc
        q ^ 5 = q * q ^ 4 := by ring
        _ ≤ (n : ℝ) * q ^ 4 := by gcongr
    calc
      9 * C ^ 4 * q ^ 5 ≤ 9 * C ^ 4 * ((n : ℝ) * q ^ 4) := by gcongr
      _ ≤ 9 * C ^ 6 * ((n : ℝ) * q ^ 4) := by gcongr
      _ ≤ 9 * C ^ 6 * ((n : ℝ) ^ 2 * q ^ 4) := by gcongr
      _ = 9 * Z := by dsimp only [Z]; ring
  have hChZ : C * h ≤ 3 * Z := by
    apply (mul_le_mul_of_nonneg_left hh hC0).trans
    calc
      C * (3 * C ^ 2 * q ^ 3) = 3 * C ^ 3 * q ^ 3 := by ring
      _ ≤ 3 * C ^ 6 * q ^ 3 := by gcongr
      _ ≤ 3 * C ^ 6 * q ^ 4 := by gcongr
      _ ≤ 3 * C ^ 6 * ((n : ℝ) ^ 2 * q ^ 4) := by
        have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
        gcongr
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hn2 (pow_nonneg hq0 4)
      _ = 3 * Z := by dsimp only [Z]; ring
  have hCbZ : C * b ≤ 3 * Z := by
    apply (mul_le_mul_of_nonneg_left hb hC0).trans
    calc
      C * (3 * x ^ 2) = 3 * C ^ 3 * q ^ 2 := by dsimp only [x]; ring
      _ ≤ 3 * C ^ 6 * q ^ 2 := by gcongr
      _ ≤ 3 * C ^ 6 * q ^ 4 := by gcongr
      _ ≤ 3 * C ^ 6 * ((n : ℝ) ^ 2 * q ^ 4) := by
        have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
        gcongr
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hn2 (pow_nonneg hq0 4)
      _ = 3 * Z := by dsimp only [Z]; ring
  have hCnbhZ : 4 * C * (n : ℝ) * b * h ≤ 36 * Z := by
    calc
      4 * C * (n : ℝ) * b * h = 4 * C * (n : ℝ) * (b * h) := by ring
      _ ≤ 4 * C * (n : ℝ) * (9 * C ^ 4 * q ^ 5) := by gcongr
      _ = 36 * C ^ 5 * (n : ℝ) * q ^ 5 := by ring
      _ ≤ 36 * C ^ 5 * (n : ℝ) * ((n : ℝ) * q ^ 4) := by
        gcongr
      _ = 36 * C ^ 5 * (n : ℝ) ^ 2 * q ^ 4 := by ring
      _ ≤ 36 * C ^ 6 * (n : ℝ) ^ 2 * q ^ 4 := by gcongr
      _ = 36 * Z := by dsimp only [Z]; ring
  have hnbZ : (n : ℝ) * b ≤ 3 * Z := by
    apply (mul_le_mul_of_nonneg_left hb hn0).trans
    calc
      (n : ℝ) * (3 * x ^ 2) = 3 * C ^ 2 * (n : ℝ) * q ^ 2 := by
        dsimp only [x]
        ring
      _ ≤ 3 * C ^ 6 * (n : ℝ) * q ^ 2 := by gcongr
      _ ≤ 3 * C ^ 6 * (n : ℝ) ^ 2 * q ^ 2 := by gcongr
      _ ≤ 3 * C ^ 6 * (n : ℝ) ^ 2 * q ^ 4 := by gcongr
      _ = 3 * Z := by dsimp only [Z]; ring
  have hregularZ :
      (48 * (n : ℝ) ^ 2 * (C * q ^ 2) + 16 * n) * C ^ 2 *
          (C * q) * (C * q) ≤ 64 * Z := by
    have hfirst : C ^ 5 * (n : ℝ) ^ 2 * q ^ 4 ≤ Z := by
      dsimp only [Z]
      gcongr
    have hsecond : C ^ 4 * (n : ℝ) * q ^ 2 ≤ Z := by
      calc
        C ^ 4 * (n : ℝ) * q ^ 2 ≤ C ^ 6 * (n : ℝ) * q ^ 2 := by gcongr
        _ ≤ C ^ 6 * (n : ℝ) ^ 2 * q ^ 2 := by gcongr
        _ ≤ C ^ 6 * (n : ℝ) ^ 2 * q ^ 4 := by gcongr
        _ = Z := by dsimp only [Z]
    calc
      (48 * (n : ℝ) ^ 2 * (C * q ^ 2) + 16 * n) * C ^ 2 *
          (C * q) * (C * q) =
        48 * (C ^ 5 * (n : ℝ) ^ 2 * q ^ 4) +
          16 * (C ^ 4 * (n : ℝ) * q ^ 2) := by ring
      _ ≤ 48 * Z + 16 * Z := by gcongr
      _ = 64 * Z := by ring
  have hlastZ :
      8 * (n : ℝ) * n * C * (C * q) * (C * q) ≤ 8 * Z := by
    calc
      8 * (n : ℝ) * n * C * (C * q) * (C * q) =
          8 * C ^ 3 * (n : ℝ) ^ 2 * q ^ 2 := by ring
      _ ≤ 8 * C ^ 6 * (n : ℝ) ^ 2 * q ^ 2 := by gcongr
      _ ≤ 8 * C ^ 6 * (n : ℝ) ^ 2 * q ^ 4 := by gcongr
      _ = 8 * Z := by dsimp only [Z]; ring
  calc
    finiteLengthMCAEnvelope lambda n D B M H ≤
        2 * b * h + C * (h + b + 4 * n * b * h) + n * b +
          (48 * n ^ 2 * (C * q ^ 2) + 16 * n) * C ^ 2 *
            (C * q) * (C * q) +
          8 * n * n * C * (C * q) * (C * q) := hraw
    _ ≤ 140 * C ^ 6 * n ^ 2 * q ^ 4 := by
      dsimp only [Z] at hbhZ hChZ hCbZ hCnbhZ hnbZ hregularZ hlastZ
      nlinarith

/-- The exact line-MCA expression has the manuscript's
`O(n² / (eta + 1/n)^4)` envelope. -/
theorem finiteLengthMCAEnvelope_le
    {C eta lambda : ℝ} {n D B M H : ℕ}
    (hC : 1 ≤ C) (heta : 0 < eta) (hn : 1 ≤ n)
    (hsOne : finiteLengthSlack eta n ≤ 1)
    (hDn : D ≤ n) (hlambda0 : 0 ≤ lambda) (hlambda : lambda ≤ C)
    (hB : (B : ℝ) ≤ C / finiteLengthSlack eta n)
    (hM : (M : ℝ) ≤ C / finiteLengthSlack eta n)
    (hH : (H : ℝ) ≤ C / finiteLengthSlack eta n ^ 2) :
    finiteLengthMCAEnvelope lambda n D B M H ≤
      140 * C ^ 6 * n ^ 2 / finiteLengthSlack eta n ^ 4 := by
  let s := finiteLengthSlack eta n
  let q := 1 / s
  have hs : 0 < s := finiteLengthSlack_pos heta (by omega)
  have hq : 1 ≤ q := (one_le_div hs).2 hsOne
  have hqN : q ≤ (n : ℝ) := by
    dsimp only [q, s]
    exact finiteLengthSlack_inv_le_length heta.le (by omega)
  have hraw := finiteLengthMCAEnvelope_le_rateEnvelope hC hq hn hqN hDn
    hlambda0 hlambda (by simpa [q, s, div_eq_mul_inv] using hB)
      (by simpa [q, s, div_eq_mul_inv] using hM)
      (by dsimp only [q, s]; field_simp [ne_of_gt hs] at hH ⊢; nlinarith)
  dsimp only [q, s] at hraw ⊢
  field_simp [ne_of_gt hs] at hraw ⊢
  nlinarith

/-- Simpler inverse-`eta` consequence of the finite-length line envelope. -/
theorem finiteLengthMCAEnvelope_le_inv_eta
    {C eta lambda : ℝ} {n D B M H : ℕ}
    (hC : 1 ≤ C) (heta : 0 < eta) (hn : 1 ≤ n)
    (hsOne : finiteLengthSlack eta n ≤ 1)
    (hDn : D ≤ n) (hlambda0 : 0 ≤ lambda) (hlambda : lambda ≤ C)
    (hB : (B : ℝ) ≤ C / finiteLengthSlack eta n)
    (hM : (M : ℝ) ≤ C / finiteLengthSlack eta n)
    (hH : (H : ℝ) ≤ C / finiteLengthSlack eta n ^ 2) :
    finiteLengthMCAEnvelope lambda n D B M H ≤
      140 * C ^ 6 * n ^ 2 / eta ^ 4 := by
  apply (finiteLengthMCAEnvelope_le hC heta hn hsOne hDn hlambda0 hlambda
    hB hM hH).trans
  exact div_finiteLengthSlack_four_le_div_eta_four
    (by positivity : 0 ≤ 140 * C ^ 6 * (n : ℝ) ^ 2) heta (by omega)

end

end ReedSolomon.FirstOrder
