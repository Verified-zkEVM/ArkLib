/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Profile

/-!
# Finite-length first-order parameter bounds

This file defines the finite-length slack `η + 1/n` and gives squarefree list and line-MCA
envelopes in terms of that slack. The interpolation parameters remain natural numbers, preserving
their exact ceilings, floors, and truncated differences.

## Main statements

* `squarefreeListExpression_le_finiteLength`: a finite-length squarefree list envelope.
* `finiteLengthMcaEnvelope`: the exact natural-parameter line-MCA expression.
* `finiteLengthMcaEnvelope_le` and `finiteLengthMcaEnvelope_le_inv_eta`: fourth-power bounds for
  the line-MCA expression.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon.FirstOrder

open ReedSolomon.HiddenDerivative
open ReedSolomon.FirstOrder.Squarefree

noncomputable section

set_option autoImplicit false

/-- The exact finite-length gap `s = eta + 1/n` used by the first-order theorem.

Here `eta` is the positive real gap above the asymptotic first-order agreement curve and `n` is
the block length. The extra `1/n` absorbs the one-degree difference between message dimension `k`
and maximum polynomial degree `k - 1`; replacing `s` by `eta` gives the coarser headline bounds. -/
def finiteLengthSlack (eta : ℝ) (n : ℕ) : ℝ := eta + 1 / (n : ℝ)

/-- The finite-length slack is positive for positive `eta`. -/
theorem finiteLengthSlack_pos {eta : ℝ} {n : ℕ} (heta : 0 < eta) :
    0 < finiteLengthSlack eta n := by
  unfold finiteLengthSlack
  positivity

/-- The finite-length slack is at least `eta`. -/
theorem eta_le_finiteLengthSlack {eta : ℝ} {n : ℕ} :
    eta ≤ finiteLengthSlack eta n := by
  unfold finiteLengthSlack
  exact le_add_of_nonneg_right (by positivity)

/-- The one-degree saving gives the exact absorption inequality `1/s ≤ n`. -/
theorem finiteLengthSlack_inv_le_length {eta : ℝ} {n : ℕ}
    (heta : 0 ≤ eta) (hn : 0 < n) :
    1 / finiteLengthSlack eta n ≤ n :=
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  (one_div_le (by unfold finiteLengthSlack; positivity) hn').2 (le_add_of_nonneg_left heta)

private theorem div_finiteLengthSlack_pow_le_div_eta_pow
    {C eta : ℝ} {n : ℕ} (hC : 0 ≤ C) (heta : 0 < eta) (p : ℕ) :
    C / finiteLengthSlack eta n ^ p ≤ C / eta ^ p := by
  have hs := eta_le_finiteLengthSlack (eta := eta) (n := n)
  exact div_le_div_of_nonneg_left hC (pow_pos heta p)
    (pow_le_pow_left₀ heta.le hs p)

/-- Replacing the finite-length slack by `eta` only weakens a square-power bound. -/
theorem div_finiteLengthSlack_sq_le_div_eta_sq
    {C eta : ℝ} {n : ℕ} (hC : 0 ≤ C) (heta : 0 < eta) :
    C / finiteLengthSlack eta n ^ 2 ≤ C / eta ^ 2 :=
  div_finiteLengthSlack_pow_le_div_eta_pow hC heta 2

/-- Replacing the finite-length slack by `eta` only weakens a fourth-power bound. -/
theorem div_finiteLengthSlack_four_le_div_eta_four
    {C eta : ℝ} {n : ℕ} (hC : 0 ≤ C) (heta : 0 < eta) :
    C / finiteLengthSlack eta n ^ 4 ≤ C / eta ^ 4 :=
  div_finiteLengthSlack_pow_le_div_eta_pow hC heta 4

/-- A common inverse-finite-slack cap gives the squarefree list envelope
`O(n / (eta + 1/n)^2)`. -/
theorem squarefreeListExpression_le_finiteLength
    {C eta lambda : ℝ} {n D B M : ℕ}
    (hC : 1 ≤ C) (heta : 0 < eta) (hn : 1 ≤ n)
    (hsOne : finiteLengthSlack eta n ≤ 1)
    (hD : 1 ≤ D) (hDn : D ≤ n) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hlambda0 : 0 ≤ lambda) (hlambda : lambda ≤ C)
    (hB : (B : ℝ) ≤ C / finiteLengthSlack eta n) :
    (firstOrderCurveFiberStageOne (D + 1) B M (regularTaylorExponent D) : ℝ) * lambda +
        ordinaryDegreeEnvelope B M ≤
      7 * C ^ 3 * n / finiteLengthSlack eta n ^ 2 := by
  have hs : 0 < finiteLengthSlack eta n := finiteLengthSlack_pos heta
  have hraw := FirstOrder.Squarefree.squarefreeListExpression_le_rate_envelope hC
    ((one_le_div hs).2 hsOne) hn hD hDn hM hMB hlambda0 hlambda
    (hB.trans_eq (div_eq_mul_one_div _ _))
  rwa [one_div_pow, ← div_eq_mul_one_div] at hraw

/-- Exact finite first-order line-MCA expression.  The natural subtractions preserve the
small-length and full-agreement boundary behavior of the semantic counting theorem. -/
def finiteLengthMcaEnvelope
    (lambda : ℝ) (n D B M H : ℕ) : ℝ :=
  let b := B * (2 * M + 1)
  let h := H * (2 * M + 1)
  (((2 * b - 1 : ℕ) : ℝ) * h +
      lambda * (h + b + 4 * D * b * h) +
      ((n - D - 1 : ℕ) : ℝ) * b) +
    (48 * (D : ℝ) ^ 2 * H + 16 * D) * lambda ^ 2 * B * M +
    8 * D * ((n - D - 1 : ℕ) : ℝ) * lambda * B * M

/-- A monomial `C^a n^c q^d` with `a ≤ 6`, `c ≤ 2` and `c + d ≤ 6` is at most `C⁶ n² q⁴` when
`1 ≤ C` and `1 ≤ q ≤ n`. -/
private theorem monomial_le_rateMonomial {C q n : ℝ} (hC : 1 ≤ C) (hq : 1 ≤ q) (hqn : q ≤ n)
    {a c d : ℕ} (ha : a ≤ 6 := by norm_num) (hc : c ≤ 2 := by norm_num)
    (hcd : c + d ≤ 6 := by norm_num) :
    C ^ a * n ^ c * q ^ d ≤ C ^ 6 * n ^ 2 * q ^ 4 := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hn : 1 ≤ n := hq.trans hqn
  have hnq : n ^ c * q ^ d ≤ n ^ 2 * q ^ 4 := by
    rcases le_or_gt d 4 with hd | hd
    · exact mul_le_mul (pow_le_pow_right₀ hn hc) (pow_le_pow_right₀ hq hd)
        (pow_nonneg hq0 d) (pow_nonneg (zero_le_one.trans hn) 2)
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hd
      calc
        n ^ c * q ^ (4 + e + 1) = n ^ c * q ^ (e + 1) * q ^ 4 := by ring
        _ ≤ n ^ c * n ^ (e + 1) * q ^ 4 := by gcongr
        _ = n ^ (c + (e + 1)) * q ^ 4 := by ring
        _ ≤ n ^ 2 * q ^ 4 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hn (by omega)) (pow_nonneg hq0 4)
  calc
    C ^ a * n ^ c * q ^ d = C ^ a * (n ^ c * q ^ d) := by ring
    _ ≤ C ^ 6 * (n ^ 2 * q ^ 4) :=
      mul_le_mul (pow_le_pow_right₀ hC ha) hnq (by positivity) (by positivity)
    _ = C ^ 6 * n ^ 2 * q ^ 4 := by ring

/-- The real-arithmetic core of `finiteLengthMcaEnvelope_le_rateEnvelope`, with `b` and `h`
standing for `B (2M + 1)` and `H (2M + 1)`, `s` for `2b - 1` and `t` for `n - D - 1`. -/
private theorem mcaEnvelope_arith_le {C q n lambda D t B M H b h s : ℝ}
    (hC : 1 ≤ C) (hq : 1 ≤ q) (hqN : q ≤ n) (hD0 : 0 ≤ D) (hD : D ≤ n)
    (ht0 : 0 ≤ t) (ht : t ≤ n) (hlambda0 : 0 ≤ lambda) (hlambda : lambda ≤ C) (hB0 : 0 ≤ B)
    (hB : B ≤ C * q) (hM0 : 0 ≤ M) (hM : M ≤ C * q) (hH0 : 0 ≤ H) (hH : H ≤ C * q ^ 2)
    (hb0 : 0 ≤ b) (hb : b ≤ 3 * C ^ 2 * q ^ 2) (hh0 : 0 ≤ h) (hh : h ≤ 3 * C ^ 2 * q ^ 3)
    (hs : s ≤ 2 * b) :
    s * h + lambda * (h + b + 4 * D * b * h) + t * b +
        (48 * D ^ 2 * H + 16 * D) * lambda ^ 2 * B * M + 8 * D * t * lambda * B * M ≤
      140 * C ^ 6 * n ^ 2 * q ^ 4 := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hn : 1 ≤ n := hq.trans hqN
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hbh0 : 0 ≤ b * h := mul_nonneg hb0 hh0
  have hbh : b * h ≤ 3 * C ^ 2 * q ^ 2 * (3 * C ^ 2 * q ^ 3) :=
    mul_le_mul hb hh hh0 (by positivity)
  have hfirst : s * h ≤ 2 * b * h := mul_le_mul_of_nonneg_right hs hh0
  have hDbh : D * (b * h) ≤ n * (b * h) := mul_le_mul_of_nonneg_right hD hbh0
  have hmiddle : lambda * (h + b + 4 * D * b * h) ≤ C * (h + b + 4 * n * (b * h)) :=
    mul_le_mul hlambda (by linarith) (by positivity) hC0
  have htail : t * b ≤ n * b := mul_le_mul_of_nonneg_right ht hb0
  have hregular : (48 * D ^ 2 * H + 16 * D) * lambda ^ 2 * B * M ≤
      (48 * n ^ 2 * (C * q ^ 2) + 16 * n) * C ^ 2 * (C * q) * (C * q) := by
    gcongr
  have hlast : 8 * D * t * lambda * B * M ≤ 8 * n * n * C * (C * q) * (C * q) := by
    gcongr
  have hCh := mul_le_mul_of_nonneg_left hh hC0
  have hCb := mul_le_mul_of_nonneg_left hb hC0
  have hnb := mul_le_mul_of_nonneg_left hb hn0
  have hCnbh := mul_le_mul_of_nonneg_left hbh (mul_nonneg hC0 hn0)
  have := monomial_le_rateMonomial (a := 4) (c := 0) (d := 5) hC hq hqN
  have := monomial_le_rateMonomial (a := 3) (c := 0) (d := 3) hC hq hqN
  have := monomial_le_rateMonomial (a := 3) (c := 0) (d := 2) hC hq hqN
  have := monomial_le_rateMonomial (a := 5) (c := 1) (d := 5) hC hq hqN
  have := monomial_le_rateMonomial (a := 2) (c := 1) (d := 2) hC hq hqN
  have := monomial_le_rateMonomial (a := 5) (c := 2) (d := 4) hC hq hqN
  have := monomial_le_rateMonomial (a := 4) (c := 1) (d := 2) hC hq hqN
  have := monomial_le_rateMonomial (a := 3) (c := 2) (d := 2) hC hq hqN
  linarith

/-- The line-MCA envelope is at most `140 C⁶ n² q⁴` under the displayed parameter bounds. -/
theorem finiteLengthMcaEnvelope_le_rateEnvelope
    {C q lambda : ℝ} {n D B M H : ℕ}
    (hC : 1 ≤ C) (hq : 1 ≤ q) (_hn : 1 ≤ n) (hqN : q ≤ n)
    (hDn : D ≤ n) (hlambda0 : 0 ≤ lambda) (hlambda : lambda ≤ C)
    (hB : (B : ℝ) ≤ C * q) (hM : (M : ℝ) ≤ C * q)
    (hH : (H : ℝ) ≤ C * q ^ 2) :
    finiteLengthMcaEnvelope lambda n D B M H ≤ 140 * C ^ 6 * n ^ 2 * q ^ 4 := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have htwoM : 2 * (M : ℝ) + 1 ≤ 3 * (C * q) := by
    linarith [one_le_mul_of_one_le_of_one_le hC hq]
  have hb : ((B * (2 * M + 1) : ℕ) : ℝ) ≤ 3 * C ^ 2 * q ^ 2 := by
    push_cast
    calc
      (B : ℝ) * (2 * M + 1) ≤ C * q * (3 * (C * q)) :=
        mul_le_mul hB htwoM (by positivity) (by positivity)
      _ = 3 * C ^ 2 * q ^ 2 := by ring
  have hh : ((H * (2 * M + 1) : ℕ) : ℝ) ≤ 3 * C ^ 2 * q ^ 3 := by
    push_cast
    calc
      (H : ℝ) * (2 * M + 1) ≤ C * q ^ 2 * (3 * (C * q)) :=
        mul_le_mul hH htwoM (by positivity) (by positivity)
      _ = 3 * C ^ 2 * q ^ 3 := by ring
  have hs : ((2 * (B * (2 * M + 1)) - 1 : ℕ) : ℝ) ≤ 2 * ((B * (2 * M + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le _ 1
  exact mcaEnvelope_arith_le hC hq hqN (Nat.cast_nonneg D)
    (by exact_mod_cast hDn) (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le n (D + 1))
    hlambda0 hlambda
    (Nat.cast_nonneg B) hB (Nat.cast_nonneg M) hM (Nat.cast_nonneg H) hH (Nat.cast_nonneg _) hb
    (Nat.cast_nonneg _) hh hs

/-- The line-MCA envelope is at most `140 C⁶ n² / (eta + 1/n)⁴` under the displayed bounds. -/
theorem finiteLengthMcaEnvelope_le
    {C eta lambda : ℝ} {n D B M H : ℕ}
    (hC : 1 ≤ C) (heta : 0 < eta) (hn : 1 ≤ n)
    (hsOne : finiteLengthSlack eta n ≤ 1)
    (hDn : D ≤ n) (hlambda0 : 0 ≤ lambda) (hlambda : lambda ≤ C)
    (hB : (B : ℝ) ≤ C / finiteLengthSlack eta n)
    (hM : (M : ℝ) ≤ C / finiteLengthSlack eta n)
    (hH : (H : ℝ) ≤ C / finiteLengthSlack eta n ^ 2) :
    finiteLengthMcaEnvelope lambda n D B M H ≤
      140 * C ^ 6 * n ^ 2 / finiteLengthSlack eta n ^ 4 := by
  let s := finiteLengthSlack eta n
  let q := 1 / s
  have hs : 0 < s := finiteLengthSlack_pos heta
  have hq : 1 ≤ q := (one_le_div hs).2 hsOne
  have hqN : q ≤ (n : ℝ) := finiteLengthSlack_inv_le_length heta.le (by omega)
  have hraw := finiteLengthMcaEnvelope_le_rateEnvelope hC hq hn hqN hDn
    hlambda0 hlambda (hB.trans_eq (div_eq_mul_one_div _ _))
      (hM.trans_eq (div_eq_mul_one_div _ _))
      (hH.trans_eq (by rw [one_div_pow, div_eq_mul_one_div]))
  rwa [one_div_pow, ← div_eq_mul_one_div] at hraw

/-- The line-MCA envelope is at most `140 C⁶ n² / eta⁴` under the displayed bounds. -/
theorem finiteLengthMcaEnvelope_le_inv_eta
    {C eta lambda : ℝ} {n D B M H : ℕ}
    (hC : 1 ≤ C) (heta : 0 < eta) (hn : 1 ≤ n)
    (hsOne : finiteLengthSlack eta n ≤ 1)
    (hDn : D ≤ n) (hlambda0 : 0 ≤ lambda) (hlambda : lambda ≤ C)
    (hB : (B : ℝ) ≤ C / finiteLengthSlack eta n)
    (hM : (M : ℝ) ≤ C / finiteLengthSlack eta n)
    (hH : (H : ℝ) ≤ C / finiteLengthSlack eta n ^ 2) :
    finiteLengthMcaEnvelope lambda n D B M H ≤
      140 * C ^ 6 * n ^ 2 / eta ^ 4 := by
  apply (finiteLengthMcaEnvelope_le hC heta hn hsOne hDn hlambda0 hlambda
    hB hM hH).trans
  exact div_finiteLengthSlack_four_le_div_eta_four
    (by positivity : 0 ≤ 140 * C ^ 6 * (n : ℝ) ^ 2) heta

end

end ReedSolomon.FirstOrder
