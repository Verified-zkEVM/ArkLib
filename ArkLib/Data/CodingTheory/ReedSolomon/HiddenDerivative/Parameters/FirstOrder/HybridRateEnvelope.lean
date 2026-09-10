/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.HybridConstants
/-!
# Scalar envelopes for the first-order constants

The physical rate bounds the agreement ratio independently of block length. Uniform bounds
on the recipe parameters then give the cubic list and quintic exception slack exponents.
The automatic recipe estimates are supplied by separate arithmetic theorems.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

set_option autoImplicit false

/-- The physical rate supplies the denominator gap in the retained agreement ratio. -/
theorem hybridTheta_le_rate_gap {n D A : ℕ} {rho a : ℝ}
    (hDn : D ≤ n) (hDA : D < A)
    (hD : (D : ℝ) ≤ rho * n) (hA : a * n ≤ A) (hgap : rho < a) :
    hybridTheta n D A ≤ 1 / (a - rho) := by
  have hden : (0 : ℝ) < (A - D : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hDA
  have hgap' : 0 < a - rho := sub_pos.mpr hgap
  unfold hybridTheta
  apply (div_le_div_iff₀ hden hgap').mpr
  rw [Nat.cast_sub hDn, Nat.cast_sub hDA.le]
  have hnonneg : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  nlinarith

private theorem monomial_bound {C N q : ℝ} (hC : 1 ≤ C) (hN : 1 ≤ N) (hq : 1 ≤ q)
    (r s t : ℕ) (hr : r ≤ 4) (hs : s ≤ 2) (ht : t ≤ 5) :
    C ^ r * N ^ s * q ^ t ≤ C ^ 4 * N ^ 2 * q ^ 5 := by
  gcongr

/-- A common scalar budget gives the cubic list envelope. Here `q` is an inverse slack. -/
theorem hybridLambdaClosed_le_rate_envelope {C q theta : ℝ} {n D mu M : ℕ}
    (hC : 1 ≤ C) (hq : 1 ≤ q) (hn : 1 ≤ n) (hD : D ≤ n)
    (htheta0 : 0 ≤ theta) (htheta : theta ≤ C)
    (hmu : (mu : ℝ) ≤ C * q) (hT0 : 0 ≤ hybridT mu M)
    (hT : hybridT mu M ≤ C * q ^ 3) :
    hybridLambdaClosed theta D mu M ≤ 3 * C ^ 2 * n * q ^ 3 := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD' : (D : ℝ) ≤ n := by exact_mod_cast hD
  have hsub : ((mu - M : ℕ) : ℝ) ≤ mu := by exact_mod_cast Nat.sub_le mu M
  have hq3 : q ≤ q ^ 3 := by simpa using (pow_le_pow_right₀ hq (by decide : 1 ≤ 3))
  have hC2 : C ≤ C ^ 2 := by simpa using (pow_le_pow_right₀ hC (by decide : 1 ≤ 2))
  calc
    hybridLambdaClosed theta D mu M ≤ 2 * n * C * (C * q ^ 3) + C * q := by
      unfold hybridLambdaClosed
      gcongr
      exact hsub.trans hmu
    _ ≤ 2 * n * C * (C * q ^ 3) + C ^ 2 * n * q ^ 3 := by
      apply add_le_add_right
      calc
        C * q ≤ C ^ 2 * q ^ 3 := by gcongr
        _ ≤ C ^ 2 * n * q ^ 3 := by
          calc
            C ^ 2 * q ^ 3 = C ^ 2 * 1 * q ^ 3 := by ring
            _ ≤ C ^ 2 * n * q ^ 3 := by gcongr
    _ = 3 * C ^ 2 * n * q ^ 3 := by ring

/-- A common scalar budget gives the quintic exception envelope. Here `q` is an inverse slack. -/
theorem hybridEClosed_le_rate_envelope {C q theta : ℝ} {n D h mu M : ℕ}
    (hC : 1 ≤ C) (hq : 1 ≤ q) (hn : 1 ≤ n) (hD : D ≤ n)
    (htheta0 : 0 ≤ theta) (htheta : theta ≤ C)
    (hmuPos : 1 ≤ mu) (hmu : (mu : ℝ) ≤ C * q)
    (hh : (h : ℝ) ≤ C * q ^ 2) (hT0 : 0 ≤ hybridT mu M)
    (hT : hybridT mu M ≤ C * q ^ 3) :
    hybridEClosed theta n D h mu M ≤ 45 * C ^ 4 * n ^ 2 * q ^ 5 := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD' : (D : ℝ) ≤ n := by exact_mod_cast hD
  have hsub : ((n - D - 1 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (Nat.sub_le (n - D) 1).trans (Nat.sub_le n D)
  have hmu' : ((2 * mu - 1 : ℕ) : ℝ) ≤ 2 * (C * q) := by
    calc
      ((2 * mu - 1 : ℕ) : ℝ) ≤ 2 * (mu : ℝ) := by
        exact_mod_cast Nat.sub_le (2 * mu) 1
      _ ≤ 2 * (C * q) := by gcongr
  have hzero : mu ≠ 0 := by omega
  calc
    hybridEClosed theta n D h mu M ≤
        2 * (C * q) * (C * q ^ 2) +
        C * (C * q ^ 2 + C * q + 4 * n * (C * q) * (C * q ^ 2)) +
        n * (C * q) + (24 * n ^ 2 * (C * q ^ 2) + 8 * n) * C ^ 2 * (C * q ^ 3) +
        4 * n * n * C * (C * q ^ 3) := by
      unfold hybridEClosed hybridOrdinaryRaw
      rw [if_neg hzero]
      gcongr
    _ = 2 * (C ^ 2 * (n : ℝ) ^ 0 * q ^ 3) +
        (C ^ 2 * (n : ℝ) ^ 0 * q ^ 2) +
        (C ^ 2 * (n : ℝ) ^ 0 * q ^ 1) +
        4 * (C ^ 3 * (n : ℝ) ^ 1 * q ^ 3) +
        (C ^ 1 * (n : ℝ) ^ 1 * q ^ 1) +
        24 * (C ^ 4 * (n : ℝ) ^ 2 * q ^ 5) +
        8 * (C ^ 3 * (n : ℝ) ^ 1 * q ^ 3) +
        4 * (C ^ 2 * (n : ℝ) ^ 2 * q ^ 3) := by ring
    _ ≤ 45 * C ^ 4 * n ^ 2 * q ^ 5 := by
      have h203 := monomial_bound hC hN hq 2 0 3 (by decide) (by decide) (by decide)
      have h202 := monomial_bound hC hN hq 2 0 2 (by decide) (by decide) (by decide)
      have h201 := monomial_bound hC hN hq 2 0 1 (by decide) (by decide) (by decide)
      have h313 := monomial_bound hC hN hq 3 1 3 (by decide) (by decide) (by decide)
      have h111 := monomial_bound hC hN hq 1 1 1 (by decide) (by decide) (by decide)
      have h223 := monomial_bound hC hN hq 2 2 3 (by decide) (by decide) (by decide)
      nlinarith
end ReedSolomon.HiddenDerivative
