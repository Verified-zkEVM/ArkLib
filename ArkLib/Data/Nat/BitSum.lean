/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

/-!
# Sums of powers of two weighted by bits

A vector of `B` bits `b₀, …, b_{B-1}` encodes the number `∑ₖ 2ᵏ · bₖ`. This file proves that such a
number is below `2 ^ B`.
-/

@[expose] public section

open Finset

namespace Nat

/-- A vector of bits `b₀, …, b_{B-1} ∈ {0, 1}` encodes a number below `2 ^ B`. -/
theorem sum_pow_two_mul_lt {B : ℕ} (b : Fin B → ℕ) (hb : ∀ k, b k ≤ 1) :
    ∑ k : Fin B, 2 ^ (k : ℕ) * b k < 2 ^ B := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Fin.sum_univ_succ]
    have h := ih (fun k => b k.succ) (fun k => hb _)
    have h0 := hb 0
    have hs : ∑ k : Fin B, 2 ^ ((k.succ : Fin (B + 1)) : ℕ) * b k.succ =
        2 * ∑ k : Fin B, 2 ^ (k : ℕ) * b k.succ := by
      rw [mul_sum]
      exact sum_congr rfl fun k _ => by simp [pow_succ]; ring
    rw [hs, pow_succ]
    simp only [Fin.val_zero, pow_zero, one_mul]
    omega

end Nat
