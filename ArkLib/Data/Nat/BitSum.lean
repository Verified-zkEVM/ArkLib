/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.GeomSum

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
  have h : ∑ k : Fin B, 2 ^ (k : ℕ) * b k =
      ∑ k ∈ (univ.filter fun k : Fin B => b k = 1).map Fin.valEmbedding, 2 ^ k := by
    rw [sum_map, sum_filter]
    refine sum_congr rfl fun k _ => ?_
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hb k) with h0 | h1 <;> simp [*]
  rw [h]
  exact Nat.geomSum_lt le_rfl fun k hk => by
    obtain ⟨a, _, rfl⟩ := mem_map.1 hk
    exact a.isLt

end Nat
