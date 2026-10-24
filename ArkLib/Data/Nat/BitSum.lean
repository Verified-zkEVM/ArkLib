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
number is below `2 ^ B` and that the encoding is injective on bit vectors.
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

/-- Distinct bit vectors encode distinct numbers. -/
theorem eq_of_sum_pow_two_mul_eq {m : ℕ} (b b' : Fin m → ℕ)
    (hb : ∀ i, b i ≤ 1) (hb' : ∀ i, b' i ≤ 1)
    (h : ∑ i : Fin m, 2 ^ (i : ℕ) * b i = ∑ i : Fin m, 2 ^ (i : ℕ) * b' i) : b = b' := by
  induction m with
  | zero => exact funext fun i => i.elim0
  | succ m ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h
    have hs : ∀ c : Fin (m + 1) → ℕ, ∑ i : Fin m, 2 ^ ((i.succ : Fin (m + 1)) : ℕ) * c i.succ =
        2 * ∑ i : Fin m, 2 ^ (i : ℕ) * c i.succ := fun c => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        simp [pow_succ, Nat.mul_left_comm, Nat.mul_assoc]
    rw [hs b, hs b'] at h
    simp only [Fin.val_zero, pow_zero, one_mul] at h
    have h0 : b 0 = b' 0 := by have := hb 0; have := hb' 0; omega
    have h1 : ∑ i : Fin m, 2 ^ (i : ℕ) * b i.succ = ∑ i : Fin m, 2 ^ (i : ℕ) * b' i.succ := by
      omega
    have := ih (fun i => b i.succ) (fun i => b' i.succ) (fun i => hb _) (fun i => hb' _) h1
    funext i
    exact Fin.cases h0 (fun i => congrFun this i) i

end Nat
