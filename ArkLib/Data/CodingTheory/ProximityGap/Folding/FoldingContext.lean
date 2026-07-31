/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov
-/

import Mathlib.Data.Nat.Basic

namespace ProximityGap

class FoldingContextLeft (k d : outParam ℕ) where
  k_ge_1 : 1 ≤ k
  k_le_d : k ≤ d

class FoldingContextRight (d n : outParam ℕ) where
  d_le_n : d ≤ n

class FoldingContextMiddle (k n : outParam ℕ) where
  k_le_n : k ≤ n

class FoldingContext (k d n : outParam ℕ) extends 
  FoldingContextLeft k d, FoldingContextRight d n

instance {k d n : ℕ} [FoldingContext k d n] : FoldingContextMiddle k n where
  k_le_n := 
    le_trans FoldingContextLeft.k_le_d FoldingContextRight.d_le_n

instance {k d : ℕ} [FoldingContextLeft k d] : NeZero k where
  out := by 
    have := FoldingContextLeft.k_ge_1
    omega

instance {k d : ℕ} [FoldingContextLeft k d] : NeZero d where
  out := by 
    have := FoldingContextLeft.k_ge_1
    have := FoldingContextLeft.k_le_d 
    omega

instance {k d n : ℕ} [FoldingContext k d n] : NeZero d where
  out := by 
    have := FoldingContextLeft.k_ge_1
    have := FoldingContextLeft.k_le_d 
    omega


namespace FoldingContext

@[simp]
lemma k_le_d' {k d : ℕ} [FoldingContextLeft k d] :
  k ≤ d := FoldingContextLeft.k_le_d 

@[simp]
lemma d_le_n' {d n : ℕ} [FoldingContextRight d n] :
  d ≤ n := FoldingContextRight.d_le_n

@[simp]
lemma k_le_n {k n : ℕ} [FoldingContextMiddle k n] :
  k ≤ n := FoldingContextMiddle.k_le_n

@[simp]
lemma two_pow_k_le_two_pow_n {k d n : ℕ} [FoldingContext k d n] :
  2 ^ k ≤ 2 ^ n := by simp [Nat.pow_le_pow_right]

end FoldingContext

end ProximityGap


