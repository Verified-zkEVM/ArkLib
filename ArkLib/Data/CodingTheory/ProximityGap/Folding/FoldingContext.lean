/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.Data.Nat.Basic
import ArkLib.Data.Fin.Basic

namespace ProximityGap

class FoldingContextLeft (k d : outParam ℕ) where
  k_ge_1 : 1 ≤ k
  k_le_d : k ≤ d

class FoldingContextRight (d n : outParam ℕ) where
  d_le_n : d ≤ n

class FoldingContextMiddle (k n : outParam ℕ) where
  k_ge_1 : 1 ≤ k
  k_le_n : k ≤ n

class FoldingContext (k d n : outParam ℕ) extends
  FoldingContextLeft k d, FoldingContextRight d n

instance {k d n : ℕ} [FoldingContext k d n] : FoldingContextMiddle k n where
  k_ge_1 := FoldingContextLeft.k_ge_1
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

instance {k d n : ℕ} [FoldingContext k d n] : NeZero n where
  out := by
    have := FoldingContextLeft.k_ge_1
    have := FoldingContextMiddle.k_le_n
    omega

namespace FoldingContext

@[reducible]
def mk' {k d n : ℕ} (h_k_ge_1 : 1 ≤ k) (h_k_le_d : k ≤ d)
  (h_d_le_n : d ≤ n) : FoldingContext k d n where
  k_ge_1 := h_k_ge_1
  k_le_d := h_k_le_d
  d_le_n := h_d_le_n

@[reducible]
def ofMiddle {k n : ℕ} [FoldingContextMiddle k n] : FoldingContext k n n where
  k_ge_1 := FoldingContextMiddle.k_ge_1
  k_le_d := FoldingContextMiddle.k_le_n
  d_le_n := le_refl _

@[simp, grind →]
lemma k_ge_1' {k d : ℕ} [FoldingContextLeft k d] :
  1 ≤ k := FoldingContextLeft.k_ge_1

@[simp, grind! →]
lemma k_le_d' {k d : ℕ} [FoldingContextLeft k d] :
  k ≤ d := FoldingContextLeft.k_le_d

@[simp, grind! →]
lemma d_le_n' {d n : ℕ} [FoldingContextRight d n] :
  d ≤ n := FoldingContextRight.d_le_n

@[simp, grind! →]
lemma k_le_n {k n : ℕ} [FoldingContextMiddle k n] :
  k ≤ n := FoldingContextMiddle.k_le_n

@[simp high, grind! →]
lemma k_sub_one_le_n_sub_one {k d n : ℕ} [FoldingContext k d n] :
  k - 1 ≤ n - 1 := by
  have := k_ge_1'
  have := k_le_n
  omega

@[simp, grind! →]
lemma two_pow_k_le_two_pow_n
  {A : Type*} [Monoid A] [LinearOrder A] [MulLeftMono A] [OfNat A 2]
  {k d n : ℕ} [FoldingContext k d n] (h_two : (1 : A) ≤ 2) :
  (2 : A) ^ k ≤ (2 : A) ^ n := pow_le_pow_right' h_two (by simp)

@[simp, grind! →]
lemma two_pow_k_le_two_pow_d
  {A : Type*} [Monoid A] [LinearOrder A] [MulLeftMono A] [OfNat A 2]
  {k d n : ℕ} [FoldingContext k d n] (h_two : (1 : A) ≤ 2) :
  (2 : A) ^ k ≤ (2 : A) ^ d := pow_le_pow_right' h_two (by simp)

@[simp, grind! →]
lemma two_pow_d_le_two_pow_n
  {A : Type*} [Monoid A] [LinearOrder A] [MulLeftMono A] [OfNat A 2]
  {d n : ℕ} [FoldingContextRight d n] (h_two : (1 : A) ≤ 2) :
  (2 : A) ^ d ≤ (2 : A) ^ n := pow_le_pow_right' h_two (by simp)

@[simp, grind! →]
lemma two_pow_d_sub_k_le_two_pow_n_sub_k
  {A : Type*} [Monoid A] [LinearOrder A] [MulLeftMono A] [OfNat A 2]
  {k d n : ℕ} [FoldingContext k d n] (h_two : (1 : A) ≤ 2) :
  (2 : A) ^ (d - k) ≤ (2 : A) ^ (n - k) :=
  pow_le_pow_right' h_two (by simp)

@[simp, grind =]
lemma one_add_sub_one {k d : ℕ} [FoldingContextLeft k d] :
  1 + (k - 1) = k := by
  rw [Nat.add_sub_cancel' (by simp)]

@[simp, grind =]
lemma n_sub_1_sub_k_sub_1_eq_n_sub_k {k d n : ℕ} [FoldingContext k d n] :
  n - 1 - (k - 1) = n - k := by
  have := k_ge_1'
  have := k_le_n
  omega

@[simp, grind =]
lemma pow_2_n_sub_k_eq_n_sub_k
  {A : Type*} [Group A] [LinearOrder A] [MulLeftMono A] [OfNat A 2]
  {k d n : ℕ} [FoldingContext k d n] :
  (2 : A) ^ n / (2 : A) ^ k = (2 : A) ^ (n - k) := by
  calc
    (2 : A) ^ n / (2 : A) ^ k =
      (2 : A) ^ (n - k) := by
      rw [div_eq_mul_inv]
      exact (pow_sub 2 (by simp)).symm
    _ = (2 : A) ^ (n - k) := by simp

@[simp, grind =]
lemma pow_2_n_sub_1_sub_k_sub_1_eq_n_sub_k
  {A : Type*} [Group A] [LinearOrder A] [MulLeftMono A] [OfNat A 2]
  {k d n : ℕ} [FoldingContext k d n] :
  (2 : A) ^ (n - 1) / (2 : A) ^ ((k - 1)) = (2 : A) ^ (n - k) := by
  calc
    (2 : A) ^ (n - 1) / (2 : A) ^ (k - 1) =
      (2 : A) ^ ((n - 1) - (k - 1)) := by
      rw [div_eq_mul_inv]
      exact (pow_sub 2 (by simp)).symm
    _ = (2 : A) ^ (n - k) := by simp

@[simp, grind =]
lemma n_sub_k_add_k {k n : ℕ} [FoldingContextMiddle k n] :
  n - k + k = n := by
  have := k_le_n
  omega

@[simp, grind =]
lemma d_sub_k_add_k {k d : ℕ} [FoldingContextLeft k d] :
  d - k + k = d := by
  have := k_le_d'
  omega

@[grind =]
lemma d_sub_k_add_n {k d n : ℕ} [FoldingContext k d n] :
  d - k + n = n + d - k := by
  have := k_le_d'
  have := d_le_n'
  omega

@[grind =]
lemma n_sub_k_add_d {k d n : ℕ} [FoldingContext k d n] :
  n - k + d = n + d - k := by
  have := k_le_d'
  have := d_le_n'
  omega

@[simp, grind =]
lemma pow_2_d_sub_k_mul_pow_2_k
  {A : Type*} [Monoid A] [OfNat A 2]
  {k d : ℕ} [FoldingContextLeft k d] :
  (2 : A) ^ (d - k) * (2 : A) ^ k = (2 : A) ^ d := by
  simp [←pow_add]

@[simp, grind =]
lemma pow_2_k_mul_pow_2_d_sub_k
  {A : Type*} [Monoid A] [OfNat A 2]
  {k d : ℕ} [FoldingContextLeft k d] :
  (2 : A) ^ k * (2 : A) ^ (d - k) = (2 : A) ^ d := by simp [←pow_add]

@[simp, grind =]
lemma min_pow_2_d_pow_2_n
  {d n : ℕ} [FoldingContextRight d n] :
  min ((2 : ℕ) ^ d) ((2 : ℕ) ^ n) = 2 ^ d := by simp

@[grind! →]
lemma pow_2_k_mul_le_pow_2_d_of
  {A : Type*} [Monoid A] [LinearOrder A] [MulLeftMono A]
  [OfNat A 2] {k d : ℕ} [FoldingContextLeft k d] {x : A}
  (h : x ≤ (2 : A) ^ (d - k)) :
    (2 : A) ^ k * x ≤ (2 : A) ^ d := by
  calc
    (2 : A) ^ k * x ≤ (2 : A) ^ k * (2 : A) ^ (d - k) :=
      mul_le_mul_right h _
    _ = (2 : A) ^ d := by grind

@[simp]
lemma pow_2_k_mul_le_pow_2_d_iff
  {A : Type*} [Monoid A] [LinearOrder A] [MulLeftMono A]
  [MulLeftStrictMono A]
  [OfNat A 2] {k d : ℕ} [FoldingContextLeft k d] {x : A} :
  (2 : A) ^ k * x ≤ (2 : A) ^ d ↔
    x ≤ (2 : A) ^ (d - k) where
  mp h := by
    by_contra! contra
    have : 2 ^ d < 2 ^ k * x := by
      rw [←pow_2_k_mul_pow_2_d_sub_k]
      exact mul_lt_mul_right contra _
    have : 2 ^ d < 2 ^ d := by grind
    simp_all
  mpr h := by grind

end FoldingContext

end ProximityGap


