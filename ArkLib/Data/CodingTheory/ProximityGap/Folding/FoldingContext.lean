/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Order.Lattice.Nat

/-! # The folding context

Folding arguments (as in FRI/STIR/WHIR) are parameterized by three natural numbers:
* `k` — the folding arity exponent: each folding step collapses blocks of `2 ^ k` points;
* `d` — the degree exponent: messages are polynomials of degree `< 2 ^ d`;
* `n` — the domain exponent: the evaluation domain has `2 ^ n` points.

These are always subject to the constraints `1 ≤ k ≤ d ≤ n`. Carrying those inequalities
around by hand is noisy, so this file packages them into typeclasses and derives the
arithmetic facts (`n - k + k = n`, `2 ^ k * 2 ^ (d - k) = 2 ^ d`, …) that downstream
proofs repeatedly need. Most lemmas are tagged `@[grind]` so that
`grind` can discharge these side conditions automatically.

## Main definitions

* `FoldingContextLeft k d` — the constraints `1 ≤ k` and `k ≤ d`.
* `FoldingContextRight d n` — the constraint `d ≤ n`.
* `FoldingContextMiddle k n` — the derived constraints `1 ≤ k` and `k ≤ n`.
* `FoldingContext k d n` — the full context `1 ≤ k ≤ d ≤ n`.
-/

namespace ProximityGap

/-- The "left half" of a folding context: the folding arity exponent `k` is positive
  and does not exceed the degree exponent `d`. -/
class FoldingContextLeft (k d : outParam ℕ) where
  /-- Folding is done in blocks of `2 ^ k` points, so at least one halving step occurs. -/
  k_ge_1 : 1 ≤ k
  /-- One cannot fold away more degree than the message has. -/
  k_le_d : k ≤ d

/-- The "right half" of a folding context: the degree exponent `d` does not exceed the
  domain exponent `n`, i.e. the code has rate at most one. -/
class FoldingContextRight (d n : outParam ℕ) where
  /-- The evaluation domain is at least as large as the message space. -/
  d_le_n : d ≤ n

/-- The composite of `FoldingContextLeft` and `FoldingContextRight`, stated directly in
  terms of `k` and `n`: the folding arity exponent is positive and fits inside the
  domain exponent. This is the weakest context under which `foldWord` makes sense. -/
class FoldingContextMiddle (k n : outParam ℕ) where
  /-- Folding is done in blocks of `2 ^ k` points, so at least one halving step occurs. -/
  k_ge_1 : 1 ≤ k
  /-- One cannot fold a domain by more than its own size. -/
  k_le_n : k ≤ n

/-- A full folding context: `1 ≤ k ≤ d ≤ n`, where `2 ^ k` is the folding arity,
  `2 ^ d` bounds the degree of messages, and `2 ^ n` is the size of the evaluation
  domain. -/
class FoldingContext (k d n : outParam ℕ) extends
  FoldingContextLeft k d, FoldingContextRight d n where

namespace FoldingContext

/-- A full context yields the middle one by transitivity: `k ≤ d ≤ n`. -/
scoped instance {k d n : ℕ} [FoldingContext k d n] : FoldingContextMiddle k n where
  k_ge_1 := FoldingContextLeft.k_ge_1
  k_le_n :=
    le_trans FoldingContextLeft.k_le_d FoldingContextRight.d_le_n

/-- `k` is nonzero in a `FoldingContextLeft k d`. -/
scoped instance {k d : ℕ} [FoldingContextLeft k d] : NeZero k where
  out := by
    have := FoldingContextLeft.k_ge_1
    omega

/-- `d` is nonzero, since `1 ≤ k ≤ d`, in a `FoldingContextLeft k d`. -/
scoped instance {k d : ℕ} [FoldingContextLeft k d] : NeZero d where
  out := by
    have := FoldingContextLeft.k_ge_1
    have := FoldingContextLeft.k_le_d
    omega

/-- `n` is nonzero, since `1 ≤ k ≤ n`, in a `FoldingContextMiddle k n`. -/
scoped instance {k n : ℕ} [FoldingContextMiddle k n] : NeZero n where
  out := by
    have := FoldingContextMiddle.k_ge_1
    have := FoldingContextMiddle.k_le_n
    omega

set_option linter.defProp false in
/-- Build a `FoldingContext` from the three inequalities `1 ≤ k`, `k ≤ d` and `d ≤ n`. -/
@[reducible]
def mk' {k d n : ℕ} (h_k_ge_1 : 1 ≤ k) (h_k_le_d : k ≤ d)
  (h_d_le_n : d ≤ n) : FoldingContext k d n where
  k_ge_1 := h_k_ge_1
  k_le_d := h_k_le_d
  d_le_n := h_d_le_n

set_option linter.defProp false in
/-- Any `FoldingContextMiddle k n` upgrades to the degenerate full context
  `FoldingContext k n n`, i.e. the rate-one case where messages may have degree up to
  the size of the domain. Useful for reusing full-context lemmas when only the middle
  context is available. -/
@[reducible]
def ofMiddle {k n : ℕ} [FoldingContextMiddle k n] : FoldingContext k n n where
  k_ge_1 := FoldingContextMiddle.k_ge_1
  k_le_d := FoldingContextMiddle.k_le_n
  d_le_n := le_refl _

set_option linter.defProp false in
/-- If `k` folding steps are allowed then so is just one step. -/
@[reducible]
def oneStep {k d n : ℕ} [FoldingContext k d n] : FoldingContext 1 d n where
  k_ge_1 := by rfl
  k_le_d := by
    have := FoldingContextLeft.k_ge_1
    have := FoldingContextLeft.k_le_d
    omega
  d_le_n := FoldingContextRight.d_le_n

attribute [grind →] FoldingContextLeft.k_ge_1 FoldingContextLeft.k_le_d
                          FoldingContextRight.d_le_n FoldingContextMiddle.k_le_n

attribute [grind cases] FoldingContext

/-- Monotonicity of truncated subtraction on the context bounds: `k - 1 ≤ n - 1`.
  Appears when comparing block indices after a single halving step. -/
@[grind! →]
lemma k_sub_one_le_n_sub_one {k n : ℕ} [FoldingContextMiddle k n] :
  k - 1 ≤ n - 1 := by
  grind

/-- `2 ^ k ≤ 2 ^ n` in any ordered monoid where `1 ≤ 2`: the block size never exceeds
  the domain size. -/
@[grind! →]
lemma two_pow_k_le_two_pow_n
  {A : Type*} [Monoid A] [LinearOrder A] [MulLeftMono A] [OfNat A 2]
  {k d n : ℕ} [FoldingContext k d n] (h_two : (1 : A) ≤ 2) :
  (2 : A) ^ k ≤ (2 : A) ^ n := pow_le_pow_right' h_two (by grind)

/-- `2 ^ k ≤ 2 ^ d` in any ordered monoid where `1 ≤ 2`: the block size never exceeds
  the degree bound. -/
@[grind! →]
lemma two_pow_k_le_two_pow_d
  {A : Type*} [Monoid A] [LinearOrder A] [MulLeftMono A] [OfNat A 2]
  {k d n : ℕ} [FoldingContext k d n] (h_two : (1 : A) ≤ 2) :
  (2 : A) ^ k ≤ (2 : A) ^ d := pow_le_pow_right' h_two (by grind)

/-- `2 ^ d ≤ 2 ^ n` in any ordered monoid where `1 ≤ 2`: the code has rate at most one. -/
@[grind! →]
lemma two_pow_d_le_two_pow_n
  {A : Type*} [Monoid A] [LinearOrder A] [MulLeftMono A] [OfNat A 2]
  {d n : ℕ} [FoldingContextRight d n] (h_two : (1 : A) ≤ 2) :
  (2 : A) ^ d ≤ (2 : A) ^ n := pow_le_pow_right' h_two (by grind)

/-- The folded code still has rate at most one: `2 ^ (d - k) ≤ 2 ^ (n - k)`. -/
@[grind! →]
lemma two_pow_d_sub_k_le_two_pow_n_sub_k
  {A : Type*} [Monoid A] [LinearOrder A] [MulLeftMono A] [OfNat A 2]
  {k d n : ℕ} [FoldingContext k d n] (h_two : (1 : A) ≤ 2) :
  (2 : A) ^ (d - k) ≤ (2 : A) ^ (n - k) :=
  pow_le_pow_right' h_two (by grind)

/-- Truncated subtraction cancels on the left of `k`, since `1 ≤ k`. -/
@[grind =]
lemma one_add_sub_one {k d : ℕ} [FoldingContextLeft k d] :
  1 + (k - 1) = k := by
  rw [Nat.add_sub_cancel' (by grind)]

/-- Truncated subtraction cancels on the left of `k`, since `1 ≤ k`. -/
@[grind =]
lemma one_add_sub_one' {k n : ℕ} [FoldingContextMiddle k n] :
  1 + (k - 1) = k := by
  have := FoldingContextMiddle.k_ge_1
  rw [Nat.add_sub_cancel' (by omega)]

/-- Shifting both sides of `n - k` down by one is harmless: `n - 1 - (k - 1) = n - k`.
  This is the index-arithmetic counterpart of folding one step at a time. -/
@[grind =]
lemma n_sub_1_sub_k_sub_1_eq_n_sub_k {k n : ℕ} [FoldingContextMiddle k n] :
  n - 1 - (k - 1) = n - k := by
  have := FoldingContextMiddle.k_ge_1
  have := FoldingContextMiddle.k_le_n
  omega

/-- In a group, `2 ^ n / 2 ^ k = 2 ^ (n - k)`: the folded domain size is the quotient of
  the original size by the block size. -/
@[grind =]
lemma pow_2_n_sub_k_eq_n_sub_k
  {A : Type*} [Group A] [OfNat A 2]
  {k n : ℕ} [FoldingContextMiddle k n] :
  (2 : A) ^ n / (2 : A) ^ k = (2 : A) ^ (n - k) := by
  calc
    (2 : A) ^ n / (2 : A) ^ k =
      (2 : A) ^ (n - k) := by
      rw [div_eq_mul_inv]
      exact (pow_sub 2 (by grind)).symm
    _ = (2 : A) ^ (n - k) := by simp

/-- The shifted-by-one variant of `pow_2_n_sub_k_eq_n_sub_k`:
  `2 ^ (n - 1) / 2 ^ (k - 1) = 2 ^ (n - k)`. -/
@[grind =]
lemma pow_2_n_sub_1_div_pow_2_k_sub_1_eq_n_sub_k
  {A : Type*} [Group A] [OfNat A 2]
  {k d n : ℕ} [FoldingContext k d n] :
  (2 : A) ^ (n - 1) / (2 : A) ^ ((k - 1)) = (2 : A) ^ (n - k) := by
  calc
    (2 : A) ^ (n - 1) / (2 : A) ^ (k - 1) =
      (2 : A) ^ ((n - 1) - (k - 1)) := by
      rw [div_eq_mul_inv]
      exact (pow_sub 2 (by grind)).symm
    _ = (2 : A) ^ (n - k) := by grind

/-- `n - k + k` cancels, since `k ≤ n`. -/
@[grind =]
lemma n_sub_k_add_k {k n : ℕ} [FoldingContextMiddle k n] :
  n - k + k = n := by
  grind

/-- `d - k + k` cancels, since `k ≤ d`. -/
@[grind =]
lemma d_sub_k_add_k {k d : ℕ} [FoldingContextLeft k d] :
  d - k + k = d := by
  grind

/-- Reassociation of subtraction for `grind`: `(d - k) + n = (n + d) - k`. -/
@[grind _=_]
lemma d_sub_k_add_n {k d n : ℕ} [FoldingContext k d n] :
  d - k + n = n + d - k := by
  grind

/-- Reassociation of subtraction for `grind`: `(n - k) + d = (n + d) - k`. -/
@[grind _=_]
lemma n_sub_k_add_d {k d n : ℕ} [FoldingContext k d n] :
  n - k + d = n + d - k := by
  grind

/-- The folded degree bound times the block size recovers the original degree bound:
  `2 ^ (d - k) * 2 ^ k = 2 ^ d`. -/
@[grind _=_]
lemma pow_2_d_sub_k_mul_pow_2_k {A : Type*} [Monoid A] [OfNat A 2]
  {k d : ℕ} [FoldingContextLeft k d] :
  (2 : A) ^ (d - k) * (2 : A) ^ k = (2 : A) ^ d := by
  aesop (add safe [(by rw [←pow_add]), (by grind)])

/-- Commuted form of `pow_2_d_sub_k_mul_pow_2_k`: `2 ^ k * 2 ^ (d - k) = 2 ^ d`. -/
@[grind _=_]
lemma pow_2_k_mul_pow_2_d_sub_k {A : Type*} [Monoid A] [OfNat A 2]
  {k d : ℕ} [FoldingContextLeft k d] :
  (2 : A) ^ k * (2 : A) ^ (d - k) = (2 : A) ^ d := by
  aesop (add safe [(by rw [←pow_add]), (by grind)])

/-- Since `d ≤ n`, the minimum of the message-space and domain sizes is `2 ^ d`. This is
  the shape in which the rate of a Reed–Solomon code is computed. -/
@[grind =]
lemma min_pow_2_d_pow_2_n {d n : ℕ} [FoldingContextRight d n] :
  min ((2 : ℕ) ^ d) ((2 : ℕ) ^ n) = 2 ^ d := by grind

/-- Forward direction of `pow_2_k_mul_le_pow_2_d_iff`, stated with the minimal typeclass
  assumptions: bounding `x` by the folded degree bound bounds `2 ^ k * x` by `2 ^ d`. -/
@[grind! →]
lemma pow_2_k_mul_le_pow_2_d_of {A : Type*} [Monoid A] [LinearOrder A] [MulLeftMono A] [OfNat A 2]
  {k d : ℕ} [FoldingContextLeft k d] {x : A}
  (h : x ≤ (2 : A) ^ (d - k)) :
    (2 : A) ^ k * x ≤ (2 : A) ^ d := by grind [mul_le_mul_right]

/-- `2 ^ k * x ≤ 2 ^ d` exactly when `x ≤ 2 ^ (d - k)`. Used to transfer degree bounds
  between a polynomial and its `2 ^ k`-fold. -/
@[grind .]
lemma pow_2_k_mul_le_pow_2_d_iff {A : Type*} [Monoid A] [LinearOrder A] [MulLeftMono A]
  [MulLeftStrictMono A]
  [OfNat A 2] {k d : ℕ} [FoldingContextLeft k d] {x : A} :
  (2 : A) ^ k * x ≤ (2 : A) ^ d ↔
    x ≤ (2 : A) ^ (d - k) where
  mp h := by
    by_contra! contra
    have : 2 ^ d < 2 ^ k * x := by
      grind [mul_lt_mul_right]
    grind
  mpr h := by grind

end FoldingContext

end ProximityGap
