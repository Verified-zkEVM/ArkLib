/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Data.Finset.Sym
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Evaluating complete homogeneous symmetric polynomials

Mathlib defines the complete homogeneous symmetric polynomial `MvPolynomial.hsymm σ R k` as a sum
over `Sym σ k`. This file evaluates it at a point `c : σ → R` as a sum over exponent vectors,
`∑ a ∈ piAntidiag univ k, ∏ i, c i ^ a i`, which is the form produced by the multinomial theorem
`Finset.sum_pow_eq_sum_piAntidiag`. It then writes the evaluations in degrees `2` and `3` in terms
of the power sums `p q = ∑ i, c i ^ q`:

* `2 * h₂ = p₁ ^ 2 + p₂`;
* `6 * h₃ = p₁ ^ 3 + 3 * p₁ * p₂ + 2 * p₃`.

These are the first cases of Newton's identities for complete homogeneous symmetric polynomials.
They are stated with the factorials multiplied out, so they hold over every commutative semiring.
Degree `1` is Mathlib's `MvPolynomial.hsymm_one`.

The proofs split off one index at a time with `Finset.piAntidiag_cons`: for `a ∉ s`, the sum over
`piAntidiag (cons a s) k` is `∑ (p, q) ∈ antidiagonal k, c a ^ p * (sum over piAntidiag s q)`.

## Main statements

* `MvPolynomial.eval_hsymm_eq_sum_piAntidiag`: the evaluation as a sum over exponent vectors.
* `MvPolynomial.two_mul_eval_hsymm_two` and `MvPolynomial.six_mul_eval_hsymm_three`: the
  power-sum forms in degrees `2` and `3`.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- The complete homogeneous symmetric polynomial of degree `k`, evaluated at `c`, is the sum of
all monomials `∏ i, c i ^ a i` with `∑ i, a i = k`. This converts Mathlib's sum over `Sym σ k`
into the exponent-vector form produced by the multinomial theorem. -/
theorem eval_hsymm_eq_sum_piAntidiag [Fintype σ] [DecidableEq σ] (c : σ → R) (k : ℕ) :
    eval c (hsymm σ R k) = ∑ a ∈ piAntidiag univ k, ∏ i, c i ^ a i := by
  rw [hsymm, map_sum, ← map_sym_eq_piAntidiag, sum_map, sym_univ]
  refine sum_congr rfl fun s _ ↦ ?_
  rw [map_multiset_prod, Multiset.map_map]
  simp only [Function.comp_apply, eval_X, Function.Embedding.coeFn_mk, Sym.val_eq_coe]
  rw [prod_multiset_map_count]
  refine prod_subset (subset_univ _) fun i _ hi ↦ ?_
  rw [Multiset.count_eq_zero_of_notMem (by simpa using hi), pow_zero]

section piAntidiag

variable {ι : Type*} [DecidableEq ι]

/-- Splitting off one index `a ∉ s`: a monomial sum over `piAntidiag (cons a s) k` is a
convolution of the powers of `c a` with the monomial sums over `piAntidiag s q`. -/
private theorem sum_piAntidiag_cons_prod_pow {a : ι} {s : Finset ι} (ha : a ∉ s) (c : ι → R)
    (k : ℕ) :
    ∑ f ∈ piAntidiag (cons a s ha) k, ∏ i ∈ cons a s ha, c i ^ f i =
      ∑ p ∈ antidiagonal k, c a ^ p.1 * ∑ f ∈ piAntidiag s p.2, ∏ i ∈ s, c i ^ f i := by
  rw [piAntidiag_cons, sum_disjiUnion]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [sum_map, mul_sum]
  refine sum_congr rfl fun f hf ↦ ?_
  have hfa : f a = 0 := by
    by_contra h
    exact ha ((mem_piAntidiag.1 hf).2 a h)
  rw [prod_cons]
  simp only [addRightEmbedding_apply, Pi.add_apply, hfa, zero_add]
  congr 1
  refine prod_congr rfl fun i hi ↦ ?_
  simp [ne_of_mem_of_not_mem hi ha]

private theorem sum_piAntidiag_zero_prod_pow (s : Finset ι) (c : ι → R) :
    ∑ f ∈ piAntidiag s 0, ∏ i ∈ s, c i ^ f i = 1 := by
  simp

private theorem sum_piAntidiag_one_prod_pow (s : Finset ι) (c : ι → R) :
    ∑ f ∈ piAntidiag s 1, ∏ i ∈ s, c i ^ f i = ∑ i ∈ s, c i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [sum_piAntidiag_cons_prod_pow ha, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [sum_range_succ, sum_range_zero, Nat.sub_self, Nat.sub_zero,
      sum_piAntidiag_zero_prod_pow, ih, sum_cons]
    ring

private theorem two_mul_sum_piAntidiag_two_prod_pow (s : Finset ι) (c : ι → R) :
    2 * ∑ f ∈ piAntidiag s 2, ∏ i ∈ s, c i ^ f i = (∑ i ∈ s, c i) ^ 2 + ∑ i ∈ s, c i ^ 2 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [sum_piAntidiag_cons_prod_pow ha, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [sum_range_succ, sum_range_zero, sum_cons]
    norm_num
    rw [sum_piAntidiag_one_prod_pow]
    set H₂ := ∑ f ∈ piAntidiag s 2, ∏ i ∈ s, c i ^ f i
    rw [show 2 * (H₂ + c a * ∑ i ∈ s, c i + c a ^ 2) =
      2 * H₂ + 2 * (c a * ∑ i ∈ s, c i) + 2 * c a ^ 2 by ring, ih]
    ring

private theorem six_mul_sum_piAntidiag_three_prod_pow (s : Finset ι) (c : ι → R) :
    6 * ∑ f ∈ piAntidiag s 3, ∏ i ∈ s, c i ^ f i =
      (∑ i ∈ s, c i) ^ 3 + 3 * (∑ i ∈ s, c i) * (∑ i ∈ s, c i ^ 2) +
        2 * ∑ i ∈ s, c i ^ 3 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [sum_piAntidiag_cons_prod_pow ha, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [sum_range_succ, sum_range_zero, sum_cons]
    norm_num
    rw [sum_piAntidiag_one_prod_pow]
    have h2 := two_mul_sum_piAntidiag_two_prod_pow s c
    set H₂ := ∑ f ∈ piAntidiag s 2, ∏ i ∈ s, c i ^ f i
    set H₃ := ∑ f ∈ piAntidiag s 3, ∏ i ∈ s, c i ^ f i
    rw [show 6 * (H₃ + c a * H₂ + c a ^ 2 * ∑ i ∈ s, c i + c a ^ 3) =
      6 * H₃ + 3 * c a * (2 * H₂) + 6 * c a ^ 2 * ∑ i ∈ s, c i + 6 * c a ^ 3 by ring, ih, h2]
    ring

end piAntidiag

variable [Fintype σ] [DecidableEq σ]

/-- Newton's identity in degree `2`: `2 * h₂(c) = (∑ i, c i) ^ 2 + ∑ i, c i ^ 2`. The factor `2`
is kept on the left so that the identity holds over every commutative semiring. -/
theorem two_mul_eval_hsymm_two (c : σ → R) :
    2 * eval c (hsymm σ R 2) = (∑ i, c i) ^ 2 + ∑ i, c i ^ 2 := by
  rw [eval_hsymm_eq_sum_piAntidiag]
  exact two_mul_sum_piAntidiag_two_prod_pow univ c

/-- Newton's identity in degree `3`:
`6 * h₃(c) = (∑ i, c i) ^ 3 + 3 * (∑ i, c i) * (∑ i, c i ^ 2) + 2 * ∑ i, c i ^ 3`. The factor `6`
is kept on the left so that the identity holds over every commutative semiring. -/
theorem six_mul_eval_hsymm_three (c : σ → R) :
    6 * eval c (hsymm σ R 3) =
      (∑ i, c i) ^ 3 + 3 * (∑ i, c i) * (∑ i, c i ^ 2) + 2 * ∑ i, c i ^ 3 := by
  rw [eval_hsymm_eq_sum_piAntidiag]
  exact six_mul_sum_piAntidiag_three_prod_pow univ c

end MvPolynomial
