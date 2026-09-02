/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/
import Mathlib.Algebra.Polynomial.BigOperators

import ArkLib.Data.Polynomial.FoldingPolynomial

/-!
# Generalized polynomial splitting and folding

This file defines n-way splitting and folding operations on polynomials.

## Main definitions

* `Polynomial.splitNth f n i`: Splits polynomial `f` into `n` component polynomials,
  where `splitNth f n i` extracts coefficients at positions `j ≡ i (mod n)`.

* `FoldingPolynomial.polyFold f n r`: Recombines the n-way split of `f` using powers of `r`,
  computing `∑ i : Fin n, r^i * splitNth f n i` (see `polyFold_eq_sum_of_splitNth`). This is
  the core operation in FRI-style polynomial commitment schemes.

## Implementation notes

When `n = 2`, this recovers the even/odd splitting: `splitNth f 2 0` gives the even
coefficients and `splitNth f 2 1` gives the odd coefficients (after appropriate
reindexing).

-/

open Polynomial

namespace Polynomial

variable {𝔽 : Type} [CommSemiring 𝔽]

/--
Splits a polynomial into `n` component polynomials based on coefficient indices modulo `n`.

For a polynomial `f = ∑ⱼ aⱼ Xʲ` and index `i : Fin n`, returns the polynomial whose
coefficients are extracted from positions `j ≡ i (mod n)`, reindexed by `j / n`.
Formally: `splitNth f n i = ∑_{j ≡ i (mod n)} aⱼ X^(j/n)`.
-/
def splitNth (f : 𝔽[X]) (n : ℕ) (i : Fin n) : 𝔽[X] :=
  if hn : n = 0 then f else -- unreachable: `Fin 0` is uninhabited
  Polynomial.ofFinsupp
    ⟨
      Finset.filterMap (fun x ↦ if x % n = i.1 then .some (x / n) else .none)
      f.support
      (fun a a' b ↦ by
        have := Nat.div_add_mod' a n
        have := Nat.div_add_mod' a' n
        aesop),
      fun e ↦ f.coeff (e * n + i.1),
      fun a ↦ by
        simp only [Finset.mem_filterMap, mem_support_iff, ne_eq, Option.ite_none_right_eq_some,
          Option.some.injEq]
        constructor
        · rintro ⟨a', g⟩
          have : a' = a * n + i.1 := by
            have := Nat.div_add_mod' a' n
            aesop
          aesop
        · intros h
          exists (a * n + i.1)
          have {a b : ℕ} : (a * n + b) / n = a + (b / n) := by
            have := Nat.zero_lt_of_ne_zero hn
            have := Nat.mod_lt b this
            aesop (add simp [Nat.add_div])
          aesop (add simp [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt])
    ⟩

/-- Non-computable helper definition. -/
private noncomputable def splitNthNoncomputable (f : 𝔽[X]) (n : ℕ) (i : Fin n) : 𝔽[X] :=
  if n = 0 then f else
  ∑ k ∈ f.support,
    if k % n = i.1 then Polynomial.C (f.coeff k) * Polynomial.X ^ (k / n) else 0

@[simp]
private lemma splitNthNoncomputable_of_neZero {f : 𝔽[X]} {n : ℕ} [inst : NeZero n] {i : Fin n} :
  splitNthNoncomputable f n i =
    ∑ k ∈ f.support,
      if k % n = i.1 then Polynomial.C (f.coeff k) * Polynomial.X ^ (k / n) else 0 := by
  have := inst.out
  aesop (add simp splitNthNoncomputable)

/-- Coefficient formula for `splitNth`: the `e`-th coefficient of the `i`-th component
  is the coefficient of `f` at position `e * n + i`. -/
@[simp]
lemma splitNth_coeff {n : ℕ} {f : 𝔽[X]} (i : Fin n) (m : ℕ) :
    (splitNth f n i).coeff m = f.coeff (m * n + i.1) := by
  aesop
    (add unsafe [cases Fin])
    (add simp [splitNth, Polynomial.coeff_ofFinsupp])

@[simp]
private lemma splitNthNoncomputable_coeff {n : ℕ} {f : 𝔽[X]} (i : Fin n) (m : ℕ) :
    (splitNthNoncomputable f n i).coeff m = f.coeff (m * n + i.1) := by
  by_cases! hn : n ≠ 0
  · simp only [splitNthNoncomputable, hn, ↓reduceIte, finsetSum_coeff]
    have hi : i.1 < n := i.2
    have hdiv : (m * n + i.1) / n = m := by
      rw [mul_comm, Nat.mul_add_div (Nat.pos_of_ne_zero hn), Nat.div_eq_of_lt hi, Nat.add_zero]
    have hmod : (m * n + i.1) % n = i.1 := by
      rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
    have key : ∀ k ∈ f.support,
        (if k % n = i.1 then Polynomial.C (f.coeff k) * Polynomial.X ^ (k / n) else 0).coeff m
          = if k = m * n + i.1 then f.coeff k else 0 := by
      intro k hk
      have hdm : n * (k / n) + k % n = k := Nat.div_add_mod k n
      by_cases h : k % n = i.1
      · simp only [h, if_true]
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        by_cases hm : m = k / n <;> grind
      · aesop
    rw [Finset.sum_congr rfl key]
    by_cases hmem : m * n + i.1 ∈ f.support <;>
      aesop (add simp [Finset.sum_eq_single,
                       Finset.sum_eq_zero,
                       Polynomial.mem_support_iff])
  · aesop (add safe [cases Fin, (by omega)])

private lemma splitNth_eq_splitNthNoncomputable {n : ℕ} {f : 𝔽[X]} :
  splitNth f n = splitNthNoncomputable f n := by
  funext i
  ext m
  rw [splitNth_coeff, splitNthNoncomputable_coeff]

/-- The key identity `splitNth` satisfies: `f` is recovered from its `n` components. -/
lemma eq_sum_splitNth (n : ℕ) [inst : NeZero n] (f : 𝔽[X]) :
    f =
      ∑ i : Fin n,
        (Polynomial.X ^ i.1) *
          Polynomial.eval₂ Polynomial.C (Polynomial.X ^ n) (splitNth f n i) := by
  rw [splitNth_eq_splitNthNoncomputable]
  have hn : 0 < n := Nat.pos_of_ne_zero inst.out
  conv_lhs => rw [Polynomial.as_sum_support_C_mul_X_pow f]
  simp only [splitNthNoncomputable_of_neZero, eval₂_finsetSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hstep : ∀ i : Fin n, X ^ i.1 * eval₂ C (X ^ n)
      (if k % n = i.1 then C (f.coeff k) * X ^ (k / n) else 0)
      = if k % n = i.1 then C (f.coeff k) * X ^ k else (0 : 𝔽[X]) := fun i ↦ by
    have := Nat.div_add_mod k n
    have : X ^ i.1 * (C (f.coeff k) * X ^ (n * (k / n))) =
      C (f.coeff k) * X ^ (i.1 + n * (k / n)) := by ring
    aesop
      (add simp [eval₂_mul, eval₂_C, eval₂_X_pow])
      (add unsafe (by rw [← pow_mul]))
      (add safe (by omega))
  rw [Finset.sum_congr rfl (fun i _ => hstep i),
      Finset.sum_eq_single (⟨k % n, Nat.mod_lt k hn⟩ : Fin n)] <;> aesop

/-- Lemma bounding degree of each `n`-split polynomial. -/
lemma splitNth_degree_le {n : ℕ} {f : 𝔽[X]} [inst : NeZero n] {i : Fin n} :
    (splitNth f n i).natDegree ≤ f.natDegree / n := by
  have hn := inst.out
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  have hjn : j * n - 1 < j * n := Nat.sub_one_lt (by aesop)
  rw [Nat.div_lt_iff_lt_mul (by omega),
      Nat.lt_iff_le_pred (by omega),
      Polynomial.natDegree_le_iff_coeff_eq_zero] at hj
  simp only [splitNth_coeff]
  exact hj _ (by omega)

/-- `foldingPolynomial` in terms of `splitNth`
    when `q = X ^ n`. -/
@[simp low]
lemma folding_polynomial_eq_sum_splitNth {𝔽 : Type} [Field 𝔽] {f : Polynomial 𝔽}
    {n : ℕ} [inst : NeZero n] :
  FoldingPolynomial.foldingPolynomial (X ^ n) f =
    ∑ i, C (splitNth f n i) * (X ^ i.val) := by
  symm
  apply FoldingPolynomial.folding_polynomial_is_unique'
  · conv_rhs => rw [eq_sum_splitNth (f := f) (inst := inst)]
    rw [Polynomial.map_sum, Polynomial.eval_finsetSum]
    aesop
      (add simp [comp])
      (add safe (by ac_nf))
  · aesop
      (add simp [Bivariate.degreeX, splitNth_degree_le])
      (add safe natDegree_sum_le_of_forall_le)
  · simp only [Bivariate.natDegreeY, natDegree_pow, natDegree_X, mul_one]
    exact Nat.lt_of_le_pred (by aesop (add unsafe Nat.zero_lt_of_ne_zero)) <| by
      exact Polynomial.natDegree_sum_le_of_forall_le _ _ <| fun i _ ↦
        Nat.le_trans Polynomial.natDegree_mul_le <| by aesop (add safe (by omega))

/-- `polyFold` in terms of `splitNth`. -/
@[simp low]
lemma polyFold_eq_sum_of_splitNth {𝔽 : Type} [Field 𝔽]
    {f : 𝔽[X]} {n : ℕ} {r : 𝔽} [inst : NeZero n] :
  FoldingPolynomial.polyFold f n r =
    ∑ i, C (r ^ i.val) * splitNth f n i := by
  aesop
    (add simp [FoldingPolynomial.polyFold, Polynomial.eval_finsetSum])
    (add safe (by grind))

/-- `splitNth` is the left inverse of the `n`-way recombination: splitting the polynomial
  `∑ j, X^j * (u j)(X^n)` recovers `u i` for each component `i`. -/
@[simp]
lemma splitNth_of_sum_comp {n : ℕ} [inst : NeZero n] (u : Fin n → 𝔽[X]) (i : Fin n) :
    splitNth (∑ j : Fin n, X ^ (j : ℕ) * (u j).comp (X ^ n)) n i = u i := by
  have hn : 0 < n := Nat.pos_of_ne_zero inst.out
  ext e
  rw [splitNth_coeff, finsetSum_coeff, Finset.sum_eq_single i]
  · aesop (add unsafe (by rw [←expand_eq_comp_X_pow]))
  · intro j _ hj
    rw [coeff_X_pow_mul']
    by_cases hle : (j : ℕ) ≤ e * n + i
    · rw [if_pos hle, ←expand_eq_comp_X_pow, coeff_expand hn, if_neg]
      intro hdvd
      have hmod := (Nat.modEq_iff_dvd' hle).mpr hdvd
      aesop
        (add safe cases Fin)
        (add simp [Nat.ModEq, Nat.mod_eq_of_lt])
    · simp_all
  · aesop

/-- `foldingPolynomial` of an `n`-way recombination `∑ i, X^i * (u i)(X^n)` is the
    bivariate polynomial `∑ i, X^i * C (u i)`, i.e. its `Y`-coefficients are exactly the
    components `u i`. -/
@[simp high]
theorem foldingPolynomial_sum {𝔽 : Type} [Field 𝔽]
    {n : ℕ} {u : Fin n → 𝔽[X]} [inst : NeZero n] :
  FoldingPolynomial.foldingPolynomial (X ^ n)
    (∑ i, Polynomial.X ^ i.val * (u i).comp (Polynomial.X ^ n)) =
      ∑ i, Polynomial.X ^ i.val * C (u i) := by
  rw [folding_polynomial_eq_sum_splitNth]
  simp only [splitNth_of_sum_comp, mul_comm]

/-- `polyFold` of an `n`-way recombination `∑ i, X^i * (u i)(X^n)` is the
    polynomial `∑ i, r^i * u i`. -/
@[simp high]
theorem polyFold_sum {𝔽 : Type} [Field 𝔽] {r : 𝔽}
    {n : ℕ} {u : Fin n → 𝔽[X]} [inst : NeZero n] :
  FoldingPolynomial.polyFold
    (∑ i, Polynomial.X ^ i.val * (u i).comp (Polynomial.X ^ n)) n r =
      ∑ i, r ^ i.val • (u i) := by
  rw [polyFold_eq_sum_of_splitNth]
  simp only [splitNth_of_sum_comp, Polynomial.smul_eq_C_mul]

/--
Lemma bridges the coefficient-level identity `eq_sum_splitNth` and
evaluation-level reasoning about `splitNth` and `polyFold`.
-/
lemma splitNth_eval_comp_pow {n : ℕ} [NeZero n] (f : 𝔽[X]) (x : 𝔽) (i : Fin n) :
    (eval₂ C (X ^ n) (splitNth f n i)).eval x = (splitNth f n i).eval (x ^ n) := by
  rw [eval₂_eq_sum]
  unfold Polynomial.eval
  rw [Polynomial.eval₂_sum, eval₂_eq_sum]
  simp_all

end Polynomial
