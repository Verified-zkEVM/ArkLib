/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov
-/
import Mathlib.Algebra.Polynomial.BigOperators

import ArkLib.Data.Polynomial.FoldingPolynomial

/-!
# Generalized polynomial splitting and folding

This file defines n-way splitting and folding operations on polynomials.

## Main definitions

* `Polynomial.splitNth f n i`: Splits polynomial `f` into `n` component polynomials,
  where `splitNth f n i` extracts coefficients at positions `j ≡ i (mod n)`.

* `Polynomial.foldNth n f α`: Recombines the n-way split of `f` using powers of `α`,
  computing `∑ i : Fin n, α^i * splitNth f n i`. This is the core operation in
  FRI-style polynomial commitment schemes.

## Implementation notes

When `n = 2`, this recovers the even/odd splitting: `splitNth f 2 0` gives the even
coefficients and `splitNth f 2 1` gives the odd coefficients (after appropriate
reindexing).

-/

open Polynomial

namespace Polynomial

variable {𝔽 : Type} [CommSemiring 𝔽] [NoZeroDivisors 𝔽]

/--
Splits a polynomial into `n` component polynomials based on coefficient indices modulo `n`.

For a polynomial `f = ∑ⱼ aⱼ Xʲ` and index `i : Fin n`, returns the polynomial whose
coefficients are extracted from positions `j ≡ i (mod n)`, reindexed by `j / n`.
Formally: `splitNth f n i = ∑_{j ≡ i (mod n)} aⱼ X^(j/n)`.
-/
def splitNth (f : 𝔽[X]) (n : ℕ) [inst : NeZero n] : Fin n → 𝔽[X] :=
  fun i ↦
    let sup :=
      Finset.filterMap (fun x ↦ if x % n = i.1 then .some (x / n) else .none)
      f.support
      (fun a a' b ↦ by
        have := Nat.div_add_mod' a n
        have := Nat.div_add_mod' a' n
        aesop)
    Polynomial.ofFinsupp
      ⟨
        sup,
        fun e ↦ f.coeff (e * n + i.1),
        fun a ↦ by
          simp only [Finset.mem_filterMap, mem_support_iff, ne_eq, Option.ite_none_right_eq_some,
            Option.some.injEq, sup]
          constructor
          · rintro ⟨a', g⟩
            have : a' = a * n + i.1 := by
              have := Nat.div_add_mod' a' n
              aesop
            aesop
          · intros h
            exists (a * n + i.1)
            have {a b : ℕ} : (a * n + b) / n = a + (b / n) := by
              have := Nat.zero_lt_of_ne_zero inst.out
              have := Nat.mod_lt b this
              aesop (add simp [Nat.add_div])
            aesop (add simp [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt])
      ⟩

/- Proof of key identity `splitNth` has to satisfy. -/
omit [NoZeroDivisors 𝔽] in
lemma splitNth_def (n : ℕ) (f : 𝔽[X]) [inst : NeZero n] :
    f =
      ∑ i : Fin n,
        (Polynomial.X ^ i.1) *
          Polynomial.eval₂ Polynomial.C (Polynomial.X ^ n) (splitNth f n i) := by
  ext e
  rw [Polynomial.finsetSum_coeff]
  have h₀ {b e : ℕ} {f : 𝔽[X]} : (X ^ b * f).coeff e = if e < b then 0 else f.coeff (e - b) := by
    rw [Polynomial.coeff_X_pow_mul' f b e]
    aesop
  have h₁ {e : ℕ} {f : 𝔽[X]}  :
    (eval₂ C (X ^ n) f).coeff e =
      if e % n = 0
      then f.coeff (e / n)
      else 0 := by
    rw [Polynomial.eval₂_def, Polynomial.coeff_sum, Polynomial.sum_def]
    conv =>
      lhs
      congr
      · skip
      ext n
      rw [←pow_mul, Polynomial.coeff_C_mul_X_pow]
    by_cases h : e % n = 0 <;> simp only [h, ↓reduceIte]
    · rw [Finset.sum_eq_single (e / n)]
      · have : e = n * (e / n) :=
          Nat.eq_mul_of_div_eq_right
            (Nat.dvd_of_mod_eq_zero h) rfl
        rw [if_pos]
        exact this
      · intros b h₀ h₁
        have : ¬ (e = n * b) := by
          intros h'
          apply h₁
          rw [h']
          exact Nat.eq_div_of_mul_eq_right inst.out rfl
        simp [this]
      · intros h'
        split_ifs with h''
        · exact notMem_support_iff.mp h'
        · rfl
    · have {α : Type} {a b : α} : ∀ m, (if e = n * m then a else b) = b := by aesop
      conv =>
        lhs
        congr
        · skip
        ext m
        rw [this m]
      rw [Finset.sum_const_zero]
  conv =>
    rhs
    congr
    · skip
    · ext b
      rw [h₀, h₁]
  unfold splitNth
  simp only [coeff_ofFinsupp, Finsupp.coe_mk]
  rw [Finset.sum_eq_single ⟨e % n, by refine Nat.mod_lt e (by have := inst.out; omega)⟩]
  · simp only
    have h₁ : ¬ (e < e % n) := by
      by_cases h : e < n
      · rw [Nat.mod_eq_of_lt h]
        simp
      · simp only [not_lt] at h ⊢
        exact Nat.mod_le e n
    have h₂ : (e - e % n) % n = 0 := Nat.sub_mod_eq_zero_of_mod_eq (by simp)
    simp only [h₁, h₂, Eq.symm Nat.div_eq_sub_mod_div, Nat.div_add_mod' e n, ↓reduceIte]
  · rintro ⟨b, h⟩ _
    simp only [ne_eq, Fin.mk.injEq, ite_eq_left_iff, not_lt, ite_eq_right_iff]
    intros h₀ h₁ h₂
    exfalso
    apply h₀
    have : e % n = b % n := by
      have h₁' := h₁
      rw [←Nat.div_add_mod' e n, ←Nat.div_add_mod' b n] at h₁ h₂
      by_cases h' : e % n ≥ b % n
      · have eq1 : e / n * n + e % n - (b / n * n + b % n) =
                   e / n * n + e % n - b / n * n - b % n := by omega
        rw [eq1] at h₁ h₂
        have eq2 : e / n * n + e % n - b / n * n = ((e / n) - (b / n)) * n + e % n := by
          have : e / n * n + e % n - b / n * n = (e / n * n - b / n * n) + e % n :=
            Nat.sub_add_comm (Nat.mul_le_mul (Nat.div_le_div_right h₁') (by rfl))
          rw [this, ←Nat.sub_mul]
        rw [eq2] at h₂
        have eq3 : ((e / n) - (b / n)) * n + e % n - b % n = ((e / n - b / n) * n) + (e % n - b % n) :=
          Nat.add_sub_assoc h' ((e / n - b / n) * n)
        rw [eq3] at h₂
        rw [Nat.mul_add_mod_self_right] at h₂
        rw [Nat.mod_eq_of_lt (Nat.sub_lt_of_lt (Nat.mod_lt _ (by linarith)))] at h₂
        omega
      · simp only [ge_iff_le, not_le] at h'
        have eq1 : e / n * n + e % n - (b / n * n + b % n) =
                   e / n * n + e % n - b / n * n - b % n := by omega
        rw [eq1] at h₁ h₂
        have eq2 : e / n * n + e % n - b / n * n = ((e / n) - (b / n)) * n + e % n := by
          have : e / n * n + e % n - b / n * n = (e / n * n - b / n * n) + e % n :=
            Nat.sub_add_comm (Nat.mul_le_mul (Nat.div_le_div_right h₁') (by rfl))
          rw [this, ←Nat.sub_mul]
        rw [eq2] at h₂
        have step1 : e / n - b / n = (e / n - b / n - 1) + 1 := by
          refine Eq.symm (Nat.sub_add_cancel ?_)
          rw [Nat.one_le_iff_ne_zero]
          intros hz
          have : e / n ≤ b / n := Nat.le_of_sub_eq_zero hz
          nlinarith
        rw (occs := .pos [1]) [step1] at eq2
        rw [right_distrib, one_mul, add_assoc] at eq2
        have : ((e / n - b / n - 1) + 1) * n = (e / n - b / n - 1) * n + n := by ring
        rw [this] at eq2
        have step2 : (e / n - b / n - 1) * n + n + e % n - b % n =
                     ((e / n - b / n - 1) * n) + (n - (b % n - e % n)) := by
          have : n + e % n = e % n + n := by ring
          have : n + e % n - b % n = (n - (b % n - e % n)) + e % n := by
            have bmod_le : b % n ≤ n := Nat.mod_lt b (by linarith)
            omega
          omega
        rw [step2] at h₂
        rw [Nat.mul_add_mod_self_right] at h₂
        have {a : ℕ} : (n - a) % n = 0 ∧ a < n → a = 0 := by
          intros ⟨hmod, hlt⟩
          rcases exists_eq_mul_left_of_dvd (Nat.dvd_of_mod_eq_zero hmod) with ⟨c, hc⟩
          have : a = (1 - c)*n := by omega
          have : (1 - c) * n < n := this ▸ hlt
          omega
        exact this ⟨h₂, by apply Nat.sub_lt_of_lt; apply Nat.mod_lt; linarith⟩
    rw [this]
    exact Eq.symm (Nat.mod_eq_of_lt h)
  · intros h
    simp at h

/- Lemma bounding degree of each `n`-split polynomial. -/
omit [NoZeroDivisors 𝔽] in
lemma splitNth_degree_le {n : ℕ} {f : 𝔽[X]} [inst : NeZero n] {i : Fin n} :
  (splitNth f n i).natDegree ≤ f.natDegree / n := by
  have hn := inst.out
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  have hjn : j * n - 1 < j * n := Nat.sub_one_lt (by aesop)
  rw [Nat.div_lt_iff_lt_mul (by omega),
      Nat.lt_iff_le_pred (by omega),
      Polynomial.natDegree_le_iff_coeff_eq_zero] at hj
  exact hj _ (by omega)

/-- `foldingPolynomial` in terms of `splitNth`
    when `q = X ^ n`. -/
@[simp low]
lemma folding_polynomial_eq_sum_splitNth {𝔽 : Type} [Field 𝔽]
  {f : Polynomial 𝔽} {n : ℕ}
  [inst : NeZero n] :
  FoldingPolynomial.foldingPolynomial (X ^ n) f =
    ∑ i, C (splitNth f n i) * (X ^ i.val) := by
  symm
  apply FoldingPolynomial.folding_polynomial_is_unique'
  · conv =>
      rhs
      rw [splitNth_def (f := f) (inst := inst)]
    rw [
      Polynomial.map_sum,
      Polynomial.eval_finsetSum]
    simp only [Polynomial.map_mul, map_C, coe_compRingHom, Polynomial.map_pow, map_X,
    eval_mul, eval_C, eval_pow, eval_X]
    simp only [comp]
    conv =>
      lhs
      rhs
      ext x
      rw [mul_comm]
      rfl
  · simp only [Bivariate.degreeX, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one,
    mul_zero, natDegree_pow, natDegree_X]
    simp only [Finset.sup_le_iff, mem_support_iff, finsetSum_coeff, coeff_C_mul, coeff_X_pow,
    mul_ite, mul_one, mul_zero, ne_eq]
    intro b hb
    apply natDegree_sum_le_of_forall_le
    rintro ⟨i, hi⟩ _
    by_cases heq: b = i
    · simp only [heq, ↓reduceIte]
      exact splitNth_degree_le
    · simp [heq]
  · simp only [Bivariate.natDegreeY, natDegree_pow, natDegree_X, mul_one]
    apply Nat.lt_of_le_pred (by {
      apply Nat.zero_lt_of_ne_zero
      aesop
    })
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    apply Nat.le_trans Polynomial.natDegree_mul_le
    rcases i with ⟨i, hi⟩
    simp
    omega

/-- `polyFold` in terms of `splitNth`. -/
@[simp low]
lemma polyFold_eq_sum_of_splitNth {𝔽 : Type} [Field 𝔽]
  {f : 𝔽[X]} {n : ℕ} {r : 𝔽}
  [inst : NeZero n] :
  FoldingPolynomial.polyFold f n r =
    ∑ i, C (r ^ i.val) * splitNth f n i := by
  aesop
    (add simp [FoldingPolynomial.polyFold, Polynomial.eval_finsetSum])
    (add safe (by grind))

omit [NoZeroDivisors 𝔽] in
/-- Coefficient formula for `splitNth`: the `e`-th coefficient of the `i`-th component
  is the coefficient of `f` at position `e * n + i`. -/
@[simp]
lemma splitNth_coeff {n : ℕ} [NeZero n] {g : 𝔽[X]} {i : Fin n} {e : ℕ} :
  (splitNth g n i).coeff e = g.coeff (e * n + i.1) := by simp [splitNth]

omit [NoZeroDivisors 𝔽] in
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
      ∑ i, Polynomial.X ^ i.val * C (u i) := by simp_all

/-- `polyFold` of an `n`-way recombination `∑ i, X^i * (u i)(X^n)` is the
    polynomial `∑ i, r^i * u i`. -/
@[simp high]
theorem polyFold_sum {𝔽 : Type} [Field 𝔽] {r : 𝔽}
  {n : ℕ} {u : Fin n → 𝔽[X]} [inst : NeZero n] :
  FoldingPolynomial.polyFold
    (∑ i, Polynomial.X ^ i.val * (u i).comp (Polynomial.X ^ n)) n r =
      ∑ i, r ^ i.val • (u i) := by
  aesop
    (add simp [FoldingPolynomial.polyFold,
               Polynomial.eval_finsetSum,
               Polynomial.smul_eq_C_mul])
    (add safe (by grind))

omit [NoZeroDivisors 𝔽] in
/--
Lemma bridges the coefficient-level identity `splitNth_def` and
evaluation-level reasoning about `splitNth` and `foldNth`.
-/
lemma splitNth_eval_comp_pow {n : ℕ} [NeZero n] (f : 𝔽[X]) (x : 𝔽) (i : Fin n) :
    (eval₂ C (X ^ n) (splitNth f n i)).eval x = (splitNth f n i).eval (x ^ n) := by
  rw [eval₂_eq_sum]
  unfold Polynomial.eval
  rw [Polynomial.eval₂_sum, eval₂_eq_sum]
  simp_all

/-!
# Evaluation-level lemmas for `splitNth` and `foldNth`

This section adds evaluation-level lemmas to complement the existing coefficient-level
definitions in this file.

**Context**: These lemmas arise naturally when verifying Plonky3's FRI folding
operation. The existing file defines `splitNth` with coefficient-level identities
(`splitNth_def`) and degree bounds (`splitNth_degree_le`), but provides no evaluation-level
results.

The lemmas below fill that gap. Together they prove that `foldNth 2 f β` evaluated at `x²`
equals the standard FRI fold of `f(x)` and `f(-x)`.

Addresses: https://github.com/Verified-zkEVM/ArkLib/issues/450
-/

variable {𝔽 : Type*} [Field 𝔽]

/-- Helper lemma: `splitNth` of monomial at even position -/
lemma splitNth_monomial_even (a : 𝔽) (k : ℕ) :
    splitNth (monomial (2 * k) a) 2 0 = monomial k a := by
  ext j; simp [splitNth_def, coeff_monomial]; omega

/-- Helper lemma: `splitNth` of monomial at odd position -/
lemma splitNth_monomial_odd (a : 𝔽) (k : ℕ) :
    splitNth (monomial (2 * k + 1) a) 2 1 = monomial k a := by
  ext j; simp [splitNth_def, coeff_monomial]; omega

/-- Definition: `foldNth n f β` is the linear combination of the n-way splits.

For a polynomial `f` split into `n` component polynomials `splitNth f n 0, ..., splitNth f n (n-1)`,
this recombines them using powers of `β`:
`foldNth n f β = ∑ i : Fin n, β ^ i * splitNth f n i`

This is the core operation in FRI-style polynomial commitment schemes. -/
def foldNth (n : ℕ) (f : 𝔽[X]) (β : 𝔽) [NeZero n] : 𝔽[X] :=
  ∑ i : Fin n, β ^ i.val * splitNth f n i

lemma foldNth_eq_sum_splitNth {n : ℕ} [NeZero n] (f : 𝔽[X]) (β : 𝔽) :
    foldNth n f β = ∑ i : Fin n, β ^ i.val * splitNth f n i := rfl

/-- Lemma 2: Even evaluation identity

For any polynomial `f` and field element `x`,
`f(x) + f(-x) = 2 * (even part of f)(x²)`

where the "even part" is `splitNth f 2 0` — the sub-polynomial collecting all
coefficients of `f` at even-degree positions. -/
lemma splitNth_two_eval_add (f : 𝔽[X]) (x : 𝔽) :
    f.eval x + f.eval (-x) = 2 * (splitNth f 2 0).eval (x ^ 2) := by
  induction f using Polynomial.induction_on' with
  | h_add p q hp hq =>
    simp [eval_add, hp, hq]
    ring
  | h_monomial n a =>
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- even case: n = 2k
      subst hk
      simp [splitNth_monomial_even, eval_monomial]
      ring_nf
      simp [neg_pow, even_two_mul]
      ring
    · -- odd case: n = 2k + 1
      subst hk
      simp [splitNth_monomial_odd, eval_monomial]
      ring_nf
      simp [neg_pow, Nat.odd_add, odd_two_mul_add_one]
      ring

/-- Lemma 3: Odd evaluation identity

For any polynomial `f` and field element `x`,
`f(x) - f(-x) = 2 * x * (odd part of f)(x²)`

where the "odd part" is `splitNth f 2 1` — collecting coefficients at odd positions. -/
lemma splitNth_two_eval_sub (f : 𝔽[X]) (x : 𝔽) :
    f.eval x - f.eval (-x) = 2 * x * (splitNth f 2 1).eval (x ^ 2) := by
  induction f using Polynomial.induction_on' with
  | h_add p q hp hq =>
    simp [eval_add, hp, hq]
    ring
  | h_monomial n a =>
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- even case: contributes 0 to the odd part
      subst hk
      simp [splitNth_monomial_even, eval_monomial]
      ring_nf
      simp [neg_pow, even_two_mul]
      ring
    · -- odd case: n = 2k+1
      subst hk
      simp [splitNth_monomial_odd, eval_monomial]
      ring_nf
      simp [neg_pow, odd_two_mul_add_one]
      ring

/-- Lemma 4: FRI folding evaluation

The main result: `foldNth 2 f β` evaluated at `x²` equals the standard
FRI fold formula in terms of `f(x)` and `f(-x)`. -/
lemma foldNth_two_eval (f : 𝔽[X]) (x β : 𝔽)
    (hx : x ≠ 0) (h2 : (2 : 𝔽) ≠ 0) :
    (foldNth 2 f β).eval (x ^ 2) =
    (f.eval x + f.eval (-x) +
      β * (f.eval x - f.eval (-x)) * x⁻¹) * (2 : 𝔽)⁻¹ := by
  rw [foldNth_eq_sum_splitNth]
  simp only [Fin.sum_univ_two, eval_add, eval_mul, eval_pow, eval_X]
  rw [← splitNth_two_eval_add, ← splitNth_two_eval_sub]
  field_simp
  ring

end Polynomial
