/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julek, Elijah Vlasov
-/
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Generalized polynomial splitting and folding

This file defines n-way splitting and folding operations on polynomials,
generalizing the 2-way even/odd splitting found in `Polynomial/EvenAndOdd.lean`.

## Main definitions

* `Polynomial.splitNth f n i`: Splits polynomial `f` into `n` component polynomials,
  where `splitNth f n i` extracts coefficients at positions `j ≡ i (mod n)`.

* `Polynomial.foldNth n f α`: Recombines the n-way split of `f` using powers of `α`,
  computing `∑ i : Fin n, α^i * splitNth f n i`. This is the core operation in
  FRI-style polynomial commitment schemes.

## Implementation notes

When `n = 2`, this recovers the even/odd splitting: `splitNth f 2 0` gives the even
coefficients and `splitNth f 2 1` gives the odd coefficients (after appropriate
reindexing). The formal connection will be established in future work.

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
  fun i =>
    let sup :=
      Finset.filterMap (fun x => if x % n = i.1 then .some (x / n) else .none)
      f.support
      (by
        intros a a' b
        simp only [Option.mem_def, Option.ite_none_right_eq_some, Option.some.injEq, and_imp]
        intros h g h' g'
        rw [Eq.symm (Nat.div_add_mod' a n), Eq.symm (Nat.div_add_mod' a' n)]
        rw [h, g, h', g'])
    Polynomial.ofFinsupp
      ⟨
        sup,
        fun e => f.coeff (e * n + i.1),
        by
          intros a
          dsimp [sup]
          simp only [Finset.mem_filterMap, mem_support_iff, ne_eq, Option.ite_none_right_eq_some,
            Option.some.injEq]
          apply Iff.intro
          · rintro ⟨a', g⟩
            have : a' = a * n + i.1 := by
              rw [Eq.symm (Nat.div_add_mod' a' n)]
              rw [g.2.1, g.2.2]
            rw [this.symm]
            exact g.1
          · intros h
            exists (a * n + i.1)
            apply And.intro h
            rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt i.2]
            apply And.intro rfl
            have {a b : ℕ} : (a * n + b) / n = a + (b / n) := by
              have := inst.out
              have ne_zero : 0 < n := by omega
              rw [Nat.add_div ne_zero, Nat.mul_mod_left, zero_add, Nat.mul_div_cancel a ne_zero]
              have : ¬ (n ≤ b % n) := by
                simp only [not_le]
                exact Nat.mod_lt b ne_zero
              simp [this]
            simp [this]
      ⟩

/- Proof of key identity `splitNth` has to satisfy. -/
omit [NoZeroDivisors 𝔽] in
lemma splitNth_def (n : ℕ) (f : 𝔽[X]) [inst : NeZero n] :
    f =
      ∑ i : Fin n,
        (Polynomial.X ^ i.1) *
          Polynomial.eval₂ Polynomial.C (Polynomial.X ^ n) (splitNth f n i) := by
  ext e
  rw [Polynomial.finset_sum_coeff]
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
      · have : e / n * n + e % n - (b / n * n + b % n) =
                ((e / n - b / n) * n) + (e % n - b % n) := by
          have : e / n * n + e % n - (b / n * n + b % n) =
                  e / n * n + e % n - b / n * n - b % n := by
            omega
          rw [this]
          have : e / n * n + e % n - b / n * n = ((e / n) - (b / n)) * n + e % n := by
            have : e / n * n + e % n - b / n * n = (e / n * n - b / n * n) + e % n :=
              Nat.sub_add_comm (Nat.mul_le_mul (Nat.div_le_div_right h₁') (by rfl))
            rw [this, ←Nat.sub_mul]
          rw [this]
          exact Nat.add_sub_assoc h' ((e / n - b / n) * n)
        rw [
          this, Nat.mul_add_mod_self_right,
          Nat.mod_eq_of_lt (Nat.sub_lt_of_lt (Nat.mod_lt _ (by linarith)))
        ] at h₂
        omega
      · simp only [ge_iff_le, not_le] at h'
        have : e / n * n + e % n - (b / n * n + b % n) =
                ((e / n - b / n - 1) * n) + (n - (b % n - e % n)) := by
          have : e / n * n + e % n - (b / n * n + b % n) =
                  e / n * n + e % n - b / n * n - b % n := by
            omega
          rw [this]
          have : e / n * n + e % n - b / n * n = ((e / n) - (b / n)) * n + e % n := by
            have : e / n * n + e % n - b / n * n = (e / n * n - b / n * n) + e % n :=
              Nat.sub_add_comm (Nat.mul_le_mul (Nat.div_le_div_right h₁') (by rfl))
            rw [this, ←Nat.sub_mul]
          rw [this]
          have : e / n - b / n = (e / n - b / n - 1) + 1 := by
            refine Eq.symm (Nat.sub_add_cancel ?_)
            rw [Nat.one_le_iff_ne_zero]
            intros h
            have h := Nat.le_of_sub_eq_zero h
            nlinarith
          rw (occs := .pos [1]) [this]
          rw
            [
              right_distrib, one_mul, add_assoc,
              Nat.add_sub_assoc (Nat.le_add_right_of_le (Nat.le_of_lt (Nat.mod_lt_of_lt h)))
            ]
          congr 1
          grind
        rw [this, Nat.mul_add_mod_self_right] at h₂
        have {a : ℕ} : (n - a) % n = 0 ∧ a < n → a = 0 := by
          intros h
          rcases exists_eq_mul_left_of_dvd (Nat.dvd_of_mod_eq_zero h.1) with ⟨c, h'⟩
          have : a = (1 - c)*n := by
            have : n = a + c * n := by omega
            have : n - c * n = a := by omega
            rw [←this]
            have : n = 1 * n := by rw [one_mul]
            rewrite (occs := .pos [1]) [this]
            exact Eq.symm (Nat.sub_mul 1 c n)
          have h' := this ▸ h.2
          rw [this]
          have : 1 - c = 0 := by
            have : n = 1 * n := by rw [one_mul]
            rw (occs := .pos [2]) [this] at h'
            have h' := Nat.lt_of_mul_lt_mul_right h'
            linarith
          simp [this]
        exfalso
        have h₂ := this ⟨h₂, by apply Nat.sub_lt_of_lt; apply Nat.mod_lt; linarith⟩
        omega
    rw [this]
    exact Eq.symm (Nat.mod_eq_of_lt h)
  · intros h
    simp at h

/- Lemma bounding degree of each `n`-split polynomial. -/
omit [NoZeroDivisors 𝔽] in
lemma splitNth_degree_le {n : ℕ} {f : 𝔽[X]} [inst : NeZero n] :
    ∀ {i}, (splitNth f n i).natDegree ≤ f.natDegree / n := by
    intros i
    unfold splitNth Polynomial.natDegree Polynomial.degree
    simp only [support_ofFinsupp]
    rw [WithBot.unbotD_le_iff (by simp)]
    simp only [Finset.max_le_iff, Finset.mem_filterMap, mem_support_iff, ne_eq,
      Option.ite_none_right_eq_some, Option.some.injEq, WithBot.coe_le_coe, forall_exists_index,
      and_imp]
    intros _ _ h _ h'
    rw [←h']
    refine Nat.div_le_div ?_ (Nat.le_refl n) inst.out
    exact le_natDegree_of_ne_zero h

/--
Generalized n-way folding of a polynomial.

Given a polynomial `f`, splits it into `n` component polynomials via `splitNth`,
then recombines them with powers of `α` as coefficients:
`foldNth n f α = ∑ i : Fin n, α^i * splitNth f n i`.

This operation is central to FRI-style polynomial folding, where a polynomial
over a domain of size `M` is reduced to a polynomial over a domain of size `M/n`.
-/
noncomputable def foldNth (n : ℕ) (f : 𝔽[X]) (α : 𝔽) [inst : NeZero n] : 𝔽[X] :=
  ∑ i : Fin n, Polynomial.C α ^ i.1 * splitNth f n i

private lemma fold_max_lemma {ι : Type} {s : Finset ι} {f : ι → ℕ} {n : ℕ} :
    (∀ i ∈ s, f i ≤ n) → Finset.fold max 0 f s ≤ n := by
  intros h
  apply Nat.le_of_lt_succ
  rw [Finset.fold_max_lt]
  apply And.intro (Nat.zero_lt_succ n)
  intros x h'
  exact Nat.lt_add_one_of_le (h x h')

/- Lemma bounding degree of folded polynomial. -/
omit [NoZeroDivisors 𝔽] in
lemma foldNth_degree_le {n : ℕ} {f : 𝔽[X]} {α : 𝔽} [inst : NeZero n] :
    (foldNth n f α).natDegree ≤ f.natDegree / n := by
  unfold foldNth
  by_cases h : α = 0
  · have : ∑ i, C α ^ i.1 * splitNth f n i = splitNth f n 0 := by
      rw [h]
      simp only [map_zero]
      have : splitNth f n 0 = (0 ^ ((0 : Fin n) : ℕ)) * splitNth f n 0 := by
        simp
      rw [this]
      apply Finset.sum_eq_single (ι := Fin n) 0
      · intros b _ h
        simp [h]
      · simp
    rw [this]
    exact splitNth_degree_le
  · transitivity
    · exact Polynomial.natDegree_sum_le _ _
    · rw [Function.comp_def]
      apply fold_max_lemma
      intros i _
      transitivity
      · exact Polynomial.natDegree_mul_le
      · rw [←Polynomial.C_pow, Polynomial.natDegree_C, zero_add]
        exact splitNth_degree_le

/- Lemma bounding degree of folded polynomial. -/
omit [NoZeroDivisors 𝔽] in
lemma foldNth_degree_le' {n : ℕ} {f : 𝔽[X]} {α : 𝔽} [inst : NeZero n] :
    n * (foldNth n f α).natDegree ≤ f.natDegree := by
  rw [mul_comm]
  apply (Nat.le_div_iff_mul_le (Nat.zero_lt_of_ne_zero inst.out)).mp
  exact foldNth_degree_le

omit [NoZeroDivisors 𝔽] in
lemma foldNth_zero {s : ℕ} {α : 𝔽} : foldNth (2 ^ s) 0 α = 0 := by
  unfold foldNth splitNth
  have :
    { toFinsupp := { support := ∅, toFun := fun e ↦ 0, mem_support_toFun := (by simp) } } =
      (0 : 𝔽[X]) := by rfl
  simp [this]

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
  congr
  ext e a
  rw [← eval]
  simp

end Polynomial
