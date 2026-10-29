/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Finsupp.Weight

/-!
# Joint degree bounds for multivariate polynomials over a polynomial ring

A multivariate polynomial `P` with coefficients in `R[X]` has two kinds of degree: the degree of
each coefficient in the coefficient variable, and the weight of each monomial for a weight
`w : σ → ℕ` on the multivariate variables. This file bounds their sum: `P` lies in
`restrictJointDegree w B` when every nonzero coefficient `P.coeff e` satisfies
`(P.coeff e).natDegree + e.weight w ≤ B`.

This joint bound is preserved by products and by substitutions whose generator images satisfy
the corresponding bounds. For the zero weight it is a plain bound on the degrees of the
coefficients. For a positive weight it also records that monomials of large weight have
coefficients of small degree, and that monomials of weight above `B` do not occur.

## Main statements

* `mem_restrictJointDegree`: membership is the coefficientwise joint bound.
* `mul_mem_restrictJointDegree`, `pow_mem_restrictJointDegree`, `prod_mem_restrictJointDegree`:
  joint bounds add under products.
* `bind₁_mem_restrictJointDegree`: substitution preserves joint bounds when the image of each
  variable is bounded by the weight of that variable.
* `natDegree_coeff_le_of_mem_restrictJointDegree` and
  `coeff_eq_zero_of_mem_restrictJointDegree`: the coefficient-degree and vanishing consequences.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

/-- The polynomials over `R[X]` in which every monomial `e` with coefficient `p` satisfies
`p.natDegree + e.weight w ≤ B`, stated coefficientwise: every nonzero coefficient of `X^n` in
`p` has `n + e.weight w ≤ B`. -/
def restrictJointDegree (w : σ → ℕ) (B : ℕ) : Submodule R (MvPolynomial σ R[X]) where
  carrier := {P | ∀ e n, (P.coeff e).coeff n ≠ 0 → n + e.weight w ≤ B}
  add_mem' {P Q} hP hQ e n hne := by
    rw [show (P + Q).coeff e = P.coeff e + Q.coeff e by simp, Polynomial.coeff_add] at hne
    by_cases hp : (P.coeff e).coeff n = 0
    · exact hQ e n (by simpa [hp] using hne)
    · exact hP e n hp
  zero_mem' e n hne := by simp at hne
  smul_mem' r P hP e n hne := by
    rw [MvPolynomial.coeff_smul, Polynomial.coeff_smul, smul_eq_mul] at hne
    exact hP e n (right_ne_zero_of_mul hne)

/-- Membership in `restrictJointDegree w B`, coefficientwise: every nonzero coefficient of `X^n`
in `P.coeff e` has `n + e.weight w ≤ B`. -/
theorem mem_restrictJointDegree_iff_coeff {w : σ → ℕ} {B : ℕ} {P : MvPolynomial σ R[X]} :
    P ∈ restrictJointDegree (R := R) w B ↔
      ∀ e n, (P.coeff e).coeff n ≠ 0 → n + e.weight w ≤ B :=
  Iff.rfl

/-- Membership in `restrictJointDegree w B`: every nonzero coefficient `P.coeff e` has
`(P.coeff e).natDegree + e.weight w ≤ B`. -/
theorem mem_restrictJointDegree {w : σ → ℕ} {B : ℕ} {P : MvPolynomial σ R[X]} :
    P ∈ restrictJointDegree (R := R) w B ↔
      ∀ e, P.coeff e ≠ 0 → (P.coeff e).natDegree + e.weight w ≤ B := by
  rw [mem_restrictJointDegree_iff_coeff]
  constructor
  · intro hP e he
    exact hP e _ (Polynomial.leadingCoeff_ne_zero.mpr he)
  · intro hP e n hne
    have he : P.coeff e ≠ 0 := fun h => hne (by simp [h])
    exact (Nat.add_le_add_right (Polynomial.le_natDegree_of_ne_zero hne) _).trans (hP e he)

/-- Relaxing the bound enlarges the submodule. -/
theorem restrictJointDegree_mono (w : σ → ℕ) {A B : ℕ} (hAB : A ≤ B) :
    restrictJointDegree (R := R) w A ≤ restrictJointDegree (R := R) w B :=
  fun _ hP => mem_restrictJointDegree_iff_coeff.mpr fun e n hne =>
    (mem_restrictJointDegree_iff_coeff.mp hP e n hne).trans hAB

/-- A member of `restrictJointDegree w B` has coefficient degree at most `B - e.weight w` at every
monomial `e`. -/
theorem natDegree_coeff_le_of_mem_restrictJointDegree {w : σ → ℕ} {B : ℕ}
    {P : MvPolynomial σ R[X]} (hP : P ∈ restrictJointDegree (R := R) w B) (e : σ →₀ ℕ) :
    (P.coeff e).natDegree ≤ B - e.weight w := by
  by_cases he : P.coeff e = 0
  · simp [he]
  · exact Nat.le_sub_of_add_le (mem_restrictJointDegree.mp hP e he)

/-- A member of `restrictJointDegree w B` has no monomial of weight above `B`. -/
theorem coeff_eq_zero_of_mem_restrictJointDegree {w : σ → ℕ} {B : ℕ}
    {P : MvPolynomial σ R[X]} (hP : P ∈ restrictJointDegree (R := R) w B) {e : σ →₀ ℕ}
    (he : B < e.weight w) : P.coeff e = 0 := by
  by_contra hne
  have := mem_restrictJointDegree.mp hP e hne
  omega

/-- For the zero weight the joint bound is a bound on the degree of every coefficient. -/
theorem mem_restrictJointDegree_zero_iff {B : ℕ} {P : MvPolynomial σ R[X]} :
    P ∈ restrictJointDegree (R := R) (0 : σ → ℕ) B ↔ ∀ e, (P.coeff e).natDegree ≤ B := by
  have hw : ∀ e : σ →₀ ℕ, e.weight (0 : σ → ℕ) = 0 := fun e => by
    simp [Finsupp.weight_apply]
  simp only [mem_restrictJointDegree, hw, add_zero]
  constructor
  · intro h e
    by_cases he : P.coeff e = 0
    · simp [he]
    · exact h e he
  · exact fun h e _ => h e

/-- A monomial `monomial e p` satisfies the joint bound when
`p.natDegree + e.weight w ≤ B`. -/
theorem monomial_mem_restrictJointDegree {w : σ → ℕ} {B : ℕ} (e : σ →₀ ℕ) {p : R[X]}
    (hp : p.natDegree + e.weight w ≤ B) :
    monomial e p ∈ restrictJointDegree (R := R) w B := by
  classical
  rw [mem_restrictJointDegree]
  intro e' he'
  rw [coeff_monomial] at he' ⊢
  split_ifs at he' ⊢ with h
  · exact h ▸ hp
  · exact absurd rfl he'

/-- A constant `C p` satisfies every bound at least `p.natDegree`. -/
theorem C_mem_restrictJointDegree (w : σ → ℕ) {B : ℕ} {p : R[X]} (hp : p.natDegree ≤ B) :
    C p ∈ restrictJointDegree (R := R) w B := by
  rw [← monomial_zero']
  exact monomial_mem_restrictJointDegree 0 (by simpa using hp)

/-- The variable `X i` satisfies every bound at least `w i`. -/
theorem X_mem_restrictJointDegree (w : σ → ℕ) {B : ℕ} (i : σ) (hi : w i ≤ B) :
    X i ∈ restrictJointDegree (R := R) w B :=
  monomial_mem_restrictJointDegree _ (by simpa [Finsupp.weight_single] using hi)

/-- Joint bounds add under multiplication. -/
theorem mul_mem_restrictJointDegree {w : σ → ℕ} {A B : ℕ} {P Q : MvPolynomial σ R[X]}
    (hP : P ∈ restrictJointDegree (R := R) w A) (hQ : Q ∈ restrictJointDegree (R := R) w B) :
    P * Q ∈ restrictJointDegree (R := R) w (A + B) := by
  classical
  rw [mem_restrictJointDegree_iff_coeff] at hP hQ ⊢
  intro e n hne
  rw [coeff_mul, Polynomial.finsetSum_coeff] at hne
  obtain ⟨x, hx, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [Polynomial.coeff_mul] at hxne
  obtain ⟨y, hy, hyne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hxne
  rw [Finset.mem_antidiagonal] at hx hy
  have h₁ := hP x.1 y.1 (left_ne_zero_of_mul hyne)
  have h₂ := hQ x.2 y.2 (right_ne_zero_of_mul hyne)
  rw [← hx, ← hy, map_add]
  omega

/-- The `n`th power of a polynomial with joint bound `B` has joint bound `n * B`. -/
theorem pow_mem_restrictJointDegree {w : σ → ℕ} {B : ℕ} {P : MvPolynomial σ R[X]}
    (hP : P ∈ restrictJointDegree (R := R) w B) (n : ℕ) :
    P ^ n ∈ restrictJointDegree (R := R) w (n * B) := by
  induction n with
  | zero =>
      rw [pow_zero, zero_mul, ← C_1]
      exact C_mem_restrictJointDegree w (by simp)
  | succ n ih =>
      rw [pow_succ, Nat.succ_mul]
      exact mul_mem_restrictJointDegree ih hP

/-- A finite product satisfies the sum of the factors' joint bounds. -/
theorem prod_mem_restrictJointDegree {ι : Type*} {w : σ → ℕ} (s : Finset ι) {B : ι → ℕ}
    {P : ι → MvPolynomial σ R[X]} (hP : ∀ i ∈ s, P i ∈ restrictJointDegree (R := R) w (B i)) :
    ∏ i ∈ s, P i ∈ restrictJointDegree (R := R) w (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, ← C_1]
      exact C_mem_restrictJointDegree w (by simp)
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact mul_mem_restrictJointDegree (hP i (Finset.mem_insert_self i s))
        (ih fun j hj => hP j (Finset.mem_insert_of_mem hj))

/-- Substitution preserves joint bounds: if the image of each variable `i` has joint bound `w i`
for the weight `v`, then a polynomial with joint bound `B` for `w` is sent to a polynomial with
joint bound `B` for `v`. -/
theorem bind₁_mem_restrictJointDegree {w : σ → ℕ} {v : τ → ℕ} {B : ℕ}
    {f : σ → MvPolynomial τ R[X]} {P : MvPolynomial σ R[X]}
    (hf : ∀ i, f i ∈ restrictJointDegree (R := R) v (w i))
    (hP : P ∈ restrictJointDegree (R := R) w B) :
    bind₁ f P ∈ restrictJointDegree (R := R) v B := by
  classical
  rw [P.as_sum, map_sum]
  refine Submodule.sum_mem _ fun e he => ?_
  have he' : P.coeff e ≠ 0 := mem_support_iff.mp he
  rw [bind₁_monomial]
  have hprod := prod_mem_restrictJointDegree (R := R) (w := v) e.support
    (B := fun i => e i * w i) (P := fun i => f i ^ e i)
    fun i _ => pow_mem_restrictJointDegree (hf i) (e i)
  have hweight : ∑ i ∈ e.support, e i * w i = e.weight w := by
    simp [Finsupp.weight_apply, Finsupp.sum]
  rw [hweight] at hprod
  exact restrictJointDegree_mono v (mem_restrictJointDegree.mp hP e he')
    (mul_mem_restrictJointDegree (C_mem_restrictJointDegree v le_rfl) hprod)

end MvPolynomial
