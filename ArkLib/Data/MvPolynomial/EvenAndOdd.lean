/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.CharP.Basic

import CompPoly.Data.MvPolynomial.Notation
import ArkLib.Data.MvPolynomial.Interpolation
import ArkLib.Data.MvPolynomial.LinearMvExtension

namespace MvPolynomial

open BigOperators Fintype Finset

variable {R : Type} [Field R]
variable {n : ℕ} [NeZero n]
variable {p : MvPolynomial (Fin n) R}

private noncomputable def substPlus (p : MvPolynomial (Fin n) R) :
    MvPolynomial (Fin n) R :=
  p.aeval (fun i ↦ if i = 0 then 1 else (MvPolynomial.X i : MvPolynomial (Fin n) R))

private noncomputable def substMinus (p : MvPolynomial (Fin n) R) :
    MvPolynomial (Fin n) R :=
  p.aeval (fun i ↦ if i = 0 then -1 else MvPolynomial.X i)

private lemma substPlus_mem_restrictDegree
  (hp : p ∈ restrictDegree (Fin n) R 1) :
  substPlus p ∈ restrictDegree (Fin n) R 1 := by
  have h_support : ∀ m ∈ p.support, ∀ i, m i ≤ 1 := by
    rwa [mem_restrictDegree] at hp
  unfold substPlus
  have h_monomial : ∀ m ∈ p.support,
    (MvPolynomial.monomial m (p.coeff m)).aeval
      (fun i ↦ if i = 0 then 1 else (MvPolynomial.X i : MvPolynomial (Fin n) R)) ∈
        restrictDegree (Fin n) R 1 := by
    intro m hm
    have h_monomial :
      (MvPolynomial.monomial m (p.coeff m)).aeval (fun i ↦
        if i = 0 then 1 else (MvPolynomial.X i : MvPolynomial (Fin n) R)) =
          MvPolynomial.monomial (m.erase 0) (p.coeff m) := by
      simp [MvPolynomial.monomial_eq, Finset.prod_ite, Finset.filter_ne', Finsupp.erase]
    rw [mem_restrictDegree]
    intro s hs i
    by_cases hi : i = 0 <;> aesop
  rw [MvPolynomial.as_sum p]
  convert Submodule.sum_mem _ h_monomial using 1
  rw [map_sum]

private lemma substMinus_mem_restrictDegree
  (hp : p ∈ restrictDegree (Fin n) R 1) :
  substMinus p ∈ restrictDegree (Fin n) R 1 := by
  have := substPlus_mem_restrictDegree hp
  unfold substPlus substMinus at *
  have h_subst :
    ∀ i : Fin n,
      (MvPolynomial.degreeOf i
        (MvPolynomial.bind₁ (fun i ↦ if i = 0 then -1 else X i) p)) ≤ 1 := by
    intro i
    have h_subst : ∀ m ∈ p.support,
      (MvPolynomial.degreeOf i
        (MvPolynomial.bind₁
          (fun i ↦ if i = 0 then -1 else X i) (MvPolynomial.monomial m (p.coeff m)))) ≤ 1 := by
      intro m hm
      have h_deg : ∀ i, m i ≤ 1 := by aesop
      simp_all only [aeval_eq_bind₁, mem_support_iff, ne_eq, bind₁_monomial, ite_pow,
        ge_iff_le]
      apply le_trans (MvPolynomial.degreeOf_mul_le _ _ _) _
      simp_all only [degreeOf_C, zero_add]
      apply le_trans (MvPolynomial.degreeOf_prod_le _ _ _) _
      rw [Finset.sum_eq_add_sum_diff_singleton i _ (by aesop)]
      rw [Finset.sum_equiv
            (t := m.support \ {i})
            (Equiv.refl _)
            (by simp)
            (g := fun x ↦ 0)
            (fun j hj ↦ by
              split_ifs with hjeq0
              · have : m 0 = 1 := by grind
                aesop
              · have : i ≠ j := by aesop
                exact Nat.eq_zero_of_le_zero <|
                  le_trans (MvPolynomial.degreeOf_pow_le _ _ _) <| by
                  simp [MvPolynomial.degreeOf_X, this])]
      split_ifs
      · by_cases hm0 : m 0 = 0
        · aesop
        · have : m 0 = 1 := by grind
          aesop
      · simp only [sum_const_zero, add_zero]
        apply le_trans (MvPolynomial.degreeOf_pow_le _ _ _)
        simp [MvPolynomial.degreeOf, h_deg]
    rw [MvPolynomial.as_sum p, map_sum]
    exact le_trans
      (MvPolynomial.degreeOf_sum_le _ _ _)
      (Finset.sup_le fun m hm => h_subst m hm)
  aesop
    (add simp [MvPolynomial.degreeOf_eq_sup, mem_restrictDegree, mem_support_iff])

omit [NeZero n] in
private lemma mul_C_mem_restrictDegree
  (hp : p ∈ restrictDegree (Fin n) R 1)
  (c : R) : p * C c ∈ restrictDegree (Fin n) R 1 := by
  convert Submodule.smul_mem _ c hp using 1
  rw [mul_comm, MvPolynomial.C_mul']

private lemma even_mem (p : R⦃≤ 1⦄[X (Fin n)]) :
  (substPlus p.1 + substMinus p.1) * C (2⁻¹) ∈ restrictDegree (Fin n) R 1 :=
  mul_C_mem_restrictDegree ((restrictDegree (Fin n) R 1).add_mem
    (substPlus_mem_restrictDegree p.2) (substMinus_mem_restrictDegree p.2)) _

private lemma odd_mem (p : R⦃≤ 1⦄[X (Fin n)]) :
  (substPlus p.1 - substMinus p.1) * C (2⁻¹) ∈ restrictDegree (Fin n) R 1 :=
  mul_C_mem_restrictDegree ((restrictDegree (Fin n) R 1).sub_mem
    (substPlus_mem_restrictDegree p.2) (substMinus_mem_restrictDegree p.2)) _

noncomputable def even (p : R⦃≤ 1⦄[X (Fin n)]) :
  R⦃≤ 1⦄[X (Fin n)] :=
    ⟨(substPlus p.1 + substMinus p.1) * C (2⁻¹), even_mem p⟩

noncomputable def odd (p : R⦃≤ 1⦄[X (Fin n)]) :
  R⦃≤ 1⦄[X (Fin n)] :=
    ⟨(substPlus p.1 - substMinus p.1) * C (2⁻¹), odd_mem p⟩

private lemma formula_for_monomial
  (h2ne0 : (2 : R) ≠ 0)
  (m : Fin n →₀ ℕ) (c : R) (hm : ∀ i, m i ≤ 1) :
  (substPlus (monomial m c) + substMinus (monomial m c)) * C (2⁻¹) +
  X 0 * ((substPlus (monomial m c) - substMinus (monomial m c)) * C (2⁻¹)) = monomial m c := by
  by_cases h0 : m 0 = 0
  · have h_subst :
      substPlus (MvPolynomial.monomial m c) =
        MvPolynomial.monomial m c ∧
          substMinus (MvPolynomial.monomial m c) = MvPolynomial.monomial m c := by
      simp [substPlus, substMinus, MvPolynomial.bind₁_monomial]
      simp [MvPolynomial.monomial_eq, Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', h0]
    simp only [h_subst, sub_self, zero_mul, mul_zero, add_zero]
    rw [←two_smul R, smul_mul_assoc, ←MvPolynomial.C_mul']
    ring_nf
    rw [mul_right_comm, ←MvPolynomial.C_mul, mul_inv_cancel₀ h2ne0, MvPolynomial.C_1, one_mul]
  · have h_monomial : monomial m c = C c * X 0 * ∏ i ∈ m.support \ {0}, X i ^ (m i) := by
      rw [MvPolynomial.monomial_eq]
      simp only [Finsupp.prod, prod_X_pow_eq_monomial, mul_assoc, mul_eq_mul_left_iff, map_eq_zero]
      have hsup : 0 ∈ m.support := by simp [h0]
      have : (X 0 : R[X (Fin n)]) = X 0 ^ (m 0) := by simp [show m 0 = 1 by grind]
      rw [this,
          ←Finset.prod_eq_mul_prod_diff_singleton (s := m.support) 0
            (f := fun i ↦ X i ^ m i) (by aesop)]
      aesop
    aesop
      (add simp [
        substPlus, substMinus,
        Finset.prod_ite, Finset.filter_ne', Finset.filter_eq',
        mul_assoc, inv_mul_cancel₀])
      (add unsafe [(by ring_nf), (by erw [←map_mul])])

private lemma formula_generic
  (h2ne0 : (2 : R) ≠ 0)
  (p : MvPolynomial (Fin n) R) (hp : p ∈ restrictDegree (Fin n) R 1) :
  (substPlus p + substMinus p) * C (2⁻¹) +
  X 0 * ((substPlus p - substMinus p) * C (2⁻¹)) = p := by
  have h_expand :
    ∀ m ∈ p.support,
      (substPlus (monomial m (p.coeff m)) +
        substMinus (monomial m (p.coeff m))) * C (2⁻¹) +
          X 0 * ((substPlus (monomial m (p.coeff m)) -
          substMinus (monomial m (p.coeff m))) * C (2⁻¹)) = monomial m (p.coeff m) :=
   by aesop
        (add unsafe [formula_for_monomial])
        (add simp [mem_restrictDegree])
  rw [MvPolynomial.as_sum p]
  convert Finset.sum_congr rfl h_expand using 1
  simp only [substPlus, aeval_eq_bind₁, support_sum_monomial_coeff, substMinus, mul_comm, mul_add,
    sum_add_distrib]
  conv_lhs => rw [MvPolynomial.as_sum p]
  simp only [map_sum]
  simp [mul_sub, Finset.mul_sum]

lemma even_and_odd_formula
  (hchar : ¬CharP R 2)
  {p : R⦃≤ 1⦄[X (Fin n)]} :
  (even p).1 + (MvPolynomial.X 0) * (odd p).1 = p.1 := formula_generic
    (by aesop (add simp [CharP.charP_iff_prime_eq_zero, Nat.prime_two])) p.1 p.2

private noncomputable def shiftDown (q : MvPolynomial (Fin n) R) : MvPolynomial (Fin (n - 1)) R :=
  q.aeval (fun i ↦ if h : i = (0 : Fin n) then 0 else X ⟨i.val - 1, by omega⟩)

private lemma shiftDown_shiftUp_eq (q : MvPolynomial (Fin n) R) :
  (shiftDown q).aeval
    (fun i : Fin (n - 1) ↦ (X (⟨i.val + 1, by omega⟩ : Fin n) : MvPolynomial (Fin n) R)) =
    q.aeval (fun i ↦ if h : i = (0 : Fin n) then 0 else X i) := by
  unfold MvPolynomial.shiftDown
  grind +suggestions

private lemma substNoX0_eq_self_of_even
  (p : restrictDegree (Fin n) R 1) :
  (even p).1.aeval
    (fun i : Fin n ↦
      if _ : i = (0 : Fin n) then (0 : MvPolynomial (Fin n) R) else X i) = (even p).1 := by
  unfold even
  simp only [aeval_eq_bind₁, substPlus, substMinus, map_mul, map_add, algHom_C, algebraMap_eq,
    mul_eq_mul_right_iff, map_eq_zero, inv_eq_zero]
  left
  congr! 1
  all_goals induction p.val using MvPolynomial.induction_on <;> aesop

private lemma substNoX0_eq_self_of_odd
  (p : restrictDegree (Fin n) R 1) :
  (odd p).1.aeval
    (fun i : Fin n ↦
      if _ : i = (0 : Fin n) then (0 : MvPolynomial (Fin n) R) else X i) = (odd p).1 := by
  unfold odd
  unfold MvPolynomial.substPlus MvPolynomial.substMinus
  simp only [aeval_eq_bind₁, sub_mul, map_sub, map_mul, algHom_C, algebraMap_eq]
  congr! 2
  all_goals induction p.val using MvPolynomial.induction_on <;> aesop

-- For the case m 0 ≠ 0: the product contains a zero factor
private lemma aeval_shift_monomial_zero_case {n : ℕ} [NeZero n]
  (m : Fin n →₀ ℕ) (c : R) (hm : ∀ i, m i ≤ 1) (h0 : m 0 ≠ 0) :
  (monomial m c).aeval (fun i : Fin n ↦ if h : i = (0 : Fin n)
    then (0 : MvPolynomial (Fin (n - 1)) R)
    else X ⟨i.val - 1, by omega⟩) = 0 := by
  change bind₁ _ (monomial m c) = 0
  rw [bind₁_monomial]
  have h01 : m 0 = 1 := Nat.le_antisymm (hm 0) (Nat.pos_of_ne_zero h0)
  have h0s : (0 : Fin n) ∈ m.support := by simp [Finsupp.mem_support_iff, h0]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero h0s
  simp [h01]

/-
For the case m 0 = 0: the result is a shifted monomial
-/
private lemma aeval_shift_monomial_nonzero_case
  (m : Fin n →₀ ℕ) (c : R) (hm : ∀ i, m i ≤ 1) (h0 : m 0 = 0) :
  (monomial m c).aeval (fun i : Fin n ↦ if h : i = (0 : Fin n)
      then (0 : MvPolynomial (Fin (n - 1)) R)
      else X ⟨i.val - 1, by omega⟩) ∈ restrictDegree (Fin (n - 1)) R 1 := by
  rw [MvPolynomial.mem_restrictDegree]
  intro s hs i
  contrapose! hs
  simp_all only [aeval_eq_bind₁, monomial_eq, Finsupp.prod_pow, map_mul, algHom_C, algebraMap_eq,
    map_prod, map_pow, bind₁_X_right, dite_pow, pow_zero, mem_support_iff, coeff_C_mul, ne_eq,
    mul_eq_zero, not_or, not_and, not_not]
  have h_coeff :
    coeff s (∏ x : Fin n,
      if h : x = 0
      then 1
      else (MvPolynomial.X ⟨↑x - 1, by omega⟩ : MvPolynomial (Fin (n - 1)) R) ^ m x) = 0 := by
    have h_coeff :
      ∀ (t : Fin n → ℕ),
        (∏ x : Fin n,
          if h : x = 0
          then 1
          else (MvPolynomial.X ⟨↑x - 1, by omega⟩ : MvPolynomial (Fin (n - 1)) R) ^ t x) =
            MvPolynomial.monomial
              (∑ x : Fin n, if h : x = 0 then 0 else Finsupp.single ⟨↑x - 1, by omega⟩ (t x)) 1 :=
      by
      intro t
      induction (Finset.univ : Finset (Fin n)) using Finset.induction
        <;> aesop
              (add simp [Finset.prod_insert, MvPolynomial.monomial_mul,
                          MvPolynomial.X_pow_eq_monomial])
    simp_all only [coeff_monomial, ite_eq_right_iff, one_ne_zero, imp_false, ne_eq]
    intro h
    replace h := congr_arg (fun f ↦ f i) h
    simp_all only [sum_apply']
    rw
      [Finset.sum_eq_single ⟨i + 1, by grind⟩] at h
      <;> aesop (add safe (by grind))
  exact fun _ => h_coeff

lemma aeval_shift_monomial_mem {n : ℕ} [NeZero n]
    (m : Fin n →₀ ℕ) (c : R) (hm : ∀ i, m i ≤ 1) :
    (monomial m c).aeval (fun i : Fin n ↦ if h : i = (0 : Fin n)
      then (0 : MvPolynomial (Fin (n - 1)) R)
      else X ⟨i.val - 1, by omega⟩) ∈ restrictDegree (Fin (n - 1)) R 1 := by
  by_cases h0 : m 0 = 0
  · exact aeval_shift_monomial_nonzero_case m c hm h0
  · rw [aeval_shift_monomial_zero_case m c hm h0]; exact zero_mem _

lemma aeval_shift_mem_restrictDegree
  (q : MvPolynomial (Fin n) R) (hq : q ∈ restrictDegree (Fin n) R 1) :
  q.aeval (fun i ↦ if h : i = (0 : Fin n) then (0 : MvPolynomial (Fin (n - 1)) R)
    else X ⟨i.val - 1, by omega⟩) ∈ restrictDegree (Fin (n - 1)) R 1 := by
  rw [MvPolynomial.as_sum q, map_sum]
  apply Submodule.sum_mem
  intro m hm
  exact aeval_shift_monomial_mem m (q.coeff m) (fun i => (mem_restrictDegree _ q 1).mp hq m hm i)

noncomputable def even_pred (p : R⦃≤ 1⦄[X (Fin n)]) : R⦃≤ 1⦄[X (Fin (n - 1))] :=
  ⟨(even p).1.aeval
    (fun i ↦ if h : i = 0 then 0 else X (σ := Fin (n - 1)) ⟨i.val - 1, by omega⟩),
      by exact aeval_shift_mem_restrictDegree (even p).1 (even p).2
  ⟩

noncomputable def odd_pred (p : R⦃≤ 1⦄[X (Fin n)]) : R⦃≤ 1⦄[X (Fin (n - 1))] :=
  ⟨(odd p).1.aeval
    (fun i ↦ if h : i = 0 then 0 else X (σ := Fin (n - 1)) ⟨i.val - 1, by omega⟩),
      by exact aeval_shift_mem_restrictDegree (odd p).1 (odd p).2⟩

lemma even_and_odd_formula'
  (hchar : ¬CharP R 2)
  {p : R⦃≤ 1⦄[X (Fin n)]} :
  (even_pred p).1.aeval
    (fun i ↦ X (⟨i.val + 1, by omega⟩ : Fin n)) +
      (MvPolynomial.X 0) * (odd_pred p).1.aeval
        (fun i ↦ X (⟨i.val + 1, by omega⟩ : Fin n)) = p.1 := by
  change
    (shiftDown (even p).1).aeval _ + X 0 * (shiftDown (odd p).1).aeval _ = p.1
  rw [shiftDown_shiftUp_eq, shiftDown_shiftUp_eq]
  rw [substNoX0_eq_self_of_even, substNoX0_eq_self_of_odd]
  exact even_and_odd_formula hchar

lemma even_and_odd_eval
  (hchar : ¬CharP R 2)
  {p : R⦃≤ 1⦄[X (Fin n)]}
  {α : R} :
  p.1.aeval
    (fun i ↦ if h : i = 0 then C α else (X ⟨i.val - 1, by omega⟩ :  R[X (Fin (n - 1))])) =
    (even_pred p).1 + C α * (odd_pred p).1 := by
  conv_lhs => rw [←even_and_odd_formula' hchar]
  aesop
    (add safe [(by erw [MvPolynomial.aeval_bind₁])])

noncomputable def shiftedPowAlgHom :
    MvPolynomial (Fin (n - 1)) R →ₐ[R] Polynomial R :=
  MvPolynomial.aeval fun j : Fin (n - 1) => Polynomial.X ^ (2 ^ (j.val + 1))

omit [NeZero n] in
open LinearMvExtension in
lemma shiftedPowAlgHom_eq_powAlgHom_comp_sq_x
  {p : MvPolynomial (Fin (n - 1)) R} :
  shiftedPowAlgHom p = (powAlgHom p).comp (Polynomial.X ^ 2) := by
  induction p using MvPolynomial.induction_on
    <;> aesop
      (add simp [shiftedPowAlgHom, powAlgHom])
      (add unsafe (by ring_nf))

omit [NeZero n] in
open LinearMvExtension in
private lemma powAlgHom_aeval_shift (q : MvPolynomial (Fin (n - 1)) R) :
  powAlgHom (q.aeval (fun i : Fin (n - 1) ↦
    (X (⟨i.val + 1, by omega⟩ : Fin n) : MvPolynomial (Fin n) R))) =
  shiftedPowAlgHom q := by
  induction q using MvPolynomial.induction_on
    <;> aesop (add simp [powAlgHom, shiftedPowAlgHom])

open LinearMvExtension in
lemma powAlgHom_eq_even_add_odd
  (hchar : ¬CharP R 2)
  {p : R⦃≤ 1⦄[X (Fin n)]} :
  powAlgHom p.1 =
    shiftedPowAlgHom (even_pred p).1 +
    Polynomial.X * shiftedPowAlgHom (odd_pred p).1 := by
  conv_lhs => rw [←even_and_odd_formula' hchar]
  aesop
    (erase aeval_eq_bind₁)
    (add simp [powAlgHom_aeval_shift, powAlgHom_aeval_shift])
    (add unsafe (by rw [powAlgHom]))

open LinearMvExtension in
lemma powAlgHom_eq_even_add_odd_powAlgHom
  (hchar : ¬CharP R 2)
  {p : R⦃≤ 1⦄[X (Fin n)]} :
  powAlgHom p.1 =
    (powAlgHom (even_pred p).1).comp (Polynomial.X ^ 2) +
    Polynomial.X * (powAlgHom (odd_pred p).1).comp (Polynomial.X ^ 2) := by
  conv_lhs => rw [powAlgHom_eq_even_add_odd hchar]
  simp [shiftedPowAlgHom_eq_powAlgHom_comp_sq_x]

end MvPolynomial
