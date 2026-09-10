/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Clearing a common-power denominator in multivariate substitution

This construction is a literal finite polynomial sum. If the source monomials use at most
`H` powers of a common denominator, it represents that denominator to power `H` times
the rational substitution. It is used for the rational Taylor numerator recurrence.
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

open scoped BigOperators

variable {F R E τ : Type*} [CommSemiring F] [CommRing R] [Field E]

/-- Clear a common-power denominator monomial by monomial in a polynomial substitution. -/
def clearedSubstitution (f : F →+* R) (S : R) (N : τ → R) (d : τ → ℕ)
    (H : ℕ) (Q : MvPolynomial τ F) : R :=
  ∑ m ∈ Q.support, f (coeff m Q) *
    (∏ i ∈ m.support, N i ^ m i) * S ^ (H - Finsupp.weight d m)

/-- Mapping a cleared substitution needs no invertibility or denominator-budget hypothesis. -/
theorem ringHom_clearedSubstitution {T : Type*} [CommRing T]
    (f : F →+* R) (φ : R →+* T) (S : R) (N : τ → R) (d : τ → ℕ)
    (H : ℕ) (Q : MvPolynomial τ F) :
    φ (clearedSubstitution f S N d H Q) =
      clearedSubstitution (φ.comp f) (φ S) (fun i ↦ φ (N i)) d H Q := by
  classical
  simp [clearedSubstitution]

/-- Coefficient specialization commutes with clearing denominators, including when
specialization removes monomials from the support. -/
theorem clearedSubstitution_map {A : Type*} [CommSemiring A]
    (f : F →+* A) (g : A →+* R) (S : R) (N : τ → R) (d : τ → ℕ)
    (H : ℕ) (Q : MvPolynomial τ F) :
    clearedSubstitution g S N d H (map f Q) =
      clearedSubstitution (g.comp f) S N d H Q := by
  classical
  unfold clearedSubstitution
  simp only [coeff_map, RingHom.comp_apply]
  apply Finset.sum_subset (support_map_subset f Q)
  intro m _ hm
  have hzero : f (coeff m Q) = 0 := by
    simpa only [notMem_support_iff, coeff_map] using hm
  simp [hzero]

/-- The explicit cleared polynomial represents the rational substitution when all monomials
fit within the chosen denominator budget. -/
theorem map_clearedSubstitution (f : F →+* R) (φ : R →+* E) (S : R)
    (hS : φ S ≠ 0) (N : τ → R) (d : τ → ℕ) (H : ℕ) (Q : MvPolynomial τ F)
    (hQ : ∀ m ∈ Q.support, Finsupp.weight d m ≤ H) :
    φ (clearedSubstitution f S N d H Q) =
      φ S ^ H * eval₂ (φ.comp f) (fun i ↦ φ (N i) / φ S ^ d i) Q := by
  classical
  rw [clearedSubstitution, map_sum, eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [map_mul, map_prod, map_pow, RingHom.comp_apply, div_pow, ← pow_mul]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  have hweight : (∑ i ∈ m.support, d i * m i) = Finsupp.weight d m := by
    simp [Finsupp.weight_apply, Finsupp.sum, Nat.mul_comm]
  rw [hweight]
  have he : φ S ^ (H - Finsupp.weight d m) * φ S ^ Finsupp.weight d m = φ S ^ H := by
    rw [← pow_add, Nat.sub_add_cancel (hQ m hm)]
  rw [← mul_div_assoc, ← mul_div_assoc]
  apply (eq_div_iff (pow_ne_zero _ hS)).mpr
  rw [mul_assoc, he]
  ring

/-- Degree control for the explicit common-denominator numerator. -/
theorem totalDegree_clearedSubstitution {K σ : Type*} [CommRing K]
    (S : MvPolynomial σ K) (N : τ → MvPolynomial σ K) (d : τ → ℕ)
    (H b v : ℕ) (Q : MvPolynomial τ K)
    (hS : S.totalDegree ≤ b) (hN : ∀ i, (N i).totalDegree ≤ d i * b + 1)
    (hQ : ∀ m ∈ Q.support, Finsupp.weight d m ≤ H)
    (hv : Q.totalDegree ≤ v) :
    (clearedSubstitution C S N d H Q).totalDegree ≤ H * b + v := by
  classical
  apply totalDegree_finsetSum_le
  intro m hm
  have hprod : (∏ i ∈ m.support, N i ^ m i).totalDegree ≤
      Finsupp.weight d m * b + m.sum (fun _ e ↦ e) := by
    apply (totalDegree_finsetProd _ _).trans
    calc
      _ ≤ ∑ i ∈ m.support, m i * (d i * b + 1) := by
        apply Finset.sum_le_sum
        intro i _
        exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hN i))
      _ = Finsupp.weight d m * b + m.sum (fun _ e ↦ e) := by
        simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hpow := (totalDegree_pow S (H - Finsupp.weight d m)).trans
    (Nat.mul_le_mul_left _ hS)
  have hmon := (le_totalDegree hm).trans hv
  have hbudget := Nat.sub_add_cancel (hQ m hm)
  have hmul := totalDegree_mul
    (C (coeff m Q) * ∏ i ∈ m.support, N i ^ m i)
    (S ^ (H - Finsupp.weight d m))
  have hcoeff := totalDegree_mul (C (coeff m Q)) (∏ i ∈ m.support, N i ^ m i)
  rw [totalDegree_C, zero_add] at hcoeff
  nlinarith

end

end MvPolynomial
