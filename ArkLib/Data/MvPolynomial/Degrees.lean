/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import CompPoly.Data.MvPolynomial.Notation

/-!
  # Lemmas about degrees of multivariate polynomials

  TODO: write a `poly_degree` tactic that can prove goals involving degrees of univariate or
  multivariate polynomials

  (will need to prove by hand first before knowing how to write the tactic)
-/

noncomputable section

open Set Function Finsupp AddMonoidAlgebra

open BigOperators

variable {R : Type*} {S : Type*}

namespace MvPolynomial

variable {σ τ ι : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring

variable [CommSemiring R] {p q : MvPolynomial σ R}

/-- `C : R →+* MvPolynomial σ R` as an embedding -/
def CEmbedding : R ↪ MvPolynomial σ R := ⟨C, C_injective σ R⟩

section Support

theorem support_C {r : R} [h : Decidable (r = 0)] :
    (@C R σ _ r).support = if r = 0 then ∅ else { 0 } := by
  rw [←monomial_zero', support_monomial]

theorem support_C_subset {r : R} : (@C R σ _ r).support ⊆ { 0 } := by
  rw [←monomial_zero']
  exact support_monomial_subset

theorem support_C_mul_le (p : MvPolynomial σ R) (r : R) : (C r * p).support ⊆ p.support := by
  classical
  refine subset_trans (support_mul _ _) ?_
  rw [support_C]
  by_cases h : r = 0
  · simp [h]
  · simp [h, Finset.singleton_add, Finset.vadd_finset_def]

theorem support_mul_C_le (p : MvPolynomial σ R) (r : R) : (p * C r).support ⊆ p.support := by
  rw [mul_comm]
  exact support_C_mul_le p r

theorem support_eval [DecidableEq σ] {τ : Type*} {f : τ → R} {p : R[X σ][X τ]} :
    (eval (C ∘ f) p).support ⊆ p.support.biUnion (fun c => (coeff c p).support) := by
  classical
  rw [eval_eq]
  refine subset_trans support_sum (Finset.biUnion_mono (fun c _ => ?_))
  conv =>
    enter [1, 1, 2, 2]
    intro x
    rw [comp_apply, ←C_pow (f x)]
  rw [←map_prod]
  exact support_mul_C_le _ _

end Support

section Rename

theorem rename_ne_zero_of_injective {τ : Type*} {f : σ → τ} (hf : Function.Injective f)
    {p : MvPolynomial σ R} (h : p ≠ 0) : rename f p ≠ 0 := by
  rw [← map_zero (rename f)]
  exact fun a ↦ h (rename_injective f hf a)

theorem rename_eq_zero_of_injective {τ : Type*} {f : σ → τ} (hf : Function.Injective f)
    {p : MvPolynomial σ R} (h : rename f p = 0) : p = 0 := by
  rw [← map_zero (rename f)] at h
  exact (rename_injective f hf).eq_iff.mp h

end Rename

section Degrees

theorem degrees_C_mul_le (p : MvPolynomial σ R) (c : R) : (C c * p).degrees ≤ p.degrees := by
  refine le_trans degrees_mul_le ?_
  simp [degrees_C]

theorem degrees_mul_C_le (p : MvPolynomial σ R) (c : R) : (p * C c).degrees ≤ p.degrees := by
  rw [mul_comm]
  exact degrees_C_mul_le p c

theorem degrees_eval [DecidableEq σ] {τ : Type*} {f : τ → R} {p : R[X σ][X τ]} :
    (eval (C ∘ f) p).degrees ≤ p.support.sup (fun c => (coeff c p).degrees)  := by
  classical
  rw [eval_eq]
  refine le_trans (degrees_sum_le _ _) (Finset.sup_mono_fun (fun b _ => ?_))
  conv =>
    enter [1, 1, 2, 2]
    intro x
    rw [comp_apply, ←C_pow (f x)]
  rw [←map_prod]
  exact degrees_mul_C_le _ _

end Degrees

section DegreeOf

-- TODO we can prove equality here if R is a domain
-- theorem degreeOf_mul_eq' [IsDomain R] (i : σ) (f g : MvPolynomial σ R) :
--     degreeOf i (f * g) = degreeOf i f + degreeOf i g := by
--   classical
--   repeat' rw [degreeOf]
--   simp [degreeOf]

-- TODO in the following we have equality iff f ≠ 0
-- theorem degreeOf_mul_X_eq' (j : σ) (f : MvPolynomial σ R) (h : f ≠ 0) :
--     degreeOf j (f * X j) = degreeOf j f + 1 := by
--   classical
--   repeat' rw [degreeOf]
--   apply (Multiset.count_add j (degrees_mul f (X j))).trans
--   simp only [Multiset.count_add, add_le_add_iff_left]
--   convert Multiset.count_le_of_le j (degrees_X' (R := R) j)
--   rw [Multiset.count_singleton_self]

/-- Variant of `degreeOf_X` with no `DecidableEq` on `σ` or `Nontrivial` condition on `R` -/
theorem degreeOf_X_le (i j : σ) : degreeOf i (X (R := R) j) ≤ 1 := by
  classical
  simp only [degreeOf]
  apply le_trans (Multiset.count_le_card _ _) _
  exact Multiset.card_le_card (degrees_X' (R := R) j)

theorem degreeOf_X_of_ne (i j : σ) (h : i ≠ j) : degreeOf i (X (R := R) j) = 0 := by
  classical
  simp [degreeOf]
  intro hMem
  have hSub := degrees_X' (R := R) j
  aesop

theorem degreeOf_linear_le {a b : R} : degreeOf n (C a + C b * p) ≤ degreeOf n p := by
  apply le_trans (degreeOf_add_le _ _ _) _
  rw [max_def]
  split_ifs <;> simp [degreeOf_C_mul_le]

-- theorem degreeOf_pow_le (i : σ) (n : ℕ) (p : MvPolynomial σ R) :
--     degreeOf i (p ^ n) ≤ n * degreeOf i p := by
--   classical
--   repeat' rw [degreeOf]
--   convert Multiset.count_le_of_le i (degrees_pow p n)
--   rw [Multiset.count_nsmul]

-- theorem degreeOf_sum_le (n : σ) (s : Finset ι) (f : ι → MvPolynomial σ R) :
--     degreeOf n (∑ i in s, f i) ≤ s.sup fun i => degreeOf n (f i) := by
--   simp_rw [degreeOf_eq_sup]
--   exact supDegree_sum_le

-- theorem degreeOf_prod_le (n : σ) (s : Finset ι) (f : ι → MvPolynomial σ R) :
--     degreeOf n (∏ i in s, f i) ≤ ∑ i in s, (f i).degreeOf n := by
--   simp_rw [degreeOf_eq_sup]
--   exact supDegree_prod_le (by simp only [coe_zero, Pi.zero_apply])
--     (fun _ _ => by simp only [coe_add, Pi.add_apply])

theorem mem_restrictDegree_iff_degreeOf_le (p : MvPolynomial σ R) (n : ℕ) :
    p ∈ restrictDegree σ R n ↔ ∀ i, p.degreeOf i ≤ n := by
  classical
  apply Iff.trans (mem_restrictDegree_iff_sup σ p n)
  simp only [degreeOf]

end DegreeOf


section Equiv

variable {n : ℕ}

theorem degreeOf_eval_C_finSuccEquiv (p : MvPolynomial (Fin (n + 1)) R) (j : Fin n) (x : R) :
    degreeOf j (Polynomial.eval (C x) (finSuccEquiv R n p)) ≤ degreeOf j.succ p := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  calc
  _ ≤ ((finSuccEquiv R n) p).support.sup
        (fun i => degreeOf j (((finSuccEquiv R n) p).coeff i * C x ^ i)) := by
    apply MvPolynomial.degreeOf_sum_le
  _ ≤ ((finSuccEquiv R n) p).support.sup
        (fun i => degreeOf j (((finSuccEquiv R n) p).coeff i) + degreeOf j (C x ^ i)) := by
    gcongr
    apply MvPolynomial.degreeOf_mul_le
  _ ≤ ((finSuccEquiv R n) p).support.sup
        (fun i => degreeOf j (((finSuccEquiv R n) p).coeff i) + i * degreeOf j (C x)) := by
    gcongr
    apply MvPolynomial.degreeOf_pow_le
  _ ≤ ((finSuccEquiv R n) p).support.sup
        (fun i => degreeOf j (((finSuccEquiv R n) p).coeff i) + 0) := by
    simp only [degreeOf_C, mul_zero, add_zero, le_refl]
  _ ≤ ((finSuccEquiv R n) p).support.sup (fun i => degreeOf j.succ p + 0) := by
    gcongr
    exact degreeOf_coeff_finSuccEquiv p j _
  _ ≤ degreeOf j.succ p := Finset.sup_const_le

theorem eval_comp_eval_C_finSuccEquiv (p : R[X (Fin (n + 1))]) (y : Fin n → R) (x : R) :
    eval y (Polynomial.eval (C x) (finSuccEquiv R n p)) = eval (Fin.cons x y) p := by
  rw [eval_eq_eval_mv_eval', Polynomial.eval_map, Polynomial.eval_eq_sum]
  simp only [Polynomial.eval₂, Polynomial.sum, map_sum, map_mul, map_pow, eval_C]

end Equiv

end CommSemiring

section CommRing

variable [CommRing R]

end CommRing

section Aesop

attribute [aesop unsafe 50%] degreeOf_add_le degreeOf_mul_le degreeOf_sum_le degreeOf_prod_le
  degreeOf_X

variable [CommSemiring R]

-- theorem degreeOf_add_le' {n : σ} {d : ℕ} {f g : MvPolynomial σ R}
--     (hf : degreeOf n f ≤ d) (hg : degreeOf n g ≤ d) : degreeOf n (f + g) ≤ d :=
--   le_trans (degreeOf_add_le _ _ _) (max_le hf hg)

-- theorem degreeOf_mul_le' {n : σ} {d : ℕ} {f g : MvPolynomial σ R}
--     (h : degreeOf n f + degreeOf n g ≤ d) : degreeOf n (f * g) ≤ d :=
--   le_trans (degreeOf_mul_le _ _ _) h

-- theorem degreeOf_sum_le' {n : σ} {d : ℕ} {f : ι → MvPolynomial σ R}
--     (h : ∀ i, degreeOf n (f i) ≤ d) :
--     degreeOf n (∑ i, f i) ≤ d :=
--   le_trans (degreeOf_sum_le _ _ _) (Finset.sup_le h)

-- theorem degreeOf_prod_le' {n : σ} {d : ℕ} {f : ι → MvPolynomial σ R}
--     (h : ∀ i, degreeOf n (f i) ≤ d) :
--     degreeOf n (∏ i, f i) ≤ d :=
--   le_trans (degreeOf_prod_le _ _ _) (Finset.sum_le_sum h)

-- attribute [aesop unsafe 80%] degreeOf_add_le' degreeOf_mul_le' degreeOf_X_le add_le_add
-- degreeOf_sum_le' degreeOf_prod_le'
  -- degreeOf_X_le

-- theorem test [CommSemiring R] [Nontrivial R] :
--     degreeOf (R := R) (σ := Fin 3) 0 (X 0 * X 1) ≤ 1 := by
--   exact le_trans (le_trans (degreeOf_mul_le _ _ _)
--         (add_le_add (le_of_eq (degreeOf_X _ _)) (le_of_eq (degreeOf_X _ _)))) (by norm_num)

end Aesop

end MvPolynomial
