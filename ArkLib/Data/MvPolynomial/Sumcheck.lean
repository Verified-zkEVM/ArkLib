/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Monad

/-!
  # Auxiliary functions for sum-check over multivariate polynomials
-/

noncomputable section

open BigOperators Finset Fintype Finsupp Function

/-- Equivalence that splits `Fin (m + n)` to `Fin m` and `Fin n`, then swaps the two -/
def Fin.sumCommEquiv (m : ℕ) (n : ℕ) : Fin (m + n) ≃ (Fin n) ⊕ (Fin m) :=
  (@finSumFinEquiv m n).symm.trans (Equiv.sumComm (Fin m) (Fin n))

namespace MvPolynomial

variable {R : Type*} [CommSemiring R] {σ : Type*} {m n : ℕ}

-- /-- Evaluate the first variable of a multivariate polynomial -/
-- def evalFirstVar (p : MvPolynomial (Fin n) R) (r : R) (pos : n > 0) :
--     MvPolynomial (Fin (n - 1)) R := by
--   have : n = n - 1 + 1 := by omega
--   rw [this] at p
--   exact (finSuccEquiv R (n - 1) p).eval (C r)


open scoped Polynomial

section PartialEval

variable {σ σ₁ σ₂ : Type*}

/-- Partial evaluation of multivariate polynomials given a mapping to a sum type `σ → σ₁ ⊕ σ₂`
and a partial evaluation point `x : σ₁ → R` -/
def peval (f : σ → σ₁ ⊕ σ₂) (x : σ₁ → R) : MvPolynomial σ R →+* MvPolynomial σ₂ R :=
  eval₂Hom C (Sum.elim (fun i => C (x i)) X ∘ f)

theorem peval_def (f : σ → σ₁ ⊕ σ₂) (x : σ₁ → R) (p : MvPolynomial σ R) :
    peval f x p = eval₂ C (Sum.elim (fun i => C (x i)) X ∘ f) p := rfl

theorem peval_eq_eval_sumToIter_rename (f : σ → σ₁ ⊕ σ₂) (x : σ₁ → R) (p : MvPolynomial σ R) :
    peval f x p = eval (C ∘ x) (sumToIter R σ₁ σ₂ (rename f p)) := by
  induction p using MvPolynomial.induction_on with
  | C => simp [peval]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s hp =>
      simp [hp]
      congr
      simp only [peval, eval₂Hom_X', comp_apply, sumToIter]
      by_cases h : Sum.isLeft (f s)
      · have : f s = Sum.inl ((f s).getLeft h) := by simp only [Sum.inl_getLeft]
        rw [this, Sum.elim_inl]
        simp only [comp_apply, eval_X]
      · have h' : Sum.isRight (f s) = true := by exact Sum.not_isLeft.mp h
        have : f s = Sum.inr ((f s).getRight h') := by simp only [Sum.inr_getRight]
        rw [this, Sum.elim_inr]
        simp only [comp_apply, eval_C]

theorem degrees_peval {x : σ₁ → R} {f : σ → σ₁ ⊕ σ₂} {p : MvPolynomial σ R} :
    (peval f x p).degrees ≤ (p.degrees.map f).filterMap Sum.getRight? := by
  classical
  rw [peval_eq_eval_sumToIter_rename]
  refine le_trans (degrees_eval) ?_
  simp only [Finset.sup_le_iff, mem_support_iff, ne_eq]
  intro b h
  sorry

end PartialEval

/-- A `R`-linear mapping that sends

  `p(X_0,\dots,X_{m-1},X_m,\dots,X_{m+n-1})` to

  `\sum_{x_m ∈ D 0, ..., x_{m+n-1} ∈ D (n-1)} p(X_0,\dots,X_{m-1},x_m,\dots,x_{m+n-1})`
-/
def sumPartial (m : ℕ) (n : ℕ) (D : Fin n → Finset R) :
    MvPolynomial (Fin (m + n)) R →ₗ[R] MvPolynomial (Fin m) R where
  toFun := fun p => ∑ x ∈ Fintype.piFinset D, peval (Fin.sumCommEquiv m n) x p
  map_add' := fun p q => by simp only [map_add, sum_add_distrib]
  map_smul' := fun r p => by simp [peval, smul_eq_C_mul, Finset.mul_sum]

/-- Special case of `sumPartialFinset` when `m = 0`. Directly returns `R` -/
def sumAll (n : ℕ) (D : Fin n → Finset R) : MvPolynomial (Fin n) R →ₗ[R] R := by
  rw [← Nat.zero_add n]
  exact (isEmptyAlgEquiv R (Fin 0)).toLinearMap.comp (sumPartial 0 n D)

/-- Special case of `sumPartialFinset` when `m = 1`. Directly returns `R[X]` -/
def sumExceptFirst (n : ℕ) (D : Fin n → Finset R) :
    MvPolynomial (Fin (n + 1)) R →ₗ[R] Polynomial R := by
  rw [Nat.add_comm n 1]
  exact (finOneEquiv R).toLinearMap.comp (sumPartial 1 n D)

/-- Variant of `sumFinsetExceptFirst` where we replace `n` with `n - 1` -/
def sumExceptFirst' (n : ℕ) (h : n > 0) (D : Fin (n - 1) → Finset R) :
    MvPolynomial (Fin n) R →ₗ[R] Polynomial R := by
  have : n - 1 + 1 = n := @Nat.sub_add_cancel n 1 (gt_iff_lt.mp h)
  exact this ▸ sumExceptFirst (n - 1) D

@[simp]
theorem sumExceptFirst'_degree_le (n : ℕ) (h : n > 0) (D : Fin (n - 1) → Finset R)
    (p : MvPolynomial (Fin n) R) : (sumExceptFirst' n h D p).degree ≤ p.degreeOf ⟨0, h⟩ := by
  sorry

-- @[simp]
-- theorem sum_of_sumExceptFirst'_eval_eq_sumAll (n : ℕ+) (D : Finset R)
    -- (p : MvPolynomial (Fin n) R) (i : ℕ) :
    -- (sumExceptFirst' n D p).coeff i = p.coeff (Fin.castSucc i) := by
--   sorry

end MvPolynomial

end
