/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import CompPoly.Multivariate.Operations
public import Mathlib.Algebra.MvPolynomial.Equiv
/-!
# Coefficients in the first computable multivariate variable

The first variable of a `CMvPolynomial (n + 1) R` can be viewed as the outer variable of a
univariate polynomial whose coefficients are `CMvPolynomial n R`. This file implements extraction
of one such coefficient without crossing through the noncomputable representation equivalence.
-/

@[expose] public section

namespace CPoly.CMvPolynomial

variable {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- Remove the first coordinate from a computable monomial. -/
def tailMonomial {n : ℕ} (monomial : CMvMonomial (n + 1)) : CMvMonomial n :=
  Vector.ofFn fun i => monomial.get i.succ

@[simp]
theorem toFinsupp_tailMonomial {n : ℕ} (monomial : CMvMonomial (n + 1)) :
    (tailMonomial monomial).toFinsupp = monomial.toFinsupp.tail := by
  ext i
  simp [Finsupp.tail_apply, tailMonomial, CMvMonomial.toFinsupp]

/-- Extract the coefficient of `X 0 ^ exponent`, retaining variables `X 1, ..., X n`. -/
def headCoefficient {n : ℕ} (exponent : ℕ) (p : CMvPolynomial (n + 1) R) :
    CMvPolynomial n R :=
  Std.ExtTreeMap.foldl
    (fun acc monomial coefficient =>
      (if monomial.get 0 = exponent then
        CMvPolynomial.monomial (tailMonomial monomial) coefficient
      else 0) + acc)
    0 p.1

/-- Executable first-variable coefficient extraction agrees with `MvPolynomial.finSuccEquiv`. -/
theorem fromCMvPolynomial_headCoefficient {n : ℕ} (exponent : ℕ)
    (p : CMvPolynomial (n + 1) R) :
    fromCMvPolynomial (headCoefficient exponent p) =
      (MvPolynomial.finSuccEquiv R n (fromCMvPolynomial p)).coeff exponent := by
  have hfold : headCoefficient exponent p =
      Finsupp.sum (AddMonoidAlgebra.coeff (fromCMvPolynomial p))
        (fun monomial coefficient =>
          if monomial 0 = exponent then
            CMvPolynomial.monomial
              (tailMonomial (CMvMonomial.ofFinsupp monomial)) coefficient
          else 0) := by
    unfold headCoefficient
    rw [CPoly.foldl_eq_sum]
    congr 1
    funext monomial coefficient
    simp only [Function.comp_apply]
    congr 1
    simp [CMvMonomial.ofFinsupp]
  rw [hfold, fromCMvPolynomial_finsupp_sum]
  apply MvPolynomial.ext
  intro monomial
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  simp only [apply_ite, fromCMvPolynomial_monomial, toFinsupp_tailMonomial,
    CMvMonomial.toFinsupp_ofFinsupp, map_zero]
  rw [Finsupp.sum]
  let q := fromCMvPolynomial p
  change MvPolynomial.coeff monomial
      (∑ source ∈ q.support, if source 0 = exponent then
        MvPolynomial.monomial source.tail (q.coeff source) else 0) =
    q.coeff (monomial.cons exponent)
  rw [MvPolynomial.coeff_sum]
  by_cases hmem : monomial.cons exponent ∈ q.support
  · rw [Finset.sum_eq_single (monomial.cons exponent)]
    · simp only [Finsupp.cons_zero, ↓reduceIte, Finsupp.tail_cons,
        MvPolynomial.coeff_monomial]
    · intro source hsource hne
      by_cases hhead : source 0 = exponent
      · rw [if_pos hhead, MvPolynomial.coeff_monomial, if_neg]
        intro htail
        apply hne
        rw [← Finsupp.cons_tail source, hhead, htail]
      · simp only [hhead, ↓reduceIte, MvPolynomial.coeff_zero]
    · intro hnot
      exact (hnot hmem).elim
  · rw [Finset.sum_eq_zero]
    · exact (MvPolynomial.notMem_support_iff.mp hmem).symm
    · intro source hsource
      by_cases hhead : source 0 = exponent
      · rw [if_pos hhead, MvPolynomial.coeff_monomial, if_neg]
        intro htail
        apply hmem
        have heq : source = monomial.cons exponent := by
          rw [← Finsupp.cons_tail source, hhead, htail]
        simpa only [← heq] using hsource
      · simp only [hhead, ↓reduceIte, MvPolynomial.coeff_zero]

end CPoly.CMvPolynomial
