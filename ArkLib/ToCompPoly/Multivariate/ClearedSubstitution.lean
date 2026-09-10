/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToCompPoly.Multivariate.Substitution
public import ArkLib.ToCompPoly.Multivariate.Eval
public import ArkLib.ToMathlib.MvPolynomial.ClearedSubstitution
/-!
# Computable denominator-cleared substitution

This is the concrete counterpart of `MvPolynomial.clearedSubstitution`. It traverses the stored
monomials once, substitutes supplied computable numerators, and inserts the remaining common
denominator power. Natural subtraction gives a total executable function; the semantic Taylor
support theorem separately ensures that the chosen denominator budget is sufficient.
-/

@[expose] public section

namespace CPoly.CMvPolynomial

variable {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]

/-- Weighted degree of one concrete monomial. -/
def monomialWeight {n : ℕ} (weight : Fin n → ℕ) (monomial : CMvMonomial n) : ℕ :=
  ∑ i, weight i * monomial.get i

theorem monomialWeight_eq_finsuppWeight {n : ℕ} (weight : Fin n → ℕ)
    (monomial : CMvMonomial n) :
    monomialWeight weight monomial = Finsupp.weight weight monomial.toFinsupp := by
  rw [monomialWeight, Finsupp.weight_apply, Finsupp.sum]
  simp only [smul_eq_mul, CPoly.CMvMonomial.toFinsupp]
  rw [show (∑ i : Fin n, weight i * monomial.get i) =
      ∑ i : Fin n, monomial.get i * weight i by
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.mul_comm _ _]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hinot
  have hzero : monomial[(i : ℕ)] = 0 := by
    by_contra hne
    apply hinot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hne
  change monomial.get i * weight i = 0
  rw [Vector.get_eq_getElem, hzero, zero_mul]

/-- Clear a common denominator during computable polynomial substitution. -/
def clearedSubstitution {n m : ℕ} (denominator : CMvPolynomial m R)
    (numerator : Fin n → CMvPolynomial m R) (weight : Fin n → ℕ)
    (budget : ℕ) (p : CMvPolynomial n R) : CMvPolynomial m R :=
  Std.ExtTreeMap.foldl
    (fun acc monomial coefficient =>
      CMvPolynomial.C coefficient * MonoR.evalMonomial numerator monomial *
        denominator ^ (budget - monomialWeight weight monomial) + acc)
    0 p.1

theorem fromCMvPolynomial_evalMonomial {n m : ℕ}
    (f : Fin n → CMvPolynomial m R) (monomial : CMvMonomial n) :
    fromCMvPolynomial (MonoR.evalMonomial f monomial) =
      ∏ i ∈ monomial.toFinsupp.support,
        fromCMvPolynomial (f i) ^ monomial.toFinsupp i := by
  unfold MonoR.evalMonomial
  change CPoly.polyRingEquiv (∏ i, f i ^ monomial.get i) = _
  rw [map_prod]
  simp_rw [map_pow]
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hinot
  rw [Finsupp.notMem_support_iff] at hinot
  simp [hinot]

theorem fromCMvPolynomial_pow {n : ℕ} (p : CMvPolynomial n R) (e : ℕ) :
    fromCMvPolynomial (p ^ e) = fromCMvPolynomial p ^ e := by
  change CPoly.polyRingEquiv (p ^ e) = _
  exact map_pow CPoly.polyRingEquiv p e

/-- Computable cleared substitution agrees exactly with the mathematical finite sum. -/
theorem fromCMvPolynomial_clearedSubstitution {n m : ℕ}
    (denominator : CMvPolynomial m R) (numerator : Fin n → CMvPolynomial m R)
    (weight : Fin n → ℕ) (budget : ℕ) (p : CMvPolynomial n R) :
    fromCMvPolynomial (clearedSubstitution denominator numerator weight budget p) =
      MvPolynomial.clearedSubstitution MvPolynomial.C
        (fromCMvPolynomial denominator) (fun i => fromCMvPolynomial (numerator i))
        weight budget (fromCMvPolynomial p) := by
  have hfold : clearedSubstitution denominator numerator weight budget p =
      Finsupp.sum (AddMonoidAlgebra.coeff (fromCMvPolynomial p))
        (fun monomial coefficient =>
          CMvPolynomial.C coefficient *
            MonoR.evalMonomial numerator (CMvMonomial.ofFinsupp monomial) *
            denominator ^ (budget - Finsupp.weight weight monomial)) := by
    unfold clearedSubstitution
    rw [CPoly.foldl_eq_sum]
    congr 1
    funext monomial coefficient
    simp only [Function.comp_apply]
    rw [monomialWeight_eq_finsuppWeight]
    simp only [CMvMonomial.toFinsupp_ofFinsupp]
  rw [hfold, fromCMvPolynomial_finsupp_sum]
  simp_rw [fromCMvPolynomial_mul']
  simp_rw [fromCMvPolynomial_C]
  simp_rw [fromCMvPolynomial_evalMonomial]
  simp_rw [fromCMvPolynomial_pow]
  simp only [CMvMonomial.toFinsupp_ofFinsupp]
  rw [Finsupp.sum, MvPolynomial.clearedSubstitution,
    MvPolynomial.finsupp_support_eq_support]
  rfl

end CPoly.CMvPolynomial
