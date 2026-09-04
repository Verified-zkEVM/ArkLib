/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Individual degree under multivariate partial differentiation

This file records characteristic-sensitive facts about formal partial derivatives of
multivariate polynomials. The strict bound against `ringChar R` is load-bearing: in
characteristic `p`, the partial derivative of `X i ^ p` is zero.

The main results are:

* `MvPolynomial.degreeOf_pderiv_le_sub_one`, the characteristic-free upper bound;
* `MvPolynomial.degreeOf_pderiv_eq_sub_one_of_lt_ringChar`, exact degree loss below the
  characteristic;
* `MvPolynomial.iteratePDeriv_ne_zero_of_lt_ringChar`, nonvanishing throughout the corresponding
  derivative chain.
-/

namespace MvPolynomial

noncomputable section

open Finsupp

variable {R σ : Type*} [CommSemiring R]

/-- A partial derivative lowers the degree in its differentiation variable by at least one.

The statement is valid in every characteristic. Equality can fail when the leading exponent
vanishes in the coefficient ring. -/
theorem degreeOf_pderiv_le_sub_one (i : σ) (p : MvPolynomial σ R) :
    degreeOf i (pderiv i p) ≤ degreeOf i p - 1 := by
  rw [degreeOf_le_iff]
  intro m hm
  have hcoeff : coeff m (pderiv i p) ≠ 0 := mem_support_iff.mp hm
  have horig : coeff (m + single i 1) p ≠ 0 := by
    intro hzero
    rw [coeff_pderiv, hzero, zero_mul] at hcoeff
    exact hcoeff rfl
  have hmem : m + single i 1 ∈ p.support := mem_support_iff.mpr horig
  have hle := monomial_le_degreeOf i hmem
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hle
  omega

/-- Partial differentiation cannot increase the degree in any variable. -/
theorem degreeOf_pderiv_le (i j : σ) (p : MvPolynomial σ R) :
    degreeOf j (pderiv i p) ≤ degreeOf j p := by
  rw [degreeOf_le_iff]
  intro m hm
  have hcoeff : coeff m (pderiv i p) ≠ 0 := mem_support_iff.mp hm
  have horig : coeff (m + single i 1) p ≠ 0 := by
    intro hzero
    rw [coeff_pderiv, hzero, zero_mul] at hcoeff
    exact hcoeff rfl
  have hmem : m + single i 1 ∈ p.support := mem_support_iff.mpr horig
  have hle := monomial_le_degreeOf j hmem
  have hcoord : m j ≤ (m + (single i 1 : σ →₀ ℕ)) j := by
    simp only [Finsupp.add_apply]
    omega
  exact hcoord.trans hle

/-- A positive individual degree strictly below the characteristic survives one formal partial
derivative.

The theorem deliberately mentions `ringChar R`, rather than the cardinality of `R`: extension
fields have more elements but the same differentiation obstruction. -/
theorem pderiv_ne_zero_of_degreeOf_pos_of_lt_ringChar [NoZeroDivisors R] [Nontrivial R]
    (i : σ) (p : MvPolynomial σ R) (hpos : 0 < degreeOf i p)
    (hchar : degreeOf i p < ringChar R) : pderiv i p ≠ 0 := by
  classical
  have hsupp : p.support.Nonempty := support_nonempty.mpr <|
    ne_zero_of_degreeOf_ne_zero (p := p) (i := i) (Nat.ne_of_gt hpos)
  obtain ⟨m, hm, heq⟩ := Finset.exists_mem_eq_sup p.support hsupp fun m ↦ m i
  rw [← degreeOf_eq_sup i p] at heq
  rw [heq] at hpos hchar
  have hmi : m i ≠ 0 := Nat.ne_of_gt hpos
  have hcast : (m i : R) ≠ 0 := by
    intro hzero
    exact Nat.not_dvd_of_pos_of_lt hpos hchar ((ringChar.spec R _).mp hzero)
  let m' := m - single i 1
  have hm'_add : m' + single i 1 = m := sub_add_single_one_cancel hmi
  have hm'i : m' i + 1 = m i := by
    dsimp [m']
    rw [Finsupp.single_eq_same]
    omega
  have hcast_eq : (↑(m' i) + 1 : R) = (m i : R) := by
    rw [← Nat.cast_one, ← Nat.cast_add, hm'i]
  intro hderiv
  have hzero : coeff m' (pderiv i p) = 0 := by rw [hderiv, coeff_zero]
  rw [coeff_pderiv, hm'_add, hcast_eq] at hzero
  exact mul_ne_zero (mem_support_iff.mp hm) hcast hzero

/-- Below the characteristic, a partial derivative of a polynomial that depends on its variable
loses exactly one in that individual degree. -/
theorem degreeOf_pderiv_eq_sub_one_of_lt_ringChar [NoZeroDivisors R] [Nontrivial R]
    (i : σ) (p : MvPolynomial σ R) (hpos : 0 < degreeOf i p)
    (hchar : degreeOf i p < ringChar R) :
    degreeOf i (pderiv i p) = degreeOf i p - 1 := by
  classical
  apply Nat.le_antisymm (degreeOf_pderiv_le_sub_one i p)
  have hsupp : p.support.Nonempty := support_nonempty.mpr <|
    ne_zero_of_degreeOf_ne_zero (p := p) (i := i) (Nat.ne_of_gt hpos)
  obtain ⟨m, hm, heq⟩ := Finset.exists_mem_eq_sup p.support hsupp fun m ↦ m i
  rw [← degreeOf_eq_sup i p] at heq
  rw [heq] at hpos hchar ⊢
  have hmi : m i ≠ 0 := Nat.ne_of_gt hpos
  have hcast : (m i : R) ≠ 0 := by
    intro hzero
    exact Nat.not_dvd_of_pos_of_lt hpos hchar ((ringChar.spec R _).mp hzero)
  let m' := m - single i 1
  have hm'_add : m' + single i 1 = m := sub_add_single_one_cancel hmi
  have hm'i : m' i + 1 = m i := by
    dsimp [m']
    rw [Finsupp.single_eq_same]
    omega
  have hcast_eq : (↑(m' i) + 1 : R) = (m i : R) := by
    rw [← Nat.cast_one, ← Nat.cast_add, hm'i]
  have hm'supp : m' ∈ (pderiv i p).support := by
    rw [mem_support_iff, coeff_pderiv, hm'_add, hcast_eq]
    exact mul_ne_zero (mem_support_iff.mp hm) hcast
  have hlower := monomial_le_degreeOf i hm'supp
  omega

/-- The `a`-fold formal partial derivative in variable `i`. -/
def iteratePDeriv (i : σ) (a : ℕ) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  (pderiv i)^[a] p

@[simp]
theorem iteratePDeriv_zero (i : σ) (p : MvPolynomial σ R) : iteratePDeriv i 0 p = p := by
  simp [iteratePDeriv]

@[simp]
theorem iteratePDeriv_succ (i : σ) (a : ℕ) (p : MvPolynomial σ R) :
    iteratePDeriv i (a + 1) p = pderiv i (iteratePDeriv i a p) := by
  simp [iteratePDeriv, Function.iterate_succ_apply']

/-- Below the characteristic, every initial segment of the derivative chain has the expected
individual degree. -/
theorem degreeOf_iteratePDeriv_eq_sub_of_lt_ringChar [NoZeroDivisors R] [Nontrivial R]
    (i : σ) (a : ℕ) (p : MvPolynomial σ R) (ha : a ≤ degreeOf i p)
    (hchar : degreeOf i p < ringChar R) :
    degreeOf i (iteratePDeriv i a p) = degreeOf i p - a := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [iteratePDeriv_succ,
        degreeOf_pderiv_eq_sub_one_of_lt_ringChar i (iteratePDeriv i a p)]
      · rw [ih (by omega)]
        omega
      · rw [ih (by omega)]
        omega
      · rw [ih (by omega)]
        exact (Nat.sub_le _ _).trans_lt hchar

/-- Iterated partial differentiation cannot increase any individual degree. -/
theorem degreeOf_iteratePDeriv_le (i j : σ) (a : ℕ) (p : MvPolynomial σ R) :
    degreeOf j (iteratePDeriv i a p) ≤ degreeOf j p := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [iteratePDeriv_succ]
      exact (degreeOf_pderiv_le i j _).trans ih

/-- Every partial derivative through the full active degree is nonzero when that degree is
positive and strictly below the characteristic. In particular, differentiation exactly through
the active degree produces a nonzero polynomial independent of that variable. -/
theorem iteratePDeriv_ne_zero_of_lt_ringChar [NoZeroDivisors R] [Nontrivial R]
    (i : σ) (a : ℕ) (p : MvPolynomial σ R) (hpos : 0 < degreeOf i p)
    (ha : a ≤ degreeOf i p) (hchar : degreeOf i p < ringChar R) :
    iteratePDeriv i a p ≠ 0 := by
  induction a with
  | zero =>
      simp only [iteratePDeriv_zero]
      exact ne_zero_of_degreeOf_ne_zero (i := i) (Nat.ne_of_gt hpos)
  | succ a ih =>
      rw [iteratePDeriv_succ]
      apply pderiv_ne_zero_of_degreeOf_pos_of_lt_ringChar
      · rw [degreeOf_iteratePDeriv_eq_sub_of_lt_ringChar i a p (by omega) hchar]
        omega
      · rw [degreeOf_iteratePDeriv_eq_sub_of_lt_ringChar i a p (by omega) hchar]
        exact (Nat.sub_le _ _).trans_lt hchar

end

end MvPolynomial
