/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.WeightedDegree
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Weighted degree after moving one variable into the coefficient ring

The equivalence `optionEquivRight` regards the distinguished `none` variable as the polynomial
variable in the coefficient ring.  The total degree in the remaining variables is therefore the
weighted total degree that gives `none` weight zero and every `some` variable weight one.  Over a
domain, this realizes that weighted degree as an ordinary total degree and hence makes it additive
under multiplication and monotone under divisibility.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R]

/-- Moving the distinguished variable into the coefficient ring sends a monomial to the
corresponding monomial in the remaining variables with a univariate monomial coefficient. -/
theorem optionEquivRight_monomial (d : Option σ →₀ ℕ) (r : R) :
    optionEquivRight R σ (monomial d r) =
      monomial d.some (Polynomial.monomial (d none) r) := by
  classical
  rw [optionEquivRight_apply, aeval_monomial]
  rw [Finsupp.prod_option_index d _ (by simp) (by intros; rw [pow_add])]
  simp only [Option.elim_none, Option.elim_some]
  rw [monomial_eq]
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  change C (Polynomial.C r) * (C Polynomial.X ^ d none * _) =
    C (Polynomial.C r * Polynomial.X ^ d none) * _
  rw [← map_pow (C : Polynomial R →+* MvPolynomial σ (Polynomial R))]
  rw [map_mul]
  exact (mul_assoc _ _ _).symm

/-- Coefficients are preserved when an exponent is split into its distinguished and remaining
coordinates. -/
theorem optionEquivRight_coeff_coeff
    (p : MvPolynomial (Option σ) R) (m : σ →₀ ℕ) (i : ℕ) :
    Polynomial.coeff (coeff m (optionEquivRight R σ p)) i =
      coeff (m.optionElim i) p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, Polynomial.coeff_add, hp, hq]
  | monomial d r =>
    rw [optionEquivRight_monomial]
    simp only [coeff_monomial]
    split_ifs with hmd him
    · subst m
      have hnone : d none = i := by
        have h := congrArg (fun e : Option σ →₀ ℕ ↦ e none) him
        simpa using h
      rw [Polynomial.coeff_monomial, if_pos hnone]
    · subst m
      rw [Polynomial.coeff_monomial, if_neg]
      intro hnone
      apply him
      rw [← hnone]
      exact (Finsupp.optionElim_some d).symm
    · exfalso
      apply hmd
      rename_i hEq
      rw [hEq]
      simp
    · simp

/-- Splitting off a weight-zero coordinate preserves the degree in all weight-one coordinates. -/
theorem weight_optionElim_zero_one (m : σ →₀ ℕ) (i : ℕ) :
    (m.optionElim i).weight (fun v ↦ v.elim 0 (fun _ ↦ 1)) = m.degree := by
  rw [Finsupp.weight_apply, Finsupp.sum_option_index]
  · simp only [Finsupp.optionElim_apply_none, Finsupp.some_optionElim,
      Option.elim_none, Option.elim_some, nsmul_eq_mul, mul_zero, zero_add, mul_one]
    rfl
  · simp
  · intro o a b
    rcases o with _ | x <;> simp

set_option maxHeartbeats 1000000 in
-- Comparing both finite supports through the coefficient formula needs a larger elaboration budget.
/-- The total degree after `optionEquivRight` is the source weighted degree that ignores the
distinguished variable. -/
theorem totalDegree_optionEquivRight (p : MvPolynomial (Option σ) R) :
    (optionEquivRight R σ p).totalDegree =
      p.weightedTotalDegree (fun v ↦ v.elim 0 (fun _ ↦ 1)) := by
  classical
  apply le_antisymm
  · rw [totalDegree, Finset.sup_le_iff]
    intro m hm
    have hcoeff : coeff m (optionEquivRight R σ p) ≠ 0 := mem_support_iff.mp hm
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr hcoeff
    have hle := le_weightedTotalDegree
      (fun v ↦ v.elim 0 (fun _ ↦ 1))
      (mem_support_iff.mpr (show coeff (m.optionElim i) p ≠ 0 by
        rw [← optionEquivRight_coeff_coeff]
        exact Polynomial.mem_support_iff.mp hi))
    rwa [weight_optionElim_zero_one] at hle
  · rw [weightedTotalDegree, Finset.sup_le_iff]
    intro d hd
    have htarget : d.some ∈ (optionEquivRight R σ p).support := by
      apply mem_support_iff.mpr
      intro hzero
      have hcoeffzero := congrArg (fun q : Polynomial R ↦ q.coeff (d none)) hzero
      rw [optionEquivRight_coeff_coeff] at hcoeffzero
      simp only [Finsupp.optionElim_some] at hcoeffzero
      exact mem_support_iff.mp hd hcoeffzero
    have hle := le_totalDegree htarget
    have heq := weight_optionElim_zero_one d.some (d none)
    simp only [Finsupp.optionElim_some] at heq
    exact heq.trans_le hle

/-- Over a domain, the weighted degree that ignores the distinguished variable is additive on
nonzero products. -/
theorem weightedTotalDegree_option_zero_one_mul [NoZeroDivisors R]
    (p q : MvPolynomial (Option σ) R) (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).weightedTotalDegree (fun v ↦ v.elim 0 (fun _ ↦ 1)) =
      p.weightedTotalDegree (fun v ↦ v.elim 0 (fun _ ↦ 1)) +
        q.weightedTotalDegree (fun v ↦ v.elim 0 (fun _ ↦ 1)) := by
  rw [← totalDegree_optionEquivRight, ← totalDegree_optionEquivRight,
    ← totalDegree_optionEquivRight, map_mul]
  apply totalDegree_mul_of_isDomain
  · exact (optionEquivRight R σ).injective.ne_iff.mpr hp
  · exact (optionEquivRight R σ).injective.ne_iff.mpr hq

/-- Over a domain, a nonzero divisor cannot have larger degree in the weight-one coordinates than
the nonzero dividend. -/
theorem weightedTotalDegree_option_zero_one_le_of_dvd [NoZeroDivisors R]
    (p q : MvPolynomial (Option σ) R) (hp : p ≠ 0) (hq : q ≠ 0) (hdiv : p ∣ q) :
    p.weightedTotalDegree (fun v ↦ v.elim 0 (fun _ ↦ 1)) ≤
      q.weightedTotalDegree (fun v ↦ v.elim 0 (fun _ ↦ 1)) := by
  obtain ⟨r, rfl⟩ := hdiv
  have hr : r ≠ 0 := right_ne_zero_of_mul hq
  rw [weightedTotalDegree_option_zero_one_mul p r hp hr]
  omega

end MvPolynomial
