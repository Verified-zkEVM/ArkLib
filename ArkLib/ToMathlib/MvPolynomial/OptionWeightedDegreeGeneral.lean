/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.MvPolynomial.OptionWeightedDegree

/-!
# Arbitrary weights after moving one variable into the coefficient ring

`optionEquivRight` preserves every weighted degree on the remaining variables when the
distinguished variable is assigned weight zero.  The existing zero-one theorem is the special
case in which every remaining variable has weight one.
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

variable {R sigma : Type*} [CommSemiring R]

private theorem weight_optionElim_zero_general
    (w : sigma → ℕ) (m : sigma →₀ ℕ) (i : ℕ) :
    (m.optionElim i).weight (fun v ↦ v.elim 0 w) = m.weight w := by
  rw [Finsupp.weight_apply, Finsupp.sum_option_index]
  · simp only [Finsupp.optionElim_apply_none, Finsupp.some_optionElim,
      Option.elim_none, Option.elim_some, nsmul_eq_mul, mul_zero, zero_add]
    rfl
  · simp
  · intro o a b
    rcases o with _ | x
    · simp
    · simp only [Option.elim_some, add_nsmul]

/-- Moving `none` into the polynomial coefficient ring preserves an arbitrary weight on all
`some` variables and assigns weight zero to `none`. -/
theorem weightedTotalDegree_optionEquivRight_general
    (w : sigma → ℕ) (p : MvPolynomial (Option sigma) R) :
    (optionEquivRight R sigma p).weightedTotalDegree w =
      p.weightedTotalDegree (fun v ↦ v.elim 0 w) := by
  classical
  apply le_antisymm
  · rw [weightedTotalDegree, Finset.sup_le_iff]
    intro m hm
    have hcoeff : coeff m (optionEquivRight R sigma p) ≠ 0 := mem_support_iff.mp hm
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr hcoeff
    have hle := le_weightedTotalDegree (fun v ↦ v.elim 0 w)
      (mem_support_iff.mpr (show coeff (m.optionElim i) p ≠ 0 by
        rw [← optionEquivRight_coeff_coeff]
        exact Polynomial.mem_support_iff.mp hi))
    rwa [weight_optionElim_zero_general] at hle
  · rw [weightedTotalDegree, Finset.sup_le_iff]
    intro d hd
    have htarget : d.some ∈ (optionEquivRight R sigma p).support := by
      apply mem_support_iff.mpr
      intro hzero
      have hcoeffzero := congrArg (fun q : Polynomial R ↦ q.coeff (d none)) hzero
      rw [optionEquivRight_coeff_coeff] at hcoeffzero
      simp only [Finsupp.optionElim_some] at hcoeffzero
      exact mem_support_iff.mp hd hcoeffzero
    have hle := le_weightedTotalDegree w htarget
    have heq := weight_optionElim_zero_general w d.some (d none)
    simp only [Finsupp.optionElim_some] at heq
    exact heq.trans_le hle

end

end MvPolynomial
