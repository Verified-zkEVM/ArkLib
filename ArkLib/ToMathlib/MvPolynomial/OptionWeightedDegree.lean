/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Weighted degree after moving one variable into the coefficient ring

Mathlib's `MvPolynomial.optionEquivRight` identifies `MvPolynomial (Option σ) R` with
`MvPolynomial σ R[X]`: the distinguished variable `none` becomes the variable of the univariate
coefficient ring. This file computes monomials and coefficients through that equivalence and shows
that, for every weight `w : σ → ℕ`, the `w`-weighted degree of the image equals the weighted degree
of the original polynomial for the weight that gives `none` weight zero and `some i` weight `w i`.
Taking `w = 1` identifies the ordinary total degree of the image with the weighted degree that
ignores `none`.

## Main statements

* `MvPolynomial.optionEquivRight_monomial`: the image of a monomial.
* `MvPolynomial.optionEquivRight_coeff_coeff`: coefficient extraction through the equivalence.
* `Finsupp.weight_optionElim`: the weight of an exponent vector split into its `none` and `some`
  coordinates.
* `MvPolynomial.weightedTotalDegree_optionEquivRight`: the weighted-degree identity for any `w`.
* `MvPolynomial.totalDegree_optionEquivRight`: the case `w = 1`.

Additivity under multiplication and monotonicity under divisibility over a ring without zero
divisors need no separate statement here: they are `MvPolynomial.weightedTotalDegree_mul` and
`MvPolynomial.weightedTotalDegree_le_of_dvd` in `ArkLib.Data.MvPolynomial.WeightedDegree.Products`,
which hold for every weight, applied to the weight `fun v ↦ v.elim 0 (fun _ ↦ 1)`.
-/

@[expose] public section

noncomputable section

namespace Finsupp

variable {σ : Type*}

/-- The weight of the exponent vector with `none`-coordinate `i` and `some`-coordinates `m`, for
the weight that is `c` on `none` and `w` on `some`, is `c * i + m.weight w`. -/
theorem weight_optionElim (c : ℕ) (w : σ → ℕ) (m : σ →₀ ℕ) (i : ℕ) :
    (m.optionElim i).weight (fun v ↦ v.elim c w) = c * i + m.weight w := by
  rw [weight_apply, sum_option_index]
  · simp only [optionElim_apply_none, some_optionElim, Option.elim_none, Option.elim_some,
      smul_eq_mul, Nat.mul_comm i c]
    rfl
  · simp
  · intro o a b
    rcases o with _ | x <;> simp [Nat.add_mul]

end Finsupp

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R]

/-- Moving the distinguished variable into the coefficient ring sends the monomial `r * x^d` to
the monomial in the remaining variables with exponent `d.some` and univariate coefficient
`r * X ^ d none`. -/
theorem optionEquivRight_monomial (d : Option σ →₀ ℕ) (r : R) :
    optionEquivRight R σ (monomial d r) =
      monomial d.some (Polynomial.monomial (d none) r) := by
  classical
  rw [optionEquivRight_apply, aeval_monomial]
  rw [Finsupp.prod_option_index d _ (by simp) (by intros; rw [pow_add])]
  simp only [Option.elim_none, Option.elim_some]
  rw [monomial_eq, ← Polynomial.C_mul_X_pow_eq_monomial]
  change C (Polynomial.C r) * (C Polynomial.X ^ d none * _) =
    C (Polynomial.C r * Polynomial.X ^ d none) * _
  rw [← map_pow (C : Polynomial R →+* MvPolynomial σ (Polynomial R)), map_mul]
  exact (mul_assoc _ _ _).symm

/-- The coefficient of `X ^ i` in the coefficient of the monomial `m` of `optionEquivRight R σ p`
is the coefficient of `p` at the exponent vector with `none`-coordinate `i` and `some`-coordinates
`m`. -/
theorem optionEquivRight_coeff_coeff
    (p : MvPolynomial (Option σ) R) (m : σ →₀ ℕ) (i : ℕ) :
    ((optionEquivRight R σ p).coeff m).coeff i = p.coeff (m.optionElim i) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [-optionEquivRight_apply, hp, hq]
  | monomial d r =>
    rw [optionEquivRight_monomial]
    simp only [coeff_monomial]
    split_ifs with hmd him
    · subst m
      have hnone : d none = i := by
        simpa using congrArg (fun e : Option σ →₀ ℕ ↦ e none) him
      rw [Polynomial.coeff_monomial, ite_eq_left_of_eq_true _ _ (eq_true hnone)]
    · subst m
      rw [Polynomial.coeff_monomial, ite_eq_right_of_eq_false _ _ (eq_false ?_)]
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

/-- Splitting off a weight-zero coordinate preserves the degree in the weight-one coordinates.
This is `Finsupp.weight_optionElim` with `c = 0` and `w = 1`. -/
theorem weight_optionElim_zero_one (m : σ →₀ ℕ) (i : ℕ) :
    (m.optionElim i).weight (fun v ↦ v.elim 0 (fun _ ↦ 1)) = m.degree := by
  rw [Finsupp.weight_optionElim, Nat.zero_mul, Nat.zero_add, Finsupp.degree_eq_weight_one]

/-- For every weight `w` on the remaining variables, the `w`-weighted degree of
`optionEquivRight R σ p` equals the weighted degree of `p` that gives the distinguished variable
weight zero and `some i` weight `w i`. The distinguished variable has weight zero because it has
moved into the coefficient ring, where the weighted degree does not see it. -/
theorem weightedTotalDegree_optionEquivRight (w : σ → ℕ) (p : MvPolynomial (Option σ) R) :
    (optionEquivRight R σ p).weightedTotalDegree w =
      p.weightedTotalDegree (fun v ↦ v.elim 0 w) := by
  classical
  have hw (m : σ →₀ ℕ) (i : ℕ) : (m.optionElim i).weight (fun v ↦ v.elim 0 w) = m.weight w := by
    rw [Finsupp.weight_optionElim, Nat.zero_mul, Nat.zero_add]
  apply le_antisymm
  · rw [weightedTotalDegree, Finset.sup_le_iff]
    intro m hm
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (mem_support_iff.mp hm)
    have hle := le_weightedTotalDegree (fun v ↦ v.elim 0 w)
      (mem_support_iff.mpr (show p.coeff (m.optionElim i) ≠ 0 by
        rw [← optionEquivRight_coeff_coeff]
        exact Polynomial.mem_support_iff.mp hi))
    rwa [hw] at hle
  · rw [weightedTotalDegree, Finset.sup_le_iff]
    intro d hd
    have htarget : d.some ∈ (optionEquivRight R σ p).support := by
      apply mem_support_iff.mpr
      intro hzero
      have hcoeffzero := congrArg (fun q : Polynomial R ↦ q.coeff (d none)) hzero
      simp only [optionEquivRight_coeff_coeff, Finsupp.optionElim_some] at hcoeffzero
      simp only [Polynomial.coeff_zero] at hcoeffzero
      exact mem_support_iff.mp hd hcoeffzero
    have heq := hw d.some (d none)
    rw [Finsupp.optionElim_some] at heq
    exact heq.trans_le (le_weightedTotalDegree w htarget)

/-- The total degree after `optionEquivRight` is the weighted degree that gives the distinguished
variable weight zero and every other variable weight one. -/
theorem totalDegree_optionEquivRight (p : MvPolynomial (Option σ) R) :
    (optionEquivRight R σ p).totalDegree =
      p.weightedTotalDegree (fun v ↦ v.elim 0 (fun _ ↦ 1)) := by
  rw [← weightedTotalDegree_one, weightedTotalDegree_optionEquivRight]
  rfl

end MvPolynomial
