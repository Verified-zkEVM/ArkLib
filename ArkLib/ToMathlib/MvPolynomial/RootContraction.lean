/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Expanding and contracting one variable of a multivariate polynomial

View a polynomial in the variables `Option σ` as a univariate polynomial in the distinguished
variable `none` whose coefficients are polynomials in the variables `σ`, through
`MvPolynomial.optionEquivLeft`. Under this presentation the partial derivative in `none` is the
univariate derivative.

`rootExpansion s` substitutes `X none ^ s` for `X none`, and `rootContraction s` keeps only the
exponents of `X none` divisible by `s` and divides them by `s`. Both are `Polynomial.expand` and
`Polynomial.contract` transported through `optionEquivLeft`. Contraction undoes expansion. The
coefficient of `m` in `rootContraction s P` is the coefficient of `P` at `m` with the exponent of
`X none` multiplied by `s`, so contraction does not increase the degree in any variable `some j`.
Over a domain of characteristic `p`, if the partial derivative in `none` vanishes, then
contraction by `p` divides the degree in `none` by `p` exactly.

## Main statements

* `MvPolynomial.map_optionEquivLeft`: coefficient maps commute with `optionEquivLeft`.
* `MvPolynomial.optionEquivLeft_pderiv_none`: the partial derivative in `none` is the univariate
  derivative.
* `MvPolynomial.eval_rootExpansion`, `MvPolynomial.map_rootExpansion`,
  `MvPolynomial.eval₂_rootExpansion`, and `MvPolynomial.rootContraction_rootExpansion`.
* `MvPolynomial.coeff_rootContraction` and `MvPolynomial.degreeOf_rootContraction_some_le`.
* `MvPolynomial.degreeOf_rootContraction_none_mul`: the degree identity for a contraction of a
  polynomial with vanishing partial derivative in `none`.
-/

@[expose] public section

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R]

/-- `optionEquivLeft` commutes with maps of polynomial coefficients. -/
theorem map_optionEquivLeft {S : Type*} [CommSemiring S] (f : R →+* S)
    (P : MvPolynomial (Option σ) R) :
    Polynomial.map (map f) (optionEquivLeft R σ P) = optionEquivLeft S σ (map f P) := by
  have he : (Polynomial.mapRingHom (map f)).comp (optionEquivLeft R σ).toRingHom =
      (optionEquivLeft S σ).toRingHom.comp (map f) := by
    ext a : 2
    · simp
    · cases a <;> simp
  exact DFunLike.congr_fun he P

/-- Under `optionEquivLeft`, the partial derivative in `none` is the univariate derivative. -/
theorem optionEquivLeft_pderiv_none (P : MvPolynomial (Option σ) R) :
    optionEquivLeft R σ (pderiv none P) =
      Polynomial.derivative (optionEquivLeft R σ P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP =>
    cases j with
    | none => simp [Polynomial.derivative_mul, hP, mul_comm]
    | some j => simp [Polynomial.derivative_mul, hP, mul_comm]

/-- Substitute `X none ^ s` for the distinguished variable `X none`. -/
noncomputable def rootExpansion (s : ℕ) (P : MvPolynomial (Option σ) R) :
    MvPolynomial (Option σ) R :=
  (optionEquivLeft R σ).symm
    (Polynomial.expand (MvPolynomial σ R) s (optionEquivLeft R σ P))

/-- Evaluating `rootExpansion s P` at `y` in the distinguished variable evaluates `P` at `y ^ s`
in that variable. -/
theorem eval_rootExpansion (s : ℕ) (P : MvPolynomial (Option σ) R)
    (x : σ → R) (y : R) :
    eval (fun j ↦ Option.elim j y x) (rootExpansion s P) =
      eval (fun j ↦ Option.elim j (y ^ s) x) P := by
  rw [optionEquivLeft_elim_eval, rootExpansion, AlgEquiv.apply_symm_apply,
    Polynomial.map_expand, Polynomial.expand_eval, optionEquivLeft_elim_eval]

/-- Mapping coefficients commutes with expansion in the distinguished variable. -/
theorem map_rootExpansion {S : Type*} [CommSemiring S] (f : R →+* S) (s : ℕ)
    (P : MvPolynomial (Option σ) R) :
    map f (rootExpansion s P) = rootExpansion s (map f P) := by
  apply (optionEquivLeft S σ).injective
  rw [← map_optionEquivLeft]
  simp [rootExpansion, Polynomial.map_expand, map_optionEquivLeft]

/-- Evaluating `rootExpansion s P` through `f` at `y` evaluates `P` at `y ^ s`. -/
theorem eval₂_rootExpansion {S : Type*} [CommSemiring S] (f : R →+* S) (s : ℕ)
    (P : MvPolynomial (Option σ) R) (x : σ → S) (y : S) :
    eval₂ f (fun o ↦ o.elim y x) (rootExpansion s P) =
      eval₂ f (fun o ↦ o.elim (y ^ s) x) P := by
  rw [eval₂_eq_eval_map, map_rootExpansion, eval_rootExpansion,
    ← eval₂_eq_eval_map]

/-- Keep the exponents of `X none` divisible by `s` and divide them by `s`. The coefficients in
the other variables are unchanged. -/
noncomputable def rootContraction (s : ℕ) (P : MvPolynomial (Option σ) R) :
    MvPolynomial (Option σ) R :=
  (optionEquivLeft R σ).symm (Polynomial.contract s (optionEquivLeft R σ P))

/-- Contraction by a nonzero `s` undoes expansion by `s`. -/
theorem rootContraction_rootExpansion {s : ℕ} (hs : s ≠ 0)
    (P : MvPolynomial (Option σ) R) :
    rootContraction s (rootExpansion s P) = P := by
  simp only [rootContraction, rootExpansion, AlgEquiv.apply_symm_apply,
    Polynomial.contract_expand s hs, AlgEquiv.symm_apply_apply]

/-- The coefficient of `m` in `rootContraction s P` is the coefficient of `P` at `m` with the
exponent of `X none` multiplied by `s`. -/
theorem coeff_rootContraction {s : ℕ} (hs : s ≠ 0)
    (P : MvPolynomial (Option σ) R) (m : Option σ →₀ ℕ) :
    (rootContraction s P).coeff m = P.coeff (m.some.optionElim (m none * s)) := by
  rw [← optionEquivLeft_coeff_some_coeff_none R σ m, rootContraction,
    AlgEquiv.apply_symm_apply, Polynomial.coeff_contract hs]
  simpa only [Finsupp.some_optionElim, Finsupp.optionElim_apply_none] using
    optionEquivLeft_coeff_some_coeff_none R σ (m.some.optionElim (m none * s)) P

/-- Contraction in the distinguished variable does not increase the degree in any other
variable. -/
theorem degreeOf_rootContraction_some_le {s : ℕ} (hs : s ≠ 0)
    (P : MvPolynomial (Option σ) R) (j : σ) :
    (rootContraction s P).degreeOf (some j) ≤ P.degreeOf (some j) := by
  classical
  apply degreeOf_le_iff.mpr
  intro m hm
  have hm' : m.some.optionElim (m none * s) ∈ P.support := by
    rw [mem_support_iff] at hm ⊢
    rwa [coeff_rootContraction hs] at hm
  simpa only [Finsupp.optionElim_apply_some, Finsupp.some_apply] using
    le_degreeOf_of_mem_support (some j) hm'

/-- Over a ring without zero divisors of characteristic `p ≠ 0`, if the partial derivative in
`none` vanishes, then contraction by `p` divides the degree in `none` by `p` exactly. -/
theorem degreeOf_rootContraction_none_mul [NoZeroDivisors R] (p : ℕ) [CharP R p]
    (hp : p ≠ 0) (P : MvPolynomial (Option σ) R) (hder : pderiv none P = 0) :
    (rootContraction p P).degreeOf none * p = P.degreeOf none := by
  have hder' : Polynomial.derivative (optionEquivLeft R σ P) = 0 := by
    rw [← optionEquivLeft_pderiv_none, hder, map_zero]
  have h := congrArg Polynomial.natDegree (Polynomial.expand_contract p hder' hp)
  rw [Polynomial.natDegree_expand, natDegree_optionEquivLeft] at h
  rw [← natDegree_optionEquivLeft R, rootContraction, AlgEquiv.apply_symm_apply]
  exact h

end MvPolynomial
