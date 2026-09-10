/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.CharP.Algebra

/-!
# Contracting one multivariate root coordinate

View `none` as the polynomial variable and the other coordinates as coefficients.
Contraction selects coefficients and therefore cannot increase any other coordinate degree.
-/

@[expose] public section

namespace MvPolynomial

variable {R σ : Type*} [CommRing R]

/-- Differentiation in the distinguished coordinate is ordinary polynomial differentiation
under the coefficient-ring presentation. -/
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

/-- Expand only the distinguished root variable. -/
noncomputable def rootExpansion (s : ℕ) (P : MvPolynomial (Option σ) R) :
    MvPolynomial (Option σ) R :=
  (optionEquivLeft R σ).symm
    (Polynomial.expand (MvPolynomial σ R) s (optionEquivLeft R σ P))

/-- Root expansion is substitution of `y^s` for the distinguished variable. -/
theorem eval_rootExpansion (s : ℕ) (P : MvPolynomial (Option σ) R)
    (x : σ → R) (y : R) :
    eval (fun j ↦ Option.elim j y x) (rootExpansion s P) =
      eval (fun j ↦ Option.elim j (y ^ s) x) P := by
  rw [optionEquivLeft_elim_eval, rootExpansion, AlgEquiv.apply_symm_apply,
    Polynomial.map_expand, Polynomial.expand_eval, optionEquivLeft_elim_eval]

/-- Contract only the distinguished root variable, preserving the coefficient ring. -/
noncomputable def rootContraction (s : ℕ) (P : MvPolynomial (Option σ) R) :
    MvPolynomial (Option σ) R :=
  (optionEquivLeft R σ).symm (Polynomial.contract s (optionEquivLeft R σ P))

/-- Contracting an expanded root recovers the original equation. -/
theorem rootContraction_rootExpansion {s : ℕ} (hs : s ≠ 0)
    (P : MvPolynomial (Option σ) R) :
    rootContraction s (rootExpansion s P) = P := by
  simp only [rootContraction, rootExpansion, AlgEquiv.apply_symm_apply,
    Polynomial.contract_expand s hs, AlgEquiv.symm_apply_apply]

/-- A nonconstant coefficient-coordinate canary: only the root exponent changes. -/
theorem rootContraction_coefficient_canary {s : ℕ} (hs : s ≠ 0) (j : σ) :
    rootContraction s (X (some j) * X none ^ s : MvPolynomial (Option σ) R) =
      X (some j) * X none := by
  have he : rootExpansion s (X (some j) * X none : MvPolynomial (Option σ) R) =
      X (some j) * X none ^ s := by
    apply (optionEquivLeft R σ).injective
    simp [rootExpansion]
  rw [← he, rootContraction_rootExpansion hs]

/-- The coefficient selected by a root contraction. -/
theorem coeff_rootContraction {s : ℕ} (hs : s ≠ 0)
    (P : MvPolynomial (Option σ) R) (m : Option σ →₀ ℕ) :
    coeff m (rootContraction s P) = coeff (m.some.optionElim (m none * s)) P := by
  rw [← optionEquivLeft_coeff_some_coeff_none R σ m, rootContraction,
    AlgEquiv.apply_symm_apply, Polynomial.coeff_contract hs]
  simpa only [Finsupp.some_optionElim, Finsupp.optionElim_apply_none] using
    optionEquivLeft_coeff_some_coeff_none R σ (m.some.optionElim (m none * s)) P

/-- Contracting the root variable does not increase a coefficient-coordinate degree. -/
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

/-- A derivative-zero contraction divides the distinguished degree exactly. -/
theorem degreeOf_rootContraction_none_mul [IsDomain R] (p : ℕ) [CharP R p]
    (hp : p ≠ 0) (P : MvPolynomial (Option σ) R)
    (hder : Polynomial.derivative (optionEquivLeft R σ P) = 0) :
    (rootContraction p P).degreeOf none * p = P.degreeOf none := by
  let : CharP (MvPolynomial σ R) p := charP_of_injective_ringHom (C_injective σ R) p
  have h := congrArg Polynomial.natDegree (Polynomial.expand_contract p hder hp)
  rw [Polynomial.natDegree_expand, natDegree_optionEquivLeft] at h
  rw [← natDegree_optionEquivLeft R, rootContraction, AlgEquiv.apply_symm_apply]
  exact h

end MvPolynomial
