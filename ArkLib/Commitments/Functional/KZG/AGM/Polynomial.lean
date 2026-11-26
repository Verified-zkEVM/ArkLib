/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.Basic
public import CompPoly.Univariate.Roots.Correctness

/-!
# KZG algebraic opening polynomials

An inconsistent accepted opening supplies a nonzero polynomial vanishing at the trapdoor.
The executable finite-field backend supplies the required complete root finder.

References: [KZG10TR]; Fuchsbauer, Kiltz, and Loss, *The Algebraic Group Model and its
Applications*, CRYPTO 2018.
-/

@[expose] public section

open CompPoly

namespace KZG.AGM

variable {F : Type} [Field F] [DecidableEq F] {n : ℕ}

/-- The polynomial equation imposed by an explained opening. -/
def openingPolynomial (f q : Fin (n + 1) → F) (z v : F) : CPolynomial F :=
  CPolynomial.ofFn f - CPolynomial.C v -
    CPolynomial.ofFn q * (CPolynomial.X - CPolynomial.C z)

@[simp] theorem eval_openingPolynomial (f q : Fin (n + 1) → F) (z v a : F) :
    (openingPolynomial f q z v).eval a = evaluate f a - v - evaluate q a * (a - z) := by
  simp [openingPolynomial, evaluate, CPolynomial.eval_sub, CPolynomial.eval_mul,
    CPolynomial.eval_C, CPolynomial.eval_X]

/-- An opening inconsistent with the extracted coefficients gives a nonzero polynomial. -/
theorem openingPolynomial_ne_zero (f q : Fin (n + 1) → F) (z v : F)
    (h : v ≠ evaluate f z) : openingPolynomial f q z v ≠ 0 := by
  intro hz
  have := congrArg (CPolynomial.eval z) hz
  simp only [eval_openingPolynomial, sub_self, mul_zero, sub_zero,
    CPolynomial.eval_zero] at this
  exact h (sub_eq_zero.mp this).symm

variable {G₁ G₂ Gₜ : Type} [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]

/-- Bilinearity makes an inconsistent accepted algebraic opening a nonzero root equation.
No generation or surjectivity assumption on either source group is used. -/
theorem accepted_opening_root {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (he : e g₁ g₂ ≠ 0) (f q : Fin (n + 1) → F) (τ z v : F)
    (haccept : verifyOpening e g₁ (verifierKey g₂ τ)
      (commit (committerKey g₁ τ n) f) z v (commit (committerKey g₁ τ n) q) = true)
    (hbad : v ≠ evaluate f z) :
    openingPolynomial f q z v ≠ 0 ∧ (openingPolynomial f q z v).eval τ = 0 := by
  refine ⟨openingPolynomial_ne_zero f q z v hbad, ?_⟩
  have h := of_decide_eq_true haccept
  simp only [commit_committerKey, verifierKey, Matrix.cons_val_zero, Matrix.cons_val_one,
    ← sub_smul, map_smul, LinearMap.smul_apply, smul_smul] at h
  have hs := (smul_left_injective F he) h
  rw [eval_openingPolynomial, sub_eq_zero]
  simpa only [mul_comm] using hs

/-- CompPoly's executable finite-field roots satisfy the completeness contract used by KZG. -/
theorem rootsInFiniteField_complete
    (ctx : CPolynomial.Roots.FiniteField.FiniteFieldContext F)
    (splitter : CPolynomial.Roots.FiniteField.LinearFactorProductSplitter F)
    (splitterValid : ∀ {p : CPolynomial F}, p ≠ 0 →
      splitter.validInput ctx.q (CPolynomial.Roots.FiniteField.finiteFieldRootProduct ctx p)) :
    ∀ p : CPolynomial F, p ≠ 0 → ∀ a : F, p.eval a = 0 →
      a ∈ (CPolynomial.Roots.FiniteField.rootsInFiniteField ctx splitter p).toList := by
  intro p hp a ha
  exact CPolynomial.Roots.FiniteField.rootsInFiniteField_complete ctx splitter splitterValid hp ha

end KZG.AGM
