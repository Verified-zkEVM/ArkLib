/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.RootContraction
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.ComputeDegree

/-!
# Acceptance tests for expanding and contracting one variable

The examples cover:

* the monomial computation `rootContraction s (X (some j) * X none ^ s) = X (some j) * X none`;
* evaluation of an expansion at a concrete point;
* contraction by `0` does not undo expansion by `0`, so `s ≠ 0` is needed in
  `rootContraction_rootExpansion`;
* the degree identity for `X (some ()) + X none ^ 2` over `ZMod 2`, and the failure of that
  identity for `X none ^ 3`, whose partial derivative in `none` is nonzero.
-/

open MvPolynomial

section Monomial

variable {R σ : Type*} [CommSemiring R]

/-- Expanding `X (some j) * X none` by `s` gives `X (some j) * X none ^ s`. -/
private theorem rootExpansion_X_some_mul_X_none (s : ℕ) (j : σ) :
    rootExpansion s (X (some j) * X none : MvPolynomial (Option σ) R) =
      X (some j) * X none ^ s := by
  apply (optionEquivLeft R σ).injective
  simp [rootExpansion, optionEquivLeft_X_some, optionEquivLeft_X_none]

/-- Contracting `X (some j) * X none ^ s` by `s ≠ 0` gives `X (some j) * X none`. -/
example {s : ℕ} (hs : s ≠ 0) (j : σ) :
    rootContraction s (X (some j) * X none ^ s : MvPolynomial (Option σ) R) =
      X (some j) * X none := by
  rw [← rootExpansion_X_some_mul_X_none, rootContraction_rootExpansion hs]

/-- Evaluating the expansion of `X (some j) * X none` by `s` at `(x, y)` gives `x j * y ^ s`. -/
example (s : ℕ) (j : σ) (x : σ → R) (y : R) :
    eval (fun i ↦ Option.elim i y x)
        (rootExpansion s (X (some j) * X none : MvPolynomial (Option σ) R)) = x j * y ^ s := by
  rw [eval_rootExpansion]
  simp

example :
    map (Int.castRingHom ℚ)
        (rootExpansion 2
          (monomial (Finsupp.single none 2 + Finsupp.single (some ()) 1) 7 :
            MvPolynomial (Option Unit) ℤ)) =
      (monomial (Finsupp.single none 4 + Finsupp.single (some ()) 1) (7 : ℚ) :
        MvPolynomial (Option Unit) ℚ) := by
  rw [map_rootExpansion]
  apply (optionEquivLeft ℚ Unit).injective
  simp [rootExpansion, optionEquivLeft_monomial, Polynomial.expand_monomial]

example :
    eval₂ (Int.castRingHom ℚ) (fun o : Option Unit => o.elim 2 (fun _ => 3))
        (rootExpansion 2
          (monomial (Finsupp.single none 2 + Finsupp.single (some ()) 1) 7 :
            MvPolynomial (Option Unit) ℤ)) = 336 := by
  rw [eval₂_rootExpansion]
  norm_num

end Monomial

/-- The hypothesis `s ≠ 0` is needed in `rootContraction_rootExpansion`: expansion by `0` sends
`X none` to `1`, and contraction by `0` fixes `1`. -/
example :
    rootContraction 0 (rootExpansion 0 (X none : MvPolynomial (Option Unit) ℚ)) ≠ X none := by
  intro h
  have h' := congrArg (optionEquivLeft ℚ Unit) h
  simp only [rootContraction, rootExpansion, AlgEquiv.apply_symm_apply,
    optionEquivLeft_X_none, Polynomial.expand_X, pow_zero] at h'
  rw [← Polynomial.C_1, Polynomial.contract_C] at h'
  have := congrArg Polynomial.natDegree h'
  simp at this

/-- Over `ZMod 2`, `X (some ()) + X none ^ 2` has vanishing partial derivative in `none`, and its
contraction by `2` has degree `1` in `none`. -/
example :
    (rootContraction 2 (X (some ()) + X none ^ 2 : MvPolynomial (Option Unit) (ZMod 2))).degreeOf
      none = 1 := by
  have hder : pderiv none (X (some ()) + X none ^ 2 : MvPolynomial (Option Unit) (ZMod 2)) = 0 := by
    simp [pderiv_X, show (2 : MvPolynomial (Option Unit) (ZMod 2)) = 0 from
      CharP.ofNat_eq_zero _ 2]
  have hdeg :
      (X (some ()) + X none ^ 2 : MvPolynomial (Option Unit) (ZMod 2)).degreeOf none = 2 := by
    rw [← natDegree_optionEquivLeft, map_add, map_pow, optionEquivLeft_X_some,
      optionEquivLeft_X_none]
    compute_degree!
  have h := degreeOf_rootContraction_none_mul 2 two_ne_zero _ hder
  omega

/-- The hypothesis on the partial derivative is needed in `degreeOf_rootContraction_none_mul`:
over `ZMod 2`, contracting `X none ^ 3` by `2` gives `0`, whose degree times `2` is not `3`. -/
example :
    (rootContraction 2 (X none ^ 3 : MvPolynomial (Option Unit) (ZMod 2))).degreeOf none * 2 ≠
      (X none ^ 3 : MvPolynomial (Option Unit) (ZMod 2)).degreeOf none := by
  have hzero : rootContraction 2 (X none ^ 3 : MvPolynomial (Option Unit) (ZMod 2)) = 0 := by
    apply (optionEquivLeft (ZMod 2) Unit).injective
    simp only [rootContraction, AlgEquiv.apply_symm_apply, map_pow, optionEquivLeft_X_none,
      map_zero]
    ext n
    rw [Polynomial.coeff_contract two_ne_zero, Polynomial.coeff_X_pow, Polynomial.coeff_zero]
    split_ifs with hn
    · omega
    · rfl
  rw [hzero, degreeOf_zero, degreeOf_X_self_pow]
  omega
