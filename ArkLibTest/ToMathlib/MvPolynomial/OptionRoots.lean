/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.OptionRoots
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Acceptance tests for roots in a distinguished variable

* On the plane curve `y ^ 2 = t ^ 2` over `ℚ`, at most two polynomials `q` satisfy
  `q ^ 2 = X ^ 2`, and `X` and `-X` do.
* Injectivity of `aeval φ` is needed in `card_le_degreeOf_none_of_aeval_eq_zero`: for
  `g = X (some ()) * X none` and `φ = 0`, the two values `0` and `1` are roots, while
  `g.degreeOf none = 1`.
* Over a field `F`, polynomial graphs on a nonzero plane equation in `Option (Fin 1)` number at
  most its degree in the graph coordinate `X (some 0)`.
* On the curve `y = t ^ s`, at most one polynomial graph lies, for every `s` and in every
  characteristic, although the graph `X ^ s` has degree `s`.
-/

open MvPolynomial
open scoped Polynomial

namespace OptionRootsTest

/-- At most two polynomials `q` over `ℚ` satisfy `q ^ 2 = X ^ 2`. -/
example (Q : Finset ℚ[X])
    (hQ : ∀ q ∈ Q, aeval (fun o : Option (Fin 1) ↦ o.elim Polynomial.X fun _ ↦ q)
      (X (some 0) ^ 2 - X none ^ 2 : MvPolynomial (Option (Fin 1)) ℚ) = 0) :
    Q.card ≤ 2 := by
  have hg : (X (some 0) ^ 2 - X none ^ 2 : MvPolynomial (Option (Fin 1)) ℚ) ≠ 0 := by
    intro h
    have := congrArg (aeval fun o : Option (Fin 1) ↦ o.elim (0 : ℚ) fun _ ↦ 1) h
    simp at this
  refine (card_le_degreeOf_some_of_aeval_eq_zero hg Q hQ).trans ?_
  refine (degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · exact (degreeOf_pow_le _ _ _).trans (by simp)
  · simp [degreeOf_X_pow_of_ne]

/-- The two graphs `X` and `-X` lie on `y ^ 2 = t ^ 2`. -/
example : ∀ q ∈ ({Polynomial.X, -Polynomial.X} : Finset ℚ[X]),
    aeval (fun o : Option (Fin 1) ↦ o.elim Polynomial.X fun _ ↦ q)
      (X (some 0) ^ 2 - X none ^ 2 : MvPolynomial (Option (Fin 1)) ℚ) = 0 := by
  simp

/-- Injectivity of `aeval φ` is needed in `card_le_degreeOf_none_of_aeval_eq_zero`. For
`σ = Unit`, `φ = 0` and `g = X (some ()) * X none`, both `0` and `1` are roots, but
`g.degreeOf none ≤ 1`. -/
example :
    let g : MvPolynomial (Option Unit) ℚ := X (some ()) * X none
    g ≠ 0 ∧ (∀ y ∈ ({0, 1} : Finset ℚ), aeval (fun o ↦ o.elim y fun _ ↦ (0 : ℚ)) g = 0) ∧
      ¬ ({0, 1} : Finset ℚ).card ≤ g.degreeOf none := by
  intro g
  refine ⟨mul_ne_zero (X_ne_zero _) (X_ne_zero _), by simp [g], fun h ↦ ?_⟩
  have hdeg : g.degreeOf none ≤ 1 :=
    (degreeOf_mul_le _ _ _).trans (by simp [degreeOf_X])
  have hcard : ({0, 1} : Finset ℚ).card = 2 := by decide
  omega

/-- Polynomial graphs on a plane equation over a field, in the original coordinates:
parameter `X none` and graph coordinate `X (some 0)`. -/
theorem card_polynomialGraphs_le_degreeOf {F : Type*} [Field F]
    (g : MvPolynomial (Option (Fin 1)) F) (hg : g ≠ 0) (graphs : Finset F[X])
    (hgraphs : ∀ q ∈ graphs, aeval (fun i : Option (Fin 1) ↦ i.elim Polynomial.X
      fun _ ↦ q) g = 0) :
    graphs.card ≤ g.degreeOf (some 0) :=
  card_le_degreeOf_some_of_aeval_eq_zero hg graphs hgraphs

/-- At most one polynomial graph lies on `y = t ^ s`, for every `s` and every field. -/
theorem card_polynomialGraphs_le_one_of_frobenius {F : Type*} [Field F] (s : ℕ)
    (graphs : Finset F[X])
    (hgraphs : ∀ q ∈ graphs, aeval (fun i : Option (Fin 1) ↦ i.elim Polynomial.X
      fun _ ↦ q) (X (some 0) - X none ^ s : MvPolynomial (Option (Fin 1)) F) = 0) :
    graphs.card ≤ 1 := by
  have hg : (X (some 0) - X none ^ s : MvPolynomial (Option (Fin 1)) F) ≠ 0 := by
    intro h
    have := congrArg (aeval fun o : Option (Fin 1) ↦ o.elim (0 : F) fun _ ↦ 0 ^ s + 1) h
    simp at this
  refine (card_polynomialGraphs_le_degreeOf _ hg graphs hgraphs).trans ?_
  refine (degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · simp
  · simp [degreeOf_X_pow_of_ne]

end OptionRootsTest
