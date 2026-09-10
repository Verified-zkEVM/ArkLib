/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.GraphPullback
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Counting polynomial graphs on a plane hypersurface

Distinct polynomial graphs lying on a nonzero plane equation are bounded by its degree
in the graph coordinate. This includes inseparable parameterizations without a degree
factor for the retained parameter.
-/

@[expose] public section

noncomputable section

namespace AffineHilbert

open MvPolynomial

variable {F : Type*} [Field F]

/-- View a plane equation as a polynomial in its jet coordinate. -/
def oneJetRootPolynomial (g : MvPolynomial (Option (Fin 1)) F) :
    Polynomial (MvPolynomial (Fin 1) F) :=
  optionEquivLeft F (Fin 1)
    (renameEquiv F (Equiv.swap none (some 0)) g)

/-- Swapping the two coordinates makes the outer degree exactly the jet degree. -/
theorem natDegree_oneJetRootPolynomial (g : MvPolynomial (Option (Fin 1)) F) :
    (oneJetRootPolynomial g).natDegree = g.degreeOf (some 0) := by
  rw [oneJetRootPolynomial, natDegree_optionEquivLeft]
  simpa only [renameEquiv_apply, Equiv.swap_apply_right] using
    degreeOf_rename_of_injective (p := g)
      (Equiv.swap none (some (0 : Fin 1))).injective (some 0)

/-- Graph pullback is evaluation of the same equation in its jet variable. -/
theorem eval_oneJetRootPolynomial (g : MvPolynomial (Option (Fin 1)) F)
    (q : Polynomial F) :
    uniqueAlgEquiv F (Fin 1)
      ((oneJetRootPolynomial g).eval ((uniqueAlgEquiv F (Fin 1)).symm q)) =
      polynomialGraphPullback (fun _ : Fin 1 ↦ q) g := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [oneJetRootPolynomial, polynomialGraphPullback]
  | add g h hg hh =>
    simp only [oneJetRootPolynomial, map_add, Polynomial.eval_add] at *
    exact congrArg₂ (· + ·) hg hh
  | mul_X g i hg =>
    cases i with
    | none =>
      simpa [oneJetRootPolynomial, polynomialGraphPullback] using
        congrArg (· * Polynomial.X) hg
    | some i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [oneJetRootPolynomial, map_mul, renameEquiv_apply, rename_X,
        Equiv.swap_apply_right, optionEquivLeft_X_none, Polynomial.eval_mul,
        Polynomial.eval_X, polynomialGraphPullback, aeval_X, Option.elim_some] at hg ⊢
      rw [AlgEquiv.apply_symm_apply, hg]

/-- A finite family of distinct polynomial graphs on a plane hypersurface is bounded by
its jet degree, independently of the degrees of the graph parameterizations. -/
theorem polynomialGraphs_card_le_degreeOf (g : MvPolynomial (Option (Fin 1)) F)
    (hg : g ≠ 0) (graphs : Finset (Polynomial F))
    (hgraphs : ∀ q ∈ graphs, polynomialGraphPullback (fun _ : Fin 1 ↦ q) g = 0) :
    graphs.card ≤ g.degreeOf (some 0) := by
  classical
  let roots := graphs.image (uniqueAlgEquiv F (Fin 1)).symm
  have hnonzero : oneJetRootPolynomial g ≠ 0 := by
    intro hz
    apply hg
    apply (renameEquiv F (Equiv.swap none (some (0 : Fin 1)))).injective
    apply (optionEquivLeft F (Fin 1)).injective
    simpa only [oneJetRootPolynomial, map_zero] using hz
  have hroots : roots.val ⊆ (oneJetRootPolynomial g).roots := by
    intro u hu
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
    apply (Polynomial.mem_roots hnonzero).mpr
    apply (uniqueAlgEquiv F (Fin 1)).injective
    rw [map_zero, eval_oneJetRootPolynomial]
    exact hgraphs q hq
  have hcard := Polynomial.card_le_degree_of_subset_roots hroots
  rw [natDegree_oneJetRootPolynomial] at hcard
  simpa only [roots, Finset.card_image_of_injective _
    (uniqueAlgEquiv F (Fin 1)).symm.injective] using hcard

/-- A purely inseparable graph still counts as one graph, even when its parameter degree
is arbitrarily large. This canary works in positive characteristic as well as zero. -/
theorem polynomialGraphs_frobenius_canary (s : ℕ) (hs : 0 < s)
    (graphs : Finset (Polynomial F))
    (hgraphs : ∀ q ∈ graphs, polynomialGraphPullback (fun _ : Fin 1 ↦ q)
      (X (some 0) - X none ^ s) = 0) : graphs.card ≤ 1 := by
  have hg : (X (some 0) - X none ^ s : MvPolynomial (Option (Fin 1)) F) ≠ 0 := by
    intro hz
    have heval := congrArg (aeval (fun i : Option (Fin 1) ↦ i.elim 0 (fun _ ↦ (1 : F)))) hz
    simp [ne_of_gt hs] at heval
  apply (polynomialGraphs_card_le_degreeOf _ hg graphs hgraphs).trans
  apply (degreeOf_sub_le _ _ _).trans
  apply max_le
  · simp
  · rw [degreeOf_X_pow_of_ne s (by simp : (some (0 : Fin 1)) ≠ none)]
    omega

end AffineHilbert
