/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComap

/-!
# Acceptance tests for affine Hilbert functions of pulled-back ideals

The examples pull ideals back along the identity and along the map collapsing two variables to
one, compute the natural degrees of the kernel and of a pulled-back hypersurface, and show that the
dimension count in a quotient needs `g ≠ 0`.
-/

open MvPolynomial

namespace AffineHilbertComapTest

/-- The map `MvPolynomial (Fin 2) ℚ → MvPolynomial (Fin 1) ℚ` sending both variables to `X 0`. -/
noncomputable abbrev collapse : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] MvPolynomial (Fin 1) ℚ :=
  aeval fun _ ↦ X 0

theorem collapse_surjective : Function.Surjective collapse := fun P ↦
  ⟨rename (fun _ ↦ 0) P, by
    have h : ((fun _ ↦ X 0) ∘ fun _ ↦ (0 : Fin 2) : Fin 1 → MvPolynomial (Fin 1) ℚ) = X :=
      funext fun i ↦ by rw [Subsingleton.elim i 0]; rfl
    rw [collapse, aeval_rename, h, aeval_X_left_apply]⟩

/-- The kernel of the collapse has affine Hilbert polynomial of natural degree `1`. -/
example : (affineHilbertPolynomial (RingHom.ker collapse)).natDegree = 1 := by
  rw [natDegree_affineHilbertPolynomial_ker_of_surjective _ collapse_surjective, Nat.card_fin]

/-- Pulled back along the collapse, the hypersurface `X 0 = 0` has affine Hilbert polynomial of
natural degree `0`. -/
example : (affineHilbertPolynomial ((Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}).comap
    collapse)).natDegree = 0 := by
  have h := natDegree_affineHilbertPolynomial_comap_span_singleton_add_one_of_surjective _
    collapse_surjective (X_ne_zero 0) fun htop ↦ by
      rw [Ideal.span_singleton_eq_top] at htop
      simpa using htop.map constantCoeff
  rw [Nat.card_fin] at h
  omega

/-- The pullback of `span {X 0}` along the collapse is the principal cut of the kernel by
`X 0`. -/
example : (Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}).comap collapse =
    RingHom.ker collapse ⊔ Ideal.span {X 0} := by
  have h := Ideal.comap_span_singleton_of_surjective collapse collapse_surjective (X 0)
  rwa [collapse, aeval_X] at h

/-- The minimal primes of a hypersurface pulled back along the collapse have total affine degree at
most its affine degree. -/
example (g : MvPolynomial (Fin 1) ℚ) :
    ∑ Q ∈ ((Ideal.span {g}).comap collapse).minimalPrimesFinset, affineDegree Q ≤
      affineDegree ((Ideal.span {g}).comap collapse) :=
  sum_affineDegree_minimalPrimes_comap_span_singleton_le_of_surjective _ collapse_surjective g

/-- Pulling back along the identity, the affine Hilbert function of an ideal is at most the
dimension of the image of the polynomials of total degree at most `N`. -/
example (I : Ideal (MvPolynomial (Fin 1) ℚ)) (N : ℕ) :
    affineHilbertFunction (I.comap (AlgHom.id ℚ _)) N ≤
      Module.finrank ℚ ((restrictTotalDegree (Fin 1) ℚ N).map
        (Ideal.Quotient.mkₐ ℚ I).toLinearMap) :=
  affineHilbertFunction_comap_le_finrank_map _ I _ fun _ hP ↦
    (mem_restrictTotalDegree _ _ _).mpr hP

/-- `Submodule.finrank_map_mkₐ_span_singleton_add_le` needs `g ≠ 0`: for `g = 0` and
`M = M' = span {1}`, the image of `M` in the quotient has dimension `1`, and `1 + 1 > 1`. -/
example : ¬Module.finrank ℚ ((ℚ ∙ (1 : MvPolynomial (Fin 1) ℚ)).map
      (Ideal.Quotient.mkₐ ℚ (Ideal.span {(0 : MvPolynomial (Fin 1) ℚ)})).toLinearMap) +
      Module.finrank ℚ (ℚ ∙ (1 : MvPolynomial (Fin 1) ℚ)) ≤
    Module.finrank ℚ (ℚ ∙ (1 : MvPolynomial (Fin 1) ℚ)) := by
  have hne : Ideal.Quotient.mkₐ ℚ (Ideal.span {(0 : MvPolynomial (Fin 1) ℚ)}) 1 ≠ 0 := by
    intro h
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at h
    exact one_ne_zero h
  rw [Submodule.map_span, Set.image_singleton, AlgHom.toLinearMap_apply,
    finrank_span_singleton hne, finrank_span_singleton one_ne_zero]
  omega

end AffineHilbertComapTest
