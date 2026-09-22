/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AwayPresentation
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.FiniteZeroLocus

/-!
# Points of a principal open subset of an affine zero locus

Let `k` be a field, `I` an ideal of `MvPolynomial σ k` and `s` a polynomial. The points of the
principal open subset of the zero locus of `I` cut out by `s` are the zeros `x` of `I` with
`s(x) ≠ 0`. Over any field extension `K` of `k`, forgetting the last coordinate is a bijection
from the zero locus of the presentation ideal `awayPresentationIdeal I s` in `K ^ Option σ` onto
this principal open subset; the inverse sets the new coordinate to `s(x)⁻¹`.

Over an algebraically closed field `k`, with `σ` finite and the class of `s` a non-zero-divisor on
`MvPolynomial σ k ⧸ I`, the principal open subset is finite exactly when the Hilbert polynomial of
`I` has natural degree zero. The presentation ideal has a finite zero locus, so its Hilbert
polynomial has natural degree zero
(`finite_zeroLocus_iff_natDegree_affineHilbertPolynomial_eq_zero`), and the Hilbert polynomial
of `I` has no larger natural degree (`natDegree_affineHilbertPolynomial_le_awayPresentationIdeal`).

## Main statements

* `MvPolynomial.image_comp_some_zeroLocus_awayPresentationIdeal`,
  `MvPolynomial.injOn_comp_some_zeroLocus_awayPresentationIdeal`: the bijection with the principal
  open subset.
* `MvPolynomial.finite_zeroLocus_awayPresentationIdeal_iff`: finiteness transfers along it.
* `MvPolynomial.finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero`: a principal
  open subset cut out by a regular element is finite exactly in dimension zero.

## References

Ported from `ArkLib/ToMathlib/AlgebraicGeometry/PrincipalOpen/Finite.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace `AffineHilbert`.

The source's `hilbertPolynomial_natDegree_zero_of_finite_principalOpen` assumed that `I` is prime
and `s ∉ I`. It is the forward direction of
`finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero`, which assumes only that the
class of `s` is a non-zero-divisor on the quotient; the reverse direction is new and needs no
regularity. The source's private `restrictAwayPoint` lemmas become
`image_comp_some_zeroLocus_awayPresentationIdeal` and
`injOn_comp_some_zeroLocus_awayPresentationIdeal`, stated for points in any field extension `K`
and now including surjectivity onto the principal open subset. The source's definition
`principalOpenZeroLocus P s` is not introduced; the set is written
`{x | x ∈ zeroLocus k I ∧ aeval x s ≠ 0}`.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K]

/-- The zeros of the presentation ideal of the localization away from `s`, with the last
coordinate forgotten, are exactly the zeros `x` of `I` with `s(x) ≠ 0`, for points in any field
extension `K` of `k`.

A zero `z` of the presentation ideal restricts to a zero of `I`, and the relation
`X none * s - 1` gives `z none * s(z ∘ some) = 1`. Conversely, evaluation at a zero `x` of `I`
with `s(x) ≠ 0` factors through the localization, and the extended point with last coordinate
`s(x)⁻¹` is the evaluation of the presentation there. -/
theorem image_comp_some_zeroLocus_awayPresentationIdeal (I : Ideal (MvPolynomial σ k))
    (s : MvPolynomial σ k) :
    (fun z : Option σ → K ↦ z ∘ some) '' zeroLocus K (awayPresentationIdeal I s) =
      {x | x ∈ zeroLocus K I ∧ aeval x s ≠ 0} := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hrel := hz _ (X_none_mul_rename_some_sub_one_mem_awayPresentationIdeal I s)
    rw [map_sub, map_mul, aeval_X, aeval_rename, map_one, sub_eq_zero] at hrel
    refine ⟨fun p hp ↦ ?_, right_ne_zero_of_mul_eq_one hrel⟩
    rw [← aeval_rename]
    exact hz _ (rename_some_mem_awayPresentationIdeal I s hp)
  · rintro ⟨hx, hs⟩
    let ev : (MvPolynomial σ k ⧸ I) →ₐ[k] K := Ideal.Quotient.liftₐ I (aeval x) hx
    have hev : ∀ p, ev (Ideal.Quotient.mk I p) = aeval x p := fun _ ↦ rfl
    have hunit : ∀ y : Submonoid.powers (Ideal.Quotient.mk I s), IsUnit (ev y) := by
      rintro ⟨_, n, rfl⟩
      simpa [hev] using (Ne.isUnit hs).pow n
    let f : Localization.Away (Ideal.Quotient.mk I s) →ₐ[k] K :=
      IsLocalization.liftAlgHom hunit
    have hf : ∀ a, f (algebraMap _ _ a) = ev a := fun a ↦ IsLocalization.lift_eq hunit a
    refine ⟨fun o ↦ o.elim (aeval x s)⁻¹ x, fun p hp ↦ ?_, rfl⟩
    have hcomp : f.comp (awayPresentation I s) = aeval fun o ↦ o.elim (aeval x s)⁻¹ x := by
      refine algHom_ext fun o ↦ ?_
      cases o with
      | none =>
        rw [AlgHom.comp_apply, awayPresentation_X_none, aeval_X]
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← hev, ← hf, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
      | some i =>
        rw [AlgHom.comp_apply, awayPresentation_X_some, hf, hev, aeval_X, aeval_X]
        rfl
    rw [← hcomp, AlgHom.comp_apply, (mem_awayPresentationIdeal I s).mp hp, map_zero]

/-- Forgetting the last coordinate is injective on the zeros of the presentation ideal: the
relation `X none * s - 1` determines the last coordinate as `s(z ∘ some)⁻¹`. -/
theorem injOn_comp_some_zeroLocus_awayPresentationIdeal (I : Ideal (MvPolynomial σ k))
    (s : MvPolynomial σ k) :
    Set.InjOn (fun z : Option σ → K ↦ z ∘ some) (zeroLocus K (awayPresentationIdeal I s)) := by
  intro z hz w hw hzw
  have hrel : ∀ v ∈ zeroLocus K (awayPresentationIdeal I s),
      v none * aeval (v ∘ some) s = 1 := fun v hv ↦ by
    have h := hv _ (X_none_mul_rename_some_sub_one_mem_awayPresentationIdeal I s)
    rwa [map_sub, map_mul, aeval_X, aeval_rename, map_one, sub_eq_zero] at h
  funext o
  cases o with
  | none =>
    have hz' := hrel z hz
    have hw' := hrel w hw
    simp only at hzw
    rw [hzw] at hz'
    exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one hw') (hz'.trans hw'.symm)
  | some i => exact congrFun hzw i

/-- The zero locus of the presentation ideal is finite exactly when the principal open subset
`{x ∈ zeroLocus K I | s(x) ≠ 0}` is finite. -/
theorem finite_zeroLocus_awayPresentationIdeal_iff (I : Ideal (MvPolynomial σ k))
    (s : MvPolynomial σ k) :
    (zeroLocus K (awayPresentationIdeal I s)).Finite ↔
      {x : σ → K | x ∈ zeroLocus K I ∧ aeval x s ≠ 0}.Finite := by
  rw [← image_comp_some_zeroLocus_awayPresentationIdeal,
    Set.finite_image_iff (injOn_comp_some_zeroLocus_awayPresentationIdeal I s)]

/-- Over an algebraically closed field `k`, if the class of `s` is a non-zero-divisor on
`MvPolynomial σ k ⧸ I`, the principal open subset `{x ∈ zeroLocus k I | s(x) ≠ 0}` is finite
exactly when the Hilbert polynomial of `I` has natural degree zero.

If the principal open subset is finite, so is the zero locus of the presentation ideal, whose
Hilbert polynomial then has natural degree zero; regularity of `s` bounds the natural degree for
`I` by it. Conversely, natural degree zero makes the whole zero locus of `I` finite, without any
hypothesis on `s`. Regularity is needed for the forward direction: for `I = ⊥` in one variable and
`s = 0` the principal open subset is empty, but the Hilbert polynomial has natural degree `1`. -/
theorem finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero [IsAlgClosed k]
    [Finite σ] {I : Ideal (MvPolynomial σ k)} {s : MvPolynomial σ k}
    (hs : IsLeftRegular (Ideal.Quotient.mk I s)) :
    {x : σ → k | x ∈ zeroLocus k I ∧ aeval x s ≠ 0}.Finite ↔
      (affineHilbertPolynomial I).natDegree = 0 := by
  constructor
  · intro hfin
    have hK := (finite_zeroLocus_iff_natDegree_affineHilbertPolynomial_eq_zero _).mp
      ((finite_zeroLocus_awayPresentationIdeal_iff I s).mpr hfin)
    exact Nat.eq_zero_of_le_zero
      (hK ▸ natDegree_affineHilbertPolynomial_le_awayPresentationIdeal hs)
  · intro h
    exact ((finite_zeroLocus_iff_natDegree_affineHilbertPolynomial_eq_zero I).mpr h).subset
      fun _ hx ↦ hx.1

end MvPolynomial
