/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpen
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Acceptance tests for points of principal open subsets

These examples use the public API through an ordinary import, with `K` the algebraic closure of
`ℚ`. The line minus the origin, cut out of `V(⊥)` by `x`, is infinite because `⊥` has Hilbert
polynomial of natural degree `1`. For `s = 0` the principal open subset is empty although `⊥`
has natural degree `1`, so regularity is needed. The source statement, for a prime ideal and
`s ∉ P`, is derived and applied to the kernel of evaluation at the point `1`, whose principal
open subset cut out by `x` is that single point.
-/

open MvPolynomial

namespace PrincipalOpenTest

local notation "K" => AlgebraicClosure ℚ

local notation "B" => (⊥ : Ideal (MvPolynomial (Fin 1) K))

/-- The class of `x` is regular on the domain `K[x] ⧸ ⊥`. -/
theorem isLeftRegular_X : IsLeftRegular (Ideal.Quotient.mk B (X 0)) :=
  IsLeftCancelMulZero.mul_left_cancel_of_ne_zero fun h ↦
    X_ne_zero (0 : Fin 1) ((Submodule.mem_bot _).mp (Ideal.Quotient.eq_zero_iff_mem.mp h))

/-- The line minus the origin is infinite: the Hilbert polynomial of `⊥` has natural degree `1`.
-/
example :
    {x : Fin 1 → K | x ∈ zeroLocus K B ∧ aeval x (X 0 : MvPolynomial (Fin 1) K) ≠ 0}.Infinite := by
  intro hfin
  have h := (finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero
    isLeftRegular_X).mp hfin
  simp at h

/-- Regularity is needed in the forward direction: the principal open subset cut out by `0` is
empty, hence finite, but the Hilbert polynomial of `⊥` has natural degree `1`. -/
example :
    {x : Fin 1 → K | x ∈ zeroLocus K B ∧ aeval x (0 : MvPolynomial (Fin 1) K) ≠ 0}.Finite ∧
    (affineHilbertPolynomial B).natDegree ≠ 0 := by
  refine ⟨Set.Finite.subset Set.finite_empty fun x hx ↦ hx.2 (map_zero _), ?_⟩
  simp

/-- The zeros of the presentation ideal of `K[x]` localized away from `x` are the points `z` with
`z none * z (some 0) = 1`; forgetting `z none` gives the nonzero points of the line. -/
example (x : Fin 1 → K) (hx : x 0 ≠ 0) :
    x ∈ (fun z : Option (Fin 1) → K ↦ z ∘ some) ''
      zeroLocus K (awayPresentationIdeal B (X 0)) := by
  rw [image_comp_some_zeroLocus_awayPresentationIdeal]
  exact ⟨by simp, by simpa using hx⟩

/-! ### Source-shaped statement -/

/-- The source's `hilbertPolynomial_natDegree_zero_of_finite_principalOpen`, for a prime `P` and
`s ∉ P`. -/
theorem natDegree_eq_zero_of_finite_principalOpen {k σ : Type*} [Field k] [IsAlgClosed k]
    [Finite σ] {P : Ideal (MvPolynomial σ k)} (hP : P.IsPrime) {s : MvPolynomial σ k}
    (hs : s ∉ P) (hfinite : {x | x ∈ zeroLocus k P ∧ aeval x s ≠ 0}.Finite) :
    (affineHilbertPolynomial P).natDegree = 0 :=
  have := hP
  (finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero
    (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
      (mt Ideal.Quotient.eq_zero_iff_mem.mp hs))).mp hfinite

/-- The kernel of evaluation at the point `1` is a prime ideal not containing `x`; its principal
open subset cut out by `x` is the single point `1`, so it has dimension zero. -/
example : (affineHilbertPolynomial
    (RingHom.ker (aeval (R := K) (fun _ : Fin 1 ↦ (1 : K))))).natDegree = 0 := by
  refine natDegree_eq_zero_of_finite_principalOpen (RingHom.ker_isPrime _)
    (s := X 0) (by simp) (Set.Subsingleton.finite fun x hx y hy ↦ ?_)
  have hpt : ∀ z ∈ zeroLocus K (RingHom.ker (aeval (R := K) (fun _ : Fin 1 ↦ (1 : K)))),
      z = fun _ ↦ 1 := fun z hz ↦ by
    have h := hz (X 0 - C 1) (by simp [RingHom.mem_ker])
    funext i
    rw [Subsingleton.elim i 0]
    simpa [sub_eq_zero] using h
  rw [hpt x hx.1, hpt y hy.1]

end PrincipalOpenTest
