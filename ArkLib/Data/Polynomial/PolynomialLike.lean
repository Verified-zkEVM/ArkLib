/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
  # Polynomial-like structures

  This file defines a generic type class for polynomial-like structures. The goal is to provide a
  generic interface for polynomials, which should be isomorphic to Mathlib's `Polynomial`, but also
  admit other representations that are computation friendly.
-/

universe u v w

/--
A typeclass for polynomial-like structures, being defined by the universal property of polynomial
rings:

`R[X]` is the unique `R`-algebra such that, for every algebra `A` containing `R`, and every element
`a : A`, there is a unique algebra homomorphism from `R[X]` to `A` that fixes `R`, and maps `X` to
`a`.

We can show that any `P` satisfying the `PolynomialLike` typeclass is isomorphic to `R[X]` as an
`R`-algebra, and hence inherit all relevant properties of `R[X]`.

TODO: make sure this universal property is actually correct!

This is slightly less general than `Polynomial` in mathlib, where `R` and `S` are only required to
be a `Semiring` instead of a `CommSemiring`. We need the stronger requirement on `R` and `S` to
ensure the instance `Algebra R P`, and that `eval₂` is a ring homomorphism.
-/
class PolynomialLike (R : outParam (Type u)) [CommSemiring R] (P : Type v) [Semiring P]
    extends Algebra R P where

  /-- The indeterminate `X` of the polynomial ring. -/
  X {R} : P

  /-- The ring homomorphism from `P` to a commutative semiring `S` obtained by evaluating the
  pushforward of `p` along `f` at `x`. -/
  eval₂ {S : Type w} [CommSemiring S] (f : R →+* S) (x : S) : P →+* S

  eval₂_C {r : R} {S : Type w} [CommSemiring S] (f : R →+* S) (x : S) :
    (eval₂ f x) (algebraMap r) = f r

  eval₂_X {S : Type w} [CommSemiring S] (f : R →+* S) (x : S) : eval₂ f x X = x

  eval₂_eq {S : Type w} [CommSemiring S] (f : R →+* S) (g : P →+* S) : g = eval₂ f (g X)

attribute [simp] PolynomialLike.eval₂_C PolynomialLike.eval₂_X PolynomialLike.eval₂_eq

namespace PolynomialLike

variable {R : Type u} [CommSemiring R] {P : Type v} [Semiring P] [PolynomialLike R P]

/-- The constant ring homomorphism from `R` to `P`, obtained from the `Algebra` instance. -/
@[reducible]
def C : R →+* P := algebraMap R P

@[simp]
lemma eval₂_comp_C {S : Type w} [CommSemiring S] (f : R →+* S) (x : S) :
    (eval₂ f x).comp (C : R →+* P) = f := by
  ext; exact eval₂_C _ _

@[simp]
lemma eval₂_eq' {S : Type w} [CommSemiring S] (f : R →+* S) (g : P →+* S) (p : P) :
    g p = eval₂ f (g X) p := by
  rw [eval₂_eq f g]
  simp

/-- `eval₂` as an `AlgHom`. -/
def eval₂AlgHom {A : Type w} {B : Type*} [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (b : B) : P →ₐ[R] B where
  toFun := eval₂ (f.comp (Algebra.ofId R A)) b
  map_one' := by simp
  map_mul' := by simp
  map_zero' := by simp
  map_add' := by simp
  commutes' := by intro r; simp; exact eval₂_C _ _

@[simp]
lemma eval₂AlgHom_apply {A : Type w} {B : Type*} [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (b : B) (p : P) :
    (eval₂AlgHom f b) p = eval₂ (f.comp (Algebra.ofId R A)) b p := by
  simp [eval₂AlgHom]

/-- The (algebra) evaluation map, which is the (unique) `R`-algebra homomorphism from `P` to
any `R`-algebra `A` that sends `X` to a specified element `s : A`. -/
def aeval {A : Type w} [CommSemiring A] [Algebra R A] (s : A) : P →ₐ[R] A :=
  eval₂AlgHom (Algebra.ofId R A) s

lemma aeval_apply {A : Type w} [CommSemiring A] [Algebra R A] (s : A) :
    aeval (P := P) s = eval₂AlgHom (Algebra.ofId R A) s := rfl

@[simp]
lemma aeval_C {A : Type w} [CommSemiring A] [Algebra R A] (x : A) (r : R) :
    (aeval x) (C r : P) = algebraMap R A r := by
  simp [C]

/-- The evaluation of `X` at `s` is `s`. -/
@[simp]
lemma aeval_X {A : Type w} [CommSemiring A] [Algebra R A] (s : A) : aeval s X (P := P) = s := by
  simp [aeval]

/-- Uniqueness: Any `R`-algebra homomorphism `f` from `P` to an `R`-algebra `A` is equal to the
evaluation map at the value of `f X`. -/
@[simp]
lemma aeval_eq {A : Type w} [CommSemiring A] [Algebra R A] (f : P →ₐ[R] A) : f = aeval (f X) := by
  simp only [aeval, eval₂AlgHom, Algebra.comp_ofId, RingHom.mk_coe]
  ext p
  exact eval₂_eq' _ _ _

end PolynomialLike

namespace Polynomial

noncomputable instance {R : Type u} [CommSemiring R] : PolynomialLike R R[X] where
  X := Polynomial.X
  eval₂ := Polynomial.eval₂RingHom
  eval₂_C := Polynomial.eval₂_C
  eval₂_X := Polynomial.eval₂_X
  eval₂_eq f := sorry

end Polynomial

namespace PolynomialLike

open Polynomial

variable {R : Type u} [CommSemiring R] {P : Type w} [Semiring P] [PolynomialLike R P]

/-- The unique `R`-algebra homomorphism from a `PolynomialLike` type `P` to `R[X]`. -/
noncomputable def toPolynomialAlgHom : P →ₐ[R] R[X] := PolynomialLike.aeval Polynomial.X

/-- The unique `R`-algebra homomorphism from `R[X]` to a `PolynomialLike` type `P`. -/
noncomputable def ofPolynomialAlgHom : R[X] →ₐ[R] P := Polynomial.aeval PolynomialLike.X

/--
A `PolynomialLike` type `P` is isomorphic to `R[X]` as an `R`-algebra.
This is the fundamental property ensured by the `PolynomialLike` typeclass.
-/
noncomputable def polynomialAlgEquiv : P ≃ₐ[R] R[X] where
  toFun := toPolynomialAlgHom
  invFun := ofPolynomialAlgHom
  left_inv := by
    intro p
    -- let f := ofPolynomialAlgHom.comp toPolynomialAlgHom
    -- let g := AlgHom.id R P
    sorry
    -- apply DFunLike.congr_fun (PolynomialLike.hom_ext (f := f) (g := g) (by simp [toPolynomialAlgHom, ofPolynomialAlgHom, PolynomialLike.aeval_X]))
  right_inv := by
    intro p;
    -- let f := toPolynomialAlgHom.comp ofPolynomialAlgHom
    -- let g := AlgHom.id R R[X]
    -- apply DFunLike.congr_fun (Polynomial.algHom_ext (f := f) (g := g) (by simp [toPolynomialAlgHom, ofPolynomialAlgHom, PolynomialLike.aeval_X, aeval_X]))
    sorry
  map_mul' := sorry
  map_add' := sorry
  commutes' := sorry

end PolynomialLike
