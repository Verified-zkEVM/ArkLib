/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
  # Experimental API for `Polynomial`-like structures

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

This is slightly less general than `Polynomial` in mathlib, since we put `R`,`S`,`P` to all be
`CommSemiring` instead of just `Semiring`. We need the stronger requirement on `R` and `S` to ensure
the instance `Algebra R P`, and that `eval₂` is a ring homomorphism.

TODO: make sure this universal property is actually correct! Currently there are several issues:
  - Does this actually lead to a unique `R`-algebra isomorphism `P ≃ₐ[R] R[X]`?
  - How to define coefficients and hence degree?
-/
class PolynomialLike (R : outParam (Type u)) [CommSemiring R] (P : Type v) [CommSemiring P]
    extends Algebra R P where

  /-- The indeterminate `X` of the polynomial ring. -/
  X {R} : P

  /-- The ring homomorphism from `P` to a commutative semiring `S` obtained by evaluating the
  pushforward of `p` along `f` at `x`. -/
  eval₂ {S : Type w} [CommSemiring S] (f : R →+* S) (x : S) : P →+* S

  eval₂_C {r : R} {S : Type w} [CommSemiring S] (f : R →+* S) (x : S) :
    (eval₂ f x) (_root_.algebraMap R P r) = f r

  eval₂_X {S : Type w} [CommSemiring S] (f : R →+* S) (x : S) : eval₂ f x X = x

  eval₂_eq {S : Type w} [CommSemiring S] (g : P →+* S) :
    g = eval₂ (g.comp (Algebra.ofId R P)) (g X)

/--
A custom coefficient function for a `PolynomialLike` type.

We always have a default implementation of `coeff` via first (uniquely) mapping to `Polynomial`,
then using `Polynomial.coeffs`, but this is noncomputable, and we often want to define computable
versions of `coeff` for specific `PolynomialLike` types.
-/
class PolynomialLike.LawfulCoeff (R : Type u) [CommSemiring R] (P : Type v) [CommSemiring P]
    [PolynomialLike R P] (coeff : P → ℕ → R) where
  coeff_finite (p : P) : Set.Finite {n | coeff p n ≠ 0}
  -- more conditions here

  -- /-- A finite set of indices of non-zero coefficients. -/
  -- support (p : P) : Finset ℕ
  -- /-- The `support` of a polynomial is the set of indices of its non-zero coefficients. -/
  -- mem_support_iff (p : P) (n : ℕ) : n ∈ support p ↔ coeff p n ≠ 0
  -- /-- The evaluation of a polynomial is given by the sum of its coefficients.
  -- This is the crucial axiom that connects the coefficient view with the universal property. -/
  -- eval₂_eq_sum {S : Type w} [CommSemiring S] (f : R →+* S) (x : S) (p : P) :
  --   eval₂ f x p = ∑ n ∈ support p, f (coeff p n) * x ^ n

attribute [simp] PolynomialLike.eval₂_C PolynomialLike.eval₂_X

namespace PolynomialLike

variable {R : Type u} [CommSemiring R] {P : Type v} [CommSemiring P] [PolynomialLike R P]

/-- The constant ring homomorphism from `R` to `P`, obtained from the `Algebra` instance. -/
@[reducible]
def C : R →+* P := algebraMap R P

/-- The monomial `C r * X ^ n` in `P`. -/
def monomial (n : ℕ) (r : R) : P := C r * X ^ n

@[simp]
lemma eval₂_C' {r : R} {S : Type w} [CommSemiring S] (f : R →+* S) (x : S) :
    eval₂ (P := P) f x (C r) = f r := by
  simp [C]

lemma eval₂_f_eq_C (r : R) (x : P) : eval₂ (P := P) (C : R →+* P) x (C r) = C r := by simp

@[simp]
lemma eval₂_comp_C {S : Type w} [CommSemiring S] (f : R →+* S) (x : S) :
    (eval₂ f x).comp (C : R →+* P) = f := by
  ext; exact eval₂_C _ _

lemma eval₂_eq' {S : Type w} [CommSemiring S] (g : P →+* S) (p : P) :
    g p = eval₂ (g.comp (Algebra.ofId R P)) (g X) p := by
  nth_rw 1 [eval₂_eq g]

@[simp]
lemma eval₂_monomial {S : Type w} [CommSemiring S] (f : R →+* S) (x : S) (n : ℕ) (r : R) :
    eval₂ (P := P) f x (monomial n r) = f r * x ^ n := by
  simp [monomial]

/-- `eval₂` is determined by its values on `C` and `X`. -/
lemma eval₂_induction_on : True := sorry

lemma C_injective : Function.Injective (C : R → P) := by
  intro r₁ r₂ h
  -- rw [← eval₂_f_eq_C (P := P) r₁]
  sorry

#print Polynomial.eval₂RingHom'

#print Polynomial.eval₂AlgHom'

#check IsScalarTower

/-- `eval₂` as an `AlgHom`. -/
def eval₂AlgHom {A : Type w} {B : Type*} [CommSemiring A] [CommSemiring B] [PolynomialLike A P]
    [Algebra R A] [IsScalarTower R A P] [Algebra R B] (f : A →ₐ[R] B) (b : B) :
      P →ₐ[R] B where
  toRingHom := eval₂ f b
  commutes' := by
    intro r; simp;
    refine .trans ?_ (f.commutes r)
    change (eval₂ (↑f) b) ((algebraMap R P) r) = (f : A →+* B) ((algebraMap R A) r)
    refine .trans ?_ (eval₂_C (P := P) (↑f) b (r := (algebraMap R A) r))
    rw [IsScalarTower.algebraMap_apply (S := A)]

@[simp]
lemma eval₂AlgHom_apply {A : Type w} {B : Type*} [CommSemiring A] [CommSemiring B]
    [PolynomialLike A P] [Algebra R A] [IsScalarTower R A P] [Algebra R B]
    (f : A →ₐ[R] B) (b : B) (p : P) :
    (eval₂AlgHom f b) p = eval₂ f b p := by
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

lemma aeval_eq' {A : Type w} [CommSemiring A] [Algebra R A] (f : P →ₐ[R] A) (p : P) :
    f p = aeval (f X) p := by
  simp [aeval, eval₂AlgHom]
  change (f : P →+* A) p = _
  rw [eval₂_eq' (S := A) (↑f) p]
  simp [Algebra.ofId]

/-- Uniqueness: Any `R`-algebra homomorphism `f` from `P` to an `R`-algebra `A` is equal to the
evaluation map at the value of `f X`. -/
lemma aeval_eq {A : Type w} [CommSemiring A] [Algebra R A] (f : P →ₐ[R] A) : f = aeval (f X) := by
  simp only [aeval, eval₂AlgHom]
  ext p
  exact aeval_eq' f p

end PolynomialLike

namespace Polynomial

noncomputable instance {R : Type u} [CommSemiring R] : PolynomialLike R R[X] where
  X := Polynomial.X
  eval₂ := Polynomial.eval₂RingHom
  eval₂_C := Polynomial.eval₂_C
  eval₂_X := Polynomial.eval₂_X
  eval₂_eq f := by ext r <;> simp [Algebra.ofId]

end Polynomial

namespace PolynomialLike

open Polynomial

variable {R : Type u} [CommSemiring R] {P : Type w} [CommSemiring P] [PolynomialLike R P]

/-- The unique `R`-algebra homomorphism from a `PolynomialLike` type `P` to `R[X]`. -/
noncomputable def toPolynomialAlgHom : P →ₐ[R] R[X] := PolynomialLike.aeval Polynomial.X

/-- The unique `R`-algebra homomorphism from `R[X]` to a `PolynomialLike` type `P`. -/
noncomputable def ofPolynomialAlgHom : R[X] →ₐ[R] P := Polynomial.aeval PolynomialLike.X

@[simp]
lemma toPolynomialAlgHom_X : toPolynomialAlgHom (X : P) = Polynomial.X := by
  simp [toPolynomialAlgHom, aeval, Algebra.ofId, eval₂AlgHom]

@[simp]
lemma ofPolynomialAlgHom_X : ofPolynomialAlgHom (Polynomial.X : R[X]) = (X : P) := by
  simp [ofPolynomialAlgHom]

@[simp]
lemma ofPolynomialAlgHom_toPolynomialAlgHom_C {r : R} :
    ofPolynomialAlgHom (toPolynomialAlgHom (C r : P)) = (Polynomial.C r : R[X]) := by
  simp [ofPolynomialAlgHom, toPolynomialAlgHom, aeval, Polynomial.aeval, Algebra.ofId,
    eval₂AlgHom, instPolynomialLike]

@[simp]
lemma ofPolynomialAlgHom_toPolynomialAlgHom_X :
    ofPolynomialAlgHom (toPolynomialAlgHom (X : P)) = (Polynomial.X : R[X]) := by
  simp [ofPolynomialAlgHom, toPolynomialAlgHom, aeval, Polynomial.aeval, Algebra.ofId,
    eval₂AlgHom, instPolynomialLike]

/--
A `PolynomialLike` type `P` is isomorphic to `R[X]` as an `R`-algebra.
This is the fundamental property ensured by the `PolynomialLike` typeclass.
-/
noncomputable def polynomialAlgEquiv : P ≃ₐ[R] R[X] where
  toFun := toPolynomialAlgHom
  invFun := ofPolynomialAlgHom
  left_inv := by
    intro p
    let f : R[X] →ₐ[R] P := ofPolynomialAlgHom.comp toPolynomialAlgHom
    simp [toPolynomialAlgHom]
    -- rw [← aeval_eq' () p]
    -- simp [ofPolynomialAlgHom, toPolynomialAlgHom, aeval, Polynomial.aeval,
    --   Algebra.ofId, eval₂AlgHom]
    -- Polynomial.eval₂ (algebraMap R P) X ((eval₂ Polynomial.C Polynomial.X) p) = p
    sorry
  right_inv := by
    intro p
    simp [ofPolynomialAlgHom, toPolynomialAlgHom, aeval, Polynomial.aeval, Algebra.ofId,
      eval₂AlgHom]
  map_mul' _ _ := by simp
  map_add' _ _ := by simp
  commutes' _ := by simp

-- TODO: show that this is the _unique_ such `R`-algebra isomorphism `P ≃ₐ[R] R[X]`

lemma polynomialAlgEquiv_unique (f : P ≃ₐ[R] R[X]) : f = polynomialAlgEquiv := by
  sorry

end PolynomialLike
