/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.MvPolynomial.Basic
import ArkLib.Data.Classes.FunEquiv

/-!
# Experimental API for `MvPolynomial`-like objects

This file defines the `MvPolynomialLike` type class, which aims to give a universal property
characterization of multivariate polynomials.

This is similar to `PolynomialLike`, but for multivariate polynomials.

-/

universe u v w y z

/--
A typeclass for multivariate polynomial-like structures, being defined by the universal property of
multivariate polynomial rings:

`R[Xₛ | s : σ]` is the unique `R`-algebra such that, for every algebra `A` containing `R`, and every
element `a : A`, there is a unique algebra homomorphism from `R[Xₛ | s : σ]` to `A` that fixes `R`,
and maps `Xₛ` to `aₛ` for all `s : σ`.

(we define this in terms of uniqueness of `eval₂`, and with respect to a `FunLike` type class for
functions representing the type of functions `σ → S`. Note that we do not always want the exact type
`σ → S`, we may want `Vector S n` when `σ = Fin n`, for instance.)

We can show that any `P` satisfying the `MvPolynomialLike` typeclass is isomorphic to
`R[Xₛ | s : σ]` as an `R`-algebra, and hence inherit all relevant properties of `R[Xₛ | s : σ]`.

TODO: make sure this universal property is actually correct!
-/
class MvPolynomialLike (σ : outParam (Type u)) (R : outParam (Type v)) [CommSemiring R]
    (P : Type w) [CommSemiring P] extends Algebra R P where
  /-- The indeterminates `X : σ → P` of the multivariate polynomial ring. -/
  X : σ → P

  /-- The ring homomorphism from `P` to a commutative semiring `S` obtained by evaluating the
  pushforward of `p` along `f` at `x`. -/
  eval₂ {S : Type y} [CommSemiring S] {F : Type z} [FunEquiv F σ S] (f : R →+* S) (g : F) : P →+* S

  /-- `eval₂` on the constant injection `C` is equal to applying `f` -/
  eval₂_C {S : Type y} [CommSemiring S] {F : Type z} [FunEquiv F σ S]
    (f : R →+* S) (g : F) (r : R) : (eval₂ f g) (_root_.algebraMap R P r) = f r

  /-- `eval₂` on the indeterminates `X` is equal to applying `g` -/
  eval₂_X {S : Type y} [CommSemiring S] {F : Type z} [FunEquiv F σ S]
    (f : R →+* S) (g : F) (s : σ) : (eval₂ f g) (X s) = g s

  /-- Every ring homomorphism `h : P →+* S` is equal to `eval₂` of the corresponding functions. -/
  eval₂_eq {S : Type y} [CommSemiring S] {F : Type z} [FunEquiv F σ S] (h : P →+* S) :
    h = eval₂ (h.comp (Algebra.ofId R P)) (fun s => h (X s) : F)

namespace MvPolynomialLike

variable {σ : Type u} {R : Type v} [CommSemiring R] {P : Type w} [CommSemiring P]
  [MvPolynomialLike σ R P]

@[simp]
lemma eval₂_C' {S : Type y} [CommSemiring S] {F : Type z} [FunEquiv F σ S]
    (f : R →+* S) (g : F) (r : R) : eval₂ f g (_root_.algebraMap R P r) = f r :=
  eval₂_C f g r

lemma eval₂_eq' {S : Type y} [CommSemiring S] {F : Type z} [FunEquiv F σ S] (h : P →+* S) (p : P) :
    h p = eval₂ (h.comp (Algebra.ofId R P)) (fun s => h (X s) : F) p := by
  nth_rw 1 [eval₂_eq h (F := F)]

/-- The injection of the underlying ring `R` into a `MvPolynomialLike` type `P`. -/
@[reducible]
def C : R →+* P := algebraMap R P

/-- `eval₂` as an `AlgHom`. -/
def eval₂AlgHom {A B : Type*} [CommSemiring A] [CommSemiring B] [MvPolynomialLike σ A P]
    [Algebra R A] [IsScalarTower R A P] [Algebra R B]
    (f : A →ₐ[R] B) (g : σ → B) : P →ₐ[R] B where
  toRingHom := eval₂ f g
  commutes' r := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply R A P]
    simp

@[simp]
lemma eval₂AlgHom_apply {A B : Type*} [CommSemiring A] [CommSemiring B] [MvPolynomialLike σ A P]
    [Algebra R A] [IsScalarTower R A P] [Algebra R B]
    (f : A →ₐ[R] B) (g : σ → B) (p : P) :
    (eval₂AlgHom f g) p = eval₂ f g p := rfl

/-- The (algebra) evaluation map, which is the (unique) `R`-algebra homomorphism from `P` to
any `R`-algebra `A` that sends `X` to a specified element `s : A`. -/
def aeval {A : Type y} [CommSemiring A] [Algebra R A] {F : Type z} [FunEquiv F σ A] (g : F) :
    P →ₐ[R] A :=
  eval₂AlgHom (Algebra.ofId R A) g

@[simp]
lemma aeval_X {A : Type y} [CommSemiring A] [Algebra R A] {F : Type z} [FunEquiv F σ A] (g : F)
    (s : σ) : aeval g (X s : P) = g s := by
  simp [aeval, eval₂AlgHom, Algebra.ofId]
  change _ = (g : σ → A) s
  exact eval₂_X _ _ _

lemma aeval_eq' {A : Type y} [CommSemiring A] [Algebra R A] {F : Type z} [FunEquiv F σ A]
    (f : P →ₐ[R] A) (p : P) : f p = aeval (fun s => f (X s) : F) p := by
  simp [aeval, eval₂AlgHom, Algebra.ofId]
  sorry
  -- exact eval₂_eq' _ _

/-- Uniqueness: Any `R`-algebra homomorphism `f` from `P` to an `R`-algebra `A` is equal to the
evaluation map at the value of `f X`. -/
lemma aeval_eq {A : Type y} [CommSemiring A] [Algebra R A] (f : P →ₐ[R] A) :
    f = aeval (fun s => f (X s)) :=
  AlgHom.ext (aeval_eq' f)

/-- The unique `R`-algebra homomorphism from a `MvPolynomialLike` type `P` to `MvPolynomial σ R`. -/
noncomputable def toMvPolynomialAlgHom : P →ₐ[R] MvPolynomial σ R := aeval MvPolynomial.X

/-- The unique `R`-algebra homomorphism from `MvPolynomial σ R` to a `MvPolynomialLike` type `P`. -/
noncomputable def ofMvPolynomialAlgHom : MvPolynomial σ R →ₐ[R] P := MvPolynomial.aeval X

@[simp] lemma toMvPolynomialAlgHom_X (s : σ) :
    toMvPolynomialAlgHom (X s : P) = (MvPolynomial.X s : MvPolynomial σ R) := by
  simp [toMvPolynomialAlgHom, aeval_X, DFunEquiv.instForall]

@[simp] lemma ofMvPolynomialAlgHom_X (s : σ) :
    ofMvPolynomialAlgHom (MvPolynomial.X s : MvPolynomial σ R) = (X s : P) := by
  simp [ofMvPolynomialAlgHom, MvPolynomial.aeval_X]

noncomputable def toMvPolynomialAlgEquiv : P ≃ₐ[R] MvPolynomial σ R where
  toFun := toMvPolynomialAlgHom
  invFun := ofMvPolynomialAlgHom
  left_inv p := by
    sorry
  right_inv p := by
    simp [toMvPolynomialAlgHom, ofMvPolynomialAlgHom, aeval, Algebra.ofId, DFunEquiv.instForall]
    sorry
  map_mul' := by simp
  map_add' := by simp
  commutes' := by simp

end MvPolynomialLike

noncomputable section

namespace MvPolynomial

variable {σ : Type u} {R : Type v} [CommSemiring R]

instance : MvPolynomialLike σ R (MvPolynomial σ R) where
  X := MvPolynomial.X
  eval₂ := fun f g => eval₂Hom f g
  eval₂_C := fun f g r => by simp
  eval₂_X f g s := by simp
  eval₂_eq h := by
    simp only [eval₂Hom, Algebra.ofId, algebraMap_eq, AlgHom.coe_ringHom_mk, Equiv.invFun_as_coe,
      DFunEquiv.coe_of_coe_fn, Equiv.toFun_as_coe, Equiv.apply_symm_apply]
    ext i <;> simp

end MvPolynomial

end
