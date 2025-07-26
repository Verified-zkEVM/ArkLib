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
    (f : R →+* S) (g : F) (r : R) : eval₂ f g (_root_.algebraMap R P r) = f r := by
  simp [eval₂_C]

end MvPolynomialLike

noncomputable section

namespace MvPolynomial

variable {σ : Type u} {R : Type v} [CommSemiring R]

instance : MvPolynomialLike σ R (MvPolynomial σ R) where
  X := MvPolynomial.X
  eval₂ := fun f g => MvPolynomial.eval₂Hom f g
  eval₂_C := fun f g r => by simp
  eval₂_X f g s := by simp
  eval₂_eq h := by simp; sorry

end MvPolynomial

end
