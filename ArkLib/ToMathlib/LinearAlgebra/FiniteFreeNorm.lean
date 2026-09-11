/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.RingTheory.Norm.Basic

/-!
# Norm vanishing detected by a geometric point

This file records the finite-free algebra fact used by the Reed--Solomon norm filter.  The
source algebra need not be a domain or reduced: if an element vanishes under an algebra map
to a nontrivial algebra, then its multiplication determinant vanishes over the base field.
-/

@[expose] public section

open Module

namespace Algebra

section Point

variable {K A B : Type*} [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
  [Semiring B] [Nontrivial B] [Algebra K B]

/-- An algebra point at which `x` vanishes forces the finite-free norm of `x` to vanish.

Unlike `Algebra.norm_eq_zero_iff`, this implication does not assume that the source algebra
is a domain.  This is the direction needed when a finite fiber is nonreduced or disconnected.
-/
theorem norm_eq_zero_of_algHom_eq_zero (φ : A →ₐ[K] B) {x : A} (hx : φ x = 0) :
    Algebra.norm K x = 0 := by
  rw [Algebra.norm_apply, LinearMap.det_eq_zero_iff_ker_ne_bot]
  rw [ne_eq, LinearMap.ker_eq_bot_iff_range_eq_top]
  intro hrange
  obtain ⟨y, hy⟩ := LinearMap.range_eq_top.mp hrange 1
  change x * y = 1 at hy
  have h := congrArg φ hy
  rw [map_mul, hx, zero_mul, map_one] at h
  exact zero_ne_one h

end Point

section Specialization

variable {R K A A' B ι : Type*} [CommRing R] [Field K] [Ring A] [Ring A']
  [Semiring B] [Nontrivial B] [Algebra R A] [Algebra K A'] [Algebra K B]
  [FiniteDimensional K A'] [Fintype ι] [DecidableEq ι]

/-- A multiplication determinant still detects a vanishing geometric point after arbitrary
specialization of the base ring.  The matrix equality is the concrete base-change obligation:
once the specialized multiplication matrix is identified, no reducedness hypothesis on the
fiber algebra `A'` is needed.
-/
theorem map_det_leftMulMatrix_eq_zero_of_algHom_eq_zero
    (σ : R →+* K) (b : Basis ι R A) (b' : Basis ι K A')
    (x : A) (x' : A')
    (hspecialize : σ.mapMatrix (Algebra.leftMulMatrix b x) = Algebra.leftMulMatrix b' x')
    (φ : A' →ₐ[K] B) (hx : φ x' = 0) :
    σ (Matrix.det (Algebra.leftMulMatrix b x)) = 0 := by
  rw [RingHom.map_det, hspecialize, ← Algebra.norm_eq_matrix_det b' x']
  exact norm_eq_zero_of_algHom_eq_zero φ hx

end Specialization

end Algebra
