import Mathlib.RingTheory.Norm.Basic

/-!
# Norm vanishing detected by a geometric point

This file records the finite-free algebra fact used by the Reed--Solomon norm filter.  The
source algebra need not be a domain or reduced: if an element vanishes under an algebra map
to a nontrivial algebra, then its multiplication determinant vanishes over the base field.
-/

open Module

namespace Algebra

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

end Algebra
