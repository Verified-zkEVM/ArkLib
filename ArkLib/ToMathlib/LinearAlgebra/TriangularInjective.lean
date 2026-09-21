/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Order.WellFoundedSet

/-!
# Injectivity of block-triangular sums of linear maps

Let `f i : K i →ₗ[R] V` be a finite family of linear maps indexed by a linear order, and let
`π i : V →ₗ[R] W i` be test maps. Suppose that `π i` kills the image of every `f j` with `i < j`,
and that each diagonal composite `π i ∘ f i` is injective. Then the sum map
`x ↦ ∑ i, f i (x i)` on `∀ i, K i` is injective: applying `π i` to a vanishing sum, the terms with
`j < i` vanish by induction and the terms with `j > i` vanish by hypothesis, leaving
`π i (f i (x i)) = 0`.

## Main statements

* `LinearMap.injective_sum_comp_proj_of_triangular`: the sum of a block-lower-triangular family
  with injective diagonal is injective.

## References

This generalizes the `T`-adic induction in
`ReedSolomon.HiddenDerivative.truncateLocalT_sum_exhibitedKernelFactor_mul_eq_zero_iff`, in
`Interpolation/Local/KernelSliceIndependence.lean` under
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/` at ArkLib revision
a5aa2677fee4e3a79d6bb05136631cce4a08587d. The source proved it for the coefficients of powers
of one variable over a field, indexed by `Fin m`; here the index is any finite linear order,
the test maps are arbitrary, and the scalars form a ring.

Nothing is deferred.
-/

@[expose] public section

namespace LinearMap

variable {R ι V : Type*} {K W : ι → Type*} [Ring R] [Fintype ι] [LinearOrder ι]
  [AddCommGroup V] [Module R V] [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]

/-- A block-lower-triangular sum with injective diagonal blocks is injective. The hypothesis
`hlow` says that `π i` vanishes on the image of `f j` for `i < j`; without it, two blocks with the
same image already give a non-injective sum. The diagonal hypothesis `hdiag` cannot be dropped
either, since a zero block `f i` makes the sum non-injective whenever `K i` is nontrivial. -/
theorem injective_sum_comp_proj_of_triangular (f : ∀ i, K i →ₗ[R] V) (π : ∀ i, V →ₗ[R] W i)
    (hlow : ∀ i j, i < j → ∀ x, π i (f j x) = 0)
    (hdiag : ∀ i, Function.Injective (π i ∘ₗ f i)) :
    Function.Injective
      (∑ i, (f i).comp (LinearMap.proj i : (∀ i, K i) →ₗ[R] K i) : (∀ i, K i) →ₗ[R] V) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply] at hx
  funext i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have hπ := congrArg (π i) hx
    rw [map_sum, map_zero, Finset.sum_eq_single i] at hπ
    · exact (hdiag i) (by simpa using hπ)
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hj | hj
      · simp [ih j hj]
      · exact hlow i j hj (x j)
    · simp

end LinearMap
