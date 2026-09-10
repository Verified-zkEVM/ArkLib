/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.KernelSliceIndependence
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas


/-!
# Rank bounds from exhibited local kernels

This file turns an injective family contained in the kernel of a finite-dimensional linear map
into an upper bound on the map's rank.  It then applies that rank--nullity argument to the
hidden-derivative intermediate constraint map and transfers the bound to the point-dependent
local map through the explicit factorization.

The resulting number is certified by the exhibited kernel family.  Nothing here identifies that
family with the full kernel or identifies the certified budget with the true local rank.

## References

* [Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], ECCC TR26-164, Section 3.
* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], exact finite interpolation analysis.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

namespace ReedSolomon.HiddenDerivative

open Module
open scoped BigOperators

variable {F V V₂ K : Type*}

/-- Rank--nullity with only an exhibited subspace of the kernel.  An injective map from `K` into
the kernel certifies that at least `finrank F K` dimensions are lost, without claiming that the
exhibited family spans the kernel. -/
theorem finrank_range_le_sub_finrank_of_injective_to_ker
    [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup V₂] [Module F V₂]
    [AddCommGroup K] [Module F K] [FiniteDimensional F K]
    (f : V →ₗ[F] V₂) (kernelInjection : K →ₗ[F] LinearMap.ker f)
    (hinjective : Function.Injective kernelInjection) :
    finrank F (LinearMap.range f) ≤ finrank F V - finrank F K := by
  have hkernel : finrank F K ≤ finrank F (LinearMap.ker f) :=
    kernelInjection.finrank_le_finrank_of_injective hinjective
  have hrankNullity := f.finrank_range_add_finrank_ker
  omega

/-- Composing on the right cannot increase the dimension of the outer map's range. -/
theorem finrank_range_comp_le_outer
    [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup V₂] [Module F V₂] [FiniteDimensional F V₂]
    {X : Type*} [AddCommGroup X] [Module F X]
    (g : V₂ →ₗ[F] X) (f : V →ₗ[F] V₂) :
    finrank F (LinearMap.range (g.comp f)) ≤ finrank F (LinearMap.range g) := by
  apply Submodule.finrank_mono
  rintro _ ⟨v, rfl⟩
  exact ⟨f v, rfl⟩

/-! ### Exact finite rank budget -/

/-- Subtracting the exhibited kernel rectangles from the ambient intermediate dimension gives
exactly the certified enlarged-map rank budget.  The termwise inclusion is what makes subtraction
commute with the finite sum over `T`-degrees. -/
theorem ambient_sub_exhibitedKernel_eq_certifiedEnlargedRankBound
    (d m M W : ℕ) :
    (∑ r ∈ Finset.range m,
        weightedHigherJetCount d (W + r) * ambientContactCount r M) -
      (∑ r ∈ Finset.range m,
        weightedHigherJetCount d (W + r) *
          exhibitedKernelContactCount r M (contactThreshold d m r)) =
        certifiedEnlargedRankBound d m M W := by
  rw [← Finset.sum_tsub_distrib]
  · simp only [certifiedEnlargedRankBound, certifiedContactRankBudget,
      exhibitedKernelResidualCount, Nat.mul_sub_left_distrib]
  · intro r _
    exact Nat.mul_le_mul_left _
      (exhibitedKernelContactCount_le_ambientContactCount
        r M (contactThreshold d m r))

/-! ### Hidden-derivative local rank bounds -/

/-- The point-independent intermediate map has rank at most the exact residual budget certified
by the exhibited kernel family.  This uses only an injection into `ker Γ`, so the conclusion is an
upper bound rather than an equality with the true rank. -/
theorem finrank_intermediateConstraintMap_le_certifiedEnlargedRankBound
    {F : Type*} [Field F] {d m M W : ℕ} (hd : 0 < d) :
    finrank F (LinearMap.range (intermediateConstraintMap (R := F) hd m M W)) ≤
      certifiedEnlargedRankBound d m M W := by
  have h := finrank_range_le_sub_finrank_of_injective_to_ker
    (intermediateConstraintMap (R := F) hd m M W)
    (exhibitedKernelFamilyKernelMap (F := F) (m := m) (M := M) (W := W) hd)
    (exhibitedKernelFamilyKernelMap_injective
      (F := F) (m := m) (M := M) (W := W) hd)
  rw [finrank_localIntermediateSpace hd,
    finrank_exhibitedKernelFamilySource hd,
    ambient_sub_exhibitedKernel_eq_certifiedEnlargedRankBound] at h
  exact h

/-- Uniform rank bound for the actual point-dependent local constraint map on the exact
interpolation space.  The proof first uses `Φ = Γ ∘ Ψ`, then applies the exhibited-kernel
bound for `Γ`; it does not identify either rank with the certified budget. -/
theorem finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound
    {F : Type*} [Field F] {d D A m M W : ℕ}
    (hd : 0 < d) (hdD : d < D) (center received : F) :
    finrank F (LinearMap.range
      (exactLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
        hdD m center received)) ≤ certifiedEnlargedRankBound d m M W := by
  rw [exactLocalConstraintAt_eq_intermediate_comp_translated hd hdD center received]
  exact (finrank_range_comp_le_outer
    (intermediateConstraintMap (R := F) hd m M W)
    (translatedExactLocalTruncation hd hdD center received)).trans
      (finrank_intermediateConstraintMap_le_certifiedEnlargedRankBound hd)

end ReedSolomon.HiddenDerivative
