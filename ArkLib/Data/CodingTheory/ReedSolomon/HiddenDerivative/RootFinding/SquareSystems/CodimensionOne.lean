/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.CoordinateSelection
/-!
# Square row selection on a smooth hypersurface

A nonzero hypersurface differential cuts an `(r+1)`-dimensional ambient tangent space down to
dimension `r`. If the pool differentials distinguish tangent vectors, `r` actual pool rows can be
selected so that those rows together with the hypersurface differential form an injective square
linear map. This is the linear algebra behind an invertible square-system Jacobian.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.SquareSystems

open Function

variable {F W ι : Type*} [Field F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]

/-- The hypersurface row followed by the selected pool rows. -/
def normalSelectedMap {r : ℕ} (normal : W →ₗ[F] F) (pool : W →ₗ[F] (ι → F))
    (selected : Fin r → ι) : W →ₗ[F] (F × (Fin r → F)) :=
  normal.prod (selectedCoordinateMap pool selected)

omit [FiniteDimensional F W] in
@[simp]
theorem normalSelectedMap_fst {r : ℕ} (normal : W →ₗ[F] F) (pool : W →ₗ[F] (ι → F))
    (selected : Fin r → ι) (w : W) : (normalSelectedMap normal pool selected w).1 = normal w :=
  rfl

omit [FiniteDimensional F W] in
@[simp]
theorem normalSelectedMap_snd {r : ℕ} (normal : W →ₗ[F] F) (pool : W →ₗ[F] (ι → F))
    (selected : Fin r → ι) (w : W) :
    (normalSelectedMap normal pool selected w).2 = selectedCoordinateMap pool selected w := rfl

/-- Select `r` actual pool rows whose differentials, together with a nonzero normal row, give an
injective square map. The tangent-pool hypothesis is exactly injectivity after restricting the
pool map to `ker normal`. For `r = 0`, the selected embedding has empty domain. -/
theorem exists_injective_normalSelectedMap {r : ℕ} (normal : W →ₗ[F] F)
    (pool : W →ₗ[F] (ι → F)) (hdim : Module.finrank F W = r + 1)
    (hnormal : normal ≠ 0)
    (htangent : Injective (pool.comp normal.ker.subtype)) :
    ∃ selected : Fin r ↪ ι, Injective (normalSelectedMap normal pool selected) := by
  have hsurjective : Surjective normal := LinearMap.surjective_iff_ne_zero.mpr hnormal
  have hrange : LinearMap.range normal = ⊤ := LinearMap.range_eq_top.mpr hsurjective
  have hkerDim : Module.finrank F normal.ker = r := by
    have hrankNullity := normal.finrank_range_add_finrank_ker
    rw [hrange, finrank_top, Module.finrank_self, hdim] at hrankNullity
    omega
  have hselected :=
    exists_injective_selectedCoordinateMap (pool.comp normal.ker.subtype) htangent
  rw [hkerDim] at hselected
  obtain ⟨selected, hselectedInjective⟩ := hselected
  refine ⟨selected, ?_⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  have hnormalW : normal w = 0 := congrArg Prod.fst hw
  have hpoolW : selectedCoordinateMap pool selected w = 0 := congrArg Prod.snd hw
  let tangent : normal.ker := ⟨w, hnormalW⟩
  have htangentZero :
      selectedCoordinateMap (pool.comp normal.ker.subtype) selected tangent = 0 := by
    ext j
    exact congrFun hpoolW j
  have htangentEq : tangent = 0 := hselectedInjective (by simpa using htangentZero)
  exact congrArg Subtype.val htangentEq

end ReedSolomon.HiddenDerivative.SquareSystems
