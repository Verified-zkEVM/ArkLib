/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
# Selecting a square set of coordinate rows

An injective map from an `r`-dimensional vector space into any coordinate space has `r` actual
coordinate rows that remain injective. This selects rows from the given pool itself; it does not
replace them by generic linear combinations. The empty selection handles dimension zero.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.SquareSystems

open Function Set Submodule

variable {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- The `i`th coordinate functional of a map into a function space. -/
def coordinateFunctional (map : V →ₗ[F] (ι → F)) (i : ι) : Module.Dual F V :=
  (LinearMap.proj i).comp map

/-- Restrict a coordinate-valued linear map to a selected list of coordinate rows. -/
def selectedCoordinateMap {r : ℕ} (map : V →ₗ[F] (ι → F)) (selected : Fin r → ι) :
    V →ₗ[F] (Fin r → F) :=
  LinearMap.pi fun j ↦ coordinateFunctional map (selected j)

omit [FiniteDimensional F V] in
@[simp]
theorem selectedCoordinateMap_apply {r : ℕ} (map : V →ₗ[F] (ι → F))
    (selected : Fin r → ι) (v : V) (j : Fin r) :
    selectedCoordinateMap map selected v j = map v (selected j) := rfl

/-- Some `finrank F V` distinct rows of an injective coordinate map still form an injective map.
In particular, the result selects no rows when `V` has dimension zero. -/
theorem exists_injective_selectedCoordinateMap (map : V →ₗ[F] (ι → F))
    (hmap : Injective map) :
    ∃ selected : Fin (Module.finrank F V) ↪ ι,
      Injective (selectedCoordinateMap map selected) := by
  let rows : ι → Module.Dual F V := coordinateFunctional map
  have hiInf : (⨅ i, LinearMap.ker (rows i)) = ⊥ := by
    rw [← LinearMap.ker_pi]
    have hpi : LinearMap.pi rows = map := by
      ext v i
      rfl
    rw [hpi, LinearMap.ker_eq_bot.mpr hmap]
  have hspan : Submodule.span F (Set.range rows) = ⊤ := by
    apply top_unique
    intro functional _
    apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
    rw [hiInf]
    exact bot_le
  have hfinrank : Module.finrank F (Submodule.span F (Set.range rows)) =
      Module.finrank F V := by
    rw [hspan, finrank_top, Subspace.dual_finrank_eq]
  have hchosen := Submodule.exists_fun_fin_finrank_span_eq F (Set.range rows)
  rw [hfinrank] at hchosen
  obtain ⟨functionals, hfunctionals, hspanFunctionals, hlinearIndependent⟩ := hchosen
  choose select hselect using hfunctionals
  let selected : Fin (Module.finrank F V) ↪ ι :=
    ⟨select, fun i j hij ↦ hlinearIndependent.injective (by
      rw [← hselect i, ← hselect j, hij])⟩
  refine ⟨selected, ?_⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  apply hmap
  ext i
  rw [map_zero]
  change rows i v = 0
  have hrow : rows i ∈ Submodule.span F (Set.range functionals) := by
    rw [hspanFunctionals]
    exact Submodule.subset_span ⟨i, rfl⟩
  refine Submodule.span_induction (p := fun functional _ ↦ functional v = 0) ?_ ?_ ?_ ?_ hrow
  · intro functional hfunctional
    rcases hfunctional with ⟨j, rfl⟩
    have hj := congrFun hv j
    change rows (select j) v = 0 at hj
    rwa [hselect j] at hj
  · simp
  · intro x y _ _ hx hy
    simp [hx, hy]
  · intro a x _ hx
    simp [hx]

end ReedSolomon.HiddenDerivative.SquareSystems
