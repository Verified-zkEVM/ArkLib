/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional

/-!
# Rank bounds from exhibited kernels

The first projection `ℚ × ℚ → ℚ` has the second axis in its kernel, so the exhibited-kernel bound
gives rank at most `2 - 1 = 1`, which is its true rank. Exhibiting nothing (`K = 0`) gives only
the trivial bound `2`. The composition bound is checked on a projection after an inclusion.
-/

open Module

/-- The second axis maps injectively into the kernel of the first projection. -/
example : finrank ℚ (LinearMap.range (LinearMap.fst ℚ ℚ ℚ)) ≤ 1 := by
  have h := LinearMap.finrank_range_le_sub_of_injective_ker (LinearMap.fst ℚ ℚ ℚ)
    ((LinearMap.inr ℚ ℚ ℚ).codRestrict (LinearMap.ker (LinearMap.fst ℚ ℚ ℚ))
      fun x => by simp)
    (fun _ _ hxy => congrArg Prod.snd (Subtype.ext_iff.mp hxy))
  simpa using h

/-- With an empty exhibited kernel the bound is the dimension of the source. -/
example : finrank ℚ (LinearMap.range (LinearMap.fst ℚ ℚ ℚ)) ≤ 2 := by
  have h := LinearMap.finrank_range_le_sub_of_injective_ker (W := (⊥ : Submodule ℚ ℚ))
    (LinearMap.fst ℚ ℚ ℚ) 0 (fun x y _ => Subsingleton.elim x y)
  simpa using h

/-- Precomposing the first projection with the first inclusion does not enlarge the range. -/
example :
    finrank ℚ (LinearMap.range (LinearMap.fst ℚ ℚ ℚ ∘ₗ LinearMap.inl ℚ ℚ ℚ)) ≤
      finrank ℚ (LinearMap.range (LinearMap.fst ℚ ℚ ℚ)) :=
  LinearMap.finrank_range_comp_le_left _ _

/-! ### Coordinates on the range

The first projection `ℚ × ℚ → ℚ` has a range of dimension one, so its range coordinates take
values in `Fin 1 → ℚ`. The vector `(0, 5)` lies in the kernel, so its coordinates vanish, and
`(1, 0)` does not, so its coordinates do not. -/

/-- The range of the first projection is one-dimensional. -/
example : finrank ℚ (LinearMap.range (LinearMap.fst ℚ ℚ ℚ)) = 1 := by
  rw [LinearMap.range_eq_top.mpr LinearMap.fst_surjective, finrank_top, finrank_self]

/-- A kernel vector has zero range coordinates. -/
example : (LinearMap.fst ℚ ℚ ℚ).rangeCoordinates (0, 5) = 0 :=
  (LinearMap.rangeCoordinates_eq_zero_iff _ _).mpr rfl

/-- A vector outside the kernel has nonzero range coordinates. -/
example : (LinearMap.fst ℚ ℚ ℚ).rangeCoordinates (1, 0) ≠ 0 := by
  rw [Ne, LinearMap.rangeCoordinates_eq_zero_iff]
  simp

/-- The coordinate map has the kernel of the projection and is onto its coordinate space. -/
example : LinearMap.ker (LinearMap.fst ℚ ℚ ℚ).rangeCoordinates = LinearMap.ker (LinearMap.fst ℚ ℚ ℚ)
    ∧ Function.Surjective (LinearMap.fst ℚ ℚ ℚ).rangeCoordinates :=
  ⟨LinearMap.ker_rangeCoordinates _, LinearMap.rangeCoordinates_surjective _⟩

/-! ### Nonzero kernel vectors and ranks of product maps

The first projection `ℚ × ℚ → ℚ` has rank `1 < 2`, so it kills a nonzero vector. The identity of
`ℚ` has rank equal to the dimension and kills nothing, so the strict inequality is needed. The map
`ℚ → ℚ × ℚ`, `x ↦ (x, x)`, built from two copies of the identity, has rank `1`, strictly below the
sum `2` of the component ranks. -/

/-- The first projection kills a nonzero vector. -/
example : ∃ v : ℚ × ℚ, v ≠ 0 ∧ LinearMap.fst ℚ ℚ ℚ v = 0 := by
  apply LinearMap.exists_ne_zero_map_eq_zero_of_finrank_range_lt
  rw [LinearMap.range_eq_top.mpr LinearMap.fst_surjective, finrank_top, finrank_self,
    finrank_prod, finrank_self]
  norm_num

/-- The identity of `ℚ` has rank equal to the dimension and trivial kernel. -/
example : finrank ℚ (LinearMap.range (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) = finrank ℚ ℚ ∧
    ¬ ∃ v : ℚ, v ≠ 0 ∧ (LinearMap.id : ℚ →ₗ[ℚ] ℚ) v = 0 := by
  refine ⟨by rw [LinearMap.range_id, finrank_top], ?_⟩
  rintro ⟨v, hv, hv0⟩
  exact hv hv0

/-- Two copies of the identity: the product map has rank `1`, strictly below the sum `2` that
`LinearMap.finrank_range_pi_le_sum` gives. -/
example : finrank ℚ (LinearMap.range
      (LinearMap.pi fun _ : Fin 2 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ))) = 1 ∧
    ∑ _ : Fin 2, finrank ℚ (LinearMap.range (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) = 2 := by
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · exact (LinearMap.finrank_range_le _).trans_eq (finrank_self ℚ)
  · rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
    intro h
    have := congrFun (LinearMap.congr_fun h 1) 0
    simp at this
  · rw [LinearMap.range_eq_top.mpr fun x => ⟨x, rfl⟩, finrank_top, finrank_self]
    rfl

/-! ### Joint kernels

On `ℚ³`, the first two coordinate projections have rank `1` each, so their ranks sum to
`2 < 3` and a nonzero vector lies in both kernels. The identity of `ℚ` shows that the surplus must
be strict. -/

/-- Two coordinate functionals on `ℚ³` have a common nonzero kernel vector. -/
example : ∃ v : Fin 3 → ℚ, v ≠ 0 ∧ ∀ i : Fin 2, LinearMap.proj (R := ℚ) (φ := fun _ => ℚ)
    i.castSucc v = 0 := by
  refine LinearMap.exists_ne_zero_of_sum_finrank_range_lt _ ?_
  calc ∑ i : Fin 2, finrank ℚ (LinearMap.range
        (LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) i.castSucc))
      ≤ ∑ _i : Fin 2, 1 := Finset.sum_le_sum fun i _ =>
        (Submodule.finrank_le _).trans_eq (finrank_self ℚ)
    _ < finrank ℚ (Fin 3 → ℚ) := by simp

/-- Equality is not enough: the identity of `ℚ` has rank `1 = finrank ℚ ℚ` and no nonzero kernel
vector. -/
example : ∑ _i : Fin 1, finrank ℚ (LinearMap.range (LinearMap.id (R := ℚ) (M := ℚ))) =
      finrank ℚ ℚ ∧
    ¬∃ v : ℚ, v ≠ 0 ∧ ∀ _i : Fin 1, LinearMap.id (R := ℚ) v = 0 := by
  refine ⟨?_, ?_⟩
  · rw [LinearMap.range_eq_top.mpr fun x => ⟨x, rfl⟩, finrank_top]
    simp
  rintro ⟨v, hv, h⟩
  exact hv (h 0)
