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

/-- With an empty exhibited kernel the bound is the dimension of the domain. -/
example : finrank ℚ (LinearMap.range (LinearMap.fst ℚ ℚ ℚ)) ≤ 2 := by
  have h := LinearMap.finrank_range_le_sub_of_injective_ker (W := (⊥ : Submodule ℚ ℚ))
    (LinearMap.fst ℚ ℚ ℚ) 0 (fun x y _ => Subsingleton.elim x y)
  simpa using h

/-- Precomposing the first projection with the first inclusion does not enlarge the range. -/
example :
    finrank ℚ (LinearMap.range (LinearMap.fst ℚ ℚ ℚ ∘ₗ LinearMap.inl ℚ ℚ ℚ)) ≤
      finrank ℚ (LinearMap.range (LinearMap.fst ℚ ℚ ℚ)) :=
  LinearMap.finrank_range_comp_le_left _ _

/-! ### Families of maps and nonzero kernel vectors

Combining the first projection with itself gives a map `ℚ × ℚ → (Fin 2 → ℚ)` of rank one, and the
sum bound gives `1 + 1 = 2`, so the bound need not be sharp. The first projection has rank
`1 < 2`, so it kills a nonzero vector; the identity of `ℚ` has rank equal to the dimension and
kills none, so the strict inequality is needed. -/

/-- The pair `(fst, fst)` has rank at most the sum `1 + 1` of the ranks of its components. -/
example : finrank ℚ (LinearMap.range (LinearMap.pi fun _ : Fin 2 => LinearMap.fst ℚ ℚ ℚ)) ≤ 2 := by
  refine (LinearMap.finrank_range_pi_le _).trans ?_
  rw [LinearMap.range_eq_top.mpr LinearMap.fst_surjective, finrank_top, finrank_self]
  simp

/-- The first projection kills a nonzero vector, since its rank `1` is below `2`. -/
example : ∃ v : ℚ × ℚ, v ≠ 0 ∧ LinearMap.fst ℚ ℚ ℚ v = 0 := by
  refine LinearMap.exists_ne_zero_map_eq_zero_of_finrank_range_lt _ ?_
  rw [LinearMap.range_eq_top.mpr LinearMap.fst_surjective, finrank_top, finrank_self]
  simp

/-- The identity of `ℚ` has rank equal to the dimension and kills no nonzero vector. -/
example : finrank ℚ (LinearMap.range (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) = finrank ℚ ℚ ∧
    ¬ ∃ v : ℚ, v ≠ 0 ∧ (LinearMap.id : ℚ →ₗ[ℚ] ℚ) v = 0 := by
  refine ⟨by rw [LinearMap.range_id, finrank_top], ?_⟩
  rintro ⟨v, hv, h⟩
  exact hv h

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
