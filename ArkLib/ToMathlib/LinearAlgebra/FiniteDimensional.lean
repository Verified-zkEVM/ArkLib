/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection

/-!
# Additional finite-dimensional linear-algebra lemmas

## Main statements

* `LinearMap.finrank_eq_of_map_eq` — a linear map injective on `B` and mapping `B` onto `A`
  makes the two submodules equidimensional.
* `Submodule.exists_adapted_basis` — a finite-dimensional space has a basis whose initial
  segment is a basis of a prescribed subspace.

Generic facts intended as candidates for upstreaming to Mathlib.
-/

/-- If a linear map is injective on `B` and maps `B` onto `A`, then `B` and `A`
have the same dimension. -/
lemma LinearMap.finrank_eq_of_map_eq {F M N : Type*} [Field F]
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (f : M →ₗ[F] N) (B : Submodule F M) (A : Submodule F N)
    (hinj : ∀ p ∈ B, f p = 0 → p = 0) (hmap : B.map f = A) :
    Module.finrank F B = Module.finrank F A := by
  have hg : Function.Injective (f.domRestrict B) := by
    rw [← LinearMap.ker_eq_bot]
    ext p
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_bot]
    exact ⟨fun h => Subtype.ext (hinj p.1 p.2 h), fun h => by rw [h]; simp⟩
  rw [← LinearMap.finrank_range_of_inj hg, LinearMap.range_domRestrict, hmap]

/-- A finite-dimensional space of dimension `n` has a basis indexed by `Fin n` whose first
`finrank F N` vectors lie in a prescribed subspace `N`. -/
lemma Submodule.exists_adapted_basis {F M : Type*} [Field F] [AddCommGroup M]
    [Module F M] [FiniteDimensional F M] (N : Submodule F M) {n : ℕ}
    (hn : Module.finrank F M = n) :
    ∃ b : Module.Basis (Fin n) F M,
      ∀ j : Fin n, (j : ℕ) < Module.finrank F N → b j ∈ N := by
  classical
  obtain ⟨K, hK⟩ := N.exists_isCompl
  set t := Module.finrank F N with ht
  set u := Module.finrank F K with hu
  have htu : t + u = n := by rw [ht, hu, Submodule.finrank_add_eq_of_isCompl hK, hn]
  set b₀ : Module.Basis (Fin t ⊕ Fin u) F M :=
    ((Module.finBasis F N).prod (Module.finBasis F K)).map (N.prodEquivOfIsCompl K hK)
      with hb₀
  set e : Fin t ⊕ Fin u ≃ Fin n := finSumFinEquiv.trans (finCongr htu) with he
  refine ⟨b₀.reindex e, fun j hj => ?_⟩
  have hsymm : e.symm j = Sum.inl ⟨(j : ℕ), hj⟩ := by
    rw [Equiv.symm_apply_eq]
    rw [he]
    simp [finSumFinEquiv_apply_left]
  rw [Module.Basis.reindex_apply, hsymm, hb₀]
  simp only [Module.Basis.map_apply]
  rw [Submodule.coe_prodEquivOfIsCompl', Module.Basis.prod_apply_inl_snd]
  simp only [ZeroMemClass.coe_zero, add_zero]
  rw [Module.Basis.prod_apply_inl_fst]
  exact ((Module.finBasis F N) ⟨(j : ℕ), hj⟩).2
