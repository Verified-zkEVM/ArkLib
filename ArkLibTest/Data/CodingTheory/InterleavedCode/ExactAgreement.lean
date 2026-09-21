/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement

/-!
# Exact agreement and interleaving clients

These clients check that the hypothesis `DeterminedByAgreement` of
`hasExactAgreement_of_not_isProjectionBad` cannot be dropped, compute a uniform guarantee with
no exceptional seeds for the zero code, and instantiate the counting transfer at both
alternatives of its seed-count hypothesis and at an empty row type.
-/

open Code LinearCode

namespace ExactAgreementTest

/-- A batching map with zero coefficients. -/
def zeroBatch : Unit → Fin 1 → ℚ := fun _ _ ↦ 0

/-- One received word, constant `1`. -/
def ones : Fin 1 → Fin 2 → ℚ := fun _ _ ↦ 1

/-- A codeword of the full code that agrees with the zero combined word only at `0`. -/
def c₀ : Fin 2 → ℚ := ![0, 1]

-- In the full code no seed is projection-bad.
example : ¬ IsProjectionBad zeroBatch (⊤ : ModuleCode (Fin 2) ℚ ℚ) 1 () ones := by
  rintro ⟨T, -, -, j, hj⟩
  exact hj ((mem_projectedCodeSubmod_iff _ T _).mpr ⟨ones j, Submodule.mem_top, rfl⟩)

-- Yet `c₀` agrees with the combined word on one coordinate and has no exact agreement, because
-- the only combination with coefficients `zeroBatch ()` is `0`.
example : (∀ i ∈ ({0} : Finset (Fin 2)), c₀ i = ∑ j, zeroBatch () j • ones j i) ∧
    ¬ HasExactAgreement zeroBatch (⊤ : ModuleCode (Fin 2) ℚ ℚ) () ones c₀ := by
  refine ⟨by simp [c₀, zeroBatch], ?_⟩
  rintro ⟨c', -, hc, -⟩
  have := congrFun hc 1
  simp [c₀, zeroBatch] at this

-- The missing hypothesis: the full code is not determined by one agreement.
example : ¬ DeterminedByAgreement (⊤ : ModuleCode (Fin 2) ℚ ℚ) 1 := fun h ↦ by
  have := congrFun (h c₀ Submodule.mem_top 0 Submodule.mem_top {0} (by simp)
    (by simp [c₀])) 1
  simp [c₀] at this

-- The zero code is determined by no agreements, and no seed is projection-bad for the zero
-- family, so the uniform guarantee holds with no exceptional seed.
example {S ℓ : Type} [Fintype ℓ] (G : S → ℓ → ℚ) (a : ℕ) :
    UniformExactAgreement G (⊥ : ModuleCode (Fin 3) ℚ ℚ) a 0 0 := by
  refine uniformExactAgreement_of_encard_le
    (fun c hc c' hc' _ _ _ ↦ by rw [(Submodule.mem_bot ℚ).mp hc, (Submodule.mem_bot ℚ).mp hc'])
    ?_
  have : {x | IsProjectionBad G (⊥ : ModuleCode (Fin 3) ℚ ℚ) a x 0} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨T, -, -, j, hj⟩
    exact hj ((mem_projectedCodeSubmod_iff _ T _).mpr ⟨0, Submodule.zero_mem _, rfl⟩)
  simp [this]

-- Seed space `F`: the first alternative of the seed-count hypothesis.
example {ι F A ℓ : Type} [Field F] [Fintype ℓ] [AddCommMonoid A] [Module F A]
    (G : F → ℓ → F) (C : ModuleCode ι F A) (a e : ℕ)
    (hscalar : ∀ V : ℓ → ι → A, {x | IsProjectionBad G C a x V}.encard ≤ e)
    (U : ℓ → ι → Fin 4 → A) :
    {x | IsProjectionBad G (C^⋈(Fin 4)) a x U}.encard ≤ e :=
  encard_setOf_isProjectionBad_moduleInterleavedCode_le G C a (Or.inl le_rfl) hscalar U

-- A seed space `F × F` larger than a finite field: the second alternative, with `e < |F|`.
example {ι F A ℓ : Type} [Field F] [Fintype F] [Fintype ℓ] [AddCommMonoid A] [Module F A]
    (G : F × F → ℓ → F) (C : ModuleCode ι F A) (a e : ℕ) (he : e < Fintype.card F)
    (hscalar : ∀ V : ℓ → ι → A, {x | IsProjectionBad G C a x V}.encard ≤ e)
    (U : ℓ → ι → Fin 2 → A) :
    {x | IsProjectionBad G (C^⋈(Fin 2)) a x U}.encard ≤ e :=
  encard_setOf_isProjectionBad_moduleInterleavedCode_le G C a
    (Or.inr (by rw [ENat.card_eq_coe_fintype_card]; exact_mod_cast he)) hscalar U

-- Over an infinite field the second alternative holds for every count and seed space.
example {ι A ℓ S : Type} [Fintype ℓ] [AddCommMonoid A] [Module ℚ A]
    (G : S → ℓ → ℚ) (C : ModuleCode ι ℚ ℚ) (a e : ℕ) [Finite ι]
    (hC : DeterminedByAgreement C a) (hscalar : ∀ V, UniformExactAgreement G C a e V)
    (U : ℓ → ι → Fin 3 → ℚ) :
    UniformExactAgreement G (C^⋈(Fin 3)) a e U :=
  uniformExactAgreement_moduleInterleavedCode G C a (Or.inr (by simp)) hC hscalar U

-- An empty row type is allowed.
example {ι ℓ : Type} [Fintype ℓ] [Finite ι] (G : ℚ → ℓ → ℚ) (C : ModuleCode ι ℚ ℚ) (a e : ℕ)
    (hC : DeterminedByAgreement C a) (hscalar : ∀ V, UniformExactAgreement G C a e V)
    (U : ℓ → ι → Fin 0 → ℚ) :
    UniformExactAgreement G (C^⋈(Fin 0)) a e U :=
  uniformExactAgreement_moduleInterleavedCode G C a (Or.inl le_rfl) hC hscalar U

end ExactAgreementTest
