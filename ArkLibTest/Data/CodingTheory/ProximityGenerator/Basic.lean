/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.Basic

/-!
# Same-set MCA extension clients

The generic bridge works with a module alphabet over an infinite field. The curve client checks
the constant-curve endpoint, where the MCA error event must be empty at every real radius.
-/

open CoreDefinitions LinearCode

-- No finite-field assumption: the seed is finite, while the alphabet is the module `ℚ²`.
example {ι : Type} [Fintype ι] (MC : ModuleCode ι ℚ (Fin 2 → ℚ))
    (G : Generator (Fin 1) (Fin 3) ℚ) (U : Fin 3 → ι → Fin 2 → ℚ) (δ : ℝ)
    (h : ¬ IsMCA G MC 0 U δ) (T : Finset ι)
    (hT : (T.card : ℝ) ≥ Fintype.card ι * (1 - δ))
    (hv : projectedWord (fun i => ∑ j, G 0 j • U j i) T ∈ projectedCodeSubmod MC T) :
    ∃ p : Fin 3 → MC, ∀ j i, i ∈ T → (p j).val i = U j i :=
  (not_isMCA_iff_forall_exists_codewords G MC 0 U δ).mp h T hT hv

example {ι F : Type} [Fintype ι] [Field F] [Fintype F]
    (MC : ModuleCode ι F F) (z : F) (U : Fin 1 → ι → F) (δ : ℝ) :
    ¬ IsMCA (univariatePowersGenerator F 0) MC z U δ := by
  rintro ⟨T, _, hv, j, hj⟩
  apply hj
  have hj0 : j = 0 := by omega
  simpa [univariatePowersGenerator, Fin.sum_univ_one, hj0] using hv

-- At challenge zero, the generated zero word extends but the second component does not.
example {F : Type} [Field F] [Fintype F] :
    IsMCA (univariatePowersGenerator F 1) (⊥ : ModuleCode (Fin 1) F F)
      0 ![0, 1] 0 := by
  refine ⟨Finset.univ, by norm_num, ?_, 1, ?_⟩
  · apply (mem_projectedCodeSubmod_iff _ _ _).mpr
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    ext i
    simp [projectedWord, univariatePowersGenerator, Fin.sum_univ_two]
  · intro h
    obtain ⟨p, hp, heq⟩ := (mem_projectedCodeSubmod_iff _ _ _).mp h
    have hp0 : p = 0 := hp
    have heq0 := congrFun heq ⟨0, Finset.mem_univ _⟩
    simp [hp0, projectedWord] at heq0

-- A degree-one curve can be passed directly to an affine-line consumer.
example {ι F : Type} [Fintype ι] [Field F] [Fintype F]
    (MC : ModuleCode ι F F) (z : F) (U : Fin 2 → ι → F) (δ : ℝ)
    (h : ¬ IsMCA (AffineLineGenerator F) MC z U δ) :
    ¬ IsMCA (univariatePowersGenerator F 1) MC z U δ := by
  rwa [univariatePowersGenerator_one_eq_affineLineGenerator]
