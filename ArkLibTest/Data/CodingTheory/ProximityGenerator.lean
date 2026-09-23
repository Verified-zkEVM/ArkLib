/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement
import ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldProbability
import Mathlib.Algebra.Field.ZMod

open TensorMCA
open scoped ProbabilityTheory

namespace ProximityGeneratorTest

private abbrev probabilityCode : ModuleCode (Fin 1) (ZMod 2) (ZMod 2) := ⊤

private theorem singletonLevelWitness : FullSetLevelWitness probabilityCode 1 0 := by
  intro β _ u₀ u₁
  refine ⟨∅, by simp, ?_⟩
  intro r _ c hc hagree
  have hfull : familyAgreementSet c (fun b ↦ binaryLineFold r (u₀ b) (u₁ b)) = Finset.univ :=
    Finset.eq_univ_of_card _
      (le_antisymm (Finset.card_le_univ _) (by simpa [Fintype.card_fin] using hagree))
  refine ⟨u₀, u₁, ?_, ?_, ?_, ?_⟩
  · intro b
    simp [probabilityCode]
  · intro b
    simp [probabilityCode]
  · intro b
    funext i
    have hi0 : (0 : Fin 1) ∈ familyAgreementSet c
        (fun b ↦ binaryLineFold r (u₀ b) (u₁ b)) := by
      rw [hfull]
      simp
    have hii : i ∈ familyAgreementSet c (fun b ↦ binaryLineFold r (u₀ b) (u₁ b)) := by
      have hi : i = 0 := Subsingleton.elim _ _
      rw [hi]
      exact hi0
    have hi : i ∈ familyAgreementSet c (fun b ↦ binaryLineFold r (u₀ b) (u₁ b)) := by
      exact hii
    exact (mem_familyAgreementSet _ _ _).mp hi b
  · rw [hfull]
    simp [familyAgreementSet]

private def probabilityLeaves : (Fin 3 → Bool) → Fin 1 → ZMod 2 := fun _ _ ↦ 0

example :
    Pr{let r ← $ᵗ (Fin 3 → ZMod 2)}[r ∈ tensorFoldBad singletonLevelWitness probabilityLeaves] ≤
      ENNReal.ofReal 0 := by
  simpa using tensorFoldBad_probability_height_three singletonLevelWitness probabilityLeaves

example :
    binaryTensorFold ![(0 : ℚ)]
        (fun b : Fin 1 → Bool ↦ ![if b 0 then (7 : ℚ) else 4]) =
      fun i ↦ ∑ leaf,
        PolynomialGenIsMCA.tensorGeneratorPi (fun _ ↦ binaryEqualityGenerator) ![(0 : ℚ)] leaf •
          (fun b : Fin 1 → Bool ↦ ![if b 0 then (7 : ℚ) else 4]) leaf i :=
  binaryTensorFold_eq_tensorGeneratorPi _ _

end ProximityGeneratorTest
