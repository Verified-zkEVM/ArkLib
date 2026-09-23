/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement
import ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldProbability
import ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement
import Mathlib.Algebra.Field.ZMod

open TensorMCA Code
open scoped ProbabilityTheory

namespace ProximityGeneratorTest

private abbrev probabilityCode : ModuleCode (Fin 1) (ZMod 2) (ZMod 2) := ⊤

private theorem singletonDetermined : DeterminedByAgreement probabilityCode 1 := by
  intro c _ d _ T hT hagree
  have hzero : (0 : Fin 1) ∈ T := by
    by_contra hzero
    have hTempty : T = ∅ := Finset.Subset.antisymm (by
      intro i hi
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst i
      exact False.elim (hzero hi)) (by simp)
    simp [hTempty] at hT
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa [hi] using hagree 0 hzero

private theorem singletonLineExact (V : Bool → Fin 1 → ZMod 2) :
    UniformExactAgreement binaryEqualityGenerator probabilityCode 1 0 V := by
  refine ⟨∅, by simp, ?_⟩
  intro r _ c _ T hT hagree
  have hzero : (0 : Fin 1) ∈ T := by
    by_contra hzero
    have hTempty : T = ∅ := Finset.Subset.antisymm (by
      intro i hi
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst i
      exact False.elim (hzero hi)) (by simp)
    simp [hTempty] at hT
  have hroot : c 0 = ∑ b, binaryEqualityGenerator r b • V b 0 := hagree 0 hzero
  refine ⟨V, ?_, ?_, ?_⟩
  · intro b
    simp [probabilityCode]
  · funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa [hi] using hroot
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [hroot]

private theorem singletonLevelWitness : FullSetLevelWitness probabilityCode 1 0 :=
  fullSetLevelWitness_of_uniformExactAgreement singletonDetermined singletonLineExact

private def shortLine : Bool → Fin 1 → ZMod 2 := fun _ _ ↦ 0

example : UniformExactAgreement binaryEqualityGenerator probabilityCode 1 0 shortLine :=
  (fullSetLevelWitness_iff singletonDetermined).mp singletonLevelWitness shortLine

example : FullSetLevelWitness (probabilityCode ^⋈ Unit) 1 0 :=
  singletonLevelWitness.moduleInterleavedCode

private def shortChallenges : Fin 1 → ZMod 2 := fun _ ↦ 0

private def shortLeaves : (Fin 1 → Bool) → Fin 1 → ZMod 2 := fun _ _ ↦ 0

private theorem shortBadSetEmpty : tensorFoldBad singletonLevelWitness shortLeaves = ∅ := by
  have h := tensorFoldBad_card_le singletonLevelWitness shortLeaves
  have hle : (tensorFoldBad singletonLevelWitness shortLeaves).card ≤ 0 := by
    simpa [shortLeaves] using h
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hle)

example : (tensorFoldBad singletonLevelWitness shortLeaves).card = 0 := by
  rw [shortBadSetEmpty]
  simp

example :
    ∃ leafCode : (Fin 1 → Bool) → Fin 1 → ZMod 2,
      (∀ leaf, leafCode leaf ∈ probabilityCode) ∧
      (fun _ : Fin 1 ↦ 0) = binaryTensorFold shortChallenges leafCode ∧
      fullAgreementSet (fun _ : Fin 1 ↦ 0) (binaryTensorFold shortChallenges shortLeaves) =
        Finset.univ.filter fun i ↦ ∀ leaf, leafCode leaf i = shortLeaves leaf i := by
  have hgood : shortChallenges ∉ tensorFoldBad singletonLevelWitness shortLeaves := by
    rw [shortBadSetEmpty]
    simp
  have hfull : fullAgreementSet (fun _ : Fin 1 ↦ (0 : ZMod 2))
      (binaryTensorFold shortChallenges shortLeaves) = Finset.univ := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [fullAgreementSet, shortLeaves, shortChallenges, binaryTensorFold, binaryLineFold]
  have hclose : 1 ≤ (fullAgreementSet (fun _ : Fin 1 ↦ (0 : ZMod 2))
      (binaryTensorFold shortChallenges shortLeaves)).card := by
    rw [hfull]
    simp
  exact (hasFullTensorDecomposition_of_not_mem_bad singletonLevelWitness shortChallenges
    shortLeaves hgood) (fun _ ↦ 0) (by simp [probabilityCode]) hclose

private def shortFamilyLeaves : Fin 2 → (Fin 1 → Bool) → Fin 1 → ZMod 2 :=
  fun j _ _ ↦ if j = 0 then 0 else 1

example :
    shortFamilyLeaves 0 ≠ shortFamilyLeaves 1 ∧
    (Pr{let r ← $ᵗ (Fin 1 → ZMod 2)}[r ∈ tensorFoldFamilyBad singletonLevelWitness
      shortFamilyLeaves] ≤ ENNReal.ofReal 0) ∧
    (Pr{let r ← $ᵗ (Fin 1 → ZMod 2)}[¬ HasFullTensorDecomposition probabilityCode 1 r
      shortLeaves] ≤ ENNReal.ofReal 0) := by
  refine ⟨by decide, ?_, ?_⟩
  · simpa [shortFamilyLeaves] using
      tensorFoldFamilyBad_probability_le singletonLevelWitness shortFamilyLeaves
  · simpa [shortLeaves] using
      prob_not_hasFullTensorDecomposition_le singletonLevelWitness shortLeaves

private def probabilityLeaves : (Fin 3 → Bool) → Fin 1 → ZMod 2 := fun _ _ ↦ 0

example :
    Pr{let r ← $ᵗ (Fin 3 → ZMod 2)}[r ∈ tensorFoldBad singletonLevelWitness probabilityLeaves] ≤
      ENNReal.ofReal 0 := by
  simpa using tensorFoldBad_probability_height_three singletonLevelWitness probabilityLeaves

private def twoLevelLeaves : (Fin 2 → Bool) → Fin 1 → ℚ := fun leaf _ ↦
  if leaf 0 then (if leaf 1 then 11 else 7) else (if leaf 1 then 5 else 3)

example :
    binaryTensorFold ![(2 : ℚ) / 3, 3 / 5] twoLevelLeaves =
      fun i ↦ ∑ leaf,
        PolynomialGenIsMCA.tensorGeneratorPi (fun _ ↦ binaryEqualityGenerator)
          ![(2 : ℚ) / 3, 3 / 5] leaf • twoLevelLeaves leaf i :=
  binaryTensorFold_eq_tensorGeneratorPi _ _

end ProximityGeneratorTest
