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

private def shortLine : Bool → Fin 1 → ZMod 2 := fun _ _ ↦ 0

example : FullSetLevelWitness probabilityCode 1 0 :=
  fullSetLevelWitness_of_uniformExactAgreement singletonDetermined singletonLineExact

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

private def shortFamilyLeaves : Unit → (Fin 1 → Bool) → Fin 1 → ZMod 2 :=
  fun _ _ _ ↦ 0

example :
    (Pr{let r ← $ᵗ (Fin 1 → ZMod 2)}[r ∈ tensorFoldFamilyBad singletonLevelWitness
      shortFamilyLeaves] ≤ ENNReal.ofReal 0) ∧
    (Pr{let r ← $ᵗ (Fin 1 → ZMod 2)}[¬ HasFullTensorDecomposition probabilityCode 1 r
      shortLeaves] ≤ ENNReal.ofReal 0) := by
  constructor
  · simpa [shortFamilyLeaves] using
      tensorFoldFamilyBad_probability_le singletonLevelWitness shortFamilyLeaves
  · simpa [shortLeaves] using
      prob_not_hasFullTensorDecomposition_le singletonLevelWitness shortLeaves

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
