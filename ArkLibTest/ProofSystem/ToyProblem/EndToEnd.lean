/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ProofSystem.ToyProblem.Spec.Completeness
import ArkLib.ProofSystem.ToyProblem.Impl.IRS
import Mathlib.Algebra.Field.ZMod

/-!
# Toy-problem end-to-end acceptance tests

The one-coordinate Reed–Solomon fixture over `ZMod 5` has no coding-theory failure:
its MCA error is zero and its two-row point lists have size one. At radius `1/4`
with one spot check, the executable extractor's error is exactly `4/5`. The fixed
linear constraints remain part of the knowledge relation.
-/

open OracleSpec OracleComp
open Code InterleavedCode CoreDefinitions
open scoped NNReal ENNReal ProbabilityTheory

/--
info: 'ToyProblem.Spec.oracleReduction_perfectCompleteness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ToyProblem.Spec.oracleReduction_perfectCompleteness

/--
info: 'ToyProblem.Spec.oracleVerifier_knowledgeSoundness_winningSetUpperBound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ToyProblem.Spec.oracleVerifier_knowledgeSoundness_winningSetUpperBound

/--
info: 'ToyProblem.Impl.IRS.oracleVerifier_knowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ToyProblem.Impl.IRS.oracleVerifier_knowledgeSoundness

namespace ToyProblem.EndToEndTest

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def domain : Fin 1 ↪ ZMod 5 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

private theorem mem_scalar_code (f : Fin 1 → ZMod 5) :
    f ∈ ReedSolomon.code domain 1 := by
  exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval
    (Polynomial.C (f 0)) (by simp) (by intro i; simpa using congrArg f (Subsingleton.elim i 0))

private theorem mem_irs_code (f : Fin 1 → Fin 1 → ZMod 5) :
    f ∈ ReedSolomon.Interleaved.irsCode domain 1 1 := by
  exact fun j ↦ mem_scalar_code (fun i ↦ f i j)

private theorem mca_error_zero :
    CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator (ZMod 5))
      (ReedSolomon.Interleaved.irsCode domain 1 1) (1 / 4) = 0 := by
  classical
  apply le_antisymm _ zero_le
  apply iSup_le
  intro U
  apply le_of_eq
  apply prEvent_eq_zero_of_forall_not
  intro x h
  obtain ⟨T, -, -, j, hj⟩ := h
  apply hj
  apply (LinearCode.mem_projectedCodeSubmod_iff _ T _).mpr
  exact ⟨U j, mem_irs_code _, rfl⟩

private theorem two_row_list (f : Fin 1 → Fin 2 → Fin 1 → ZMod 5) :
    Code.closeCodewordsRel
      ((ReedSolomon.Interleaved.irsCode domain 1 1 ^⋈ (Fin 2) :
        Submodule (ZMod 5) (Fin 1 → Fin 2 → Fin 1 → ZMod 5)) : Set _) f (1 / 4) = {f} := by
  classical
  ext c
  rw [Code.mem_closeCodewordsRel_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, hd⟩
    by_contra hne
    have h0 : f 0 ≠ c 0 := by
      intro heq
      apply hne
      funext i
      simpa only [Subsingleton.elim i (0 : Fin 1)] using heq.symm
    have hfilter : (Finset.univ.filter (fun i : Fin 1 ↦ f i ≠ c i)) = {0} := by
      ext i
      fin_cases i
      simp [h0]
    norm_num [Code.relHammingDist, hammingDist, hfilter] at hd
  · rintro rfl
    refine ⟨fun j ↦ mem_irs_code _, ?_⟩
    norm_num [Code.relHammingDist, hammingDist]

private theorem lambda_eq_one :
    Code.Lambda
      ((ReedSolomon.Interleaved.irsCode domain 1 1 ^⋈ (Fin 2) :
        Submodule (ZMod 5) (Fin 1 → Fin 2 → Fin 1 → ZMod 5)) :
        Set (Fin 1 → Fin 2 → Fin 1 → ZMod 5)) (1 / 4) = 1 := by
  simp only [Code.Lambda, two_row_list, Set.encard_singleton, iSup_const]

private theorem gamma_error_eq :
    Impl.IRS.certifiedGammaError 1 1 domain (1 / 4) = 1 / 5 := by
  apply ENNReal.coe_injective
  rw [Impl.IRS.coe_certifiedGammaError]
  norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  rw [mca_error_zero, lambda_eq_one]
  norm_num

private theorem extractor_error_eq :
    Impl.IRS.certifiedExtractorError 1 1 1 domain (1 / 4) = 4 / 5 := by
  change (1 - (1 / 4 : ℝ≥0)) ^ 1 +
    Impl.IRS.certifiedGammaError 1 1 domain (1 / 4) *
      (1 - (1 - (1 / 4 : ℝ≥0)) ^ 1) = 4 / 5
  rw [gamma_error_eq]
  apply NNReal.coe_injective
  norm_num [NNReal.coe_sub_def, max_def]

private theorem scalar_distance :
    Code.minRelHammingDistCode (ReedSolomon.code domain 1 : Set (Fin 1 → ZMod 5)) = 1 := by
  have h := Code.minDist_div_card_eq_minRelHammingDistCode
    (ReedSolomon.code domain 1 : Set (Fin 1 → ZMod 5))
  norm_num [ReedSolomon.minDist_eq_card_sub_min_add_1] at h
  exact_mod_cast h.symm

private theorem scalar_radius :
    (1 / 4 : ℝ≥0) <
      (Code.minRelHammingDistCode (ReedSolomon.code domain 1 : Set (Fin 1 → ZMod 5)) : ℝ≥0) := by
  rw [scalar_distance]
  norm_num

private theorem irs_radius :
    (1 / 4 : ℝ≥0) ∈ Set.Ioo 0
      (Code.minRelHammingDistCode
        (ReedSolomon.Interleaved.irsCode domain 1 1 : Set (Fin 1 → Fin 1 → ZMod 5)) : ℝ≥0) := by
  constructor
  · norm_num
  · have h : Code.minRelHammingDistCode
        (ReedSolomon.Interleaved.irsCode domain 1 1 : Set (Fin 1 → Fin 1 → ZMod 5)) =
        Code.minRelHammingDistCode (ReedSolomon.code domain 1 : Set (Fin 1 → ZMod 5)) := by
      exact Code.minRelHammingDistCode_moduleInterleavedCode
        (κ := Fin 1) (ReedSolomon.code domain 1)
    rw [h]
    exact scalar_radius

private theorem winning_density_eq :
    winningSetDensity (Impl.IRS.encoder 1 1 (by decide) domain) (1 / 4) = 1 / 5 := by
  classical
  let enc := Impl.IRS.encoder 1 1 (by decide) domain
  apply le_antisymm
  · have h := winningSetDensity_le_certifiedGammaError
      (ReedSolomon.Interleaved.irsCode domain 1 1) (1 / 4) irs_radius enc
      (Impl.IRS.encoder_injective 1 1 (by decide) domain (by decide))
      (Impl.IRS.encoder_range 1 1 (by decide) domain)
    change winningSetDensity enc (1 / 4) ≤ Impl.IRS.certifiedGammaError 1 1 domain (1 / 4)
      at h
    rwa [gamma_error_eq] at h
  · let x : ViolatingInstance enc (1 / 4) := {
      v := 0
      μ₁ := 0
      μ₂ := 1
      f₁ := 0
      f₂ := 0
      violates := by
        rintro ⟨-, ⟨M, -, hlin⟩, -⟩
        have h := hlin 1
        simp at h }
    have hwin : winningSetFor enc (1 / 4) 0 0 1 0 0 = {0} := by
      ext γ
      constructor
      · rintro ⟨-, ⟨M, -, hlin⟩, -⟩
        have h := hlin 0
        simpa using h.symm
      · rintro rfl
        refine ⟨0, ⟨0, ?_, ?_⟩, Finset.univ, ?_, ?_⟩ <;> simp
    have hratio : winningSetRatio x = 1 / 5 := by
      norm_num [winningSetRatio, x, hwin]
    rw [← hratio]
    exact winningSetRatio_le_winningSetDensity x

private theorem winning_set_error_eq :
    winningSetUpperBound (Impl.IRS.encoder 1 1 (by decide) domain) (1 / 4) 1 = 4 / 5 := by
  rw [winningSetUpperBound, winning_density_eq]
  apply NNReal.coe_injective
  norm_num [NNReal.coe_sub_def, max_def]

example : winningSetUpperBound
    (Impl.IRS.encoder 1 1 (by decide) domain) (1 / 4) 1 < 1 := by
  rw [winning_set_error_eq]
  norm_num

example : Impl.IRS.certifiedExtractorError 1 1 1 domain (1 / 4) < 1 := by
  rw [extractor_error_eq]
  norm_num

section Games

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

example : (Spec.oracleVerifier (k := 1) (t := 1)
    (Impl.IRS.encoder 1 1 (by decide) domain)).knowledgeSoundness
      (WitOut := Spec.OutputWitness) init impl
      (Spec.outputRelationFor 1 (Impl.IRS.encoder 1 1 (by decide) domain) (1 / 4))
      (Set.univ : Set ((Spec.OutputStatement × ∀ i, Spec.OutputOracleStatement i) ×
        Spec.OutputWitness))
      (4 / 5) := by
  rw [← winning_set_error_eq]
  exact Spec.oracleVerifier_knowledgeSoundness_winningSetUpperBound init impl
    (Impl.IRS.encoder 1 1 (by decide) domain) (1 / 4)

example : (Spec.oracleVerifier (k := 1) (t := 1)
    (Impl.IRS.encoder 1 1 (by decide) domain)).knowledgeSoundness
      (WitOut := Spec.OutputWitness) init impl
      (Spec.outputRelationFor 1 (Impl.IRS.encoder 1 1 (by decide) domain) (1 / 4))
      (Set.univ : Set ((Spec.OutputStatement × ∀ i, Spec.OutputOracleStatement i) ×
        Spec.OutputWitness))
      (4 / 5) := by
  rw [← extractor_error_eq]
  exact Impl.IRS.oracleVerifier_knowledgeSoundness 1 1 1 (by decide) domain
    (by decide) (1 / 4) scalar_radius init impl

end Games

end ToyProblem.EndToEndTest
