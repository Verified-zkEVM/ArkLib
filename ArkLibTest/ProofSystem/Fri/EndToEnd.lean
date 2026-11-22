/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ProofSystem.Fri.Spec.Completeness
import ArkLib.ProofSystem.Fri.Spec.KnowledgeSoundness
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Frs.LineDecoding
import Mathlib.Algebra.Field.ZMod

/-!
# FRI end-to-end acceptance tests

A binary fold over four points in `ZMod 17`, followed by one query, has knowledge
error `55 / 68`. The public knowledge contracts apply with standard axiom dependencies.
-/

/--
info: 'Fri.Spec.perfect_completeness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.perfect_completeness

/--
info: 'Fri.Spec.knowledge_soundness_with' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.knowledge_soundness_with

/--
info: 'Fri.Spec.knowledge_soundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.knowledge_soundness

namespace Fri.Spec.EndToEndTest

open Domain OracleSpec OracleComp CoreDefinitions
open scoped NNReal

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

private instance : NonBinaryField (ZMod 17) where
  toField := inferInstance
  char_neq_2 := by decide

private def root : (ZMod 17)ˣ := ⟨4, 13, by decide, by decide⟩

private def domain : SmoothCosetFftDomain 2 (ZMod 17) where
  subgroupDomain :=
    { toFun := fun i ↦ root ^ i.toAdd.val
      map_one' := by decide
      map_mul' := by decide }
  subgroupDomain_inj := by decide
  cosetGenerator := ⟨3, 6, by decide, by decide⟩

private def schedule : Fin 1 → ℕ+ := fun _ ↦ 1

/-- Uniform sampling uses a classically chosen finite enumeration. -/
noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

private def foldedDomain : Fin 2 ↪ ZMod 17 :=
  ((domain.subdomain 0).subdomain 1 : Fin 2 ↪ ZMod 17)

private theorem mca_eq :
    mcaError (AffineLineGenerator (ZMod 17)) (ReedSolomon.code foldedDomain 1) (1 / 4) =
      1 / 17 := by
  classical
  rw [mcaError_eq_of_floor_eq _ _ (δ' := 0) (by norm_num) (by norm_num) (by norm_num)]
  apply le_antisymm
  · simpa using CodingTheory.FrsInternal.mcaError_affineLine_zero_le_inv_card
      (ReedSolomon.code foldedDomain 1)
  · let U : Fin 2 → Fin 2 → ZMod 17 := ![0, ![0, 1]]
    have hbad : IsMCA (AffineLineGenerator (ZMod 17))
        (ReedSolomon.code foldedDomain 1) 0 U 0 := by
      refine ⟨Finset.univ, by norm_num, ?_, 1, ?_⟩
      · convert (Submodule.zero_mem (LinearCode.projectedCodeSubmod
            (ReedSolomon.code foldedDomain 1) Finset.univ)) using 1
        ext i
        simp [LinearCode.projectedWord, AffineLineGenerator, Fin.sum_univ_two, U]
      · intro h
        obtain ⟨c, hc, heq⟩ := (LinearCode.mem_projectedCodeSubmod_iff _ _ _).mp h
        obtain ⟨p, hp, heval⟩ := ReedSolomon.mem_code_iff_eval.mp hc
        have hpC := Polynomial.eq_C_of_degree_le_zero (Order.lt_succ_iff.mp hp)
        rw [hpC] at heval
        simp only [Polynomial.eval_C] at heval
        have h0 := congrFun heq ⟨0, Finset.mem_univ _⟩
        have h1 := congrFun heq ⟨1, Finset.mem_univ _⟩
        simp [LinearCode.projectedWord, U, ← heval] at h0 h1
        exact zero_ne_one (h0.trans h1.symm)
    calc
      (1 / 17 : ENNReal) = Pr{let x ← $ᵗ (ZMod 17)}[x = 0] := by
        rw [SampleableType.prEvent_uniformSample]
        have hf : (Finset.univ.filter fun x : ZMod 17 ↦ x = 0) = {0} := by
          ext x
          simp
        rw [hf]
        norm_num
      _ ≤ Pr{let x ← $ᵗ (ZMod 17)}[
          IsMCA (AffineLineGenerator (ZMod 17)) (ReedSolomon.code foldedDomain 1) x U 0] :=
        prEvent_mono _ _ _ (fun x hx ↦ hx ▸ hbad)
      _ ≤ _ := by
        unfold mcaError
        exact le_iSup (fun V : Fin 2 → Fin 2 → ZMod 17 ↦
          Pr{let x ← $ᵗ (ZMod 17)}[
            IsMCA (AffineLineGenerator (ZMod 17)) (ReedSolomon.code foldedDomain 1) x V 0]) U

private theorem domain_bound : 2 ^ (∑ j, (schedule j).val) * (1 : ℕ+) ≤ 2 ^ 2 := by
  decide

private theorem rate_bound :
    min (1 / 4 : ℝ) (1 / 4 : ℝ≥0) ≤
      1 - (2 ^ (∑ j, (schedule j).val) * (1 : ℕ+) : ℕ) / (2 ^ 2 : ℝ) := by
  norm_num [schedule, Fin.sum_univ_one]

private theorem error_eq : soundnessError (ω := domain) schedule 1 1 (1 / 4) (1 / 4) =
    55 / 68 := by
  have hfold : foldingError (ω := domain) schedule 1 (1 / 4) 0 = 1 / 17 := by
    unfold foldingError
    change (mcaError (univariatePowersGenerator (ZMod 17) 1)
      (ReedSolomon.code foldedDomain 1) (1 / 4)).toNNReal = 1 / 17
    rw [univariatePowersGenerator_one_eq_affineLineGenerator, mca_eq]
    norm_num [ENNReal.toNNReal_ofNat]
  calc
    soundnessError (ω := domain) schedule 1 1 (1 / 4) (1 / 4) =
        foldingError (ω := domain) schedule 1 (1 / 4) 0 + 3 / 4 := by
      rw [soundnessError, Fintype.sum_subsingleton _ (0 : Fin 1)]
      congr 1
      norm_num [Real.toNNReal_div]
    _ = 1 / 17 + 3 / 4 := congrArg (fun x ↦ x + 3 / 4) hfold
    _ = 55 / 68 := by norm_num

example : soundnessError (ω := domain) schedule 1 1 (1 / 4) (1 / 4) < 1 := by
  rw [error_eq]
  norm_num

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction (ω := domain) 0 schedule 1 domain_bound 1).perfectCompleteness init impl
      (inputRelation 0 schedule 1 domain_bound 0)
      (outputRelation 0 schedule 1 domain_bound 0) :=
  perfect_completeness schedule 1 domain_bound 1 init impl

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction (ω := domain) 0 schedule 1 domain_bound 1).verifier.knowledgeSoundnessWith
      init impl (inputRelation 0 schedule 1 domain_bound (1 / 4))
      (outputRelation 0 schedule 1 domain_bound (1 / 4))
      (Extractor.extract schedule 1 (round_bound domain_bound) 1) (55 / 68) := by
  have h := knowledge_soundness_with (ω := domain) schedule 1 1 domain_bound
    (1 / 4) (1 / 4) rate_bound init impl
  simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, error_eq] using h

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction (ω := domain) 0 schedule 1 domain_bound 1).verifier.knowledgeSoundness
      init impl (inputRelation 0 schedule 1 domain_bound (1 / 4))
      (outputRelation 0 schedule 1 domain_bound (1 / 4))
      (55 / 68) := by
  simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, error_eq] using
    knowledge_soundness (ω := domain) schedule 1 1 domain_bound
    (1 / 4) (1 / 4) rate_bound init impl

end Fri.Spec.EndToEndTest
