/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.ExactCommitment
import ArkLib.ProofSystem.RingSwitching.Packing.FullFamily.Completeness
import ArkLib.ProofSystem.RingSwitching.Packing.FullFamily.Knowledge
import ArkLibTest.ProofSystem.RingSwitching.Packing.SeparateFields
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.StdBasis

/-!
# Production acceptance cases for checked full-family packing

The execution tests use a nonconstant, nonzero family over a ring with zero divisors, packing
rank two and opening rank one. Both the verifier and complete reduction retain rejection.
Further clients instantiate separate finite fields and a larger challenge algebra.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.FullFamily

open MvPolynomial Module OracleSpec OracleComp ProtocolSpec ProbabilityTheory
open RingSwitching.Packing.FullFamily

/-- Unequal ranks with a packed algebra containing zero divisors. -/
abbrev ringData : PackingData (ZMod 6) where
  P := Fin 2 → ZMod 6
  E := ZMod 6
  ιP := Fin 2
  ιE := Unit
  packBasis := Pi.basisFun _ _
  openBasis := Basis.singleton Unit (ZMod 6)

abbrev batch := BatchingStrategy.singleton ringData.P Unit
abbrev commitment := ExactPackedCommitment.polynomialOracle ringData.P 1

def family (i : Fin 2) : (ZMod 6)⦃≤ 1⦄[X Fin 1] :=
  ⟨MLE (fun v => if i = 0 then (v 0 : ZMod 6) else 1), MLE_mem_restrictDegree _⟩

def input : Input ringData 1 :=
  (fun i => aeval (fun _ => (0 : ZMod 6)) (family i).val, fun _ => 0)

def oracle := commitment.commit (ringData.packedMLE family)

def slices := honestSlices ringData 1 input.2 (ringData.packedMLE family)

/-- The family contains a nonconstant polynomial. -/
theorem family_nonconstant :
    eval (fun _ => (0 : ZMod 6)) (family 0).val ≠
      eval (fun _ => (1 : ZMod 6)) (family 0).val := by
  have h0 := MLE_eval_zeroOne (R := ZMod 6) (fun _ : Fin 1 => (0 : Fin 2))
    (fun v : Fin 1 → Fin 2 => if (0 : Fin 2) = 0 then (v 0 : ZMod 6) else 1)
  have h1 := MLE_eval_zeroOne (R := ZMod 6) (fun _ : Fin 1 => (1 : Fin 2))
    (fun v : Fin 1 → Fin 2 => if (0 : Fin 2) = 0 then (v 0 : ZMod 6) else 1)
  change eval (fun _ => 0) (family 0).val = 0 at h0
  change eval (fun _ => 1) (family 0).val = 1 at h1
  rw [h0, h1]
  decide

/-- The input relation has a concrete nonzero witness and a matching oracle. -/
theorem input_related : ((input, oracle), family) ∈ relIn ringData 1 commitment :=
  ⟨fun _ => rfl, commitment.commitsTo_commit _⟩

/-- The honest slice is accepted. -/
theorem honest_verifier :
    (verifier ringData 1 batch commitment).toVerifier.verify (input, oracle)
      (FullTranscript.mk2 slices ()) =
      pure (nextStatement ringData 1 batch input slices (), oracle) := by
  rw [verifier_verify]
  exact if_pos (honest_check ringData 1 commitment input_related)

/-- A false public family disagrees on the nonconstant coordinate at the same point. -/
def falseInput : Input ringData 1 := (fun _ => 1, input.2)

theorem false_guard : ¬ ringData.claimConsistent falseInput.1 slices := by
  intro h
  have ht := honest_check ringData 1 commitment input_related
  have heq := ringData.transpose.injective
    (((ringData.claimConsistent_iff_transpose _ _).mp h).trans
      ((ringData.claimConsistent_iff_transpose _ _).mp ht).symm)
  have h0 := congrFun heq (0 : Fin 2)
  have hm := MLE_eval_zeroOne (R := ZMod 6) (fun _ : Fin 1 => (0 : Fin 2))
    (fun v : Fin 1 → Fin 2 => if (0 : Fin 2) = 0 then (v 0 : ZMod 6) else 1)
  change (1 : ZMod 6) = eval (fun _ => 0) (family 0).val at h0
  change eval (fun _ => 0) (family 0).val = 0 at hm
  exact (by decide : (1 : ZMod 6) ≠ 0) (h0.trans hm)

/-- Failure occurs in the materialized production verifier, without returning a dummy statement. -/
theorem false_verifier :
    (verifier ringData 1 batch commitment).toVerifier.verify (falseInput, oracle)
      (FullTranscript.mk2 slices ()) = failure := by
  rw [verifier_verify]
  exact if_neg false_guard

/-- Full honest-prover execution retains the verifier failure after its challenge query. -/
theorem false_reduction :
    ((reduction ringData 1 batch commitment).toReduction.run (falseInput, oracle) family).run =
      (do
        let _ ← liftComp ((pSpec ringData batch).getChallenge ⟨1, rfl⟩)
          ([]ₒ + [(pSpec ringData batch).Challenge]ₒ'challengeOracleInterface)
        pure none) := by
  rw [reduction_run]
  have hf : ¬ ringData.claimConsistent falseInput.1
      (honestSlices ringData 1 falseInput.2 (ringData.packedMLE family)) := false_guard
  simp only [if_neg hf]

/-- Completeness holds uniformly over oracle-state distributions, including point-mass states. -/
theorem ring_complete {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction ringData 1 batch commitment).perfectCompleteness init impl
      (relIn ringData 1 commitment) (relOut ringData 1 batch commitment) :=
  perfectCompleteness ringData 1 batch commitment init impl

/-- Rank-one coordinate batching has zero error even over the non-domain packed algebra. -/
theorem ring_worst_case {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (relIn ringData 1 commitment) (relOut ringData 1 batch commitment)
      (verifier ringData 1 batch commitment).toVerifier
      (WitMid ringData 1) (extractor ringData 1 batch commitment)
      (knowledgeStateFunction ringData 1 batch commitment init impl) (fun _ => 0) :=
  rbrKnowledgeSoundnessWorstCaseWith ringData 1 batch commitment commitment.commitsTo_functional
    Function.injective_id init impl

/-- Independent packing and opening fields also instantiate the knowledge contract. -/
theorem separate_fields_worst_case {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    let : Fintype separateFields.P := Fintype.ofFinite _
    let bat := BatchingStrategy.gammaPowers separateFields.P 3
    let pc := ExactPackedCommitment.polynomialOracle separateFields.P 0
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (relIn separateFields 0 pc) (relOut separateFields 0 bat pc)
      (verifier separateFields 0 bat pc).toVerifier
      (WitMid separateFields 0) (extractor separateFields 0 bat pc)
      (knowledgeStateFunction separateFields 0 bat pc init impl) (rbrError separateFields bat) := by
  dsimp only
  exact rbrKnowledgeSoundnessWorstCaseWith _ _ _ _
    (ExactPackedCommitment.polynomialOracle _ _).commitsTo_functional
    Function.injective_id init impl

/-- A packing field and a distinct opening algebra, with batching in a larger field. -/
abbrev extensionData : PackingData (ZMod 3) where
  P := ZMod 3
  E := Fin 2 → ZMod 3
  ιP := Unit
  ιE := Fin 2
  packBasis := Basis.singleton Unit (ZMod 3)
  openBasis := Pi.basisFun _ _

local instance : Fintype (GaloisField 3 2) := Fintype.ofFinite _

abbrev extensionBatch := BatchingStrategy.gammaPowers (GaloisField 3 2) 2
abbrev extensionCommitment := ExactPackedCommitment.polynomialOracle extensionData.P 1

/-- The enlarged challenge algebra is used by the production verifier and explicit extractor. -/
theorem extension_worst_case {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (relIn extensionData 1 extensionCommitment)
      (relOut extensionData 1 extensionBatch extensionCommitment)
      (verifier extensionData 1 extensionBatch extensionCommitment).toVerifier
      (WitMid extensionData 1) (extractor extensionData 1 extensionBatch extensionCommitment)
      (knowledgeStateFunction extensionData 1 extensionBatch extensionCommitment init impl)
      (rbrError extensionData extensionBatch) :=
  rbrKnowledgeSoundnessWorstCaseWith _ _ _ _ extensionCommitment.commitsTo_functional
    (algebraMap (ZMod 3) (GaloisField 3 2)).injective init impl

/-- The production honest execution accepts every challenge in the larger field. -/
theorem extension_verifier
    (ps : Unit → (ZMod 3)⦃≤ 1⦄[X Fin 1]) (r : Fin 1 → extensionData.E)
    (c : GaloisField 3 2) :
    let stmt : Input extensionData 1 := (fun i => aeval r (ps i).val, r)
    let p := extensionData.packedMLE ps
    let s := honestSlices extensionData 1 r p
    (verifier extensionData 1 extensionBatch extensionCommitment).toVerifier.verify
      (stmt, extensionCommitment.commit p) (FullTranscript.mk2 s c) =
      pure (nextStatement extensionData 1 extensionBatch stmt s c,
        extensionCommitment.commit p) := by
  dsimp only
  rw [verifier_verify]
  have hIn : ((((fun i => aeval r (ps i).val), r),
      extensionCommitment.commit (extensionData.packedMLE ps)), ps) ∈
      relIn extensionData 1 extensionCommitment :=
    ⟨fun _ => rfl, extensionCommitment.commitsTo_commit _⟩
  exact if_pos (honest_check extensionData 1 extensionCommitment hIn)

/-- Enlarging the challenge algebra preserves state-aware perfect completeness. -/
theorem extension_complete {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction extensionData 1 extensionBatch extensionCommitment).perfectCompleteness init impl
      (relIn extensionData 1 extensionCommitment)
      (relOut extensionData 1 extensionBatch extensionCommitment) :=
  perfectCompleteness extensionData 1 extensionBatch extensionCommitment init impl

/-- Separate fields and no retained variables satisfy the production completeness contract. -/
theorem separate_fields_complete {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    let : Fintype separateFields.P := Fintype.ofFinite _
    let bat := BatchingStrategy.gammaPowers separateFields.P 3
    let pc := ExactPackedCommitment.polynomialOracle separateFields.P 0
    (reduction separateFields 0 bat pc).perfectCompleteness init impl
      (relIn separateFields 0 pc) (relOut separateFields 0 bat pc) := by
  dsimp only
  exact perfectCompleteness separateFields 0 _ _ init impl

end RingSwitching.Packing.Tests.FullFamily

end
