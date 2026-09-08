/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLibTest.ProofSystem.RingSwitching.Legacy

/-!
# Final packing leaf over a ring with zero divisors

The committed packed polynomial is one and the public multiplier vanishes at the
opening point. The actual input relation is satisfied, the prover sends one, and
the verifier forwards one. The final extractor reconstructs the residual witness;
its zero-challenge security does not require a domain or a nonzero multiplier.
-/

open OracleSpec OracleComp ProtocolSpec MvPolynomial Sumcheck.Structured
open RingSwitching RingSwitching.LegacyTest

noncomputable section
namespace RingSwitching.FinalTest

def onePoly : MultilinearPoly L 1 :=
  ⟨1, by simp [mem_restrictDegree_iff_degreeOf_le]⟩

def oneOracles : AbstractOStmtIn L 1 where
  ιₛᵢ := Empty
  OStmtIn := fun i => nomatch i
  Oₛᵢ := fun i => nomatch i
  initialCompatibility := fun p => p.1 = onePoly

def oneOracleValues : ∀ i, oneOracles.OStmtIn i := fun i => nomatch i

def oneWitness : RingSwitching.SumcheckWitness L 1 (Fin.last 1) where
  t' := onePoly
  H := projectToMidSumcheckPolyWithParam 1
    (RingSwitching_SumcheckMultParam 1 L K profile 2 1 rfl) ctx onePoly (Fin.last 1) 1

/-- The zero-multiplier case has an actual nonzero compatible source witness. -/
lemma honest_input :
    (((finish 0, oneOracleValues), oneWitness) ∈
      sumcheckRoundRelation 1 L K profile 2 1 rfl oneOracles (Fin.last 1)) := by
  change True ∧ _ ∧ _ ∧ _
  refine ⟨trivial, rfl, ?_, rfl⟩
  apply (final_consistency profile rfl (finish 0) oneWitness rfl).mpr
  simp [finish, ctx, oneWitness, final_multiplier_zero]

/-- Honest execution sends the nonzero packed value and forwards that same statement. -/
lemma prover_sends_one :
    (SumcheckPhase.finalSumcheckProver 1 L K profile 2 1 oneOracles).run
      (finish 0, oneOracleValues) oneWitness =
    pure ((fun | ⟨0, _⟩ => (1 : L)), (⟨1, 1⟩, oneOracleValues), ⟨onePoly⟩) := by
  rw [SumcheckPhase.finalSumcheckProver_run]
  simp only [oneWitness, onePoly, finish, map_one]
  rfl

lemma verifier_forwards_one :
    (SumcheckPhase.finalSumcheckVerifier 1 L K profile 2 1 rfl oneOracles).toVerifier.verify
      (finish 0, oneOracleValues) (fun | ⟨0, _⟩ => (1 : L)) =
      pure (⟨1, 1⟩, oneOracleValues) := by
  rw [SumcheckPhase.finalSumcheckVerifier_verify]
  simp [finish, ctx, FullTranscript.messages, final_multiplier_zero]

lemma output_relation :
    ((⟨1, 1⟩, oneOracleValues), ⟨onePoly⟩) ∈ oneOracles.toRelInput := by
  change (1 : L) = MvPolynomial.eval 1 1 ∧ onePoly = onePoly
  simp

/-- The output extractor constructs the complete structured witness from the packed polynomial. -/
lemma extractor_reconstructs (tr : FullTranscript (pSpecFinalSumcheck L)) :
    (SumcheckPhase.finalSumcheckRbrExtractor.{0} 1 L K profile 2 1 rfl oneOracles).extractOut
      (finish 0, oneOracleValues) tr ⟨onePoly⟩ = oneWitness := rfl

lemma perfect_completeness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    let reduction := SumcheckPhase.finalSumcheckOracleReduction 1 L K profile 2 1 rfl oneOracles
    reduction.perfectCompleteness init impl
      (sumcheckRoundRelation 1 L K profile 2 1 rfl oneOracles (Fin.last 1))
      oneOracles.toRelInput :=
  SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness
    1 L K profile 2 1 rfl oneOracles init impl

lemma worst_case_knowledge {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    let verifier := SumcheckPhase.finalSumcheckVerifier 1 L K profile 2 1 rfl oneOracles
    verifier.toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (sumcheckRoundRelation 1 L K profile 2 1 rfl oneOracles (Fin.last 1))
      oneOracles.toRelInput 0 :=
  SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCase
    1 L K profile 2 1 rfl oneOracles init impl

end RingSwitching.FinalTest
