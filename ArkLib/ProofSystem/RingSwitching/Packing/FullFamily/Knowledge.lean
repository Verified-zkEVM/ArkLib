/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.FullFamily.Execution
import ArkLib.ProofSystem.RingSwitching.Packing.FullFamily.Separation

/-!
# Knowledge soundness of checked full-family packing

The explicit extractor unpacks the committed polynomial at the prover-message step and preserves
it at the challenge step. Its knowledge states retain the public-family check and commitment
relation. The challenge bound is proved for every fixed prefix before deriving the averaged game.
-/

noncomputable section

namespace RingSwitching.Packing.FullFamily

open OracleSpec OracleComp ProtocolSpec MvPolynomial Probability ProbabilityTheory
open scoped NNReal ENNReal

variable {B : Type} [CommRing B] (data : PackingData B) (m : ℕ)
  {C : Type} [CommRing C] [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C]
  (bat : BatchingStrategy C data.ιE) (pc : PackedCommitment data.P m)

/-- The opening family before packing, and a packed polynomial at the later stages. -/
def WitMid : Fin 3 → Type
  | ⟨0, _⟩ => data.ιP → B⦃≤ 1⦄[X Fin m]
  | ⟨1, _⟩ => data.P⦃≤ 1⦄[X Fin m]
  | ⟨2, _⟩ => data.P⦃≤ 1⦄[X Fin m]

/-- Read back the family at the message step and preserve the packed witness thereafter. -/
def extractor :
    Extractor.RoundByRound []ₒ (StmtIn := Input data m × (∀ j, pc.OStmt j))
      (WitIn := data.ιP → B⦃≤ 1⦄[X Fin m]) (WitOut := data.P⦃≤ 1⦄[X Fin m])
      (pSpec := pSpec data bat) (WitMid := WitMid data m) where
  eqIn := rfl
  extractMid i _ _ p := match i with
    | ⟨0, _⟩ => data.unpack p
    | ⟨1, _⟩ => p
  extractOut _ _ p := p

/-- Verifier knowledge states for the committed relation chain. -/
def knowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier data m bat pc).KnowledgeStateFunction init impl
      (relIn data m pc) (relOut data m bat pc) (extractor data m bat pc) where
  toFun
    | ⟨0, _⟩ => fun stmt _ ps => (stmt, ps) ∈ relIn data m pc
    | ⟨1, _⟩ => fun stmt tr p =>
      beforeChallenge data m pc stmt.1.1 stmt.1.2 stmt.2 (tr 0) p
    | ⟨2, _⟩ => fun stmt tr p =>
      afterChallenge data m bat pc stmt.1.1 stmt.1.2 stmt.2 (tr 0) (tr 1) p
  toFun_empty _ _ := Iff.rfl
  toFun_next
    | ⟨0, _⟩ => fun _ stmt tr msg p h => by
      obtain ⟨hc, hcommit, hslice⟩ := h
      refine ⟨data.openingClaimRel_of_claimConsistent hc hslice, ?_⟩
      change pc.commitsTo stmt.2 (data.packedMLE (data.unpack p))
      exact (congrArg (pc.commitsTo stmt.2) (data.packedMLE_unpack p)).mpr hcommit
    | ⟨1, _⟩ => fun hdir => nomatch hdir
  toFun_full stmt tr p h := by
    obtain ⟨hc, hrel⟩ := positive_output data m bat pc init impl stmt.1 stmt.2 tr p h
    exact ⟨hc, hrel.2, hrel.1⟩

/-- The batching strategy supplies the error at the only challenge round. -/
def rbrError (_i : (pSpec data bat).ChallengeIdx) : ℝ≥0 := bat.error

/-- Worst-case knowledge soundness with the exact extractor and knowledge-state function exposed. -/
theorem rbrKnowledgeSoundnessWorstCaseWith
    (hfunctional : pc.Functional) (hinj : Function.Injective (algebraMap data.P C))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (relIn data m pc) (relOut data m bat pc) (verifier data m bat pc).toVerifier
      (WitMid data m) (extractor data m bat pc) (knowledgeStateFunction data m bat pc init impl)
      (rbrError data bat) := by
  intro stmt i tr
  rcases i with ⟨i, hdir⟩
  fin_cases i
  · contradiction
  · change Transcript (1 : Fin 3) (pSpec data bat) at tr
    let : SampleableType bat.Challenge := SampleableType.ofFintype bat.Challenge
    change Pr[ fun c => ∃ p,
      ¬ beforeChallenge data m pc stmt.1.1 stmt.1.2 stmt.2 (tr ⟨0, by decide⟩) p ∧
        afterChallenge data m bat pc stmt.1.1 stmt.1.2 stmt.2 (tr ⟨0, by decide⟩) c p |
      $ᵗ bat.Challenge] ≤ (bat.error : ℝ≥0∞)
    rw [probEvent_uniformSample_eq_prob_uniformOfFintype]
    exact bad_event_le data m bat pc hfunctional hinj stmt.1.1 stmt.1.2 stmt.2 (tr ⟨0, by decide⟩)

/-- The averaged exact-extractor contract follows from the fixed-prefix contract. -/
theorem rbrKnowledgeSoundnessWith
    (hfunctional : pc.Functional) (hinj : Function.Injective (algebraMap data.P C))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWith init impl
      (relIn data m pc) (relOut data m bat pc) (verifier data m bat pc).toVerifier
      (WitMid data m) (extractor data m bat pc) (knowledgeStateFunction data m bat pc init impl)
      (rbrError data bat) :=
  Verifier.rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith init impl
    (rbrKnowledgeSoundnessWorstCaseWith data m bat pc hfunctional hinj init impl)

/-- The phase also supplies the library's existential averaged RBR knowledge contract. -/
theorem rbrKnowledgeSoundness
    (hfunctional : pc.Functional) (hinj : Function.Injective (algebraMap data.P C))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier data m bat pc).rbrKnowledgeSoundness init impl
      (relIn data m pc) (relOut data m bat pc) (rbrError data bat) :=
  ⟨WitMid data m, extractor data m bat pc, knowledgeStateFunction data m bat pc init impl,
    rbrKnowledgeSoundnessWith data m bat pc hfunctional hinj init impl⟩

end RingSwitching.Packing.FullFamily

end
