/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.OracleReduction.Security.RoundByRound
public import ArkLib.OracleReduction.ProtocolSpec.TranscriptMap
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Round-by-round knowledge soundness under transcript decoding

A wire transcript is decoded into a second protocol with the same round directions.
The decoder acts on one slot at a time, so it can decode a prefix without the later messages.
Challenge slots decode by bijections, preserving uniform sampling.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut WireWitIn DecodedWitIn WitOut : Type}
  {n : ℕ} {wireSpec decodedSpec : ProtocolSpec n}
  [∀ i, SampleableType (wireSpec.Challenge i)] [∀ i, SampleableType (decodedSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {wireVerifier : Verifier oSpec StmtIn StmtOut wireSpec}
  {decodedVerifier : Verifier oSpec StmtIn StmtOut decodedSpec}
  {wireRelIn : Set (StmtIn × WireWitIn)} {decodedRelIn : Set (StmtIn × DecodedWitIn)}
  {relOut : Set (StmtOut × WitOut)} {error : decodedSpec.ChallengeIdx → ℝ≥0}

/-- Pull back round-by-round knowledge soundness through a slotwise decoder. Verification on
the original transcript must equal verification on the decoded transcript as an oracle
computation. Input witnesses are mapped in the opposite direction, from the decoded protocol
back to the original one. The output relation is unchanged. -/
theorem rbrKnowledgeSoundness_of_transcriptMap (decoder : TranscriptMap wireSpec decodedSpec)
    (encodeInputWitness : DecodedWitIn → WireWitIn)
    (hInputRelation : ∀ stmt wit, (stmt, wit) ∈ decodedRelIn →
      (stmt, encodeInputWitness wit) ∈ wireRelIn)
    (hVerify : ∀ stmt transcript,
      wireVerifier.verify stmt transcript =
        decodedVerifier.verify stmt (decoder.decodeFull transcript))
    (hSound : decodedVerifier.rbrKnowledgeSoundness init impl decodedRelIn relOut error) :
    wireVerifier.rbrKnowledgeSoundness init impl wireRelIn relOut
      (error ∘ decoder.challengeIdx) := by
  obtain ⟨WitMid, decodedExtractor, decodedState, hBadTransition⟩ := hSound
  let wireExtractor : Extractor.RoundByRound oSpec StmtIn WireWitIn WitOut wireSpec WitMid :=
    { extractIn := fun stmt witMid => encodeInputWitness (decodedExtractor.extractIn stmt witMid)
      extractMid := fun i stmt wirePrefix witMid =>
        decodedExtractor.extractMid i stmt (decoder.decodePrefix wirePrefix) witMid
      extractOut := fun stmt transcript witOut =>
        decodedExtractor.extractOut stmt (decoder.decodeFull transcript) witOut }
  let wireState : wireVerifier.KnowledgeStateFunction init impl wireRelIn relOut wireExtractor :=
    { toFun := fun i stmt wirePrefix witMid =>
        decodedState.toFun i stmt (decoder.decodePrefix wirePrefix) witMid
      toFun_empty := by
        intro stmt witMid hState
        apply hInputRelation stmt (decodedExtractor.extractIn stmt witMid)
        apply decodedState.toFun_empty
        simpa only [decoder.decodePrefix_default] using hState
      toFun_next := by
        intro i hProverMessage stmt wirePrefix msg witMid hState
        change decodedState.toFun i.castSucc stmt (decoder.decodePrefix wirePrefix)
          (decodedExtractor.extractMid i stmt (decoder.decodePrefix (wirePrefix.concat msg)) witMid)
        rw [decoder.decodePrefix_concat]
        have hDecodedProverMessage : decodedSpec.dir i = .P_to_V :=
          (decoder.dir_eq i).symm.trans hProverMessage
        apply decodedState.toFun_next i hDecodedProverMessage
        simpa only [decoder.decodePrefix_concat] using hState
      toFun_full := by
        intro stmt transcript witOut hPositive
        let wireTranscript : wireSpec.FullTranscript := transcript
        change Pr{let stmtOut ← OptionT.mk do
          (simulateQ impl (wireVerifier.verify stmt wireTranscript)).run' (← init)}[
            (stmtOut, witOut) ∈ relOut] > 0 at hPositive
        rw [hVerify stmt wireTranscript] at hPositive
        exact decodedState.toFun_full stmt (decoder.decodeFull wireTranscript) witOut hPositive }
  refine ⟨WitMid, wireExtractor, wireState, ?_⟩
  intro stmt i wirePrefix
  change Pr{let challenge ← $ᵗ (wireSpec.Challenge i)}[
    ∃ witMid, ¬ decodedState.toFun i.1.castSucc stmt (decoder.decodePrefix wirePrefix)
        (decodedExtractor.extractMid i.1 stmt
          (decoder.decodePrefix (wirePrefix.concat challenge)) witMid) ∧
      decodedState.toFun i.1.succ stmt (decoder.decodePrefix (wirePrefix.concat challenge))
        witMid] ≤ _
  simp only [decoder.decodePrefix_concat]
  let badTransition : decodedSpec.Challenge (decoder.challengeIdx i) → Prop := fun challenge =>
    ∃ witMid, ¬ decodedState.toFun i.1.castSucc stmt (decoder.decodePrefix wirePrefix)
        (decodedExtractor.extractMid i.1 stmt
          ((decoder.decodePrefix wirePrefix).concat challenge) witMid) ∧
      decodedState.toFun i.1.succ stmt ((decoder.decodePrefix wirePrefix).concat challenge) witMid
  change Pr{let challenge ← $ᵗ (wireSpec.Challenge i)}[
    badTransition (decoder.decodeSlot i.1 challenge)] ≤ _
  rw [SampleableType.prEvent_uniformSample_comp_of_bijective
    (α := wireSpec.Challenge i) (β := decodedSpec.Challenge (decoder.challengeIdx i))
    (decoder.challenge_bijective i) badTransition]
  exact hBadTransition stmt (decoder.challengeIdx i) (decoder.decodePrefix wirePrefix)

end Verifier
