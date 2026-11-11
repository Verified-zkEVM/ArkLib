/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Core.Legacy.Security
import ArkLibTest.Interaction.Core.Legacy.Execution

/-! Acceptance examples for the security transfers: completeness, soundness and knowledge
soundness of an embedded legacy reduction, adversarial interaction-layer provers passed
through the soundness and knowledge-soundness transfers, and the legacy transcript prefix of a
full prefix with the round-by-round transfers. -/

open PFunctor PFunctor.FreeM OracleComp OracleSpec Interaction.Core Interaction.TwoParty.Lens
  ProtocolSpec MeasureTheory
open scoped NNReal

namespace Interaction.Core.Legacy.SecurityTests
open Interaction.Core.Legacy.ExecutionTests

/-! ### Completeness -/

example [∀ i, SampleableType (twoWay.Challenge i)] (init : ProbComp Unit)
    (impl : QueryImpl []ₒ (StateT Unit ProbComp))
    (relIn : Set (Nat × Nat)) (relOut : Set (Nat × Nat)) (ε : ℝ≥0) :
    (embedReduction counterReduction).completeness init impl
        (plainChallengeImpl ProtocolSpec.challengeQueryImpl) (relProblem relIn)
        (relProblem relOut) (fun _ o => o.1) (fun obs _ _ => obs.2.1.2) (fun _ w => w) ε ↔
      counterReduction.completeness init impl relIn relOut ε :=
  completeness_iff init impl counterReduction relIn relOut ε

/-! ### An adversarial interaction-layer prover -/

/-- A cheating prover written directly in the interaction layer: it sends `42`, answers the
challenge `true` with `7`, and claims an unrelated output `true`. It is not the embedding of any
honest legacy prover. -/
def cheat : Core.Prover plainSig []ₒ (protocol twoWay) (fun _ => Bool) :=
  pure ⟨(42 : Nat), pure fun (b : Bool) => pure ⟨(bif b then 7 else 0 : Nat), pure true⟩⟩

/-- The legacy prover translated from the cheating prover, after its outputs are replaced by
the fixed output statement `0` and the trivial witness. -/
def cheatLegacy : _root_.Prover []ₒ Nat PUnit Nat PUnit twoWay :=
  translate (Strategy.mapOutput (fun _ _ => ((0, ⟨⟩) : Nat × PUnit)) cheat)

/-- Embedding the translation gives back the cheating prover with its outputs replaced. -/
example (stmt : Nat) :
    embedProver cheatLegacy stmt ⟨⟩ =
      Strategy.mapOutput (fun _ _ => ((0, ⟨⟩) : Nat × PUnit)) cheat :=
  embedProver_translate _ stmt

def cheatOutputs (r : LegacyResult twoWay Nat PUnit) : Option (Nat × Nat × Nat) :=
  r.map fun x => (show Nat from x.1.1 0, show Nat from x.1.1 2, x.2)

/-- The translated cheating prover sends the same messages in the legacy layer: the verifier
accepts with challenge `true` and outputs `2 + 7`. -/
example : cheatOutputs (simulateQ (legacyAnswers true)
    ((⟨cheatLegacy, lastIfTrue⟩ : _root_.Reduction []ₒ Nat PUnit Nat PUnit twoWay).run 2
      ⟨⟩).run) = some (42, 7, 9) := by
  decide

/-- With challenge `false`, the verifier rejects. -/
example : cheatOutputs (simulateQ (legacyAnswers false)
    ((⟨cheatLegacy, lastIfTrue⟩ : _root_.Reduction []ₒ Nat PUnit Nat PUnit twoWay).run 2
      ⟨⟩).run) = none := by
  decide

/-- Legacy soundness of `lastIfTrue` bounds the acceptance probability of the cheating
interaction-layer prover, through the soundness transfer. -/
example [∀ i, SampleableType (twoWay.Challenge i)] (init : ProbComp Unit)
    (impl : QueryImpl []ₒ (StateT Unit ProbComp))
    (langIn langOut : Set Nat) (ε : ℝ≥0) (h : lastIfTrue.soundness init impl langIn langOut ε)
    (stmt : Nat) (hstmt : stmt ∉ langIn) :
    letI : MeasurableSpace
      (Observation plainSig (protocol twoWay) (fun _ => Bool) (fun _ => Nat)) := ⊤
    𝒟[experiment init impl (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
        ((embedVerifier lastIfTrue).run stmt cheat)]
      {obs | ∃ t, obs.2.2 = some t ∧ (langProblem langOut).language () t} ≤ ε :=
  (soundness_iff init impl lastIfTrue langIn langOut ε).mpr h (fun _ => Bool) stmt trivial
    (fun hl => hstmt ((langProblem_language langIn stmt).mp hl)) cheat

/-- Interaction-layer soundness of the embedded verifier bounds a cheating legacy prover. -/
example [∀ i, SampleableType (twoWay.Challenge i)] (init : ProbComp Unit)
    (impl : QueryImpl []ₒ (StateT Unit ProbComp))
    (langIn langOut : Set Nat) (ε : ℝ≥0)
    (h : (embedVerifier lastIfTrue).soundness init impl
      (plainChallengeImpl ProtocolSpec.challengeQueryImpl) (langProblem langIn)
      (langProblem langOut) ε) :
    lastIfTrue.soundness init impl langIn langOut ε :=
  (soundness_iff init impl lastIfTrue langIn langOut ε).mp h

/-! ### Knowledge soundness -/

/-- A cheating prover with outputs: it sends `42`, answers the challenge `true` with `7`, and
outputs the statement `0` with the witness `5`. -/
def cheatK : Core.Prover plainSig []ₒ (protocol twoWay) (fun _ => Nat × Nat) :=
  pure ⟨(42 : Nat), pure fun (b : Bool) =>
    pure ⟨(bif b then 7 else 0 : Nat), pure ((0, 5) : Nat × Nat)⟩⟩

/-- `translate` keeps the outputs: embedding the translation gives back the prover itself. -/
example (stmt : Nat) : embedProver (translate cheatK) stmt ⟨⟩ = cheatK :=
  embedProver_translate cheatK stmt

/-- A legacy extractor that returns the first message. -/
def firstMessage : _root_.Extractor.Straightline []ₒ Nat Nat Nat twoWay :=
  fun _ _ tr _ _ => pure (show Nat from tr 0)

def extractionOutputs
    (z : Observation plainSig (protocol twoWay) (fun _ => Nat × Nat) (fun _ => Nat) ×
      Option Nat) :
    Option Nat × Option Nat :=
  (z.1.2.2, z.2)

/-- In the interaction-layer extraction game, the lifted extractor reads the first message off
the decoded transcript after acceptance. -/
example : extractionOutputs (simulateQ (coreAnswers true)
    (extractionGame (embedVerifier lastIfTrue) (fun _ o => o.2) (liftExtractor firstMessage) 2
      cheatK)) = (some 9, some 42) := by
  decide

/-- After rejection, the extractor does not run. -/
example : extractionOutputs (simulateQ (coreAnswers false)
    (extractionGame (embedVerifier lastIfTrue) (fun _ o => o.2) (liftExtractor firstMessage) 2
      cheatK)) = (none, none) := by
  decide

/-- Lowering and lifting an extractor gives it back. -/
example : liftExtractor (lowerExtractor (liftExtractor firstMessage)) =
    liftExtractor firstMessage :=
  liftExtractor_lowerExtractor _

/-- Legacy knowledge soundness of `lastIfTrue` with `firstMessage` bounds the knowledge bad
event of the cheating interaction-layer prover, through the knowledge-soundness transfer. -/
example [∀ i, SampleableType (twoWay.Challenge i)] (init : ProbComp Unit)
    (impl : QueryImpl []ₒ (StateT Unit ProbComp)) (relIn relOut : Set (Nat × Nat)) (ε : ℝ≥0)
    (h : lastIfTrue.knowledgeSoundnessWith init impl relIn relOut firstMessage ε) (stmt : Nat) :
    letI : MeasurableSpace
      (Observation plainSig (protocol twoWay) (fun _ => Nat × Nat) (fun _ => Nat)) := ⊤
    letI : MeasurableSpace Nat := ⊤
    (classicalStraightline (Out := fun _ => Nat × Nat) (fun _ => Nat) (embedVerifier lastIfTrue)
        init impl (plainChallengeImpl ProtocolSpec.challengeQueryImpl) (fun _ o => o.2)).experiment
      (liftExtractor firstMessage) stmt cheatK
      {z | (knowledgeJudgement relOut).valid z.1 ∧
        ∀ wit ∈ z.2, ¬ (relProblem relIn).rel () stmt wit} ≤ ε :=
  ((knowledgeSoundnessWith_iff init impl lastIfTrue relIn relOut firstMessage ε).mpr h
    stmt trivial cheatK).2.2

/-- Interaction-layer knowledge soundness of `lastIfTrue`, embedded. -/
def coreKnowledge [∀ i, SampleableType (twoWay.Challenge i)] (init : ProbComp Unit)
    (impl : QueryImpl []ₒ (StateT Unit ProbComp)) (relIn relOut : Set (Nat × Nat)) (ε : ℝ≥0) :
    Prop :=
  letI : MeasurableSpace
    (Observation plainSig (protocol twoWay) (fun _ => Nat × Nat) (fun _ => Nat)) := ⊤
  letI : MeasurableSpace Nat := ⊤
  knowledgeSoundness
    ((embedVerifier lastIfTrue).classicalModel init impl
      (plainChallengeImpl ProtocolSpec.challengeQueryImpl))
    (relProblem relIn) (relProblem relOut) (knowledgeJudgement relOut)
    (classicalStraightline (fun _ => Nat) (embedVerifier lastIfTrue) init impl
      (plainChallengeImpl ProtocolSpec.challengeQueryImpl) (fun _ o => o.2)) ε

/-- Interaction-layer knowledge soundness of the embedded verifier gives legacy knowledge
soundness, and conversely. -/
example [∀ i, SampleableType (twoWay.Challenge i)] (init : ProbComp Unit)
    (impl : QueryImpl []ₒ (StateT Unit ProbComp)) (relIn relOut : Set (Nat × Nat)) (ε : ℝ≥0) :
    coreKnowledge init impl relIn relOut ε ↔
      lastIfTrue.knowledgeSoundness init impl relIn relOut ε :=
  knowledgeSoundness_iff init impl lastIfTrue relIn relOut ε

/-! ### Round-by-round soundness and knowledge soundness -/

/-- The full prefix after the first message `42`. -/
def afterFirst :=
  PrefixMoves.snoc plainSig (Cursor.Spine.root (protocol twoWay)) PUnit.unit (42 : Nat)

/-- After the first message `42`, the legacy prefix is at round `1` and records `42`. -/
example : (legacyPrefix _ afterFirst).1 = 1 ∧
    (show Nat from
      (show Transcript 1 twoWay from (legacyPrefix _ afterFirst).2) ⟨0, by decide⟩) = 42 :=
  ⟨rfl, rfl⟩

/-- The empty full prefix is the empty legacy transcript at round `0`. -/
example : legacyPrefix (pSpec := twoWay) (.root _) ⟨⟩ = ⟨0, default⟩ :=
  legacyPrefix_root twoWay

/-- Legacy round-by-round soundness of `lastIfTrue` transfers to the embedded verifier when
`init` is `pure ()`, which can produce every state of `Unit`: full support gives the all-state
terminal certificates. -/
example [∀ i, SampleableType (twoWay.Challenge i)] (impl : QueryImpl []ₒ (StateT Unit ProbComp))
    (langIn langOut : Set Nat) (ε : twoWay.ChallengeIdx → ℝ≥0)
    (h : lastIfTrue.rbrSoundness (pure ()) impl langIn langOut ε) :
    (embedVerifier lastIfTrue).rbrSoundness impl (langProblem langIn) (langProblem langOut)
      (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
      (fun c => ε (challengeRound 0 3 (Nat.zero_add 3) c)) :=
  embedVerifier_rbrSoundness (pure ()) impl lastIfTrue langIn langOut ε
    (StateTerminalCertificate.of_support_init fun _ => by simp) h

/-- Round-by-round soundness of the embedded verifier gives legacy round-by-round soundness for
every `init`. -/
example [∀ i, SampleableType (twoWay.Challenge i)] (init : ProbComp Unit)
    (impl : QueryImpl []ₒ (StateT Unit ProbComp)) (langIn langOut : Set Nat)
    (ε : twoWay.ChallengeIdx → ℝ≥0)
    (h : (embedVerifier lastIfTrue).rbrSoundness impl (langProblem langIn) (langProblem langOut)
      (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
      (fun c => ε (challengeRound 0 3 (Nat.zero_add 3) c))) :
    lastIfTrue.rbrSoundness init impl langIn langOut ε :=
  rbrSoundness_of_embedVerifier init impl lastIfTrue langIn langOut ε h

/-- Round-by-round knowledge soundness of the embedded verifier is legacy round-by-round
knowledge soundness, for `Nat` witnesses and `init := pure ()`. -/
example [∀ i, SampleableType (twoWay.Challenge i)] (impl : QueryImpl []ₒ (StateT Unit ProbComp))
    (relIn relOut : Set (Nat × Nat)) (ε : twoWay.ChallengeIdx → ℝ≥0) :
    Verifier.rbrKnowledgeSoundness.{0, 0, 0} (embedVerifier lastIfTrue) impl (fun _ => True)
        (fun stmt w => (stmt, w) ∈ relIn) (fun _ t w => (t, w) ∈ relOut)
        (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
        (fun c => ε (challengeRound 0 3 (Nat.zero_add 3) c)) ↔
      lastIfTrue.rbrKnowledgeSoundness (pure ()) impl relIn relOut ε :=
  rbrKnowledgeSoundness_iff (pure ()) impl lastIfTrue relIn relOut ε
    (fun _ _ => KnowledgeTerminalCertificate.of_support_init fun _ => by simp)

/-! ### A `Bool` ambient state drawn as `pure false`

`init := pure false` cannot produce the ambient state `true`, so full support fails. The verdict
of `lastIfTrue` depends only on the statement and the transcript, and its guarded form supplies
the all-state terminal certificates for this `init`. -/

/-- `lastIfTrue` is guarded: it accepts exactly when the challenge is `true`. -/
def lastIfTrueGuarded : lastIfTrue.GuardedForm where
  check _ tr := show Bool from tr 1
  out stmt tr := stmt + show Nat from tr 2
  verify_eq _ _ := Bool.cond_eq_ite _ _ _

/-- `pure false` does not produce the ambient state `true`. -/
example : true ∉ support (pure false : ProbComp Bool) := by
  simp

/-- The legacy verdict of `lastIfTrue` is the same from both ambient states. -/
example (impl : QueryImpl []ₒ (StateT Bool ProbComp)) (stmt : Nat) (tr : FullTranscript twoWay) :
    (simulateQ impl (lastIfTrue.verify stmt tr).run).run' true =
      (simulateQ impl (lastIfTrue.verify stmt tr).run).run' false := by
  rw [guarded_run' lastIfTrueGuarded, guarded_run' lastIfTrueGuarded]

/-- Legacy round-by-round soundness of `lastIfTrue` from `init := pure false` transfers to the
embedded verifier through the guarded certificates. -/
example [∀ i, SampleableType (twoWay.Challenge i)] (impl : QueryImpl []ₒ (StateT Bool ProbComp))
    (langIn langOut : Set Nat) (ε : twoWay.ChallengeIdx → ℝ≥0)
    (h : lastIfTrue.rbrSoundness (pure false) impl langIn langOut ε) :
    (embedVerifier lastIfTrue).rbrSoundness impl (langProblem langIn) (langProblem langOut)
      (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
      (fun c => ε (challengeRound 0 3 (Nat.zero_add 3) c)) :=
  embedVerifier_rbrSoundness (pure false) impl lastIfTrue langIn langOut ε
    (StateTerminalCertificate.of_guarded lastIfTrueGuarded) h

/-- Round-by-round knowledge soundness of the embedded verifier is legacy round-by-round
knowledge soundness from `init := pure false`, through the guarded certificates. -/
example [∀ i, SampleableType (twoWay.Challenge i)] (impl : QueryImpl []ₒ (StateT Bool ProbComp))
    (relIn relOut : Set (Nat × Nat)) (ε : twoWay.ChallengeIdx → ℝ≥0) :
    Verifier.rbrKnowledgeSoundness.{0, 0, 0} (embedVerifier lastIfTrue) impl (fun _ => True)
        (fun stmt w => (stmt, w) ∈ relIn) (fun _ t w => (t, w) ∈ relOut)
        (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
        (fun c => ε (challengeRound 0 3 (Nat.zero_add 3) c)) ↔
      lastIfTrue.rbrKnowledgeSoundness (pure false) impl relIn relOut ε :=
  rbrKnowledgeSoundness_iff (pure false) impl lastIfTrue relIn relOut ε
    (fun _ _ => KnowledgeTerminalCertificate.of_guarded lastIfTrueGuarded)

/-- The state-independence certificate applies to `lastIfTrue` from `init := pure false`. -/
example [∀ i, SampleableType (twoWay.Challenge i)] (impl : QueryImpl []ₒ (StateT Bool ProbComp))
    (langIn langOut : Set Nat)
    (S : lastIfTrue.StateFunction (pure false) impl langIn langOut) :
    StateTerminalCertificate S :=
  StateTerminalCertificate.of_stateIndependent (fun stmt tr _ _ => by
    rw [guarded_run' lastIfTrueGuarded, guarded_run' lastIfTrueGuarded]) S

end Interaction.Core.Legacy.SecurityTests
