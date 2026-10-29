/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Security.RoundByRound
public import ArkLib.OracleReduction.Security.SpecialSoundness
public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness

/-!
# Implications between security notions

This file identifies round-by-round knowledge soundness with soundness of the induced languages, in
both the default fixed-prefix and the prover-averaged forms, and characterizes exactly when this
holds without input witnesses. It also proves the equivalence between special soundness and its
canonical coordinate-wise form. State-restoration security is developed natively in
`Interaction.Oracle.Security.StateRestoration`. The guarded bridges from fixed-prefix round-by-round
security to ordinary security live in `Security.GuardedSoundness` and `Security.GuardedBridges`.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace Verifier

section Implications

/-- Prover-averaged round-by-round knowledge soundness with error `rbrKnowledgeError` implies
prover-averaged round-by-round soundness with the same error `rbrKnowledgeError`. -/
theorem rbrKnowledgeSoundnessAveraged_implies_rbrSoundnessAveraged
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (h : verifier.rbrKnowledgeSoundnessAveraged init impl relIn relOut rbrKnowledgeError) :
    verifier.rbrSoundnessAveraged init impl relIn.language relOut.language rbrKnowledgeError := by
  classical
  unfold rbrKnowledgeSoundnessAveraged at h
  obtain ⟨WitMid, extractor, kSF, hkSF⟩ := h
  by_cases hWout : Nonempty WitOut
  · unfold rbrSoundnessAveraged
    refine ⟨kSF.toStateFunction init impl, ?_⟩
    intro stmtIn hStmtIn WitIn' WitOut' witIn' prover i
    by_cases hWin : Nonempty WitIn
    · let prover' : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec :=
        { PrvState := prover.PrvState
          input := fun _ => prover.input (stmtIn, witIn')
          sendMessage := prover.sendMessage
          receiveChallenge := prover.receiveChallenge
          output := fun st => do
            let out ← prover.output st
            return (out.1, Classical.choice hWout) }
      have hrun : prover'.runToRound i.1.castSucc stmtIn (Classical.choice hWin) =
          prover.runToRound i.1.castSucc stmtIn witIn' := by rfl
      have hrunlog : prover'.runWithLogToRound i.1.castSucc stmtIn (Classical.choice hWin) =
          prover.runWithLogToRound i.1.castSucc stmtIn witIn' := by
        unfold Prover.runWithLogToRound
        rw [hrun]
      let logGame := do
        let s ← init
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover'.runWithLogToRound i.1.castSucc stmtIn (Classical.choice hWin)
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' s
      let plainGame := do
        let s ← init
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn'
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge))).run' s
      have hmap : (fun x => (x.1, x.2.1)) <$> logGame = plainGame := by
        simp [logGame, plainGame, ← Prover.runWithLogToRound_discard_log_eq_runToRound, hrunlog]
        rfl
      have hk := hkSF stmtIn (Classical.choice hWin) prover' i
      change Pr{let x ← plainGame}[
        ¬ (∃ w, kSF i.1.castSucc stmtIn x.1 w) ∧
          ∃ w, kSF i.1.succ stmtIn (x.1.concat x.2) w] ≤ _
      change Pr{let x ← logGame}[∃ w,
        ¬ kSF i.1.castSucc stmtIn x.1
            (extractor.extractMid i.1 stmtIn (x.1.concat x.2.1) w) ∧
          kSF i.1.succ stmtIn (x.1.concat x.2.1) w] ≤ _ at hk
      calc
        _ = Pr{let x ← logGame}[
            ¬ (∃ w, kSF i.1.castSucc stmtIn x.1 w) ∧
              ∃ w, kSF i.1.succ stmtIn (x.1.concat x.2.1) w] := by
              rw [← hmap, prEvent_map]
        _ ≤ Pr{let x ← logGame}[∃ w,
            ¬ kSF i.1.castSucc stmtIn x.1
                (extractor.extractMid i.1 stmtIn (x.1.concat x.2.1) w) ∧
              kSF i.1.succ stmtIn (x.1.concat x.2.1) w] := by
              apply prEvent_mono
              intro x hbad
              obtain ⟨hprev, w, hnext⟩ := hbad
              exact ⟨w, fun hw => hprev ⟨_, hw⟩, hnext⟩
        _ ≤ _ := hk
    · refine (prEvent_eq_zero_of_forall_not _ _ fun x hbad ↦ ?_).trans_le zero_le
      obtain ⟨-, w, hnext⟩ := hbad
      exact hWin ⟨extractor.foldPrefix stmtIn i.1.succ (x.1.concat x.2) w⟩
  · have hLangOut : relOut.language = ∅ := by
      ext stmtOut
      simp only [Set.language, Set.mem_image, Prod.exists, exists_and_right,
        exists_eq_right, Set.mem_empty_iff_false, iff_false]
      intro hex
      exact hWout ⟨hex.choose⟩
    let sF : verifier.StateFunction init impl relIn.language relOut.language :=
      { toFun := fun m stmtIn _ => m = 0 ∧ stmtIn ∈ relIn.language
        toFun_empty := by
          intro stmtIn
          exact fun h => h.2
        toFun_next := by
          intro m hdir stmtIn tr hfalse msg htrue
          exact Fin.succ_ne_zero m htrue.1
        toFun_full := by
          intro stmtIn tr hfalse
          rw [hLangOut]
          exact prEvent_eq_zero_of_forall_not _ _ fun _ ↦ by simp }
    unfold rbrSoundnessAveraged
    refine ⟨sF, ?_⟩
    intro stmtIn hStmtIn WitIn' WitOut' witIn' prover i
    exact (prEvent_eq_zero_of_forall_not _ _ fun _ hbad ↦
      Fin.succ_ne_zero i.1 hbad.2.1).trans_le zero_le

/-- Prover-averaged round-by-round soundness implies prover-averaged round-by-round knowledge
soundness with an unbounded extractor. Without input witnesses the implication holds for all
relations and errors exactly when no input statement, full transcript and output witness exist
together (`forall_rbrSoundnessAveraged_iff_rbrKnowledgeSoundnessAveraged_iff`). -/
theorem rbrSoundnessAveraged_implies_rbrKnowledgeSoundnessAveraged [Nonempty WitIn]
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (h : verifier.rbrSoundnessAveraged init impl relIn.language relOut.language ε) :
    verifier.rbrKnowledgeSoundnessAveraged init impl relIn relOut ε := by
  classical
  obtain ⟨S, hS⟩ := h
  refine ⟨_, _, S.toKnowledgeStateFunctionOfRel init impl, ?_⟩
  intro stmt wit prover i
  let logGame := do
    let s ← init
    (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (do
        let ⟨⟨tr, _⟩, log⟩ ← prover.runWithLogToRound i.1.castSucc stmt wit
        let challenge ← liftComp (pSpec.getChallenge i) _
        return (tr, challenge, log))).run' s
  let plainGame := do
    let s ← init
    (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (do
        let ⟨tr, _⟩ ← prover.runToRound i.1.castSucc stmt wit
        let challenge ← liftComp (pSpec.getChallenge i) _
        return (tr, challenge))).run' s
  have hmap : (fun x => (x.1, x.2.1)) <$> logGame = plainGame := by
    simp [logGame, plainGame, ← Prover.runWithLogToRound_discard_log_eq_runToRound]
  change Pr{let x ← logGame}[rbrExtractionFailureEvent
    (S.toKnowledgeStateFunctionOfRel init impl).toFun
    ((Extractor.RoundByRoundOneShot.ofRelation relIn).toRoundByRoundOfRel relIn)
    i stmt x.1 x.2.1] ≤ _
  by_cases hstmt : stmt ∈ relIn.language
  · refine (prEvent_eq_zero_of_forall_not _ _ fun x hbad => ?_).trans_le zero_le
    exact (S.toKnowledgeStateFunctionOfRel_failure init impl i stmt x.1 x.2.1 hbad).1 hstmt
  · calc
      _ ≤ Pr{let x ← logGame}[¬ S i.1.castSucc stmt x.1 ∧
          S i.1.succ stmt (x.1.concat x.2.1)] := by
        exact prEvent_mono _ _ _ fun x hbad =>
          (S.toKnowledgeStateFunctionOfRel_failure init impl i stmt x.1 x.2.1 hbad).2
      _ = Pr{let x ← plainGame}[¬ S i.1.castSucc stmt x.1 ∧
          S i.1.succ stmt (x.1.concat x.2)] := by
        rw [← hmap, prEvent_map]
      _ ≤ _ := hS stmt hstmt WitIn WitOut wit prover i

/-- Prover-averaged round-by-round knowledge soundness places no efficiency or access restriction
on the extractor, so it coincides with prover-averaged round-by-round soundness of the induced
languages when input witnesses are nonempty.
`rbrSoundnessAveraged_iff_rbrKnowledgeSoundnessAveraged_of_nonempty_or_isEmpty` also covers the
remaining case in which the two coincide. -/
theorem rbrSoundnessAveraged_iff_rbrKnowledgeSoundnessAveraged [Nonempty WitIn]
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {ε : pSpec.ChallengeIdx → ℝ≥0} :
    verifier.rbrSoundnessAveraged init impl relIn.language relOut.language ε ↔
      verifier.rbrKnowledgeSoundnessAveraged init impl relIn relOut ε :=
  ⟨rbrSoundnessAveraged_implies_rbrKnowledgeSoundnessAveraged init impl,
    rbrKnowledgeSoundnessAveraged_implies_rbrSoundnessAveraged init impl⟩

/-- Round-by-round knowledge soundness implies soundness of the induced languages,
with the same error at every fixed transcript prefix. -/
theorem rbrKnowledgeSoundness_implies_rbrSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (h : verifier.rbrKnowledgeSoundness init impl relIn relOut ε) :
    verifier.rbrSoundness init impl relIn.language relOut.language ε := by
  obtain ⟨WitMid, extractor, K, hK⟩ := h
  refine ⟨K.toStateFunction init impl, ?_⟩
  intro stmt _ i tr
  refine le_trans (prEvent_mono _ _ _ ?_) (hK stmt i tr)
  rintro challenge ⟨hprev, w, hnext⟩
  exact ⟨w, fun hw => hprev ⟨_, hw⟩, hnext⟩

/-- Round-by-round soundness implies knowledge soundness with an unbounded extractor.
Without input witnesses the implication holds for all relations and errors exactly when no input
statement, full transcript and output witness exist together
(`forall_rbrSoundness_iff_rbrKnowledgeSoundness_iff`). -/
theorem rbrSoundness_implies_rbrKnowledgeSoundness [Nonempty WitIn]
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (h : verifier.rbrSoundness init impl relIn.language relOut.language ε) :
    verifier.rbrKnowledgeSoundness init impl relIn relOut ε := by
  obtain ⟨S, hS⟩ := h
  refine ⟨_, _, S.toKnowledgeStateFunctionOfRel init impl, ?_⟩
  intro stmt i tr
  by_cases hstmt : stmt ∈ relIn.language
  · refine (prEvent_eq_zero_of_forall_not _ _ fun challenge hbad => ?_).trans_le zero_le
    exact (S.toKnowledgeStateFunctionOfRel_failure init impl i stmt tr challenge hbad).1 hstmt
  · refine le_trans (prEvent_mono _ _ _ ?_) (hS stmt hstmt i tr)
    exact fun challenge hbad =>
      (S.toKnowledgeStateFunctionOfRel_failure init impl i stmt tr challenge hbad).2

/-- With no efficiency or access restriction on extraction, round-by-round knowledge
soundness coincides with soundness of the induced languages for nonempty input witnesses.
`rbrSoundness_iff_rbrKnowledgeSoundness_of_nonempty_or_isEmpty` also covers the
remaining case in which the two coincide. -/
theorem rbrSoundness_iff_rbrKnowledgeSoundness [Nonempty WitIn]
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {ε : pSpec.ChallengeIdx → ℝ≥0} :
    verifier.rbrSoundness init impl relIn.language relOut.language ε ↔
      verifier.rbrKnowledgeSoundness init impl relIn relOut ε :=
  ⟨rbrSoundness_implies_rbrKnowledgeSoundness init impl,
    rbrKnowledgeSoundness_implies_rbrSoundness init impl⟩

/-- Prover-averaged round-by-round soundness is the specialization of prover-averaged knowledge
soundness to `Unit` witnesses. -/
theorem rbrSoundnessAveraged_iff_rbrKnowledgeSoundnessAveraged_unit
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {ε : pSpec.ChallengeIdx → ℝ≥0} :
    verifier.rbrSoundnessAveraged init impl langIn langOut ε ↔
      verifier.rbrKnowledgeSoundnessAveraged init impl (langIn ×ˢ (Set.univ : Set Unit))
        (langOut ×ˢ (Set.univ : Set Unit)) ε := by
  simpa only [Set.language, Set.fst_image_prod _ Set.univ_nonempty] using
    (rbrSoundnessAveraged_iff_rbrKnowledgeSoundnessAveraged init impl
      (verifier := verifier) (ε := ε)
      (relIn := langIn ×ˢ (Set.univ : Set Unit)) (relOut := langOut ×ˢ (Set.univ : Set Unit)))

/-- Round-by-round soundness is knowledge soundness specialized to `Unit` witnesses. -/
theorem rbrSoundness_iff_rbrKnowledgeSoundness_unit
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {ε : pSpec.ChallengeIdx → ℝ≥0} :
    verifier.rbrSoundness init impl langIn langOut ε ↔
      verifier.rbrKnowledgeSoundness init impl (langIn ×ˢ (Set.univ : Set Unit))
        (langOut ×ˢ (Set.univ : Set Unit)) ε := by
  simpa only [Set.language, Set.fst_image_prod _ Set.univ_nonempty] using
    (rbrSoundness_iff_rbrKnowledgeSoundness init impl
      (verifier := verifier) (ε := ε)
      (relIn := langIn ×ˢ (Set.univ : Set Unit)) (relOut := langOut ×ˢ (Set.univ : Set Unit)))

/-! ### Inhabitation of witness types

The equivalences above assume `[Nonempty WitIn]`. Without input witnesses they hold for all
relations and errors exactly when no input statement, full transcript and output witness exist
together. Otherwise no round-by-round extractor exists
(`Extractor.RoundByRound.exists_nonempty_iff`): extraction is total, so it must also map rejected
transcripts and unrelated output witnesses. The separation is therefore a consequence of extractor
totality rather than a gap in soundness: knowledge soundness fails for every pair of relations,
while soundness holds whenever the verifier never outputs a statement of the output language, for
instance when it always rejects.

The one-shot notion `rbrKnowledgeSoundnessOneShot` is not characterized here. -/

/-- Prover-averaged round-by-round soundness holds with any error for a verifier that never
outputs a statement of the output language: the everywhere false state function satisfies every
law and has no bad transition. -/
theorem rbrSoundnessAveraged_of_forall_prEvent_eq_zero {langIn : Set StmtIn}
    {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (h : ∀ stmt tr, Pr{let stmtOut ← (OptionT.mk do
      (simulateQ impl (verifier.run stmt tr)).run' (← init))}[stmtOut ∈ langOut] = 0)
    (ε : pSpec.ChallengeIdx → ℝ≥0) :
    verifier.rbrSoundnessAveraged init impl langIn langOut ε :=
  ⟨{ toFun := fun _ _ _ => False
     toFun_empty := fun _ h => h.elim
     toFun_next := fun _ _ _ _ _ _ h => h
     toFun_full := fun stmt tr _ => h stmt tr },
   fun _ _ _ _ _ _ _ => (prEvent_eq_zero_of_forall_not _ _ fun _ h ↦ h.2).trans_le zero_le⟩

/-- Round-by-round soundness holds with any error for a verifier that never outputs a statement of
the output language. -/
theorem rbrSoundness_of_forall_prEvent_eq_zero {langIn : Set StmtIn}
    {langOut : Set StmtOut} {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (h : ∀ stmt tr, Pr{let stmtOut ← (OptionT.mk do
      (simulateQ impl (verifier.run stmt tr)).run' (← init))}[stmtOut ∈ langOut] = 0)
    (ε : pSpec.ChallengeIdx → ℝ≥0) :
    verifier.rbrSoundness init impl langIn langOut ε :=
  ⟨{ toFun := fun _ _ _ => False
     toFun_empty := fun _ h => h.elim
     toFun_next := fun _ _ _ _ _ _ h => h
     toFun_full := fun stmt tr _ => h stmt tr },
   fun _ _ _ _ => (prEvent_eq_zero_of_forall_not _ _ fun _ h ↦ h.2).trans_le zero_le⟩

/-- If no input statement, full transcript and output witness exist together, prover-averaged
round-by-round knowledge soundness holds for every pair of relations, with any error. -/
theorem rbrKnowledgeSoundnessAveraged_of_isEmpty
    [IsEmpty (StmtIn × FullTranscript pSpec × WitOut)]
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} (ε : pSpec.ChallengeIdx → ℝ≥0) :
    verifier.rbrKnowledgeSoundnessAveraged init impl relIn relOut ε :=
  ⟨_, _, KnowledgeStateFunction.ofIsEmpty init impl, fun _ _ _ _ =>
    (prEvent_eq_zero_of_forall_not _ _ fun _ ⟨w, _⟩ ↦ w.elim).trans_le zero_le⟩

/-- If no input statement, full transcript and output witness exist together, round-by-round
knowledge soundness holds for every pair of relations, with any error. -/
theorem rbrKnowledgeSoundness_of_isEmpty
    [IsEmpty (StmtIn × FullTranscript pSpec × WitOut)]
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} (ε : pSpec.ChallengeIdx → ℝ≥0) :
    verifier.rbrKnowledgeSoundness init impl relIn relOut ε :=
  ⟨_, _, KnowledgeStateFunction.ofIsEmpty init impl, fun _ _ _ =>
    (prEvent_eq_zero_of_forall_not _ _ fun _ ⟨w, _⟩ ↦ w.elim).trans_le zero_le⟩

/-- With no input witnesses, an input statement, full transcript and output witness preclude
prover-averaged round-by-round knowledge soundness, whatever the relations and error. -/
theorem not_rbrKnowledgeSoundnessAveraged_of_isEmpty [IsEmpty WitIn] (stmtIn : StmtIn)
    (tr : FullTranscript pSpec) (witOut : WitOut)
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {ε : pSpec.ChallengeIdx → ℝ≥0} :
    ¬ verifier.rbrKnowledgeSoundnessAveraged init impl relIn relOut ε := fun ⟨_, E, _⟩ =>
  (Extractor.RoundByRound.isEmpty_of_isEmpty_witIn stmtIn tr witOut).false E

/-- With no input witnesses, an input statement, full transcript and output witness preclude
round-by-round knowledge soundness, whatever the relations and error. -/
theorem not_rbrKnowledgeSoundness_of_isEmpty [IsEmpty WitIn] (stmtIn : StmtIn)
    (tr : FullTranscript pSpec) (witOut : WitOut)
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {ε : pSpec.ChallengeIdx → ℝ≥0} :
    ¬ verifier.rbrKnowledgeSoundness init impl relIn relOut ε := fun ⟨_, E, _⟩ =>
  (Extractor.RoundByRound.isEmpty_of_isEmpty_witIn stmtIn tr witOut).false E

/-- Prover-averaged round-by-round soundness of the induced languages is knowledge soundness when
input witnesses exist, or when no input statement, full transcript and output witness exist
together. -/
theorem rbrSoundnessAveraged_iff_rbrKnowledgeSoundnessAveraged_of_nonempty_or_isEmpty
    (h : Nonempty WitIn ∨ IsEmpty (StmtIn × FullTranscript pSpec × WitOut))
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {ε : pSpec.ChallengeIdx → ℝ≥0} :
    verifier.rbrSoundnessAveraged init impl relIn.language relOut.language ε ↔
      verifier.rbrKnowledgeSoundnessAveraged init impl relIn relOut ε := by
  rcases h with h | h
  · exact rbrSoundnessAveraged_iff_rbrKnowledgeSoundnessAveraged init impl
  · exact ⟨fun _ => rbrKnowledgeSoundnessAveraged_of_isEmpty init impl ε,
      rbrKnowledgeSoundnessAveraged_implies_rbrSoundnessAveraged init impl⟩

/-- Round-by-round soundness of the induced languages is knowledge soundness when
input witnesses exist, or when no input statement, full transcript and output witness exist
together. -/
theorem rbrSoundness_iff_rbrKnowledgeSoundness_of_nonempty_or_isEmpty
    (h : Nonempty WitIn ∨ IsEmpty (StmtIn × FullTranscript pSpec × WitOut))
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {ε : pSpec.ChallengeIdx → ℝ≥0} :
    verifier.rbrSoundness init impl relIn.language relOut.language ε ↔
      verifier.rbrKnowledgeSoundness init impl relIn relOut ε := by
  rcases h with h | h
  · exact rbrSoundness_iff_rbrKnowledgeSoundness init impl
  · exact ⟨fun _ => rbrKnowledgeSoundness_of_isEmpty init impl ε,
      rbrKnowledgeSoundness_implies_rbrSoundness init impl⟩

/-- Prover-averaged round-by-round soundness of the induced languages coincides with prover-averaged
knowledge soundness for all relations and errors exactly when input witnesses exist, or no input
statement, full transcript and output witness exist together. The condition does not depend on the
verifier, `init`, `impl` or the error. Otherwise the empty relations separate them: soundness holds
and knowledge soundness fails. Without input witnesses the input relation is necessarily empty. -/
theorem forall_rbrSoundnessAveraged_iff_rbrKnowledgeSoundnessAveraged_iff
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} :
    (∀ (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
        (ε : pSpec.ChallengeIdx → ℝ≥0),
      verifier.rbrSoundnessAveraged init impl relIn.language relOut.language ε ↔
        verifier.rbrKnowledgeSoundnessAveraged init impl relIn relOut ε) ↔
      Nonempty WitIn ∨ IsEmpty (StmtIn × FullTranscript pSpec × WitOut) := by
  refine ⟨fun h => ?_, fun h _ _ _ =>
    rbrSoundnessAveraged_iff_rbrKnowledgeSoundnessAveraged_of_nonempty_or_isEmpty init impl h⟩
  by_contra hne
  rw [not_or, not_nonempty_iff, not_isEmpty_iff] at hne
  obtain ⟨_, ⟨stmtIn, tr, witOut⟩⟩ := hne
  refine not_rbrKnowledgeSoundnessAveraged_of_isEmpty init impl stmtIn tr witOut
    ((h ∅ ∅ 0).1 ?_)
  exact rbrSoundnessAveraged_of_forall_prEvent_eq_zero init impl
    (fun _ _ => prEvent_eq_zero_of_forall_not _ _ fun _ ↦ by simp [Set.language]) 0

/-- Round-by-round soundness of the induced languages coincides with round-by-round
knowledge soundness for all relations and errors exactly when input witnesses exist, or no input
statement, full transcript and output witness exist together. The condition does not depend on
the verifier, `init`, `impl` or the error. -/
theorem forall_rbrSoundness_iff_rbrKnowledgeSoundness_iff
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} :
    (∀ (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
        (ε : pSpec.ChallengeIdx → ℝ≥0),
      verifier.rbrSoundness init impl relIn.language relOut.language ε ↔
        verifier.rbrKnowledgeSoundness init impl relIn relOut ε) ↔
      Nonempty WitIn ∨ IsEmpty (StmtIn × FullTranscript pSpec × WitOut) := by
  refine ⟨fun h => ?_, fun h _ _ _ =>
    rbrSoundness_iff_rbrKnowledgeSoundness_of_nonempty_or_isEmpty init impl h⟩
  by_contra hne
  rw [not_or, not_nonempty_iff, not_isEmpty_iff] at hne
  obtain ⟨_, ⟨stmtIn, tr, witOut⟩⟩ := hne
  refine not_rbrKnowledgeSoundness_of_isEmpty init impl stmtIn tr witOut
    ((h ∅ ∅ 0).1 ?_)
  exact rbrSoundness_of_forall_prEvent_eq_zero init impl
    (fun _ _ => prEvent_eq_zero_of_forall_not _ _ fun _ ↦ by simp [Set.language]) 0

end Implications

end Verifier

/-! ## Coordinate-wise special soundness generalizes special soundness

Both `Verifier.specialSound` (`Security.SpecialSoundness`) and
`Verifier.coordinateWiseSpecialSound` (`Security.CoordinateWiseSpecialSoundness`) are *defined* as
instances of the shape-generic `Verifier.treeSpecialSound`, differing only in the challenge-tree
shape they fix:

* plain special soundness fixes `distinctShape k` — arity `kᵢ`, node predicate `Function.Injective`
  (the `kᵢ` sibling challenges are pairwise distinct);
* CWSS fixes `D.toShape` — arity `ℓᵢ·(kᵢ-1)+1`, node predicate `IsSpecialSoundFamily ℓᵢ kᵢ`.

For the canonical `ℓᵢ = 1` structure `CWSSStructure.ofSpecialSound k` the two shapes are *equal*
(`toShape_ofSpecialSound_eq_distinctShape`): the arity is `kᵢ` and `IsSpecialSoundFamily 1 kᵢ`
reduces to injectivity (`CoordinateWise.isSpecialSoundFamily_one_iff_injective`). The bridge
`Verifier.coordinateWiseSpecialSound_ofSpecialSound_iff` is then immediate from that shape
equality. -/

/-- Heterogeneous congruence for `Function.Injective`: injectivity transports across an equality of
the domain type together with a heterogeneous equality of the functions. -/
private theorem heq_injective {A A' β : Type} (h : A = A') {f : A → β} {g : A' → β}
    (hfg : HEq f g) : HEq (Function.Injective f) (Function.Injective g) := by
  subst h; obtain rfl := eq_of_heq hfg; exact HEq.rfl

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- The CWSS shape of the canonical `ℓᵢ = 1` structure `CWSSStructure.ofSpecialSound k` is exactly
the plain special-soundness shape `distinctShape k`. This is the structural heart of the equivalence
between CWSS and plain special soundness: both the arity (`1·(kᵢ-1)+1 = kᵢ`) and the node predicate
(`IsSpecialSoundFamily 1 kᵢ` vs. `Function.Injective`) agree. -/
theorem toShape_ofSpecialSound_eq_distinctShape (k : pSpec.ChallengeIdx → ℕ) (hk : ∀ i, 2 ≤ k i) :
    (CWSSStructure.ofSpecialSound k hk).toShape = distinctShape k := by
  have harity : (CWSSStructure.ofSpecialSound k hk).toShape.arity = (distinctShape k).arity := by
    funext i
    change 1 * (k i - 1) + 1 = k i
    have := hk i; omega
  refine ChallengeTreeShape.ext harity (Function.hfunext rfl (fun i i' hi => ?_))
  obtain rfl := eq_of_heq hi
  refine Function.hfunext (by rw [harity]) (fun c c' hc => ?_)
  refine HEq.trans (heq_of_eq (propext ?_)) (heq_injective (congrArg Fin (congrFun harity i)) hc)
  change CoordinateWise.IsSpecialSoundFamily 1 (k i)
      (fun j : Fin (1 * (k i - 1) + 1) =>
        (Equiv.funUnique (Fin 1) (pSpec.Challenge i)).symm (c j)) ↔ Function.Injective c
  rw [CoordinateWise.isSpecialSoundFamily_one_iff_injective]
  exact Equiv.comp_injective c (Equiv.funUnique (Fin 1) (pSpec.Challenge i)).symm

namespace Verifier

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **Coordinate-wise special soundness generalizes special soundness.** Coordinate-wise special
soundness for the canonical `ℓᵢ = 1` structure `CWSSStructure.ofSpecialSound k` is *equivalent* to
plain `(k)`-special soundness for the same input and output relations. Both unfold to
`Verifier.treeSpecialSound` of a shape, and the two shapes are equal
(`toShape_ofSpecialSound_eq_distinctShape`), so the bridge is immediate. This is the
`coordinateWiseSpecialSound (ofSpecialSound k) ↔ specialSound k` bridge promised in
`Security.SpecialSoundness`: CWSS recovers `k`-special soundness in the single-coordinate case. -/
theorem coordinateWiseSpecialSound_ofSpecialSound_iff (k : pSpec.ChallengeIdx → ℕ)
    (hk : ∀ i, 2 ≤ k i)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) :
    verifier.coordinateWiseSpecialSound (WitOut := WitOut) init impl
      (CWSSStructure.ofSpecialSound k hk) relIn relOut
      ↔ verifier.specialSound init impl k relIn relOut := by
  unfold Verifier.coordinateWiseSpecialSound Verifier.specialSound
  rw [toShape_ofSpecialSound_eq_distinctShape]

end Verifier

namespace OracleVerifier

open ProtocolSpec

variable {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [∀ i, OracleInterface (OStmtOut i)]
  [∀ i, OracleInterface (pSpec.Message i)]

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **Coordinate-wise special soundness vs. plain special soundness, oracle form.** The oracle-
reduction analogue of `Verifier.coordinateWiseSpecialSound_ofSpecialSound_iff`, obtained by passing
to the underlying non-oracle verifier (both notions are defined via `OracleVerifier.toVerifier`). -/
theorem coordinateWiseSpecialSound_ofSpecialSound_iff (k : pSpec.ChallengeIdx → ℕ)
    (hk : ∀ i, 2 ≤ k i)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
    verifier.coordinateWiseSpecialSound (WitOut := WitOut) init impl
      (CWSSStructure.ofSpecialSound k hk) relIn relOut
      ↔ verifier.specialSound init impl k relIn relOut :=
  Verifier.coordinateWiseSpecialSound_ofSpecialSound_iff init impl k hk relIn relOut
    verifier.toVerifier

end OracleVerifier
