/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestoration
public import ArkLib.Interaction.Oracle.Security.KnowledgeComposition
public import PolyFun.Interaction.TwoParty.Strategy

/-!
# Native verifier replay for state restoration

A scripted native prover sends selected oracle messages and remembers every public challenge.
The restricted verifier runs declared challenge programs and a terminal program that can read
only its accumulated input and message access. The existing native executor interprets that
terminal program with the closing handler of the same concrete execution path.

Path-based replay reads completed challenges from the native path itself. Completion's structural
support guarantees that this path has the selected messages, so replay makes no additional oracle
queries and requires no global response table. The ordinary uniform-program verifier satisfies
actual native challenge freshness for the uniform certificate schedule at every authored prefix.
This covers source-only terminal programs; arbitrary terminal ambient effects are outside this
supported presentation.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.Security.StateRestoration

/-- Actual ambient challenge programs, followed by their public-response-dependent continuation.
This is verifier authoring data; execution uses the existing native interpreter. -/
def ChallengePrograms {ι : Type} (ambient : OracleSpec ι) : List Round → Type
  | [] => PUnit
  | round :: rounds => OracleComp ambient round.Challenge ×
      (round.Challenge → ChallengePrograms ambient rounds)

/-- Forward ambient challenge queries into the ambient side of the restricted native signature. -/
def ambientQueries {ι : Type} (ambient : OracleSpec ι) (access : PFunctor) :
    QueryImpl ambient (OracleComp (ambient + ofPFunctor access)) :=
  fun q => liftM ((ambient + ofPFunctor access).query (Sum.inl q))

/-- Forward source-only terminal queries into the accumulated native input/message access. -/
def sourceQueries {ι : Type} (ambient : OracleSpec ι) (access : PFunctor) :
    QueryImpl (ofPFunctor access) (OracleComp (ambient + ofPFunctor access)) :=
  fun q => liftM ((ambient + ofPFunctor access).query (Sum.inr q))

/-- Native restricted verifier: oracle receives are pure; each public challenge is the supplied
ambient program. No concrete oracle payload is available to authoring. -/
def challengeFragment {ι : Type} (ambient : OracleSpec ι) : (rounds : List Round) →
    (initial : PFunctor) → ChallengePrograms ambient rounds →
    Verifier.Fragment ambient (protocol rounds).tree (protocol rounds).roles
      (protocol rounds).oracles initial (fun _ => Unit)
  | [], _, _ => ()
  | round :: rounds, initial, programs =>
      let extended := Access.extend initial round.interface
      pure (do
        let challenge ← simulateQ (ambientQueries ambient extended) programs.1
        pure ⟨challenge, challengeFragment ambient rounds extended (programs.2 challenge)⟩)

/-- Complete the native fragment with a deterministic source-only terminal program. It can
query accumulated inputs/messages; ambient randomness is confined to challenge programs. -/
def challengeVerifier {ι : Type} (ambient : OracleSpec ι) (rounds : List Round)
    (initial : PFunctor) (programs : ChallengePrograms ambient rounds)
    (Out : (protocol rounds).tree.BranchPath → Type)
    (terminal : (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (Out p)) :
    Verifier.Strategy ambient (protocol rounds).tree (protocol rounds).roles
      (protocol rounds).oracles initial Out :=
  Verifier.Fragment.mapOutput ambient (fun p _ =>
    simulateQ (sourceQueries ambient (accessAfter (protocol rounds).tree
      (protocol rounds).oracles initial p)) (terminal p))
    (challengeFragment ambient rounds initial programs)

/-- Fixed native message authoring, responding to each public challenge. -/
def messageProver {ι : Type} {Salt : Type} (ambient : OracleSpec ι) :
    (rounds : List Round) → Messages Salt rounds →
    Prover.Strategy ambient (protocol rounds).tree (protocol rounds).roles (fun _ => Unit)
  | [], _ => ()
  | _ :: rounds, (message, _, messages) =>
      pure ⟨message, fun _ => pure (messageProver ambient rounds messages)⟩

/-- Scripted native prover retains every public response in its private output. Salts only select
restoration keys and are never added to the native protocol. -/
def scriptedProver {ι : Type} {Salt : Type} (ambient : OracleSpec ι)
    (rounds : List Round) (messages : Messages Salt rounds) :
    Prover.Strategy ambient (protocol rounds).tree (protocol rounds).roles
      (fun _ => (protocol rounds).tree.BranchPath) :=
  StrategyOver.TwoParty.Focal.mapOutput
    (fun path _ => (ExecutionPath.ofTypeTreePath path).toBranchPath)
    (messageProver ambient rounds messages)

/-- Replay data reads only challenges from the native path already obtained by completion. -/
def pathPrograms {ι : Type} (ambient : OracleSpec ι) : (rounds : List Round) →
    (protocol rounds).tree.ExecutionPath → ChallengePrograms ambient rounds
  | [], _ => PUnit.unit
  | _ :: rounds, path => ⟨pure path.2.1, fun _ => pathPrograms ambient rounds path.2.2⟩

/-- Concrete oracle messages match the selected restoration messages; salts have no native role. -/
def MatchesMessages {Salt : Type} : (rounds : List Round) → Messages Salt rounds →
    (protocol rounds).tree.ExecutionPath → Prop
  | [], _, _ => True
  | _ :: rounds, (message, _, messages), path =>
      path.1 = message ∧ MatchesMessages rounds messages path.2.2

/-- Oracle simulation cannot add terminal outputs outside the original structural support. -/
private theorem simulateQ_support_subset {ι κ : Type}
    {ambient : OracleSpec ι} {source : OracleSpec κ}
    (impl : QueryImpl source (OracleComp ambient)) {α : Type} (program : OracleComp source α) :
    support (simulateQ impl program) ⊆ support program := by
  induction program using OracleComp.inductionOn with
  | pure a =>
      intro value supported
      simp only [simulateQ_pure] at supported
      have same := OracleComp.eq_of_mem_support_pure a supported
      subst value
      simp
  | query_bind q k ih =>
      intro value supported
      simp only [simulateQ_bind, simulateQ_liftM_query] at supported
      obtain ⟨response, _, hs⟩ := OracleComp.mem_support_bind_peel _ _ supported
      exact MonadAttach.mem_support_bind.mpr ⟨response, by simp, ih response hs⟩

/-- Every path in the actual open completion program has exactly the authored oracle messages. -/
theorem complete_support_matches {Input Salt : Type} (rounds : List Round) (z : Input)
    (messages : Messages Salt rounds) (path : (protocol rounds).tree.ExecutionPath)
    (supported : path ∈ support (complete rounds z messages)) :
    MatchesMessages rounds messages path := by
  induction rounds with
  | nil => trivial
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      simp only [complete] at supported
      obtain ⟨challenge, _, hs⟩ := OracleComp.mem_support_bind_peel _ _ supported
      obtain ⟨tail, htail, hpure⟩ := OracleComp.mem_support_bind_peel _ _ hs
      have same := OracleComp.eq_of_mem_support_pure _ hpure
      subst path
      exact ⟨rfl, ih messages tail (simulateQ_support_subset _ _ htail)⟩

/-- Ordinary fresh uniform challenge programs. -/
def uniformPrograms : (rounds : List Round) → ChallengePrograms unifSpec rounds
  | [] => PUnit.unit
  | round :: rounds => ⟨$ᵗ round.Challenge, fun _ => uniformPrograms rounds⟩

private theorem simulate_ambientQueries {ι : Type} (ambient : OracleSpec ι) (access : PFunctor)
    (impl : QueryImpl (ofPFunctor access) Id) {α : Type} (program : OracleComp ambient α) :
    simulateQ (Verifier.liftAccessImpl ambient access impl)
      (simulateQ (ambientQueries ambient access) program) = program := by
  rw [← QueryImpl.simulateQ_compose]
  have h : QueryImpl.compose (Verifier.liftAccessImpl ambient access impl)
      (ambientQueries ambient access) = QueryImpl.id' ambient := by
    funext q
    simp [QueryImpl.compose, ambientQueries]
  rw [h, simulateQ_id']

private theorem simulate_sourceQueries {ι : Type} (ambient : OracleSpec ι) (access : PFunctor)
    (impl : QueryImpl (ofPFunctor access) Id) {α : Type}
    (program : OracleComp (ofPFunctor access) α) :
    simulateQ (Verifier.liftAccessImpl ambient access impl)
      (simulateQ (sourceQueries ambient access) program) =
      pure (evalWithAnswerFn impl program) := by
  rw [← QueryImpl.simulateQ_compose]
  have h : QueryImpl.compose (Verifier.liftAccessImpl ambient access impl)
      (sourceQueries ambient access) = impl.liftTarget (OracleComp ambient) := by
    funext q
    simp [QueryImpl.compose, sourceQueries, QueryImpl.liftTarget]
    rfl
  rw [h, simulateQ_liftTarget]
  rfl

/-- The actual native terminal observation uses exactly the run's accumulated closing handler. -/
private theorem execute_sourceTerminal {ι : Type} (ambient : OracleSpec ι)
    (rounds : List Round) (initial : PFunctor)
    (impl : QueryImpl (ofPFunctor initial) Id) (programs : ChallengePrograms ambient rounds)
    (OutP : (protocol rounds).tree.ExecutionPath → Type)
    (prover : Prover.Strategy ambient (protocol rounds).tree (protocol rounds).roles OutP)
    (Out : (protocol rounds).tree.BranchPath → Type)
    (terminal : (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (Out p)) :
    executeStrategies ambient (protocol rounds).tree (protocol rounds).roles
      (protocol rounds).oracles initial impl prover
      (challengeVerifier ambient rounds initial programs Out terminal) =
    (fun result => let path := ExecutionPath.ofTypeTreePath result.1
      ⟨path, result.2.1, evalWithAnswerFn
        (path.closingImpl (protocol rounds).oracles initial impl)
        (terminal path.toBranchPath)⟩) <$>
      TwoParty.run (protocol rounds).tree.toTypeTree
        (RoleDecoration.toTypeTreeRoles (protocol rounds).tree (protocol rounds).roles)
        prover (Verifier.toCounterpartValue ambient (protocol rounds).tree (protocol rounds).roles
          (protocol rounds).oracles initial impl (fun _ => Unit)
          (challengeFragment ambient rounds initial programs)) := by
  have interpreted : Verifier.toCounterpart ambient (protocol rounds).tree (protocol rounds).roles
      (protocol rounds).oracles initial impl Out
      (challengeVerifier ambient rounds initial programs Out terminal) =
    StrategyOver.TwoParty.Counterpart.mapOutput (fun path _ =>
      pure (evalWithAnswerFn ((ExecutionPath.ofTypeTreePath path).closingImpl
        (protocol rounds).oracles initial impl)
        (terminal (ExecutionPath.ofTypeTreePath path).toBranchPath)))
      (Verifier.toCounterpartValue ambient (protocol rounds).tree (protocol rounds).roles
        (protocol rounds).oracles initial impl (fun _ => Unit)
        (challengeFragment ambient rounds initial programs)) := by
    unfold Verifier.toCounterpart challengeVerifier
    rw [Verifier.toCounterpartWith_mapOutput]
    simp only [simulate_sourceQueries]
    exact Verifier.toCounterpartWith_finish_eq_mapOutput ambient (protocol rounds).tree
      (protocol rounds).roles (protocol rounds).oracles initial impl (fun _ => Unit)
      (fun p => OracleComp ambient (Out p))
      (fun path actual _ => pure (evalWithAnswerFn actual (terminal path)))
      (challengeFragment ambient rounds initial programs)
  rw [executeStrategies_eq_run, interpreted, run_counterpart_mapOutput]
  simp only [map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro result
  rfl

/-- The existing paired native runner replays the supplied path when concrete messages match. -/
private theorem pathReplay_run {ι Salt : Type} (ambient : OracleSpec ι)
    (rounds : List Round) (initial : PFunctor)
    (impl : QueryImpl (ofPFunctor initial) Id) (messages : Messages Salt rounds)
    (path : (protocol rounds).tree.ExecutionPath) (matched : MatchesMessages rounds messages path) :
    TwoParty.run (protocol rounds).tree.toTypeTree
      (RoleDecoration.toTypeTreeRoles (protocol rounds).tree (protocol rounds).roles)
      (messageProver ambient rounds messages)
      (Verifier.toCounterpartValue ambient (protocol rounds).tree (protocol rounds).roles
        (protocol rounds).oracles initial impl (fun _ => Unit)
        (challengeFragment ambient rounds initial (pathPrograms ambient rounds path))) =
      pure ⟨path.toTypeTreePath, (), ()⟩ := by
  induction rounds generalizing initial with
  | nil => cases path; rfl
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      rcases path with ⟨actualMessage, challenge, tail⟩
      rcases matched with ⟨same, matched⟩
      change actualMessage = message at same
      change MatchesMessages rounds messages tail at matched
      subst actualMessage
      simp only [messageProver, pathPrograms, challengeFragment,
        protocol, Protocol.oracleWith, Protocol.public,
        Verifier.toCounterpartValue, Verifier.toCounterpartWith]
      change TwoParty.run
        (.node round.Message (fun _ => .node round.Challenge
          (fun _ => (protocol rounds).tree.toTypeTree)))
        ⟨.sender, fun _ => ⟨.receiver, fun _ => RoleDecoration.toTypeTreeRoles
          (protocol rounds).tree (protocol rounds).roles⟩⟩ _ _ = _
      refine (TwoParty.run_sender (m := OracleComp ambient) (X := round.Message)
        (rest := fun _ => _root_.Interaction.TypeTree.node round.Challenge
          (fun _ => (protocol rounds).tree.toTypeTree))
        (rRest := fun _ => ⟨.receiver, fun _ => RoleDecoration.toTypeTreeRoles
          (protocol rounds).tree (protocol rounds).roles⟩)
        (OutputP := fun _ => Unit) (OutputC := fun _ => Unit)
        (pure ⟨message, fun _ => pure (messageProver ambient rounds messages)⟩)
        (fun actualMessage => pure (pure ⟨challenge,
          Verifier.toCounterpartValue ambient (protocol rounds).tree (protocol rounds).roles
            (protocol rounds).oracles (Access.extend initial round.interface)
            (Access.extendImpl initial round.interface impl actualMessage) (fun _ => Unit)
            (challengeFragment ambient rounds (Access.extend initial round.interface)
              (pathPrograms ambient rounds tail))⟩))).trans ?_
      simp only [pure_bind]
      have receiverStep := TwoParty.run_receiver (m := OracleComp ambient) (X := round.Challenge)
        (rest := fun _ => (protocol rounds).tree.toTypeTree)
        (rRest := fun _ => RoleDecoration.toTypeTreeRoles
          (protocol rounds).tree (protocol rounds).roles)
        (OutputP := fun _ => Unit) (OutputC := fun _ => Unit)
        (fun _ => pure (messageProver ambient rounds messages))
        (pure ⟨challenge,
          Verifier.toCounterpartValue ambient (protocol rounds).tree (protocol rounds).roles
            (protocol rounds).oracles (Access.extend initial round.interface)
            (Access.extendImpl initial round.interface impl message) (fun _ => Unit)
            (challengeFragment ambient rounds (Access.extend initial round.interface)
              (pathPrograms ambient rounds tail))⟩)
      refine (congrArg (fun computation => do
        let tailOut ← computation
        pure (⟨⟨message, tailOut.1⟩, tailOut.2⟩ :
          (path : _root_.Interaction.TypeTree.Path
            (_root_.Interaction.TypeTree.node round.Message (fun _ =>
              _root_.Interaction.TypeTree.node round.Challenge (fun _ =>
                (protocol rounds).tree.toTypeTree)))) × Unit × Unit)) receiverStep).trans ?_
      simp only [pure_bind]
      simp only [bind_assoc, pure_bind]
      refine (congrArg (fun computation => do
        let tailOut ← computation
        pure (⟨⟨message, ⟨challenge, tailOut.1⟩⟩, tailOut.2⟩ :
          (path : _root_.Interaction.TypeTree.Path
            (_root_.Interaction.TypeTree.node round.Message (fun _ =>
              _root_.Interaction.TypeTree.node round.Challenge (fun _ =>
                (protocol rounds).tree.toTypeTree)))) × Unit × Unit))
        (ih (Access.extend initial round.interface)
          (Access.extendImpl initial round.interface impl message) messages tail matched)).trans ?_
      rfl

/-- Exact path-based replay in the actual native executor. The real game has only this completed
path; its verifier never inspects a global response table or makes additional oracle queries. -/
theorem execute_pathReplay {ι Salt : Type} (ambient : OracleSpec ι)
    (rounds : List Round) (initial : PFunctor)
    (impl : QueryImpl (ofPFunctor initial) Id) (messages : Messages Salt rounds)
    (path : (protocol rounds).tree.ExecutionPath) (matched : MatchesMessages rounds messages path)
    (Out : (protocol rounds).tree.BranchPath → Type)
    (terminal : (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (Out p)) :
    executeStrategies ambient (protocol rounds).tree (protocol rounds).roles
      (protocol rounds).oracles initial impl (scriptedProver ambient rounds messages)
      (challengeVerifier ambient rounds initial (pathPrograms ambient rounds path) Out terminal) =
    pure ⟨path, path.toBranchPath, evalWithAnswerFn
      (path.closingImpl (protocol rounds).oracles initial impl)
      (terminal path.toBranchPath)⟩ := by
  rw [execute_sourceTerminal]
  unfold scriptedProver
  have mapped := TwoParty.run_mapOutput_mapOutput
    (fun path (_ : Unit) => (ExecutionPath.ofTypeTreePath path).toBranchPath)
    (fun _ (out : Unit) => out) (messageProver ambient rounds messages)
    (Verifier.toCounterpartValue ambient (protocol rounds).tree (protocol rounds).roles
      (protocol rounds).oracles initial impl (fun _ => Unit)
      (challengeFragment ambient rounds initial (pathPrograms ambient rounds path)))
  simp only [StrategyOver.TwoParty.Counterpart.mapOutput_id] at mapped
  rw [mapped, pathReplay_run ambient rounds initial impl messages path matched]
  simp only [map_pure]
  congr 1
  rw [ExecutionPath.ofTypeTreePath_toTypeTreePath]

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary native verifier actually samples every receiver challenge according to the
uniform schedule, for all authored oracle messages and every supported continuation. -/
theorem uniformFragment_fresh (error : ENNReal) (rounds : List Round) (initial : PFunctor)
    (impl : QueryImpl (ofPFunctor initial) Id) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) (protocol rounds).tree
      (protocol rounds).roles (protocol rounds).oracles initial impl (fun _ => Unit)
      (challengeFragment unifSpec rounds initial (uniformPrograms rounds))
      (uniformSchedule error rounds) := by
  induction rounds generalizing initial with
  | nil => trivial
  | cons round rounds ih =>
      simp only [protocol, Protocol.oracleWith, Protocol.public, SamplesChallenges,
        challengeFragment, simulateQ_pure, simulateQ_id', uniformSchedule]
      intro message after supported
      have same := OracleComp.eq_of_mem_support_pure _ supported
      subst after
      simp only [uniformPrograms, simulateQ_map, simulate_ambientQueries, ← map_eq_pure_bind]
      constructor
      · intro event
        simp only [Functor.map_map]
      · intro chosen supported
        obtain ⟨challenge, _, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
        exact ih _ _

/-- Source-only terminal authoring preserves actual uniform challenge freshness. -/
theorem uniformVerifier_fresh (error : ENNReal) (rounds : List Round) (initial : PFunctor)
    (impl : QueryImpl (ofPFunctor initial) Id)
    (Out : (protocol rounds).tree.BranchPath → Type)
    (terminal : (p : (protocol rounds).tree.BranchPath) →
      OracleComp (ofPFunctor (accessAfter (protocol rounds).tree
        (protocol rounds).oracles initial p)) (Out p)) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) (protocol rounds).tree
      (protocol rounds).roles (protocol rounds).oracles initial impl _
      (challengeVerifier unifSpec rounds initial (uniformPrograms rounds) Out terminal)
      (uniformSchedule error rounds) := by
  unfold challengeVerifier
  exact samplesChallenges_mapOutput _ _ _ _ _ _ _ _ _ _ _ _
    (uniformFragment_fresh error rounds initial impl)

end Interaction.Oracle.Security.StateRestoration
