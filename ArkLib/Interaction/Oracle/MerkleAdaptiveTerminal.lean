/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.MerkleTerminalBatch

/-!
# Causal terminal Merkle query programs

A malicious committer completes all commitment phases before supplying one terminal list of
openings. The verifier checks every opening, then interprets a finite causal program against the
ordered list. Each later request can depend on earlier selected values. The ideal interpretation
uses the corresponding immutable commitment-time extracted values instead.
-/

@[expose] public section

namespace Interaction.Oracle.MerkleAdaptiveTerminal

open OracleComp OracleSpec Interaction.Oracle Interaction.TwoParty
open BinaryTree InductiveMerkleTree MerkleTreeMultiExtractability
open Interaction.Oracle.MerkleTerminalBatch

variable {Cfg Query Address Y : Type}
variable {config : Configuration Cfg Address} {rounds : ℕ} {α β : Type}

/-- A causal terminal program with at most `depth` requests. `done` may stop early. Each
continuation sees only the ordered digest answers to its own request. -/
inductive QueryProgram (config : Configuration Cfg Address) (rounds : ℕ) (Y : Type) :
    ℕ → Type where
  | done {depth : ℕ} (accept : Bool) : QueryProgram config rounds Y depth
  | request {depth : ℕ} (site : QuerySite config rounds)
      (next : List Y → QueryProgram config rounds Y depth) :
      QueryProgram config rounds Y (depth + 1)

/-- Embed an existing fixed query plan into the causal syntax, retaining its original ordered
decision rule. Adaptive programs extend this case by choosing later sites from earlier answers. -/
def QueryProgram.ofSites (sites : List (QuerySite config rounds))
    (decide : List (List Y) → Bool) : QueryProgram config rounds Y sites.length :=
  match sites with
  | [] => .done (decide [])
  | site :: rest => .request site (fun answer =>
      QueryProgram.ofSites rest (fun remaining => decide (answer :: remaining)))

def QueryProgram.ofQueryPlan (plan : QueryPlan config rounds Y) :
    QueryProgram config rounds Y plan.sites.length :=
  QueryProgram.ofSites plan.sites plan.decide

/-- Number of selected leaves, in the same left-to-right order as `selectedValuesList`. -/
def selectorLength : {s : Skeleton} → LeafData Bool s → ℕ
  | _, .leaf selected => if selected then 1 else 0
  | _, .internal left right => selectorLength left + selectorLength right

theorem selectedValuesList_length {s : Skeleton} {selector : LeafData Bool s}
    (values : SelectedValues Y selector) :
    (selectedValuesList values).length = selectorLength selector := by
  induction selector with
  | leaf selected =>
      cases selected <;> rfl
  | internal left right ihl ihr =>
      simp [selectedValuesList, selectorLength, ihl values.1, ihr values.2]

/-- The public request check includes the commitment occurrence, both selectors, and the
actual response length. The latter is redundant for a well-typed opening, but remains an
explicit part of transcript validation. -/
def requestValid [DecidableEq Cfg] (config : Configuration Cfg Address) {rounds : ℕ}
    (roots : List (Cfg × Y)) (site : QuerySite config rounds)
    (submitted : PublicOpening config rounds Y) : Bool :=
  siteMatches config site submitted &&
    decide (((roots[site.slot.val]?).map Prod.fst) = some site.tag) &&
    site.selector.anySelected &&
    decide ((selectedValuesList submitted.opening.values).length =
      selectorLength site.selector)

/-- Consume precisely one submitted opening for every request. Extra or missing openings
reject, including after an early `done`. -/
def checkTranscriptAux [DecidableEq Cfg] (config : Configuration Cfg Address)
    (roots : List (Cfg × Y)) :
    (depth : ℕ) → QueryProgram config rounds Y depth →
      List (PublicOpening config rounds Y) → Bool
  | _, .done accept, openings => accept && openings.isEmpty
  | _ + 1, .request site next, submitted :: rest =>
      requestValid config roots site submitted &&
        checkTranscriptAux config roots _
          (next (selectedValuesList submitted.opening.values)) rest
  | _ + 1, .request _ _, [] => false

/-- Public program validation also requires the complete prescribed commitment history. -/
def checkTranscript [DecidableEq Cfg] (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth)
    (roots : List (Cfg × Y)) (openings : List (PublicOpening config rounds Y)) : Bool :=
  decide (roots.length = rounds) && checkTranscriptAux config roots depth program openings

/-- Pure ideal interpretation. Every branch uses actual checkpoint-extracted answers; neither
the malicious terminal list nor honest opening-verification queries can affect a request. -/
def idealDecisionAux [DecidableEq Cfg] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (state : ExtractorState Cfg Query Address Y config) (fallback : Y)
    (roots : List (Cfg × Y)) :
    (depth : ℕ) → QueryProgram config rounds Y depth → Bool
  | _, .done accept => accept
  | _ + 1, .request site next =>
      decide (((roots[site.slot.val]?).map Prod.fst) = some site.tag) &&
        site.selector.anySelected &&
        idealDecisionAux model state fallback roots _
          (next (selectedValuesList
            (selectedValues (extractA model state fallback site).toLeafData
              site.selector)))

/-- The clean ideal decision is determined by public commitment roots and the immutable
checkpoint state. -/
def idealDecision [DecidableEq Cfg] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (state : ExtractorState Cfg Query Address Y config)
    (roots : List (Cfg × Y)) : Bool :=
  decide (roots.length = rounds) &&
    idealDecisionAux model state fallback roots depth program

/-- Verify every submitted opening before checking the program path and its decision. Thus the
honest query bound counts malformed and excess openings as well as matched ones. -/
def verifyBatch [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (roots : List (Cfg × Y)) (openings : List (PublicOpening config rounds Y)) :
    OracleComp (Query →ₒ Y) Bool := do
  let attempts ← verifyOpeningClaims model
    (publicClaims (Query := Query) roots fallback openings)
  return attempts.all (fun attempt => attempt.2.accepted) &&
    checkTranscript config rounds program roots openings

/-- Native verifier for the same public commitment and terminal-opening protocol. Only the
terminal decision differs from the fixed-plan verifier. -/
def verifier [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y) :
    (remaining : ℕ) → List (Cfg × Y) →
      Verifier.Strategy (Query →ₒ Y) (protocol (Y := Y) config rounds remaining).tree
        (protocol (Y := Y) config rounds remaining).roles
        (protocol (Y := Y) config rounds remaining).oracles 0 (fun _ => Bool)
  | 0, roots => fun openings => pure <| by
      change OracleComp ((Query →ₒ Y) + ofPFunctor 0) Bool
      exact simulateQ
        (fun q => liftM (((Query →ₒ Y) + ofPFunctor 0).query (.inl q)))
        (verifyBatch model config rounds program fallback roots openings)
  | remaining + 1, roots => fun root =>
      pure (verifier model config rounds program fallback remaining (roots ++ [root]))

/-- Actual native execution of the adaptive terminal verifier. -/
def nativeGame [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :=
  executeStrategies (Query →ₒ Y) (protocol (Y := Y) config rounds rounds).tree
    (protocol (Y := Y) config rounds rounds).roles
    (protocol (Y := Y) config rounds rounds).oracles 0
    (fun q => nomatch q)
    (prover config rounds adversary rounds 0 adversary.committer.initialState
      ExtractorState.empty)
    (verifier model config rounds program fallback rounds [])

def nativeExperiment [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :=
  (Query →ₒ Y).withCacheOverlay ∅
    (nativeGame model config rounds program fallback adversary)

/-- Source-order execution, used to check the actual native sender and verifier boundaries. -/
def sourceSuffix [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    (remaining firstRound : ℕ) → adversary.committer.State →
      ExtractorState Cfg Query Address Y config → List (Cfg × Y) →
      OracleComp (Query →ₒ Y) (GameView (Query := Query) config rounds Y)
  | 0, _, state, extractorState, roots => do
      let (openings, terminalSuffix) ← (adversary.opening state extractorState).withQueryLog
      let accepted ← verifyBatch model config rounds program fallback roots openings
      return { roots, openings, extractorState, terminalSuffix, accepted }
  | remaining + 1, firstRound, state, extractorState, roots => do
      let ((tag, root, nextState), phaseLog) ←
        (adversary.committer.commit firstRound state).withQueryLog
      sourceSuffix model config rounds program fallback adversary remaining (firstRound + 1)
        nextState (extractorState.record tag phaseLog root) (roots ++ [(tag, root)])

private theorem terminalForwarding_eq (program : OracleComp (Query →ₒ Y) α) :
    simulateQ (Verifier.liftAccessImpl (Query →ₒ Y) 0
      (fun q => nomatch q))
      (simulateQ
        (fun q => liftM (((Query →ₒ Y) + ofPFunctor 0).query (.inl q)))
        program) = program := by
  rw [← QueryImpl.simulateQ_compose]
  have h : QueryImpl.compose
      (Verifier.liftAccessImpl (Query →ₒ Y) 0 (fun q => nomatch q))
      (fun q => liftM (((Query →ₒ Y) + ofPFunctor 0).query (.inl q))) =
      QueryImpl.id' (Query →ₒ Y) := by
    funext q
    rfl
  rw [h, simulateQ_id']

set_option backward.isDefEq.respectTransparency false in
/-- The native executor has the advertised effect order at every public commitment prefix. -/
theorem nativeSuffix_eq_source [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y)
    (remaining firstRound : ℕ) (state : adversary.committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config)
    (prefixRoots : List (Cfg × Y)) :
    nativeView config rounds remaining prefixRoots <$>
      executeStrategies (Query →ₒ Y) (protocol (Y := Y) config rounds remaining).tree
        (protocol (Y := Y) config rounds remaining).roles
        (protocol (Y := Y) config rounds remaining).oracles 0
        (fun q => nomatch q)
        (prover config rounds adversary remaining firstRound state extractorState)
        (verifier model config rounds program fallback remaining prefixRoots) =
      sourceSuffix model config rounds program fallback adversary remaining firstRound state
        extractorState prefixRoots := by
  induction remaining generalizing firstRound state extractorState prefixRoots with
  | zero =>
      simp only [protocol, Protocol.public_tree, Protocol.public_roles,
        Protocol.public_oracles]
      rw [executeStrategies_public_sender]
      simp only [sourceSuffix, prover, verifier, nativeView, publicTranscript,
        executeStrategies_done, Protocol.done_tree, PFunctor.FreeM.liftBind_eq,
        PFunctor.selfMonomial_B, PFunctor.FreeM.bind_eq_bind,
        TypeTree.runtimeLens_toFunA_public, PFunctor.selfMonomial_A,
        Protocol.done_roles, TypeTree.RoleDecoration.toTypeTreeRoles_done,
        Protocol.done_oracles, ofPFunctor_zero, TypeTree.runtimeLens_toFunB_public,
        Prod.mk.eta, bind_pure_comp, map_bind, Functor.map_map]
      simp only [bind_map_left, simulateQ_pure, List.append_nil]
      apply bind_congr
      rintro ⟨openings, terminalSuffix⟩
      simpa using congrArg
        (fun effect : OracleComp (Query →ₒ Y) Bool =>
          (fun accepted =>
            ({ roots := prefixRoots, openings, extractorState, terminalSuffix,
               accepted } : GameView (Query := Query) config rounds Y)) <$> effect)
        (terminalForwarding_eq (Query := Query) (Y := Y)
          (verifyBatch model config rounds program fallback prefixRoots openings))
  | succ remaining ih =>
      simp only [protocol, Protocol.public_tree, Protocol.public_roles,
        Protocol.public_oracles]
      rw [executeStrategies_public_sender]
      simp only [sourceSuffix, prover, verifier, nativeView, publicTranscript,
        PFunctor.FreeM.liftBind_eq, PFunctor.selfMonomial_B,
        PFunctor.FreeM.bind_eq_bind, TypeTree.runtimeLens_toFunA_public,
        PFunctor.selfMonomial_A, ofPFunctor_zero,
        TypeTree.runtimeLens_toFunB_public, Prod.mk.eta, bind_pure_comp, map_bind,
        Functor.map_map]
      simp only [bind_map_left, simulateQ_pure]
      apply bind_congr
      rintro ⟨⟨tag, root, nextState⟩, phaseLog⟩
      have hview :
          (fun result =>
            ({ roots := prefixRoots ++ (tag, root) ::
                  (publicTranscript config rounds remaining result.1).1
               openings := (publicTranscript config rounds remaining result.1).2
               extractorState := result.2.1.extractorState
               terminalSuffix := result.2.1.terminalSuffix
               accepted := result.2.2 } : GameView (Query := Query) config rounds Y)) =
            nativeView config rounds remaining (prefixRoots ++ [(tag, root)]) := by
        funext result
        simp [nativeView, List.append_assoc]
      rw [hview]
      exact ih (firstRound + 1) nextState
        (extractorState.record tag phaseLog root) (prefixRoots ++ [(tag, root)])

theorem sourceSuffix_eq_runCommitments [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y)
    (remaining firstRound : ℕ) (state : adversary.committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config) :
    sourceSuffix model config rounds program fallback adversary remaining firstRound state
      extractorState (rootsOfState extractorState) = do
        let (finalState, finalExtractorState) ← adversary.committer.runCommitments
          remaining firstRound state extractorState
        let (openings, terminalSuffix) ←
          (adversary.opening finalState finalExtractorState).withQueryLog
        let roots := rootsOfState finalExtractorState
        let accepted ← verifyBatch model config rounds program fallback roots openings
        return { roots := roots, openings := openings, extractorState := finalExtractorState,
                 terminalSuffix := terminalSuffix, accepted := accepted } := by
  induction remaining generalizing firstRound state extractorState with
  | zero =>
      simp [sourceSuffix, SequentialCommitter.runCommitments]
  | succ remaining ih =>
      simp only [sourceSuffix, SequentialCommitter.runCommitments]
      simp only [bind_assoc]
      apply bind_congr
      rintro ⟨⟨tag, root, nextState⟩, phaseLog⟩
      rw [← rootsOfState_record, ih]

theorem nativeGame_eq_source [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    nativeView config rounds rounds [] <$>
      nativeGame model config rounds program fallback adversary = do
        let (finalState, finalExtractorState) ← adversary.committer.runFromEmpty config rounds
        let (openings, terminalSuffix) ←
          (adversary.opening finalState finalExtractorState).withQueryLog
        let roots := rootsOfState finalExtractorState
        let accepted ← verifyBatch model config rounds program fallback roots openings
        return { roots := roots, openings := openings, extractorState := finalExtractorState,
                 terminalSuffix := terminalSuffix, accepted := accepted } := by
  rw [nativeGame, nativeSuffix_eq_source]
  simpa only [SequentialCommitter.runFromEmpty, rootsOfState_empty] using
    sourceSuffix_eq_runCommitments model config rounds program fallback adversary rounds 0
      adversary.committer.initialState
      (ExtractorState.empty : ExtractorState Cfg Query Address Y config)

/-- The Boolean decision on the existing owner coupling, whose attempts record every submitted
opening in source order. -/
def coupledAccept [DecidableEq Cfg] (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth)
    (transcript : CoupledTranscript (Query := Query) config rounds Y) : Bool :=
  transcript.attempts.all (fun attempt => attempt.2.accepted) &&
    checkTranscript config rounds program transcript.roots transcript.openings

def coupledNativeView [DecidableEq Cfg] (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth)
    (transcript : CoupledTranscript (Query := Query) config rounds Y) :
    GameView (Query := Query) config rounds Y :=
  { roots := transcript.roots
    openings := transcript.openings
    extractorState := transcript.extractorState
    terminalSuffix := transcript.terminalSuffix
    accepted := coupledAccept config rounds program transcript }

/-- Public-root and private-checkpoint verification yield the same ordered acceptance bits
and the same verifier-query effects. -/
theorem verifyBatch_eq_coupled [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (state : ExtractorState Cfg Query Address Y config)
    (openings : List (PublicOpening config rounds Y)) :
    verifyBatch model config rounds program fallback (rootsOfState state) openings =
      (fun attempts => attempts.all (fun attempt => attempt.2.accepted) &&
        checkTranscript config rounds program (rootsOfState state) openings) <$>
        verifyOpeningClaims model (attachCheckpoints state fallback openings) := by
  have h := congrArg (fun effect : OracleComp (Query →ₒ Y) (List Bool) =>
      (fun bits => bits.all id &&
        checkTranscript config rounds program (rootsOfState state) openings) <$> effect)
    (verifyOpeningClaims_public_private_bits model state fallback openings)
  simpa [verifyBatch, acceptanceBits, Functor.map_map] using h

/-- Native execution is an exact marginal of the old coupling, including the complete
malicious opening phase and all honest verification effects. -/
theorem coupledInner_native_eq [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    coupledNativeView config rounds program <$>
      coupledInner model config rounds fallback adversary =
      nativeView config rounds rounds [] <$>
        nativeGame model config rounds program fallback adversary := by
  rw [nativeGame_eq_source]
  simp only [coupledInner, map_bind, map_pure]
  apply bind_congr
  rintro ⟨privateState, state⟩
  apply bind_congr
  rintro ⟨openings, terminalSuffix⟩
  rw [verifyBatch_eq_coupled]
  simp [coupledNativeView, coupledAccept, Functor.map_map]

theorem coupledExperiment_native_eq [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    coupledNativeView config rounds program <$>
      coupledExperiment model config rounds fallback adversary =
    nativeView config rounds rounds [] <$>
      nativeExperiment model config rounds program fallback adversary := by
  simp only [coupledExperiment, nativeExperiment, ← withCacheOverlay_map]
  exact congrArg ((Query →ₒ Y).withCacheOverlay ∅)
    (coupledInner_native_eq model config rounds program fallback adversary)

/-- Boolean event observed from the actual native verifier and shared random-oracle cache. -/
def realAcceptanceExperiment [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :=
  (fun view : GameView (Query := Query) config rounds Y => view.accepted) <$>
    (nativeView config rounds rounds [] <$>
      nativeExperiment model config rounds program fallback adversary)

/-- Coupled ideal event; its Boolean value depends only on commitment checkpoints and public
roots, even though the coupling retains the malicious terminal and honest verification phases. -/
def idealAcceptanceExperiment [DecidableEq Cfg] [DecidableEq Query]
    [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :=
  (fun transcript : CoupledTranscript (Query := Query) config rounds Y =>
    idealDecision model config rounds program fallback transcript.extractorState
      transcript.roots) <$>
    coupledExperiment model config rounds fallback adversary

/-- Verification-free and terminal-opening-free ideal game, stopped immediately after the
last commitment checkpoint. -/
def idealCoreExperiment [DecidableEq Cfg] [DecidableEq Query]
    [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :=
  (Query →ₒ Y).withCacheOverlay ∅
    ((fun result : adversary.committer.State × ExtractorState Cfg Query Address Y config =>
      idealDecision model config rounds program fallback result.2 (rootsOfState result.2)) <$>
      adversary.committer.runFromEmpty config rounds)

/-- An accepted checked request has exactly its checkpoint-time selected digest vector, outside
the owning accepted-opening disagreement event. This is the one-step lemma used at every branch. -/
theorem requestAnswer_eq_of_good [DecidableEq Cfg] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (state : ExtractorState Cfg Query Address Y config) (fallback : Y)
    (site : QuerySite config rounds) (submitted : PublicOpening config rounds Y)
    (attempt : AnyEvaluatedOpeningClaim Cfg Query Address Y config)
    (hrequest : requestValid config (rootsOfState state) site submitted = true)
    (hclaim : ∃ accepted : Bool,
      attempt = ⟨submitted.site.tag,
        ⟨checkpointAt state fallback submitted.site, submitted.opening, accepted⟩⟩)
    (haccepted : attempt.2.accepted = true)
    (hnobad : ¬ HasAcceptedOpeningDisagreement model.view state [attempt]) :
    selectedValuesList (selectedValues (extractA model state fallback site).toLeafData
      site.selector) = selectedValuesList submitted.opening.values := by
  have hparts : siteMatches config site submitted = true ∧
      ((rootsOfState state)[site.slot.val]?).map Prod.fst = some site.tag := by
    simp only [requestValid, Bool.and_eq_true, decide_eq_true_eq] at hrequest
    exact ⟨hrequest.1.1.1, hrequest.1.1.2⟩
  have hpairs : List.Forall₂ (fun selected opening =>
      siteMatches config selected opening = true ∧
        ((rootsOfState state)[selected.slot.val]?).map Prod.fst = some selected.tag)
      [site] [submitted] := .cons hparts .nil
  have halign : ClaimsAligned (attachCheckpoints state fallback [submitted])
      [attempt] := by
    unfold ClaimsAligned attachCheckpoints
    simp only [List.map_cons, List.map_nil]
    exact .cons hclaim .nil
  have hall : [attempt].all (fun claim => claim.2.accepted) = true := by
    simpa using haccepted
  have h := selectedAnswers_eq_of_noAcceptedDisagreement model state fallback
    hpairs halign hall hnobad
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
  exact h.1

/-- Causal path agreement: after every checked accepted request, the actual submitted answers
and immutable extracted answers induce the same continuation. The proof recurses through the
program, so it covers adaptive requests rather than a precomputed list of sites. -/
theorem checkTranscriptAux_implies_idealAux
    [DecidableEq Cfg] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (state : ExtractorState Cfg Query Address Y config) (fallback : Y)
    (depth : ℕ) (program : QueryProgram config rounds Y depth)
    (openings : List (PublicOpening config rounds Y))
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config))
    (halign : ClaimsAligned (attachCheckpoints state fallback openings) attempts)
    (hall : attempts.all (fun attempt => attempt.2.accepted) = true)
    (hnobad : ¬ HasAcceptedOpeningDisagreement model.view state attempts)
    (hcheck : checkTranscriptAux config (rootsOfState state) depth program openings = true) :
    idealDecisionAux model state fallback (rootsOfState state) depth program = true := by
  induction depth generalizing openings attempts with
  | zero =>
      cases program with
      | done accept =>
          simp only [checkTranscriptAux, Bool.and_eq_true] at hcheck
          simpa only [idealDecisionAux] using hcheck.1
  | succ depth ih =>
      cases program with
      | done accept =>
          simp only [checkTranscriptAux, Bool.and_eq_true] at hcheck
          simpa only [idealDecisionAux] using hcheck.1
      | request site next =>
          cases openings with
          | nil => simp [checkTranscriptAux] at hcheck
          | cons submitted rest =>
              cases attempts with
              | nil =>
                  simp [ClaimsAligned, attachCheckpoints] at halign
              | cons attempt restAttempts =>
                  have halign' := halign
                  unfold ClaimsAligned attachCheckpoints at halign'
                  simp only [List.map_cons] at halign'
                  cases halign' with
                  | cons hclaim hclaims =>
                      simp only [checkTranscriptAux, Bool.and_eq_true] at hcheck
                      obtain ⟨hrequest, hrest⟩ := hcheck
                      simp only [List.all_cons, Bool.and_eq_true] at hall
                      have hparts : siteMatches config site submitted = true ∧
                          ((rootsOfState state)[site.slot.val]?).map Prod.fst =
                            some site.tag ∧ site.selector.anySelected = true := by
                        simp only [requestValid, Bool.and_eq_true,
                          decide_eq_true_eq] at hrequest
                        exact ⟨hrequest.1.1.1, hrequest.1.1.2, hrequest.1.2⟩
                      have hsingleNoBad :
                          ¬ HasAcceptedOpeningDisagreement model.view state [attempt] := by
                        intro hbad
                        obtain ⟨tag, badAttempt, hmem, hrecorded, hdisagree⟩ := hbad
                        simp only [List.mem_singleton] at hmem
                        exact hnobad ⟨tag, badAttempt, by simp [hmem],
                          hrecorded, hdisagree⟩
                      have hanswer := requestAnswer_eq_of_good model config rounds state
                        fallback site submitted attempt hrequest hclaim hall.1 hsingleNoBad
                      have htailNoBad :
                          ¬ HasAcceptedOpeningDisagreement model.view state restAttempts := by
                        intro hbad
                        obtain ⟨tag, badAttempt, hmem, hrecorded, hdisagree⟩ := hbad
                        exact hnobad ⟨tag, badAttempt, by simp [hmem], hrecorded, hdisagree⟩
                      have htail := ih (next (selectedValuesList submitted.opening.values))
                        rest restAttempts hclaims hall.2 htailNoBad hrest
                      simp only [idealDecisionAux, hparts.2.1, decide_true,
                        hparts.2.2, Bool.true_and]
                      rw [hanswer]
                      exact htail

/-- On an aligned accepting coupled run with no checkpoint disagreement, the clean ideal
program takes exactly the same causal path and accepts. -/
theorem coupledAccept_implies_idealDecision_of_good
    [DecidableEq Cfg] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (transcript : CoupledTranscript (Query := Query) config rounds Y)
    (halign : ClaimsAligned
      (attachCheckpoints transcript.extractorState fallback transcript.openings)
      transcript.attempts)
    (hroots : transcript.roots = rootsOfState transcript.extractorState)
    (hreal : coupledAccept config rounds program transcript = true)
    (hgood : ¬ (coupledOwnerView transcript).HasAnyCheckpointExtractionDisagreement model) :
    idealDecision model config rounds program fallback transcript.extractorState
      transcript.roots = true := by
  unfold coupledAccept at hreal
  simp only [Bool.and_eq_true] at hreal
  obtain ⟨hall, hcheck⟩ := hreal
  unfold checkTranscript at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨hlen, hpath⟩ := hcheck
  have hnobad : ¬ HasAcceptedOpeningDisagreement model.view
      transcript.extractorState transcript.attempts := by
    intro hbad
    exact hgood (Or.inl hbad)
  rw [hroots] at hpath
  have hideal := checkTranscriptAux_implies_idealAux model config rounds
    transcript.extractorState fallback depth program transcript.openings transcript.attempts
    halign hall hnobad hpath
  unfold idealDecision
  rw [hroots] at hlen
  rw [hroots]
  simp [hlen, hideal]

theorem coupledRun_real_implies_ideal_or_bad
    [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y)
    (transcript : CoupledTranscript (Query := Query) config rounds Y)
    (hrun : transcript ∈ support
      (coupledExperiment model config rounds fallback adversary))
    (hreal : coupledAccept config rounds program transcript = true) :
    idealDecision model config rounds program fallback transcript.extractorState
      transcript.roots = true ∨
    (coupledOwnerView transcript).HasAnyCheckpointExtractionDisagreement model := by
  by_cases hbad :
      (coupledOwnerView transcript).HasAnyCheckpointExtractionDisagreement model
  · exact Or.inr hbad
  · exact Or.inl <| coupledAccept_implies_idealDecision_of_good model config rounds
      program fallback transcript
      (coupledExperiment_aligned model config rounds fallback adversary transcript hrun)
      (coupledExperiment_roots model config rounds fallback adversary transcript hrun)
      hreal hbad

/-- Exact native real-event marginal. -/
theorem prob_realAcceptance_eq_coupled
    [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Y]
    [EvalDistSemantics (OracleComp (Query →ₒ Y))]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    Pr{let accepted ← realAcceptanceExperiment model config rounds program fallback adversary}[
      accepted = true] =
      Pr{let transcript ← coupledExperiment model config rounds fallback adversary}[
        coupledAccept config rounds program transcript = true] := by
  unfold realAcceptanceExperiment
  rw [← coupledExperiment_native_eq model config rounds program fallback adversary]
  simp only [Functor.map_map, prEvent_map]
  rfl

/-- Exact coupled ideal-event marginal. -/
theorem prob_idealAcceptance_eq_coupled
    [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [EvalDistSemantics (OracleComp (Query →ₒ Y))]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    Pr{let accepted ← idealAcceptanceExperiment model config rounds program fallback adversary}[
      accepted = true] =
      Pr{let transcript ← coupledExperiment model config rounds fallback adversary}[
        idealDecision model config rounds program fallback transcript.extractorState
          transcript.roots = true] := by
  simp only [idealAcceptanceExperiment, prEvent_map]

/-- The real acceptance event is bounded by the ideal event and the exact owning VCVio
checkpoint-disagreement event. -/
theorem prob_realAcceptance_le_ideal_add_checkpointBad
    [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [EvalDistSemantics (OracleComp (Query →ₒ Y))]
    [LawfulEvalDistSemantics (OracleComp (Query →ₒ Y))]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    Pr{let accepted ← realAcceptanceExperiment model config rounds program fallback adversary}[
      accepted = true] ≤
      Pr{let accepted ← idealAcceptanceExperiment model config rounds program fallback adversary}[
        accepted = true] +
      Pr{let transcript ← (extractabilityExperiment model config rounds
        (toOwningAdversary config rounds fallback adversary))}[
        transcript.HasAnyCheckpointExtractionDisagreement model] := by
  let mx := coupledExperiment model config rounds fallback adversary
  let p := fun (transcript : CoupledTranscript (Query := Query) config rounds Y) =>
    coupledAccept config rounds program transcript = true
  let q := fun (transcript : CoupledTranscript (Query := Query) config rounds Y) =>
    idealDecision model config rounds program fallback
      transcript.extractorState transcript.roots = true
  let bad := fun (transcript : CoupledTranscript (Query := Query) config rounds Y) =>
    (coupledOwnerView transcript).HasAnyCheckpointExtractionDisagreement model
  have hmono : Pr{let transcript ← mx}[p transcript] ≤
      Pr{let transcript ← mx}[q transcript ∨ bad transcript] :=
    prEvent_mono_of_support mx p (fun transcript => q transcript ∨ bad transcript)
      (fun transcript hrun hreal =>
        coupledRun_real_implies_ideal_or_bad model config rounds program fallback adversary
          transcript hrun hreal)
  have hcore : Pr{let transcript ← mx}[p transcript] ≤
      Pr{let transcript ← mx}[q transcript] +
        Pr{let transcript ← mx}[bad transcript] :=
    hmono.trans (prEvent_or_le mx q bad)
  rw [prob_realAcceptance_eq_coupled, prob_idealAcceptance_eq_coupled,
    ← prob_coupled_bad_eq_owner]
  exact hcore

/-- The complete terminal suffix is irrelevant to the ideal Boolean decision. It is retained
only for coupling to the real adversary and owner transcript. -/
def idealTerminalSuffix [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y)
    (result : adversary.committer.State × ExtractorState Cfg Query Address Y config) :
    OracleComp (Query →ₒ Y) Unit := do
  let (openings, _) ← (adversary.opening result.1 result.2).withQueryLog
  let _ ← verifyOpeningClaims model (attachCheckpoints result.2 fallback openings)
  return ()

/-- Erasing the whole terminal phase preserves every Boolean event of the clean ideal game.
This asserts equality of observed probabilities, not equality of final random-oracle caches. -/
theorem idealAcceptanceExperiment_prEvent_eq_idealCore
    [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [IsUniformMeasureSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y)
    (event : Bool → Prop) :
    Pr{let accepted ← idealAcceptanceExperiment model config rounds program fallback adversary}[
      event accepted] =
    Pr{let accepted ← idealCoreExperiment model config rounds program fallback adversary}[
      event accepted] := by
  let observe := fun result : adversary.committer.State ×
      ExtractorState Cfg Query Address Y config =>
    idealDecision model config rounds program fallback result.2 (rootsOfState result.2)
  have h := prEvent_withCacheOverlay_skip_suffix
    (adversary.committer.runFromEmpty config rounds)
    (idealTerminalSuffix model config rounds fallback adversary) observe event
  have hleft : idealAcceptanceExperiment model config rounds program fallback adversary =
      (Query →ₒ Y).withCacheOverlay ∅ (
        adversary.committer.runFromEmpty config rounds >>= fun result =>
          (fun _ => observe result) <$>
            idealTerminalSuffix model config rounds fallback adversary result) := by
    simp only [idealAcceptanceExperiment, coupledExperiment, ← withCacheOverlay_map]
    apply congrArg ((Query →ₒ Y).withCacheOverlay ∅)
    simp only [coupledInner, idealTerminalSuffix, observe,
      bind_assoc, map_eq_bind_pure_comp]
    apply bind_congr
    intro result
    apply bind_congr
    intro opening
    apply bind_congr
    intro attempts
    rfl
  rw [hleft]
  simpa only [idealCoreExperiment, observe, withCacheOverlay_map] using h

/-- Native causal terminal Merkle transfer with the exact owning VCVio error numerator.
The adversarial prefix bound includes all commitment and terminal-opening queries; the honest
verification bound includes every submitted opening, whether matched, malformed or excess. -/
theorem realAcceptance_rom_bound_of_prefixQueryBound
    [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [IsUniformMeasureSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y)
    (queryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hquery : (toOwningAdversary config rounds fallback adversary).IsAdversaryPrefixQueryBound
      rounds queryBound)
    (hverifier : (toOwningAdversary config rounds fallback adversary).HasVerifierQueryBound
      verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr{let accepted ← realAcceptanceExperiment model config rounds program fallback adversary}[
      accepted = true] ≤
      Pr{let accepted ← idealCoreExperiment model config rounds program fallback adversary}[
        accepted = true] +
      (multiCheckpointROMErrorNumerator nodeBudget checkpointCount verifierOverhead
        queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹ := by
  have howner : Pr{let transcript ← (extractabilityExperiment model config rounds
      (toOwningAdversary config rounds fallback adversary))}[
      transcript.HasAnyCheckpointExtractionDisagreement model] ≤
      (multiCheckpointROMErrorNumerator nodeBudget checkpointCount verifierOverhead
        queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹ := by
    exact anyCheckpointDisagreement_rom_bound_of_prefixQueryBound model config rounds
      (toOwningAdversary config rounds fallback adversary) queryBound nodeBudget
      checkpointCount verifierOverhead perCheckpoint hquery hverifier hconfig hnodes
      hcheckpoints
  have hbridge := prob_realAcceptance_le_ideal_add_checkpointBad model config rounds
    program fallback adversary
  rw [idealAcceptanceExperiment_prEvent_eq_idealCore model config rounds program fallback
    adversary (fun accepted => accepted = true)] at hbridge
  exact hbridge.trans (add_le_add_right howner _)

/-- Transfer an independently established ideal-program acceptance bound `η` to the actual
native terminal verifier. -/
theorem realAcceptance_le_eta_add_romError
    [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [IsUniformMeasureSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    {depth : ℕ} (program : QueryProgram config rounds Y depth) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y)
    (queryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (η : ENNReal)
    (hquery : (toOwningAdversary config rounds fallback adversary).IsAdversaryPrefixQueryBound
      rounds queryBound)
    (hverifier : (toOwningAdversary config rounds fallback adversary).HasVerifierQueryBound
      verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount)
    (hideal :
      Pr{let accepted ←
        idealCoreExperiment model config rounds program fallback adversary}[accepted = true] ≤
        η) :
    Pr{let accepted ← realAcceptanceExperiment model config rounds program fallback adversary}[
      accepted = true] ≤
      η + (multiCheckpointROMErrorNumerator nodeBudget checkpointCount verifierOverhead
        queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹ := by
  exact (realAcceptance_rom_bound_of_prefixQueryBound model config rounds program fallback
    adversary queryBound nodeBudget checkpointCount verifierOverhead perCheckpoint hquery
    hverifier hconfig hnodes hcheckpoints).trans (add_le_add_left hideal _)

end Interaction.Oracle.MerkleAdaptiveTerminal
