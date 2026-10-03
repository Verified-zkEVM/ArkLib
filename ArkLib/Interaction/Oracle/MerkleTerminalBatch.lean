/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Execution
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.StrongBound

/-!
# Terminal-batch Merkle verification over native interactions

The prover makes a fixed number of adaptive commitments, emitting one public configuration and
root after each commitment phase. It then supplies one terminal batch of raw-digest openings.
The verifier chooses roots from the public path and verifies every supplied opening in the shared
random oracle before deciding whether to accept. Commitment-time extraction and the quantitative
transfer theorem are stated below against the owning VCVio checkpoint game.
-/

@[expose] public section

namespace Interaction.Oracle.MerkleTerminalBatch

open OracleComp OracleSpec Interaction.Oracle Interaction.TwoParty
open BinaryTree InductiveMerkleTree MerkleTreeMultiExtractability

variable {Cfg Query Address Y : Type}
variable {config : Configuration Cfg Address} {rounds : ℕ} {α β : Type}

/-- A prescribed commitment occurrence and selector of leaf positions. An all-false planned
selector cannot match a valid `BatchOpening`, so it is rejected by the public plan check. -/
structure QuerySite (config : Configuration Cfg Address) (rounds : ℕ) where
  slot : Fin rounds
  tag : Cfg
  selector : LeafData Bool (config.skeleton tag)

/-- One public terminal opening. The slot, configuration, and selector remain independently
checkable against the verifier's plan. No private checkpoint is included. -/
structure PublicOpening (config : Configuration Cfg Address) (rounds : ℕ) (Y : Type) where
  site : QuerySite config rounds
  opening : BatchOpening Y (config.skeleton site.tag)

/-- A finite, ordered selection of commitment slots and leaf positions, followed by an arbitrary
pure decision on the ordered vectors of selected digest values. -/
structure QueryPlan (config : Configuration Cfg Address) (rounds : ℕ) (Y : Type) where
  sites : List (QuerySite config rounds)
  decide : List (List Y) → Bool

/-- Flatten selected leaf values in the canonical left-to-right leaf order. -/
def selectedValuesList {α : Type} : {s : Skeleton} → {selector : LeafData Bool s} →
    SelectedValues α selector → List α
  | _, .leaf true, value => [value]
  | _, .leaf false, _ => []
  | _, .internal _ _, values =>
      selectedValuesList values.1 ++ selectedValuesList values.2

/-- Computable equality of two selectors for the same Merkle skeleton. -/
def selectorEq : {s : Skeleton} → LeafData Bool s → LeafData Bool s → Bool
  | .leaf, .leaf left, .leaf right => left == right
  | .internal _ _, .internal left₁ right₁, .internal left₂ right₂ =>
      selectorEq left₁ left₂ && selectorEq right₁ right₂

/-- The concrete values supplied in the terminal opening batch. -/
def publicAnswers {config : Configuration Cfg Address} {rounds : ℕ}
    (openings : List (PublicOpening config rounds Y)) : List (List Y) :=
  openings.map fun submitted => selectedValuesList submitted.opening.values

/-- The terminal-batch interaction has one public sender move per adaptive commitment, then one
public sender move carrying the opening list. -/
def protocol (config : Configuration Cfg Address) (rounds : ℕ) : ℕ → Protocol
  | 0 => Protocol.public .sender (List (PublicOpening config rounds Y)) fun _ => .done
  | n + 1 => Protocol.public .sender (Cfg × Y) fun _ => protocol config rounds n

/-- A malicious strategy has unrestricted adaptive oracle queries in each commitment phase and
while constructing the terminal opening batch. Its private state is never verifier-visible. -/
structure Adversary (config : Configuration Cfg Address) (rounds : ℕ) (Y : Type) where
  committer : SequentialCommitter Cfg Query Y
  opening : committer.State → ExtractorState Cfg Query Address Y config →
    OracleComp (Query →ₒ Y) (List (PublicOpening config rounds Y))

/-- Private evidence returned by the native prover: the exact commitment checkpoints and the
terminal opening-query segment. -/
structure PrivateResult (config : Configuration Cfg Address) where
  extractorState : ExtractorState Cfg Query Address Y config
  terminalSuffix : MerkleTreeExtractor.QueryLog Query Y

/-- Native malicious prover. Each checkpoint is recorded before its root is emitted as a public
move; subsequent phases receive only the newly returned private state. -/
def prover (config : Configuration Cfg Address) (rounds : ℕ)
    (adversary : Adversary (Query := Query) config rounds Y) :
    (remaining firstRound : ℕ) → adversary.committer.State →
      ExtractorState Cfg Query Address Y config →
      Prover.Strategy (Query →ₒ Y) (protocol (Y := Y) config rounds remaining).tree
        (protocol (Y := Y) config rounds remaining).roles
        (fun _ => PrivateResult (Query := Query) (Y := Y) config)
  | 0, _, state, extractorState => do
      let (openings, terminalSuffix) ← (adversary.opening state extractorState).withQueryLog
      return ⟨openings, { extractorState, terminalSuffix }⟩
  | remaining + 1, firstRound, state, extractorState => do
      let ((tag, root, nextState), phaseLog) ←
        (adversary.committer.commit firstRound state).withQueryLog
      let nextExtractorState := extractorState.record tag phaseLog root
      return ⟨(tag, root),
        prover config rounds adversary remaining (firstRound + 1) nextState nextExtractorState⟩

/-- The root selected by a public slot. Missing slots get the specified fallback digest; they
remain invalid under `PlanValid`, but their submitted openings are still verified. -/
def publicRoot (roots : List (Cfg × Y)) (fallback : Y)
    {config : Configuration Cfg Address} {rounds : ℕ}
    (site : QuerySite config rounds) : Y :=
  ((roots[site.slot.val]?).map Prod.snd).getD fallback

/-- The same slot lookup in the private, immutable commitment history. -/
def checkpointAt (state : ExtractorState Cfg Query Address Y config) (fallback : Y)
    {rounds : ℕ} (site : QuerySite config rounds) : Checkpoint Query Y config site.tag :=
  match state.checkpoints[site.slot.val]? with
  | some checkpoint =>
      { root := checkpoint.2.root, cumulativeLog := checkpoint.2.cumulativeLog }
  | none => { root := fallback, cumulativeLog := [] }

/-- Private checkpoint attachment for the owning VCVio game. The verifier never receives this
value: it selects only the corresponding public root. -/
def attachCheckpoints (state : ExtractorState Cfg Query Address Y config)
    (fallback : Y) {rounds : ℕ}
    (openings : List (PublicOpening config rounds Y)) :
    List (OpeningClaim Query Y config) :=
  openings.map fun submitted =>
    { tag := submitted.site.tag
      checkpoint := checkpointAt state fallback submitted.site
      opening := submitted.opening }

/-- Public-root version of the same verification claims. Its empty checkpoint logs have no
effect on verification, which reads only the selected root. -/
def publicClaims (roots : List (Cfg × Y)) (fallback : Y)
    {config : Configuration Cfg Address} {rounds : ℕ}
    (openings : List (PublicOpening config rounds Y)) :
    List (OpeningClaim Query Y config) :=
  openings.map fun submitted =>
    { tag := submitted.site.tag
      checkpoint := { root := publicRoot roots fallback submitted.site, cumulativeLog := [] }
      opening := submitted.opening }

/-- The planned occurrence, configuration and selector agree with a submitted opening. -/
def siteMatches [DecidableEq Cfg] (config : Configuration Cfg Address) {rounds : ℕ}
    (expected : QuerySite config rounds) (submitted : PublicOpening config rounds Y) : Bool :=
  if htag : expected.tag = submitted.site.tag then
    if expected.slot = submitted.site.slot then
      selectorEq (htag ▸ expected.selector) submitted.site.selector &&
        selectorEq (htag ▸ expected.selector) submitted.opening.selector
    else false
  else false

/-- Exact prescribed batch shape and public commitment occurrence check. -/
def planValidBool [DecidableEq Cfg] (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (roots : List (Cfg × Y))
    (openings : List (PublicOpening config rounds Y)) : Bool :=
  decide (roots.length = rounds) && decide (plan.sites.length = openings.length) &&
    (List.zip plan.sites openings).all (fun pair =>
      siteMatches config pair.1 pair.2 &&
        decide (((roots[pair.1.slot.val]?).map Prod.fst) = some pair.1.tag))

/-- The unique public validity proposition is exactly the Boolean check used by the verifier. -/
abbrev PlanValid [DecidableEq Cfg] (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (roots : List (Cfg × Y))
    (openings : List (PublicOpening config rounds Y)) : Prop :=
  planValidBool config rounds plan roots openings = true

/-- The verifier's actual terminal batch: all opening checks run before the final validity and
decision bits are combined. No malformed opening can skip an oracle query by short circuit. -/
def verifyBatch [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (roots : List (Cfg × Y)) (openings : List (PublicOpening config rounds Y)) :
    OracleComp (Query →ₒ Y) Bool := do
  let attempts ← verifyOpeningClaims model
    (publicClaims (Query := Query) roots fallback openings)
  return planValidBool config rounds plan roots openings &&
    attempts.all (fun attempt => attempt.2.accepted) &&
    plan.decide (publicAnswers openings)

/-- Native verifier. Each earlier public commitment is stored only as a public tag/root pair.
The final action forwards honest Merkle queries to the ambient oracle and runs once. -/
def verifier [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y) :
    (remaining : ℕ) → List (Cfg × Y) →
      Verifier.Strategy (Query →ₒ Y) (protocol (Y := Y) config rounds remaining).tree
        (protocol (Y := Y) config rounds remaining).roles
        (protocol (Y := Y) config rounds remaining).oracles 0 (fun _ => Bool)
  | 0, roots => fun openings => pure <| by
      change OracleComp ((Query →ₒ Y) + ofPFunctor 0) Bool
      exact simulateQ
        (fun q => liftM (((Query →ₒ Y) + ofPFunctor 0).query (.inl q)))
        (verifyBatch model config rounds plan fallback roots openings)
  | remaining + 1, roots => fun root =>
      pure (verifier model config rounds plan fallback remaining (roots ++ [root]))

/-- Total raw-digest extraction from one actual commitment-time checkpoint. Unrecovered cells
receive the specified fallback digest; future opening queries never enter this vector. -/
def extractA [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (state : ExtractorState Cfg Query Address Y config) (fallback : Y)
    {rounds : ℕ} (site : QuerySite config rounds) :
    FullData Y (config.skeleton site.tag) :=
  ((checkpointAt state fallback site).extractedTree model.view).map
    (fun cell => cell.getD fallback)

/-- Read the prescribed selected positions from a commitment-time extracted vector. -/
def idealAnswers [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (state : ExtractorState Cfg Query Address Y config) (fallback : Y)
    {rounds : ℕ} (plan : QueryPlan config rounds Y) : List (List Y) :=
  plan.sites.map fun site =>
    selectedValuesList (selectedValues (extractA model state fallback site).toLeafData
      site.selector)

/-- The ideal verifier uses only checkpoint-time extracted vectors for its answers. Malformed
public selections reject, exactly as in the real verifier. -/
def idealAccept [DecidableEq Cfg] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (state : ExtractorState Cfg Query Address Y config)
    (roots : List (Cfg × Y)) (openings : List (PublicOpening config rounds Y)) : Bool :=
  planValidBool config rounds plan roots openings &&
    plan.decide (idealAnswers model state fallback plan)

/-- The ordered public commitment occurrences and terminal batch carried by a native path. -/
def publicTranscript (config : Configuration Cfg Address) (rounds : ℕ) :
    (remaining : ℕ) → (protocol (Y := Y) config rounds remaining).tree.ExecutionPath →
      List (Cfg × Y) × List (PublicOpening config rounds Y)
  | 0, path => ([], path.1)
  | remaining + 1, path =>
      let (roots, openings) := publicTranscript config rounds remaining path.2
      (path.1 :: roots, openings)

/-- The canonical native execution of an arbitrary adaptive malicious committer and terminal
opening strategy. Each native public sender boundary is executed by `executeStrategies`. -/
def nativeGame [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :=
  executeStrategies (Query →ₒ Y) (protocol (Y := Y) config rounds rounds).tree
    (protocol (Y := Y) config rounds rounds).roles
    (protocol (Y := Y) config rounds rounds).oracles 0
    (fun q => nomatch q)
    (prover config rounds adversary rounds 0 adversary.committer.initialState
      ExtractorState.empty)
    (verifier model config rounds plan fallback rounds [])

/-- Both native experiments run the same malicious program with one shared lazy cache. -/
def nativeExperiment [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :=
  (Query →ₒ Y).withCacheOverlay ∅
    (nativeGame model config rounds plan fallback adversary)

/-- Attach private, actual commitment checkpoints only in the reduction to VCVio's owning game.
The terminal opening program remains the malicious strategy supplied to the native runner. -/
def toOwningAdversary (config : Configuration Cfg Address) (rounds : ℕ) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    MerkleTreeMultiExtractability.Adversary Cfg Query Address Y config where
  committer := adversary.committer
  opening := fun state extractorState =>
    attachCheckpoints extractorState fallback <$> adversary.opening state extractorState

/-- Public commitment sequence reconstructed from the private checkpoint record. -/
def rootsOfState (state : ExtractorState Cfg Query Address Y config) : List (Cfg × Y) :=
  state.checkpoints.map fun checkpoint => (checkpoint.1, checkpoint.2.root)

@[simp] theorem rootsOfState_empty (config : Configuration Cfg Address) :
    rootsOfState (ExtractorState.empty : ExtractorState Cfg Query Address Y config) = [] := rfl

@[simp] theorem rootsOfState_record
    (state : ExtractorState Cfg Query Address Y config)
    (tag : Cfg) (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y) :
    rootsOfState (state.record tag phaseLog root) = rootsOfState state ++ [(tag, root)] := by
  simp [rootsOfState, ExtractorState.record]

/-- Observable and private fields of a complete native terminal-batch run. -/
structure GameView (config : Configuration Cfg Address) (rounds : ℕ) (Y : Type) where
  roots : List (Cfg × Y)
  openings : List (PublicOpening config rounds Y)
  extractorState : ExtractorState Cfg Query Address Y config
  terminalSuffix : MerkleTreeExtractor.QueryLog Query Y
  accepted : Bool

/-- Erase the native path into ordered public commitments and a terminal batch, retaining the
same run's private checkpoint evidence for the security proof. -/
def nativeView (config : Configuration Cfg Address) (rounds remaining : ℕ)
    (prefixRoots : List (Cfg × Y))
    (result : (_path : (protocol (Y := Y) config rounds remaining).tree.ExecutionPath) ×
      PrivateResult (Query := Query) (Y := Y) config × Bool) :
    GameView (Query := Query) config rounds Y :=
  let publicData := publicTranscript config rounds remaining result.1
  { roots := prefixRoots ++ publicData.1
    openings := publicData.2
    extractorState := result.2.1.extractorState
    terminalSuffix := result.2.1.terminalSuffix
    accepted := result.2.2 }

/-- Source-order execution from an arbitrary native prefix. It is independent of the native
runner and exposes the expected induction target for correspondence. -/
def sourceSuffix [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    (remaining firstRound : ℕ) → adversary.committer.State →
      ExtractorState Cfg Query Address Y config → List (Cfg × Y) →
      OracleComp (Query →ₒ Y) (GameView (Query := Query) config rounds Y)
  | 0, _, state, extractorState, roots => do
      let (openings, terminalSuffix) ← (adversary.opening state extractorState).withQueryLog
      let accepted ← verifyBatch model config rounds plan fallback roots openings
      return { roots, openings, extractorState, terminalSuffix, accepted }
  | remaining + 1, firstRound, state, extractorState, roots => do
      let ((tag, root, nextState), phaseLog) ←
        (adversary.committer.commit firstRound state).withQueryLog
      sourceSuffix model config rounds plan fallback adversary remaining (firstRound + 1)
        nextState (extractorState.record tag phaseLog root) (roots ++ [(tag, root)])

/-- The native verifier's terminal forwarding handler leaves the ambient oracle program
unchanged after the native executor interprets its empty source access. -/
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
/-- Causal native/source correspondence from every reachable public commitment prefix. The
induction records a checkpoint before each public root and preserves the terminal opening-query
segment and verification effect order. -/
theorem nativeSuffix_eq_source [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
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
        (verifier model config rounds plan fallback remaining prefixRoots) =
      sourceSuffix model config rounds plan fallback adversary remaining firstRound state
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
        (fun program : OracleComp (Query →ₒ Y) Bool =>
          (fun accepted =>
            ({ roots := prefixRoots, openings, extractorState, terminalSuffix,
               accepted } : GameView (Query := Query) config rounds Y)) <$> program)
        (terminalForwarding_eq (Query := Query) (Y := Y)
          (verifyBatch model config rounds plan fallback prefixRoots openings))
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

/-- The recursive source runner is exactly the owning VCVio sequential commitment runner,
followed by one terminal opening phase and unconditional honest verification. -/
theorem sourceSuffix_eq_runCommitments [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y)
    (remaining firstRound : ℕ) (state : adversary.committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config) :
    sourceSuffix model config rounds plan fallback adversary remaining firstRound state
      extractorState (rootsOfState extractorState) = do
        let (finalState, finalExtractorState) ← adversary.committer.runCommitments
          remaining firstRound state extractorState
        let (openings, terminalSuffix) ←
          (adversary.opening finalState finalExtractorState).withQueryLog
        let roots := rootsOfState finalExtractorState
        let accepted ← verifyBatch model config rounds plan fallback roots openings
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

/-- Whole native execution, after erasing only the structural path, equals the explicit source
runner with its actual checkpoint state and terminal query segment. -/
theorem nativeGame_eq_source [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    nativeView config rounds rounds [] <$>
      nativeGame model config rounds plan fallback adversary = do
        let (finalState, finalExtractorState) ← adversary.committer.runFromEmpty config rounds
        let (openings, terminalSuffix) ←
          (adversary.opening finalState finalExtractorState).withQueryLog
        let roots := rootsOfState finalExtractorState
        let accepted ← verifyBatch model config rounds plan fallback roots openings
        return { roots := roots, openings := openings, extractorState := finalExtractorState,
                 terminalSuffix := terminalSuffix, accepted := accepted } := by
  rw [nativeGame, nativeSuffix_eq_source]
  simpa only [SequentialCommitter.runFromEmpty, rootsOfState_empty] using
    sourceSuffix_eq_runCommitments model config rounds plan fallback adversary rounds 0
      adversary.committer.initialState
      (ExtractorState.empty : ExtractorState Cfg Query Address Y config)

/-- The public root at a slot is exactly the root in its privately recorded checkpoint. -/
theorem publicRoot_rootsOfState_eq_checkpointAt_root
    (state : ExtractorState Cfg Query Address Y config) (fallback : Y)
    {rounds : ℕ} (site : QuerySite config rounds) :
    publicRoot (rootsOfState state) fallback site =
      (checkpointAt state fallback site).root := by
  simp only [publicRoot, rootsOfState, checkpointAt, List.getElem?_map]
  cases h : state.checkpoints[site.slot.val]? with
  | none => simp
  | some checkpoint => simp

/-- Honest opening verification depends on a checkpoint's root, not on its private cumulative
query log. The two claims therefore run identical oracle programs. -/
theorem verifyOpening_root_only [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (tag : Cfg)
    (left right : Checkpoint Query Y config tag)
    (opening : BatchOpening Y (config.skeleton tag))
    (hroot : left.root = right.root) :
    MerkleTreeBatchExtractability.verifyOpening model (config.addressKey tag)
      left.root opening =
    MerkleTreeBatchExtractability.verifyOpening model (config.addressKey tag)
      right.root opening := by
  rw [hroot]

/-- Honest verification bits, stripped of private checkpoint bookkeeping. -/
def acceptanceBits {config : Configuration Cfg Address}
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config)) : List Bool :=
  attempts.map fun attempt => attempt.2.accepted

/-- Public-root verification and private checkpoint verification have the same effectful
acceptance-bit trace, including every rejected or malformed opening. -/
theorem verifyOpeningClaims_public_private_bits [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (state : ExtractorState Cfg Query Address Y config) (fallback : Y)
    {rounds : ℕ} (openings : List (PublicOpening config rounds Y)) :
    acceptanceBits <$>
      verifyOpeningClaims model
        (publicClaims (Query := Query) (rootsOfState state) fallback openings) =
    acceptanceBits <$>
      verifyOpeningClaims model (attachCheckpoints state fallback openings) := by
  induction openings with
  | nil => rfl
  | cons submitted rest ih =>
      simp only [publicClaims, attachCheckpoints, List.map_cons, verifyOpeningClaims,
        publicRoot_rootsOfState_eq_checkpointAt_root]
      simp only [map_bind, map_pure]
      apply bind_congr
      intro accepted
      simpa [acceptanceBits, publicClaims, attachCheckpoints, map_bind,
        Functor.map_map, publicRoot_rootsOfState_eq_checkpointAt_root]
        using congrArg (fun p : OracleComp (Query →ₒ Y) (List Bool) =>
          (fun bits => accepted :: bits) <$> p) ih

/-- Logging a deterministic output transformation leaves the query segment unchanged. -/
theorem withQueryLog_map (program : OracleComp (Query →ₒ Y) α) (f : α → β) :
    (f <$> program).withQueryLog =
      (fun pair : α × MerkleTreeExtractor.QueryLog Query Y => (f pair.1, pair.2)) <$>
        program.withQueryLog := by
  rw [map_eq_bind_pure_comp, OracleComp.withQueryLog_bind]
  simp

/-- One run with public choices and the owning game's private evaluated claims. The native
verifier never receives the checkpoint fields; this is a proof-side coupling only. -/
structure CoupledTranscript (config : Configuration Cfg Address) (rounds : ℕ) (Y : Type) where
  roots : List (Cfg × Y)
  openings : List (PublicOpening config rounds Y)
  extractorState : ExtractorState Cfg Query Address Y config
  terminalSuffix : MerkleTreeExtractor.QueryLog Query Y
  attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config)

/-- The actual public predicate evaluated using the owning game's identical verification bits. -/
def coupledAccept [DecidableEq Cfg] (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y)
    (transcript : CoupledTranscript (Query := Query) config rounds Y) : Bool :=
  planValidBool config rounds plan transcript.roots transcript.openings &&
    transcript.attempts.all (fun attempt => attempt.2.accepted) &&
    plan.decide (publicAnswers transcript.openings)

/-- Forget private claim metadata while retaining the actual native output. -/
def coupledNativeView [DecidableEq Cfg] (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y)
    (transcript : CoupledTranscript (Query := Query) config rounds Y) :
    GameView (Query := Query) config rounds Y :=
  { roots := transcript.roots
    openings := transcript.openings
    extractorState := transcript.extractorState
    terminalSuffix := transcript.terminalSuffix
    accepted := coupledAccept config rounds plan transcript }

/-- Forget public terminal choices to obtain exactly VCVio's game transcript. -/
def coupledOwnerView (transcript : CoupledTranscript (Query := Query) config rounds Y) :
    MerkleTreeMultiExtractability.Transcript Cfg Query Address Y config :=
  { extractorState := transcript.extractorState
    terminalSuffix := transcript.terminalSuffix
    attempts := transcript.attempts }

/-- The single source-order program coupling native public verification with private checkpoint
evidence. Commitment, terminal opening, and verification queries occur in their actual order. -/
def coupledInner [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    OracleComp (Query →ₒ Y) (CoupledTranscript (Query := Query) config rounds Y) := do
  let (privateState, extractorState) ← adversary.committer.runFromEmpty config rounds
  let (openings, terminalSuffix) ← (adversary.opening privateState extractorState).withQueryLog
  let attempts ← verifyOpeningClaims model (attachCheckpoints extractorState fallback openings)
  return ⟨rootsOfState extractorState, openings, extractorState, terminalSuffix, attempts⟩

/-- The same cache covers all three phases of the coupling. -/
def coupledExperiment [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :=
  (Query →ₒ Y).withCacheOverlay ∅ (coupledInner model config rounds fallback adversary)

/-- The owning game's actual probability space is a marginal of the coupled execution. -/
theorem coupledInner_owner_eq [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    coupledOwnerView <$> coupledInner model config rounds fallback adversary =
      extractabilityInner model config rounds
        (toOwningAdversary config rounds fallback adversary) := by
  simp [coupledInner, extractabilityInner, toOwningAdversary, withQueryLog_map,
    coupledOwnerView, map_bind, Functor.map_map]

/-- The real native terminal predicate is the private coupling's predicate, as an equality of
oracle programs and thus of every interleaved verifier-query effect. -/
theorem verifyBatch_eq_coupled [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (state : ExtractorState Cfg Query Address Y config)
    (openings : List (PublicOpening config rounds Y)) :
    verifyBatch model config rounds plan fallback (rootsOfState state) openings =
      (fun attempts => planValidBool config rounds plan (rootsOfState state) openings &&
        attempts.all (fun attempt => attempt.2.accepted) &&
        plan.decide (publicAnswers openings)) <$>
        verifyOpeningClaims model (attachCheckpoints state fallback openings) := by
  have h := congrArg (fun program : OracleComp (Query →ₒ Y) (List Bool) =>
      (fun bits => planValidBool config rounds plan (rootsOfState state) openings &&
        bits.all id && plan.decide (publicAnswers openings)) <$> program)
    (verifyOpeningClaims_public_private_bits model state fallback openings)
  simpa [verifyBatch, acceptanceBits, Functor.map_map] using h

/-- Erasing only private claim metadata yields the native source-order game exactly. -/
theorem coupledInner_native_eq [DecidableEq Cfg] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    coupledNativeView config rounds plan <$> coupledInner model config rounds fallback adversary =
      nativeView config rounds rounds [] <$>
        nativeGame model config rounds plan fallback adversary := by
  rw [nativeGame_eq_source]
  simp only [coupledInner, map_bind, map_pure]
  apply bind_congr
  rintro ⟨privateState, state⟩
  apply bind_congr
  rintro ⟨openings, terminalSuffix⟩
  rw [verifyBatch_eq_coupled]
  simp [coupledNativeView, coupledAccept, Functor.map_map]

/-- The native full shared-cache experiment is an exact marginal of the coupled game. -/
theorem coupledExperiment_native_eq [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    coupledNativeView config rounds plan <$>
      coupledExperiment model config rounds fallback adversary =
    nativeView config rounds rounds [] <$>
      nativeExperiment model config rounds plan fallback adversary := by
  simp only [coupledExperiment, nativeExperiment, ← withCacheOverlay_map]
  exact congrArg ((Query →ₒ Y).withCacheOverlay ∅)
    (coupledInner_native_eq model config rounds plan fallback adversary)

/-- VCVio's full shared-cache experiment is the other exact marginal. -/
theorem coupledExperiment_owner_eq [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    coupledOwnerView <$> coupledExperiment model config rounds fallback adversary =
      extractabilityExperiment model config rounds
        (toOwningAdversary config rounds fallback adversary) := by
  simp only [coupledExperiment, extractabilityExperiment, ← withCacheOverlay_map]
  exact congrArg ((Query →ₒ Y).withCacheOverlay ∅)
    (coupledInner_owner_eq model config rounds fallback adversary)

/-- The Boolean plan check supplies a matched, ordered site for every terminal opening. -/
theorem planValidBool_pairs [DecidableEq Cfg]
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (roots : List (Cfg × Y))
    (openings : List (PublicOpening config rounds Y))
    (hvalid : planValidBool config rounds plan roots openings = true) :
    roots.length = rounds ∧
      List.Forall₂ (fun site submitted =>
        siteMatches config site submitted = true ∧
          (roots[site.slot.val]?).map Prod.fst = some site.tag)
        plan.sites openings := by
  unfold planValidBool at hvalid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
  rcases hvalid with ⟨⟨hlen, hcount⟩, hpairs⟩
  refine ⟨hlen, (List.forall₂_iff_zip).2 ⟨hcount, ?_⟩⟩
  intro site submitted hmem
  have hp := List.all_eq_true.mp hpairs (site, submitted) hmem
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using hp

/-- A public slot/tag match identifies the exact recorded checkpoint, including its private
commitment-time log. It is stronger than root equality alone. -/
theorem checkpointAt_mem_of_public_tag
    (state : ExtractorState Cfg Query Address Y config) (fallback : Y)
    {rounds : ℕ} (site : QuerySite config rounds)
    (htag : ((rootsOfState state)[site.slot.val]?).map Prod.fst = some site.tag) :
    ⟨site.tag, checkpointAt state fallback site⟩ ∈ state.checkpoints := by
  simp only [rootsOfState, List.getElem?_map] at htag
  cases hlookup : state.checkpoints[site.slot.val]? with
  | none => simp [hlookup] at htag
  | some checkpoint =>
      cases checkpoint with
      | mk tag recorded =>
          simp only [hlookup, Option.map_some, Option.some.injEq] at htag
          subst tag
          simpa [checkpointAt, hlookup] using List.mem_of_getElem? hlookup

/-- Appending a later commitment checkpoint cannot change the checkpoint at an earlier slot. -/
theorem checkpointAt_record_of_lt
    (state : ExtractorState Cfg Query Address Y config) (fallback : Y)
    (tag : Cfg) (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y)
    {rounds : ℕ} (site : QuerySite config rounds)
    (hearlier : site.slot.val < state.checkpoints.length) :
    checkpointAt (state.record tag phaseLog root) fallback site =
      checkpointAt state fallback site := by
  simp only [checkpointAt, ExtractorState.record, List.getElem?_append_left hearlier]

/-- The full raw-digest vector at an earlier occurrence is immutable under later commitments.
Terminal opening and honest verification cannot affect it because `extractA` reads only the
stored checkpoint, with no terminal log or verifier state argument. -/
theorem extractA_record_of_lt [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (state : ExtractorState Cfg Query Address Y config) (fallback : Y)
    (tag : Cfg) (phaseLog : MerkleTreeExtractor.QueryLog Query Y) (root : Y)
    {rounds : ℕ} (site : QuerySite config rounds)
    (hearlier : site.slot.val < state.checkpoints.length) :
    extractA model (state.record tag phaseLog root) fallback site =
      extractA model state fallback site := by
  simp only [extractA, checkpointAt_record_of_lt state fallback tag phaseLog root site hearlier]

/-- Verification preserves each claim, in order, and appends only its computed acceptance bit. -/
def ClaimsAligned {config : Configuration Cfg Address}
    (claims : List (OpeningClaim Query Y config))
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config)) : Prop :=
  List.Forall₂ (fun claim attempt => ∃ accepted : Bool,
    attempt = ⟨claim.tag, ⟨claim.checkpoint, claim.opening, accepted⟩⟩) claims attempts

/-- Claim alignment holds for every realized verifier path and every initial oracle cache. -/
theorem verifyOpeningClaims_aligned [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address}
    (claims : List (OpeningClaim Query Y config))
    (cache₀ cache₁ : (Query →ₒ Y).QueryCache)
    (attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config))
    (hrun : (attempts, cache₁) ∈ support
      ((simulateQ (Query →ₒ Y).cachingOracle (verifyOpeningClaims model claims)).run cache₀)) :
    ClaimsAligned claims attempts := by
  induction claims generalizing cache₀ cache₁ attempts with
  | nil =>
      simp only [verifyOpeningClaims, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hrun
      injection hrun with hattempts _
      subst attempts
      exact List.Forall₂.nil
  | cons claim claims ih =>
      simp only [verifyOpeningClaims, simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hrun
      obtain ⟨⟨accepted, cacheVerify⟩, _, hrun⟩ := hrun
      obtain ⟨⟨rest, cacheRest⟩, hrest, hfinal⟩ := hrun
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hfinal
      injection hfinal with hattempts hcache
      subst attempts
      subst cache₁
      exact List.Forall₂.cons ⟨accepted, rfl⟩ (ih cacheVerify cacheRest rest hrest)

/-- Every coupled execution retains the exact claim-to-attempt order, including under arbitrary
cache contents and adaptive commitment/opening behavior. -/
theorem coupledInner_aligned_run [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y)
    (cache₀ cache₁ : (Query →ₒ Y).QueryCache)
    (transcript : CoupledTranscript (Query := Query) config rounds Y)
    (hrun : (transcript, cache₁) ∈ support
      ((simulateQ (Query →ₒ Y).cachingOracle
        (coupledInner model config rounds fallback adversary)).run cache₀)) :
    ClaimsAligned (attachCheckpoints transcript.extractorState fallback transcript.openings)
      transcript.attempts ∧
    transcript.roots = rootsOfState transcript.extractorState := by
  unfold coupledInner at hrun
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hrun
  simp only [Set.mem_iUnion] at hrun
  obtain ⟨⟨⟨privateState, state⟩, cacheCommit⟩, _, hrun⟩ := hrun
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hrun
  simp only [Set.mem_iUnion] at hrun
  obtain ⟨⟨⟨openings, suffix⟩, cacheOpening⟩, _, hrun⟩ := hrun
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hrun
  simp only [Set.mem_iUnion] at hrun
  obtain ⟨⟨attempts, cacheVerify⟩, hverify, hfinal⟩ := hrun
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hfinal
  injection hfinal with htranscript hcache
  subst transcript
  exact ⟨verifyOpeningClaims_aligned model
    (attachCheckpoints state fallback openings) cacheOpening cacheVerify attempts hverify,
    rfl⟩

/-- Claim-to-attempt alignment holds on the actual shared-cache probability space. -/
theorem coupledExperiment_aligned [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y)
    (transcript : CoupledTranscript (Query := Query) config rounds Y)
    (hrun : transcript ∈ support
      (coupledExperiment model config rounds fallback adversary)) :
    ClaimsAligned (attachCheckpoints transcript.extractorState fallback transcript.openings)
      transcript.attempts := by
  simp only [coupledExperiment, OracleSpec.withCacheOverlay, StateT.run'_eq,
    support_map, Set.mem_image] at hrun
  obtain ⟨⟨observed, cacheFinal⟩, hfull, houtput⟩ := hrun
  cases houtput
  exact (coupledInner_aligned_run model config rounds fallback adversary ∅ cacheFinal
    observed hfull).1

/-- Public roots on every actual shared-cache run are exactly the roots of the private recorded
checkpoint sequence; this is proved from the runner rather than assumed of an arbitrary record. -/
theorem coupledExperiment_roots [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y)
    (transcript : CoupledTranscript (Query := Query) config rounds Y)
    (hrun : transcript ∈ support
      (coupledExperiment model config rounds fallback adversary)) :
    transcript.roots = rootsOfState transcript.extractorState := by
  simp only [coupledExperiment, OracleSpec.withCacheOverlay, StateT.run'_eq,
    support_map, Set.mem_image] at hrun
  obtain ⟨⟨observed, cacheFinal⟩, hfull, houtput⟩ := hrun
  cases houtput
  exact (coupledInner_aligned_run model config rounds fallback adversary ∅ cacheFinal
    observed hfull).2

/-- In an actual coupled run the returned extractor state is exactly the one produced when the
last commitment phase ended. Terminal opening and all subsequent honest verification retain it
unchanged, even though both may extend the shared oracle cache. -/
theorem coupledExperiment_state_from_commitments [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y)
    (transcript : CoupledTranscript (Query := Query) config rounds Y)
    (hrun : transcript ∈ support
      (coupledExperiment model config rounds fallback adversary)) :
    ∃ privateState cacheCommit,
      ((privateState, transcript.extractorState), cacheCommit) ∈ support
        ((simulateQ (Query →ₒ Y).cachingOracle
          (adversary.committer.runFromEmpty config rounds)).run ∅) := by
  simp only [coupledExperiment, OracleSpec.withCacheOverlay, StateT.run'_eq,
    support_map, Set.mem_image] at hrun
  obtain ⟨⟨observed, cacheFinal⟩, hfull, houtput⟩ := hrun
  cases houtput
  unfold coupledInner at hfull
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hfull
  simp only [Set.mem_iUnion] at hfull
  obtain ⟨⟨⟨privateState, state⟩, cacheCommit⟩, hcommit, htail⟩ := hfull
  rw [simulateQ_bind, StateT.run_bind, support_bind] at htail
  simp only [Set.mem_iUnion] at htail
  obtain ⟨⟨⟨openings, suffix⟩, cacheOpening⟩, _, htail⟩ := htail
  rw [simulateQ_bind, StateT.run_bind, support_bind] at htail
  simp only [Set.mem_iUnion] at htail
  obtain ⟨⟨attempts, cacheVerify⟩, _, hfinal⟩ := htail
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hfinal
  injection hfinal with htranscript _
  subst observed
  exact ⟨privateState, cacheCommit, hcommit⟩

/-- A true selector comparison is literal equality of the prescribed leaf positions. -/
theorem selectorEq_true_iff {s : Skeleton} (left right : LeafData Bool s) :
    selectorEq left right = true ↔ left = right := by
  induction s with
  | leaf =>
      cases left with | leaf left =>
      cases right with | leaf right =>
      simp [selectorEq]
  | internal l r ihl ihr =>
      cases left with | internal left₁ right₁ =>
      cases right with | internal left₂ right₂ =>
      simp [selectorEq, ihl, ihr]

/-- A checked site matches both the submitted site and opening selector. -/
theorem siteMatches_true [DecidableEq Cfg]
    (config : Configuration Cfg Address) {rounds : ℕ}
    (expected : QuerySite config rounds)
    (submitted : PublicOpening config rounds Y)
    (hmatch : siteMatches config expected submitted = true) :
    expected.slot = submitted.site.slot ∧ expected.tag = submitted.site.tag ∧
      HEq expected.selector submitted.site.selector ∧
      HEq expected.selector submitted.opening.selector := by
  unfold siteMatches at hmatch
  split_ifs at hmatch with htag hslot
  · simp only [Bool.and_eq_true] at hmatch
    obtain ⟨hleft, hright⟩ := hmatch
    have htransport : HEq expected.selector (htag ▸ expected.selector) :=
      (eqRec_heq (φ := fun tag => LeafData Bool (config.skeleton tag))
        htag expected.selector).symm
    exact ⟨hslot, htag,
      htransport.trans (heq_of_eq ((selectorEq_true_iff _ _).mp hleft)),
      htransport.trans (heq_of_eq ((selectorEq_true_iff _ _).mp hright))⟩

/-- The submitted site is literally the prescribed site once the public site check succeeds. -/
theorem siteMatches_site_eq [DecidableEq Cfg]
    (config : Configuration Cfg Address) {rounds : ℕ}
    (expected : QuerySite config rounds)
    (submitted : PublicOpening config rounds Y)
    (hmatch : siteMatches config expected submitted = true) :
    expected = submitted.site := by
  obtain ⟨hslot, htag, hselector, _⟩ := siteMatches_true config expected submitted hmatch
  cases expected with
  | mk expectedSlot expectedTag expectedSelector =>
      cases submitted with
      | mk submittedSite opening =>
          cases submittedSite with
          | mk submittedSlot submittedTag submittedSelector =>
              cases hslot
              cases htag
              cases eq_of_heq hselector
              rfl

/-- The accepted public shape check also fixes the leaf selector carried by the opening. -/
theorem siteMatches_opening_selector_eq [DecidableEq Cfg]
    (config : Configuration Cfg Address) {rounds : ℕ}
    (expected : QuerySite config rounds)
    (submitted : PublicOpening config rounds Y)
    (hmatch : siteMatches config expected submitted = true) :
    HEq expected.selector submitted.opening.selector :=
  (siteMatches_true config expected submitted hmatch).2.2.2

/-- Flattening selected values commutes with a pointwise value map. -/
theorem selectedValuesList_map (f : α → β) {s : Skeleton}
    {selector : LeafData Bool s} (values : SelectedValues α selector) :
    selectedValuesList (values.map f) = (selectedValuesList values).map f := by
  induction selector with
  | leaf selected =>
      cases selected <;> rfl
  | internal left right ihl ihr =>
      simpa [selectedValuesList, SelectedValues.map, List.map_append] using
        congrArg₂ List.append (ihl values.1) (ihr values.2)

/-- Leaf projection of a full tree commutes with pointwise mapping. -/
theorem toLeafData_map (f : α → β) {s : Skeleton} (tree : FullData α s) :
    (tree.map f).toLeafData = tree.toLeafData.map f := by
  induction tree with
  | leaf value => rfl
  | internal value left right ihl ihr =>
      simp [FullData.map, FullData.toLeafData, ihl, ihr]

/-- Agreement with the canonical partial opening forces every selected digest to equal the
commitment-time extracted digest after totalization. -/
theorem selectedValues_eq_of_noOpeningDisagreement
    [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    {config : Configuration Cfg Address} {tag : Cfg}
    (checkpoint : Checkpoint Query Y config tag) (fallback : Y)
    (opening : BatchOpening Y (config.skeleton tag))
    (hagree : checkpoint.extractedOpening model.view opening = opening.map some) :
    selectedValuesList (selectedValues
      ((checkpoint.extractedTree model.view).map (fun cell => cell.getD fallback)).toLeafData
      opening.selector) = selectedValuesList opening.values := by
  cases opening with
  | mk selector values proof =>
      simp only [Checkpoint.extractedOpening, BatchOpening.map] at hagree
      have hvalues : selectedValues (checkpoint.extractedTree model.view).toLeafData
          selector = values.map some := by
        injection hagree with _ hvalues _
      rw [toLeafData_map, ← SelectedValues.map_selectedValues, selectedValuesList_map,
        hvalues, selectedValuesList_map]
      simp

/-- Every checked, accepted terminal answer equals its prescribed commitment-time extraction
unless the owning game's recorded accepted-opening disagreement occurs. -/
theorem selectedAnswers_eq_of_noAcceptedDisagreement
    [DecidableEq Cfg] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (state : ExtractorState Cfg Query Address Y config) (fallback : Y)
    {rounds : ℕ} {sites : List (QuerySite config rounds)}
    {openings : List (PublicOpening config rounds Y)}
    {attempts : List (AnyEvaluatedOpeningClaim Cfg Query Address Y config)}
    (hpairs : List.Forall₂ (fun site submitted =>
      siteMatches config site submitted = true ∧
        ((rootsOfState state)[site.slot.val]?).map Prod.fst = some site.tag)
      sites openings)
    (halign : ClaimsAligned (attachCheckpoints state fallback openings) attempts)
    (hall : attempts.all (fun attempt => attempt.2.accepted) = true)
    (hnobad : ¬ HasAcceptedOpeningDisagreement model.view state attempts) :
    (sites.map fun site => selectedValuesList
      (selectedValues (extractA model state fallback site).toLeafData site.selector)) =
    openings.map (fun submitted => selectedValuesList submitted.opening.values) := by
  induction hpairs generalizing attempts with
  | nil =>
      cases attempts with
      | nil => rfl
      | cons attempt rest =>
          simp [ClaimsAligned, attachCheckpoints] at halign
  | cons hsite htail ih =>
      rename_i site submitted sites openings
      cases attempts with
      | nil =>
          simp [ClaimsAligned, attachCheckpoints] at halign
      | cons attempt rest =>
          have halign' := halign
          unfold ClaimsAligned attachCheckpoints at halign'
          simp only [List.map_cons] at halign'
          cases halign' with
          | cons hclaim hclaims =>
              obtain ⟨accepted, hattempt⟩ := hclaim
              subst attempt
              simp only [List.all_cons, Bool.and_eq_true] at hall
              have hcheckpoint := checkpointAt_mem_of_public_tag state fallback site hsite.2
              have hsiteEq := siteMatches_site_eq config site submitted hsite.1
              subst site
              have hselector : submitted.site.selector = submitted.opening.selector :=
                eq_of_heq (siteMatches_opening_selector_eq config submitted.site submitted hsite.1)
              have hagree : (checkpointAt state fallback submitted.site).extractedOpening
                  model.view submitted.opening = submitted.opening.map some := by
                by_contra hneq
                apply hnobad
                refine ⟨submitted.site.tag,
                  ⟨checkpointAt state fallback submitted.site, submitted.opening, accepted⟩,
                  ?_, hcheckpoint, ?_⟩
                · simp
                · exact ⟨hall.1, hneq⟩
              have hhead : selectedValuesList
                  (selectedValues (extractA model state fallback submitted.site).toLeafData
                    submitted.site.selector) =
                    selectedValuesList submitted.opening.values := by
                rw [hselector]
                exact selectedValues_eq_of_noOpeningDisagreement model
                  (checkpointAt state fallback submitted.site) fallback submitted.opening hagree
              have htailNoBad :
                  ¬ HasAcceptedOpeningDisagreement model.view state rest := by
                intro hbad
                obtain ⟨tag, badAttempt, hmem, hrecorded, hdisagree⟩ := hbad
                exact hnobad ⟨tag, badAttempt, by simp [hmem], hrecorded, hdisagree⟩
              simp only [List.map_cons]
              exact congrArg₂ List.cons hhead (ih hclaims hall.2 htailNoBad)

/-- On every aligned coupled run, acceptance transfers pointwise from the public verifier to
the prescribed checkpoint-time extractor unless VCVio's owning bad event occurs. -/
theorem coupledAccept_implies_idealAccept_of_good
    [DecidableEq Cfg] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (transcript : CoupledTranscript (Query := Query) config rounds Y)
    (halign : ClaimsAligned
      (attachCheckpoints transcript.extractorState fallback transcript.openings)
      transcript.attempts)
    (hroots : transcript.roots = rootsOfState transcript.extractorState)
    (hreal : coupledAccept config rounds plan transcript = true)
    (hgood : ¬ (coupledOwnerView transcript).HasAnyCheckpointExtractionDisagreement model) :
    idealAccept model config rounds plan fallback transcript.extractorState
      transcript.roots transcript.openings = true := by
  unfold coupledAccept at hreal
  simp only [Bool.and_eq_true] at hreal
  obtain ⟨⟨hvalid, hall⟩, hdecision⟩ := hreal
  have hpairs := (planValidBool_pairs config rounds plan transcript.roots
    transcript.openings hvalid).2
  rw [hroots] at hpairs
  have hnobad : ¬ HasAcceptedOpeningDisagreement model.view
      transcript.extractorState transcript.attempts := by
    intro hbad
    exact hgood (Or.inl hbad)
  have hanswers := selectedAnswers_eq_of_noAcceptedDisagreement model
    transcript.extractorState fallback hpairs halign hall hnobad
  change idealAnswers model transcript.extractorState fallback plan =
      publicAnswers transcript.openings at hanswers
  unfold idealAccept
  rw [hanswers]
  simp [hvalid, hdecision]

/-- Actual cached runs satisfy the real-to-ideal implication outside the owning checkpoint
disagreement event, with alignment and public/private root correspondence discharged by support. -/
theorem coupledRun_real_implies_ideal_or_bad
    [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y)
    (transcript : CoupledTranscript (Query := Query) config rounds Y)
    (hrun : transcript ∈ support
      (coupledExperiment model config rounds fallback adversary))
    (hreal : coupledAccept config rounds plan transcript = true) :
    idealAccept model config rounds plan fallback transcript.extractorState
      transcript.roots transcript.openings = true ∨
    (coupledOwnerView transcript).HasAnyCheckpointExtractionDisagreement model := by
  by_cases hbad :
      (coupledOwnerView transcript).HasAnyCheckpointExtractionDisagreement model
  · exact Or.inr hbad
  · exact Or.inl <| coupledAccept_implies_idealAccept_of_good model config rounds plan
      fallback transcript
      (coupledExperiment_aligned model config rounds fallback adversary transcript hrun)
      (coupledExperiment_roots model config rounds fallback adversary transcript hrun)
      hreal hbad

/-- The actual public acceptance bit of the native interaction, after the same shared random
oracle cache interprets all commitment, opening, and honest verification queries. -/
def realAcceptanceExperiment [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :=
  (fun view : GameView (Query := Query) config rounds Y => view.accepted) <$>
    (nativeView config rounds rounds [] <$>
      nativeExperiment model config rounds plan fallback adversary)

/-- The ideal event reads its ordered answers only from immutable commitment-time checkpoint
vectors; it shares the exact malicious execution and random-oracle cache with the real game. -/
def idealAcceptanceExperiment [DecidableEq Cfg] [DecidableEq Query]
    [DecidableEq Address] [DecidableEq Y]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :=
  (fun transcript : CoupledTranscript (Query := Query) config rounds Y =>
    idealAccept model config rounds plan fallback transcript.extractorState
      transcript.roots transcript.openings) <$>
    coupledExperiment model config rounds fallback adversary

/-- Exact real-event equality induced by the native/coupled experiment marginal. -/
theorem prob_realAcceptance_eq_coupled
    [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Y]
    [EvalDistSemantics (OracleComp (Query →ₒ Y))]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    Pr{let accepted ← realAcceptanceExperiment model config rounds plan fallback adversary}[
      accepted = true] =
      Pr{let transcript ← coupledExperiment model config rounds fallback adversary}[
        coupledAccept config rounds plan transcript = true] := by
  unfold realAcceptanceExperiment
  rw [← coupledExperiment_native_eq model config rounds plan fallback adversary]
  simp only [Functor.map_map, prEvent_map]
  rfl

/-- Exact ideal-event equality in the coupled probability space. -/
theorem prob_idealAcceptance_eq_coupled
    [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [EvalDistSemantics (OracleComp (Query →ₒ Y))]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    Pr{let accepted ← idealAcceptanceExperiment model config rounds plan fallback adversary}[
      accepted = true] =
      Pr{let transcript ← coupledExperiment model config rounds fallback adversary}[
        idealAccept model config rounds plan fallback transcript.extractorState
          transcript.roots transcript.openings = true] := by
  simp only [idealAcceptanceExperiment, prEvent_map]

/-- The owned checkpoint bad event has exactly its VCVio probability, not a surrogate event. -/
theorem prob_coupled_bad_eq_owner
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [EvalDistSemantics (OracleComp (Query →ₒ Y))]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    Pr{let transcript ← coupledExperiment model config rounds fallback adversary}[
      (coupledOwnerView transcript).HasAnyCheckpointExtractionDisagreement model] =
    Pr{let transcript ← (extractabilityExperiment model config rounds
      (toOwningAdversary config rounds fallback adversary))}[
      transcript.HasAnyCheckpointExtractionDisagreement model] := by
  rw [← coupledExperiment_owner_eq model config rounds fallback adversary,
    prEvent_map]

/-- Exact up-to-bad probability transfer for the native verifier's actual acceptance output. -/
theorem prob_realAcceptance_le_ideal_add_checkpointBad
    [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [EvalDistSemantics (OracleComp (Query →ₒ Y))]
    [LawfulEvalDistSemantics (OracleComp (Query →ₒ Y))]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y) :
    Pr{let accepted ← realAcceptanceExperiment model config rounds plan fallback adversary}[
      accepted = true] ≤
      Pr{let accepted ← idealAcceptanceExperiment model config rounds plan fallback adversary}[
        accepted = true] +
      Pr{let transcript ← (extractabilityExperiment model config rounds
        (toOwningAdversary config rounds fallback adversary))}[
        transcript.HasAnyCheckpointExtractionDisagreement model] := by
  let mx := coupledExperiment model config rounds fallback adversary
  let p := fun (transcript : CoupledTranscript (Query := Query) config rounds Y) =>
    coupledAccept config rounds plan transcript = true
  let q := fun (transcript : CoupledTranscript (Query := Query) config rounds Y) =>
    idealAccept model config rounds plan fallback
    transcript.extractorState transcript.roots transcript.openings = true
  let bad := fun (transcript : CoupledTranscript (Query := Query) config rounds Y) =>
    (coupledOwnerView transcript).HasAnyCheckpointExtractionDisagreement model
  have hmono : Pr{let transcript ← mx}[p transcript] ≤
      Pr{let transcript ← mx}[q transcript ∨ bad transcript] :=
    prEvent_mono_of_support mx p (fun transcript => q transcript ∨ bad transcript)
      (fun transcript hrun hreal =>
        coupledRun_real_implies_ideal_or_bad model config rounds plan fallback adversary
          transcript hrun hreal)
  have hcore : Pr{let transcript ← mx}[p transcript] ≤
      Pr{let transcript ← mx}[q transcript] +
        Pr{let transcript ← mx}[bad transcript] :=
    hmono.trans (prEvent_or_le mx q bad)
  rw [prob_realAcceptance_eq_coupled, prob_idealAcceptance_eq_coupled,
    ← prob_coupled_bad_eq_owner]
  exact hcore

/-- Principal native terminal-batch Merkle ROM transfer. The resource premises are imposed on
the exact checkpoint-attaching image of the native adversary, so they bound its real adaptive
commitment and terminal opening program and every honest verification path. The uniform-measure
premise matches the owning VCVio numerical theorem and fixes the oracle's native semantics. -/
theorem realAcceptance_rom_bound_of_prefixQueryBound
    [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [IsUniformMeasureSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
    (adversary : Adversary (Query := Query) config rounds Y)
    (queryBound nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hquery : (toOwningAdversary config rounds fallback adversary).IsAdversaryPrefixQueryBound
      rounds queryBound)
    (hverifier : (toOwningAdversary config rounds fallback adversary).HasVerifierQueryBound
      verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr{let accepted ← realAcceptanceExperiment model config rounds plan fallback adversary}[
      accepted = true] ≤
      Pr{let accepted ← idealAcceptanceExperiment model config rounds plan fallback adversary}[
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
  exact (prob_realAcceptance_le_ideal_add_checkpointBad model config rounds plan fallback
    adversary).trans (add_le_add_right howner _)

/-- If the ideal checkpoint-time experiment accepts with probability at most `η`, the native
public verifier has the same quantitative upper bound plus the explicit ROM error. -/
theorem realAcceptance_le_eta_add_romError
    [DecidableEq Cfg] [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y] [Inhabited Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [IsUniformMeasureSpec (Query →ₒ Y)]
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (config : Configuration Cfg Address) (rounds : ℕ)
    (plan : QueryPlan config rounds Y) (fallback : Y)
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
        idealAcceptanceExperiment model config rounds plan fallback adversary}[accepted = true] ≤
        η) :
    Pr{let accepted ← realAcceptanceExperiment model config rounds plan fallback adversary}[
      accepted = true] ≤
      η + (multiCheckpointROMErrorNumerator nodeBudget checkpointCount verifierOverhead
        queryBound : ENNReal) * (Nat.card Y : ENNReal)⁻¹ := by
  exact (realAcceptance_rom_bound_of_prefixQueryBound model config rounds plan fallback
    adversary queryBound nodeBudget checkpointCount verifierOverhead perCheckpoint hquery
    hverifier hconfig hnodes hcheckpoints).trans (add_le_add_left hideal _)

end Interaction.Oracle.MerkleTerminalBatch
