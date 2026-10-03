/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Prefix
public import ArkLib.Interaction.Oracle.Claim
public import VCVio.CryptoFoundations.RoundByRound

/-!
# Witness-indexed round-by-round knowledge certificates

Named witness maps transport candidate witnesses backward on the existing native concrete
prefixes and execution paths. Prover messages preserve knowledge after applying those maps.
If a terminal witness is known but its extracted input witness is unknown, an actual verifier
challenge on the same path violates knowledge preservation, using the witness computed from its
remaining suffix.

Local knowledge bounds are separate from this deterministic extraction theorem. They use VCVio's
`RoundByRound.GameFamily` and place the existential later witness inside each fresh-challenge
probability. Every authored prefix is covered, including those of zero ordinary execution mass.
Neither extraction efficiency nor a state-restoration bound is asserted here.
-/

@[expose] public section

universe u w

namespace Interaction.Oracle.Security

open Interaction.Oracle.TypeTree PFunctor.FreeM

/-- A witness carrier and its knowledge predicate at one concrete transcript prefix.
The carrier may be empty; existence of witnesses is never assumed by the extraction theory. -/
structure KnowledgeState where
  Witness : Type w
  holds : Witness → Prop

/-- Equality of knowledge states transports both the witness carrier and its predicate. -/
theorem KnowledgeState.holds_cast {first second : KnowledgeState.{w}} (same : first = second)
    (witness : second.Witness) : first.holds (same.symm ▸ witness) ↔ second.holds witness := by
  cases same
  rfl

/-- Total backward witness maps on actual native messages, supplied independently of knowledge.
Each child retains its own witness type and predicate. At oracle nodes that type may depend on
the concrete payload even though the structural branch is `PUnit`. Maps from an inhabited later
carrier to an empty earlier carrier cannot be supplied; that is an explicit extraction premise. -/
def RoundExtractor : (tree : Oracle.TypeTree.{u}) → KnowledgeState.{w} → Type (max (u+1) (w+1))
  | .done, _ => PUnit
  | .public Moves next, state =>
      (move : Moves) → (after : KnowledgeState.{w}) ×
        ((after.Witness → state.Witness) × RoundExtractor (next move) after)
  | .oracle Messages next, state =>
      (message : Messages) → (after : KnowledgeState.{w}) ×
        ((after.Witness → state.Witness) × RoundExtractor (next PUnit.unit) after)

namespace RoundExtractor

/-- Knowledge state after a typed native cursor spine with its concrete oracle messages. -/
def stateAt : {tree residual : Oracle.TypeTree.{u}} → {state : KnowledgeState.{w}} →
    RoundExtractor tree state → (spine : Cursor.Spine tree residual) →
    PrefixMessages.Along spine → KnowledgeState.{w}
  | _, _, state, _, .root _, _ => state
  | .public _ _, _, _, extractor, .down move tail, messages =>
      stateAt (extractor move).2.2 tail messages
  | .oracle _ _, _, _, extractor, .down _ tail, messages =>
      stateAt (extractor messages.1).2.2 tail messages.2

/-- The witness carrier and predicate at the terminal prefix of this actual native path. -/
def terminalState : {tree : Oracle.TypeTree.{u}} → {state : KnowledgeState.{w}} →
    RoundExtractor tree state → tree.ExecutionPath → KnowledgeState.{w}
  | .done, state, _, _ => state
  | .public _ _, _, extractor, path => terminalState (extractor path.1).2.2 path.2
  | .oracle _ _, _, extractor, path => terminalState (extractor path.1).2.2 path.2

/-- Execute the named backward extractor on the supplied complete native path and terminal witness.
The algorithm applies the supplied maps and neither decides knowledge nor selects a witness. -/
def extractWitness : {tree : Oracle.TypeTree.{u}} → {state : KnowledgeState.{w}} →
    (extractor : RoundExtractor tree state) → (path : tree.ExecutionPath) →
    (terminalState extractor path).Witness → state.Witness
  | .done, _, _, _, witness => witness
  | .public _ _, _, extractor, path, witness =>
      (extractor path.1).2.1 (extractWitness (extractor path.1).2.2 path.2 witness)
  | .oracle _ _, _, extractor, path, witness =>
      (extractor path.1).2.1 (extractWitness (extractor path.1).2.2 path.2 witness)

/-- Restrict witness maps to the residual selected by the native concrete prefix. -/
def restrict : {tree residual : Oracle.TypeTree.{u}} → {state : KnowledgeState.{w}} →
    (extractor : RoundExtractor tree state) → (spine : Cursor.Spine tree residual) →
    (messages : PrefixMessages.Along spine) →
    RoundExtractor residual (stateAt extractor spine messages)
  | _, _, _, extractor, .root _, _ => extractor
  | .public _ _, _, _, extractor, .down move tail, messages =>
      restrict (extractor move).2.2 tail messages
  | .oracle _ _, _, _, extractor, .down _ tail, messages =>
      restrict (extractor messages.1).2.2 tail messages.2

/-- Execute backward extraction through a native typed spine and its retained messages. -/
def extractPrefix : {tree residual : Oracle.TypeTree.{u}} → {state : KnowledgeState.{w}} →
    (extractor : RoundExtractor tree state) → (spine : Cursor.Spine tree residual) →
    (messages : PrefixMessages.Along spine) →
    (stateAt extractor spine messages).Witness → state.Witness
  | _, _, _, _, .root _, _, witness => witness
  | .public _ _, _, _, extractor, .down move tail, messages, witness =>
      (extractor move).2.1 (extractPrefix (extractor move).2.2 tail messages witness)
  | .oracle _ _, _, _, extractor, .down _ tail, messages, witness =>
      (extractor messages.1).2.1
        (extractPrefix (extractor messages.1).2.2 tail messages.2 witness)

/-- Native spine composition preserves the exact dependent knowledge state. -/
theorem stateAt_comp {tree middle residual : Oracle.TypeTree.{u}}
    {state : KnowledgeState.{w}} (extractor : RoundExtractor tree state)
    (first : Cursor.Spine tree middle) (second : Cursor.Spine middle residual)
    (left : PrefixMessages.Along first) (right : PrefixMessages.Along second) :
    stateAt extractor (first.comp second) (PrefixMessages.comp first second left right) =
      stateAt (restrict extractor first left) second right := by
  induction first generalizing state with
  | root => rfl
  | @down position next middle answer tail ih =>
      cases position with
      | «public» => exact ih (extractor answer).2.2 second left right
      | «oracle» =>
          cases answer
          exact ih (extractor left.1).2.2 second left.2 right

/-- Backward extraction respects native spine composition with explicit witness transport. -/
theorem extractPrefix_comp {tree middle residual : Oracle.TypeTree.{u}}
    {state : KnowledgeState.{w}} (extractor : RoundExtractor tree state)
    (first : Cursor.Spine tree middle) (second : Cursor.Spine middle residual)
    (left : PrefixMessages.Along first) (right : PrefixMessages.Along second)
    (witness : (stateAt (restrict extractor first left) second right).Witness) :
    extractPrefix extractor (first.comp second) (PrefixMessages.comp first second left right)
      ((stateAt_comp extractor first second left right).symm ▸ witness) =
    extractPrefix extractor first left
      (extractPrefix (restrict extractor first left) second right witness) := by
  induction first generalizing state with
  | root => rfl
  | @down position next middle answer tail ih =>
      cases position with
      | «public» =>
          exact congrArg (extractor answer).2.1
            (ih (extractor answer).2.2 second left right witness)
      | «oracle» =>
          cases answer
          exact congrArg (extractor left.1).2.1
            (ih (extractor left.1).2.2 second left.2 right witness)

/-- The knowledge state at an actual concrete execution prefix. -/
def knowledgeState {tree : Oracle.TypeTree.{u}} {state : KnowledgeState.{w}}
    (extractor : RoundExtractor tree state) (pfx : ExecutionPrefix tree) : KnowledgeState.{w} :=
  stateAt extractor pfx.cursor.spine pfx.messages

/-- The same extractor's remaining maps after an actual concrete prefix. -/
def remainingExtractor {tree : Oracle.TypeTree.{u}} {state : KnowledgeState.{w}}
    (extractor : RoundExtractor tree state) (pfx : ExecutionPrefix tree) :
    RoundExtractor pfx.cursor.residual (knowledgeState extractor pfx) :=
  restrict extractor pfx.cursor.spine pfx.messages

/-- Extract a prefix's candidate input witness by following exactly its native messages backward. -/
def extractPrefixWitness {tree : Oracle.TypeTree.{u}} {state : KnowledgeState.{w}}
    (extractor : RoundExtractor tree state) (pfx : ExecutionPrefix tree)
    (witness : (knowledgeState extractor pfx).Witness) : state.Witness :=
  extractPrefix extractor pfx.cursor.spine pfx.messages witness

/-- Native prefix composition identifies the later witness carrier with the residual extractor. -/
theorem knowledgeState_comp {tree : Oracle.TypeTree.{u}} {state : KnowledgeState.{w}}
    (extractor : RoundExtractor tree state) (first : ExecutionPrefix tree)
    (second : ExecutionPrefix first.cursor.residual) :
    knowledgeState extractor (first.comp second) =
      knowledgeState (remainingExtractor extractor first) second :=
  stateAt_comp extractor first.cursor.spine second.cursor.spine first.messages second.messages

/-- Backward extraction on native prefix composition is the composition of the named extractors.
The explicit equality transport identifies the actual dependent witness types. -/
theorem extractPrefixWitness_comp {tree : Oracle.TypeTree.{u}} {state : KnowledgeState.{w}}
    (extractor : RoundExtractor tree state) (first : ExecutionPrefix tree)
    (second : ExecutionPrefix first.cursor.residual)
    (witness : (knowledgeState (remainingExtractor extractor first) second).Witness) :
    extractPrefixWitness extractor (first.comp second)
      ((knowledgeState_comp extractor first second).symm ▸ witness) =
      extractPrefixWitness extractor first
        (extractPrefixWitness (remainingExtractor extractor first) second witness) :=
  extractPrefix_comp extractor first.cursor.spine second.cursor.spine first.messages
    second.messages witness

/-- The complete-path endpoint is the knowledge state at its actual terminal native pfx. -/
theorem terminalState_eq_knowledgeState : {tree : Oracle.TypeTree.{u}} →
    {state : KnowledgeState.{w}} → (extractor : RoundExtractor tree state) →
    (path : tree.ExecutionPath) →
    terminalState extractor path = knowledgeState extractor (ExecutionPrefix.ofExecutionPath path)
  | .done, _, _, _ => rfl
  | .public _ _, _, extractor, path =>
      terminalState_eq_knowledgeState (extractor path.1).2.2 path.2
  | .oracle _ _, _, extractor, path =>
      terminalState_eq_knowledgeState (extractor path.1).2.2 path.2

/-- Prover messages preserve knowledge after applying their named witness map. -/
def IsProverPreserving : {tree : Oracle.TypeTree.{u}} → {state : KnowledgeState.{w}} →
    RoundExtractor tree state → tree.RoleDecoration → Prop
  | .done, _, _, _ => True
  | .public _ _, state, extractor, roles =>
      (∀ move, roles.1 = .sender → ∀ witness,
        (extractor move).1.holds witness → state.holds ((extractor move).2.1 witness)) ∧
      ∀ move, IsProverPreserving (extractor move).2.2 (roles.2 move)
  | .oracle _ _, state, extractor, roles =>
      (∀ message witness, (extractor message).1.holds witness →
        state.holds ((extractor message).2.1 witness)) ∧
      ∀ message, IsProverPreserving (extractor message).2.2 (roles.2 PUnit.unit)

/-- A bad verifier challenge on this actual native path, using the witness extracted from its
actual suffix. No existential witness is selected from a knowledge-state proof. -/
def BadChallengeOnPath : {tree : Oracle.TypeTree.{u}} → {state : KnowledgeState.{w}} →
    (extractor : RoundExtractor tree state) → tree.RoleDecoration →
    (path : tree.ExecutionPath) → (terminalState extractor path).Witness → Prop
  | .done, _, _, _, _, _ => False
  | .public _ _, state, extractor, roles, path, witness =>
      (roles.1 = .receiver ∧
        ¬ state.holds ((extractor path.1).2.1
          (extractWitness (extractor path.1).2.2 path.2 witness)) ∧
        (extractor path.1).1.holds
          (extractWitness (extractor path.1).2.2 path.2 witness)) ∨
      BadChallengeOnPath (extractor path.1).2.2 (roles.2 path.1) path.2 witness
  | .oracle _ _, _, extractor, roles, path, witness =>
      BadChallengeOnPath (extractor path.1).2.2 (roles.2 PUnit.unit) path.2 witness

/-- A known terminal witness whose extracted input witness is unknown identifies a bad verifier
challenge on that same path, assuming prover preservation. Its later witness is the named suffix
extractor's output, including for dependent witness types and empty protocols. -/
theorem extraction_failure_implies_bad_challenge : {tree : Oracle.TypeTree.{u}} →
    {state : KnowledgeState.{w}} → (extractor : RoundExtractor tree state) →
    (roles : tree.RoleDecoration) → IsProverPreserving extractor roles →
    (path : tree.ExecutionPath) → (witness : (terminalState extractor path).Witness) →
    (terminalState extractor path).holds witness →
    ¬ state.holds (extractWitness extractor path witness) →
    BadChallengeOnPath extractor roles path witness
  | .done, _, _, _, _, _, _, good, bad => (bad good).elim
  | .public _ _, _, extractor, roles, preserving, path, witness, good, bad => by
      by_cases nextGood : (extractor path.1).1.holds
          (extractWitness (extractor path.1).2.2 path.2 witness)
      · refine Or.inl ⟨?_, bad, nextGood⟩
        cases roleEq : roles.1 with
        | sender => exact (bad (preserving.1 path.1 roleEq _ nextGood)).elim
        | receiver => rfl
      · exact Or.inr (extraction_failure_implies_bad_challenge (extractor path.1).2.2
          (roles.2 path.1) (preserving.2 path.1) path.2 witness good nextGood)
  | .oracle _ _, _, extractor, roles, preserving, path, witness, good, bad => by
      have nextBad : ¬ (extractor path.1).1.holds
          (extractWitness (extractor path.1).2.2 path.2 witness) :=
        fun nextGood => bad (preserving.1 path.1 _ nextGood)
      exact extraction_failure_implies_bad_challenge (extractor path.1).2.2
        (roles.2 PUnit.unit) (preserving.2 path.1) path.2 witness good nextBad

/-- Replace only the input witness carrier through an explicit equivalence. The maps remain
computational data and no relation membership is decided. -/
def changeInputState : {tree : Oracle.TypeTree.{u}} → {state : KnowledgeState.{w}} →
    RoundExtractor tree state → (input : KnowledgeState.{w}) →
    (input.Witness ≃ state.Witness) → RoundExtractor tree input
  | .done, _, _, _, _ => PUnit.unit
  | .public _ _, _, extractor, _, equiv => fun move =>
      ⟨(extractor move).1, (fun witness => equiv.symm ((extractor move).2.1 witness)),
        (extractor move).2.2⟩
  | .oracle _ _, _, extractor, _, equiv => fun message =>
      ⟨(extractor message).1, (fun witness => equiv.symm ((extractor message).2.1 witness)),
        (extractor message).2.2⟩

/-- Terminal witness identification after replacing the input carrier; it is identity unless
the protocol is empty, where the terminal carrier is the input carrier. -/
def terminalWitnessEquiv : {tree : Oracle.TypeTree.{u}} → {state : KnowledgeState.{w}} →
    (extractor : RoundExtractor tree state) → (input : KnowledgeState.{w}) →
    (equiv : input.Witness ≃ state.Witness) → (path : tree.ExecutionPath) →
    (terminalState (changeInputState extractor input equiv) path).Witness ≃
      (terminalState extractor path).Witness
  | .done, _, _, _, equiv, _ => equiv
  | .public _ _, _, _, _, _, _ => Equiv.refl _
  | .oracle _ _, _, _, _, _, _ => Equiv.refl _

/-- Replacing the input carrier also preserves terminal knowledge, including an empty protocol. -/
theorem terminalKnowledge_changeInputState {tree : Oracle.TypeTree.{u}}
    {state : KnowledgeState.{w}} (extractor : RoundExtractor tree state)
    (input : KnowledgeState.{w}) (equiv : input.Witness ≃ state.Witness)
    (compatible : ∀ witness, input.holds witness ↔ state.holds (equiv witness))
    (path : tree.ExecutionPath)
    (witness : (terminalState (changeInputState extractor input equiv) path).Witness) :
    (terminalState (changeInputState extractor input equiv) path).holds witness ↔
      (terminalState extractor path).holds
        (terminalWitnessEquiv extractor input equiv path witness) := by
    cases tree using Oracle.TypeTree.casesOn with
    | done => exact compatible witness
    | «public» => exact Iff.rfl
    | «oracle» => exact Iff.rfl

/-- Explicit input-carrier transport commutes with named complete-path extraction. -/
theorem extractWitness_changeInputState : {tree : Oracle.TypeTree.{u}} →
    {state : KnowledgeState.{w}} → (extractor : RoundExtractor tree state) →
    (input : KnowledgeState.{w}) → (equiv : input.Witness ≃ state.Witness) →
    (path : tree.ExecutionPath) →
    (witness : (terminalState (changeInputState extractor input equiv) path).Witness) →
    equiv (extractWitness (changeInputState extractor input equiv) path witness) =
      extractWitness extractor path (terminalWitnessEquiv extractor input equiv path witness)
  | .done, _, _, _, _, _, _ => rfl
  | .public _ _, _, _, _, equiv, _, _ => equiv.apply_symm_apply _
  | .oracle _ _, _, _, _, equiv, _, _ => equiv.apply_symm_apply _

/-- Equivalent input knowledge predicates preserve the prover-message laws. -/
theorem isProverPreserving_changeInputState {tree : Oracle.TypeTree.{u}}
    {state : KnowledgeState.{w}} (extractor : RoundExtractor tree state)
    (input : KnowledgeState.{w}) (equiv : input.Witness ≃ state.Witness)
    (compatible : ∀ witness, input.holds witness ↔ state.holds (equiv witness))
    (roles : tree.RoleDecoration) (preserving : IsProverPreserving extractor roles) :
    IsProverPreserving (changeInputState extractor input equiv) roles := by
  cases tree using Oracle.TypeTree.casesOn with
  | done => trivial
  | «public» Moves next =>
      refine ⟨?_, preserving.2⟩
      intro move sender witness good
      change input.holds (equiv.symm ((extractor move).2.1 witness))
      apply (compatible _).mpr
      simpa using preserving.1 move sender witness good
  | «oracle» Messages next =>
      refine ⟨?_, preserving.2⟩
      intro message witness good
      change input.holds (equiv.symm ((extractor message).2.1 witness))
      apply (compatible _).mpr
      simpa using preserving.1 message witness good

/-- The local event has its eventual witness inside the probability. -/
def badChallenge {Moves : Type u} {next : Moves → Oracle.TypeTree.{u}}
    {state : KnowledgeState.{w}} (extractor : RoundExtractor (.public Moves next) state)
    (challenge : Moves) : Prop :=
  ∃ witness, ¬ state.holds ((extractor challenge).2.1 witness) ∧
    (extractor challenge).1.holds witness

/-- VCVio's existing event-game interface, specialized to one fixed authored prefix. -/
def localGame {Moves : Type} {next : Moves → Oracle.TypeTree}
    {state : KnowledgeState.{w}} (extractor : RoundExtractor (.public Moves next) state)
    (sample : ProbComp Moves) : _root_.RoundByRound.GameFamily Unit (fun _ => Unit) where
  Result := fun _ => Moves
  sample := fun _ _ => sample
  event := fun _ _ => badChallenge extractor

/-- Fresh-challenge programs and local errors at verifier nodes; prover choices and concrete
oracle messages index every later authored prefix. This metadata does not run a protocol. -/
def ChallengeSchedule : (tree : Oracle.TypeTree.{0}) → tree.RoleDecoration → Type
  | .done, _ => PUnit
  | .public Moves next, roles =>
      (match roles.1 with
        | .sender => PUnit.{1}
        | .receiver => ProbComp Moves × ENNReal) ×
      ((move : Moves) → ChallengeSchedule (next move) (roles.2 move))
  | .oracle Messages next, roles =>
      (message : Messages) → ChallengeSchedule (next PUnit.unit) (roles.2 PUnit.unit)

/-- Every authored verifier prefix has the stated local bound, including prefixes with zero
probability in ordinary execution. The sampled challenge is fresh at that fixed prefix. -/
def IsLocallyBounded : {tree : Oracle.TypeTree.{0}} → {state : KnowledgeState.{w}} →
    (extractor : RoundExtractor tree state) → (roles : tree.RoleDecoration) →
    ChallengeSchedule tree roles → Prop
  | .done, _, _, _, _ => True
  | .public _ _, _, extractor, ⟨.sender, roles⟩, schedule =>
      ∀ move, IsLocallyBounded (extractor move).2.2 (roles move) (schedule.2 move)
  | .public _ _, _, extractor, ⟨.receiver, roles⟩, schedule =>
      (localGame extractor schedule.1.1).IsBounded (fun _ => schedule.1.2) ∧
      ∀ move, IsLocallyBounded (extractor move).2.2 (roles move) (schedule.2 move)
  | .oracle _ _, _, extractor, roles, schedule =>
      ∀ message, IsLocallyBounded (extractor message).2.2 (roles.2 PUnit.unit) (schedule message)

/-- Input-carrier transport preserves each bad-challenge event exactly. -/
theorem badChallenge_changeInputState {Moves : Type u} {next : Moves → Oracle.TypeTree.{u}}
    {state : KnowledgeState.{w}} (extractor : RoundExtractor (.public Moves next) state)
    (input : KnowledgeState.{w}) (equiv : input.Witness ≃ state.Witness)
    (compatible : ∀ witness, input.holds witness ↔ state.holds (equiv witness))
    (challenge : Moves) :
    badChallenge (changeInputState extractor input equiv) challenge ↔
      badChallenge extractor challenge := by
  simp only [badChallenge, changeInputState, compatible, Equiv.apply_symm_apply]

/-- Input-carrier transport preserves all local knowledge bounds, with the same sampler/errors. -/
theorem isLocallyBounded_changeInputState {tree : Oracle.TypeTree.{0}}
    {state : KnowledgeState.{w}} (extractor : RoundExtractor tree state)
    (input : KnowledgeState.{w}) (equiv : input.Witness ≃ state.Witness)
    (compatible : ∀ witness, input.holds witness ↔ state.holds (equiv witness))
    (roles : tree.RoleDecoration) (schedule : ChallengeSchedule tree roles)
    (bounded : IsLocallyBounded extractor roles schedule) :
    IsLocallyBounded (changeInputState extractor input equiv) roles schedule := by
  cases tree using Oracle.TypeTree.casesOn with
  | done => trivial
  | «public» Moves next =>
      rcases roles with ⟨role, roles⟩
      cases role with
      | sender => exact bounded
      | receiver =>
          rcases bounded with ⟨bound, children⟩
          refine ⟨?_, children⟩
          rw [_root_.RoundByRound.GameFamily.isBounded_iff] at bound ⊢
          intro round context
          have probability := prEvent_congr schedule.1.1
            (badChallenge (changeInputState extractor input equiv)) (badChallenge extractor)
            (badChallenge_changeInputState extractor input equiv compatible)
          exact probability.le.trans (bound round context)
  | «oracle» Messages next => exact bounded

end RoundExtractor

/-- A problem's actual claim-dependent witness relation as a knowledge state. -/
def KnowledgeState.ofProblem {Context : Type u} {family : ClaimFamily.{u, u} Context}
    (problem : Problem.{u, u, w} family) (context : Context) (claim : family.Claim context) :
    KnowledgeState.{w} :=
  ⟨problem.Witness context claim, problem.rel context claim⟩

/-- Local witness-indexed knowledge security for a native tree, with named extractors.
The certificate supplies prover preservation and bounds at every authored verifier prefix.
Its fresh challenge programs require a separate native-verifier correspondence where used. -/
structure KnowledgeCertificate (tree : Oracle.TypeTree.{0}) (roles : tree.RoleDecoration)
    (state : KnowledgeState.{w}) where
  /-- Total, named backward witness maps on the actual native messages. -/
  extractor : RoundExtractor tree state
  /-- Fresh challenge programs and local errors at each authored verifier prefix. -/
  challenges : RoundExtractor.ChallengeSchedule tree roles
  /-- Prover messages cannot create knowledge under the named witness maps. -/
  prover_preserving : extractor.IsProverPreserving roles
  /-- Every fixed-prefix bad-challenge event has its stated local error bound. -/
  local_bound : extractor.IsLocallyBounded roles challenges

/-- Identify a terminal knowledge state with a specified claim's actual witness relation.
Both the carrier identification and the equivalence of predicates are explicit. No valid
terminal witness or relation membership is assumed by this interface. -/
structure TerminalRelation {tree : Oracle.TypeTree.{u}} {state : KnowledgeState.{w}}
    (extractor : RoundExtractor tree state) {Context : Type u}
    {family : ClaimFamily.{u, u} Context} (problem : Problem.{u, u, w} family)
    (context : tree.ExecutionPath → Context)
    (claim : (path : tree.ExecutionPath) → family.Claim (context path)) where
  /-- Named identification with the problem's claim-dependent witness carrier. -/
  witnessEquiv : (path : tree.ExecutionPath) →
    (extractor.terminalState path).Witness ≃ problem.Witness (context path) (claim path)
  /-- The endpoint knowledge predicate is exactly the stated output relation. -/
  knowledge_iff : ∀ path witness, (extractor.terminalState path).holds witness ↔
    problem.rel (context path) (claim path) (witnessEquiv path witness)

/-- An explicit change of input witnesses preserves the exact terminal relation. -/
def TerminalRelation.changeInputState {tree : Oracle.TypeTree.{u}} {state : KnowledgeState.{w}}
    {extractor : RoundExtractor tree state} {Context : Type u}
    {family : ClaimFamily.{u, u} Context} {problem : Problem.{u, u, w} family}
    {context : tree.ExecutionPath → Context}
    {claim : (path : tree.ExecutionPath) → family.Claim (context path)}
    (terminal : TerminalRelation extractor problem context claim)
    (input : KnowledgeState.{w}) (equiv : input.Witness ≃ state.Witness)
    (compatible : ∀ witness, input.holds witness ↔ state.holds (equiv witness)) :
    TerminalRelation (extractor.changeInputState input equiv) problem context claim where
  witnessEquiv path := (extractor.terminalWitnessEquiv input equiv path).trans
    (terminal.witnessEquiv path)
  knowledge_iff path witness := (extractor.terminalKnowledge_changeInputState input equiv
    compatible path witness).trans (terminal.knowledge_iff path _)

namespace KnowledgeCertificate

/-- Explicit input-witness transport preserves a certificate's local errors. -/
def changeInputState {tree : Oracle.TypeTree.{0}} {roles : tree.RoleDecoration}
    {state : KnowledgeState.{w}} (certificate : KnowledgeCertificate tree roles state)
    (input : KnowledgeState.{w}) (equiv : input.Witness ≃ state.Witness)
    (compatible : ∀ witness, input.holds witness ↔ state.holds (equiv witness)) :
    KnowledgeCertificate tree roles input where
  extractor := certificate.extractor.changeInputState input equiv
  challenges := certificate.challenges
  prover_preserving := certificate.extractor.isProverPreserving_changeInputState input equiv
    compatible roles certificate.prover_preserving
  local_bound := certificate.extractor.isLocallyBounded_changeInputState input equiv
    compatible roles certificate.challenges certificate.local_bound

end KnowledgeCertificate

end Interaction.Oracle.Security
