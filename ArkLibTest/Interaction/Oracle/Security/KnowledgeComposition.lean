/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Security.KnowledgeComposition

/-!
# Dependent exported knowledge composition

The first prover sends a natural number and the verifier chooses a Boolean. That choice selects
an ordinary public-send suffix or an oracle-send suffix. The actual exported middle oracle reads
the first concrete payload, so the witness carrier is `Fin (payload + 1)`. Suffix witnesses have
an additional unit component, which the named backward extractor removes. Both middle branches
are certified, including the false branch, and the final relation uses the actual closed suffix
claim. These clients use ordinary public imports and execute both the native run and extractor.
-/

open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.TypeTree
open Interaction.TwoParty OracleComp OracleSpec PFunctor.FreeM

namespace Interaction.Oracle.Security.KnowledgeCompositionTest
set_option backward.isDefEq.respectTransparency false

@[instance_reducible] def natInterface : OracleInterface Nat where
  Query := Unit
  toOC := { spec := fun _ => Nat, impl := fun _ n => n }

@[implicit_reducible] def firstProtocol : Protocol :=
  Protocol.oracleWith Nat natInterface (Protocol.public .receiver Bool (fun _ => Protocol.done))

abbrev tree := firstProtocol.tree
abbrev roles := firstProtocol.roles
abbrev oracles := firstProtocol.oracles
abbrev initial := emptySpec.toPFunctor

def inputImpl : QueryImpl (ofPFunctor initial) Id := fun q => nomatch q

@[implicit_reducible] def exportFamily : OracleFamily Unit (fun _ => Nat) := ⟨fun _ => natInterface⟩

def firstFragment : Verifier.Fragment emptySpec tree roles oracles initial (fun _ => Unit) :=
  pure (pure ⟨true, ()⟩)

def middleLeaf (p : tree.BranchPath) :
    OpenClaim (ofPFunctor (TypeTree.accessAfter tree oracles initial p)) Bool exportFamily :=
  ⟨p.2.1, ⟨fun _ => liftM ((ofPFunctor
    (TypeTree.accessAfter tree oracles initial p)).query (Sum.inr ()))⟩⟩

def closedMid (path : tree.ExecutionPath) : ClosedClaim Bool exportFamily :=
  closedMiddle tree oracles initial inputImpl (fun _ => Bool) (fun _ _ => Nat)
    (fun _ => exportFamily) middleLeaf path

def middleProblem : Problem (ClaimFamily.closedOracle tree.BranchPath (fun _ => Bool)
    (fun _ => exportFamily)) where
  Witness := fun _ claim => Fin ((show Nat from claim.oracles ⟨(), ()⟩) + 1)
  admissible := fun _ _ => True
  rel := fun _ claim _ => claim.stmt = true
  rel_admissible := fun _ _ _ _ => trivial

def inputState : KnowledgeState := ⟨Nat, fun _ => False⟩

def firstExtractor : RoundExtractor tree inputState := fun message =>
  ⟨⟨Fin (message + 1), fun _ => False⟩, Fin.val,
    fun b => ⟨⟨Fin (message + 1), fun _ => b = true⟩, id, PUnit.unit⟩⟩

def firstSchedule : RoundExtractor.ChallengeSchedule tree roles := fun _ =>
  ⟨⟨pure true, 1⟩, fun _ => PUnit.unit⟩

def firstCertificate : KnowledgeCertificate tree roles inputState where
  extractor := firstExtractor
  challenges := firstSchedule
  prover_preserving := by
    refine ⟨?_, ?_⟩
    · intro message witness impossible
      exact impossible
    · intro message
      refine ⟨?_, fun _ => trivial⟩
      intro b sender
      cases sender
  local_bound := by
    intro message
    refine ⟨?_, fun _ => trivial⟩
    apply (_root_.RoundByRound.GameFamily.isBounded_iff _ _).mpr
    intro round context
    exact prEvent_le_one _ _

def middleEndpoint : TerminalRelation firstCertificate.extractor middleProblem
    (fun path => path.toBranchPath) closedMid where
  witnessEquiv path := Equiv.refl _
  knowledge_iff path witness := by
    rcases path with ⟨n, b, terminal⟩
    rfl

example (n : Nat) (b : Bool) : (closedMid ⟨n, ⟨b, PUnit.unit⟩⟩).oracles ⟨(), ()⟩ = n := rfl

#eval firstExtractor.extractWitness ⟨(7 : Nat), ⟨true, PUnit.unit⟩⟩ (⟨6, by decide⟩ : Fin 8)

@[implicit_reducible] def suffixProtocol (b : Bool) : Protocol :=
  if b then Protocol.public .sender Unit (fun _ => Protocol.done)
  else Protocol.oracleWith Nat natInterface Protocol.done

abbrev suffixTree (p : tree.BranchPath) := (suffixProtocol p.2.1).tree
abbrev suffixRoles (p : tree.BranchPath) := (suffixProtocol p.2.1).roles
abbrev suffixOracles (p : tree.BranchPath) := (suffixProtocol p.2.1).oracles

def pairState (root : KnowledgeState) : KnowledgeState :=
  ⟨root.Witness × Unit, fun witness => root.holds witness.1⟩

def suffixExtractor (b : Bool) (root : KnowledgeState) :
    RoundExtractor (suffixProtocol b).tree root := by
  cases b
  · exact fun _ => ⟨pairState root, Prod.fst, PUnit.unit⟩
  · exact fun _ => ⟨pairState root, Prod.fst, PUnit.unit⟩

def suffixSchedule (b : Bool) :
    RoundExtractor.ChallengeSchedule (suffixProtocol b).tree (suffixProtocol b).roles := by
  cases b
  · exact fun _ => PUnit.unit
  · exact ⟨PUnit.unit, fun _ => PUnit.unit⟩

def suffixCertificate (b : Bool) (root : KnowledgeState) :
    KnowledgeCertificate (suffixProtocol b).tree (suffixProtocol b).roles root where
  extractor := suffixExtractor b root
  challenges := suffixSchedule b
  prover_preserving := by
    cases b
    · exact ⟨fun _ _ known => known, fun _ => trivial⟩
    · exact ⟨fun _ _ _ known => known, fun _ => trivial⟩
  local_bound := by
    cases b <;> exact fun _ => trivial

def secondCertificate (path : tree.ExecutionPath) :=
  suffixCertificate path.toBranchPath.2.1
    (KnowledgeState.ofProblem middleProblem path.toBranchPath (closedMid path))

def compositeCertificate := firstCertificate.sequentialClosed suffixTree suffixRoles
  oracles initial inputImpl (fun _ => Bool) (fun _ _ => Nat) (fun _ => exportFamily)
  middleLeaf middleProblem middleEndpoint secondCertificate

def suffixFragment (p : tree.BranchPath) (_ : Bool) :
    Verifier.Fragment emptySpec (suffixTree p) (suffixRoles p) (suffixOracles p)
      exportFamily.spec.toPFunctor (fun _ => Unit) := by
  rcases p with ⟨marker, b, terminal⟩
  cases b
  · exact pure ()
  · exact fun _ => pure ()

def suffixClaim (p : tree.BranchPath) (statement : Bool)
    (q : (suffixTree p).BranchPath) :
    OpenClaim (ofPFunctor (TypeTree.accessAfter (suffixTree p) (suffixOracles p)
      exportFamily.spec.toPFunctor q)) Bool exportFamily := by
  rcases p with ⟨marker, b, terminal⟩
  cases b
  · rcases q with ⟨marker, terminal⟩
    change OpenClaim (exportFamily.spec + @OracleInterface.spec Nat natInterface)
      Bool exportFamily
    exact ⟨statement, ⟨fun _ => liftM
      ((exportFamily.spec + @OracleInterface.spec Nat natInterface).query (Sum.inl ⟨(), ()⟩))⟩⟩
  · rcases q with ⟨move, terminal⟩
    change OpenClaim exportFamily.spec Bool exportFamily
    exact ⟨statement, ⟨fun _ => liftM (exportFamily.spec.query ⟨(), ()⟩)⟩⟩

def suffixLeaf (p : tree.BranchPath) (statement : Bool)
    (q : (suffixTree p).BranchPath) := some (suffixClaim p statement q)

def secondVerifier (p : tree.BranchPath) (statement : Bool) :=
  withOutput emptySpec (suffixLeaf p statement) (suffixFragment p statement)

abbrev combined : Protocol :=
  ⟨PFunctor.FreeM.append tree suffixTree,
    PFunctor.FreeM.Displayed.Decoration.append roles suffixRoles,
    PFunctor.FreeM.Displayed.Decoration.append oracles suffixOracles⟩

def compositeVerifier : Verifier.Strategy emptySpec combined.tree combined.roles combined.oracles
    initial (fun p => Option (OpenClaim (ofPFunctor
      (TypeTree.accessAfter combined.tree combined.oracles initial p)) Bool exportFamily)) :=
  Verifier.appendExported emptySpec tree suffixTree roles suffixRoles oracles suffixOracles initial
    (fun _ => Bool) (fun _ _ => Nat) (fun _ => exportFamily)
    (fun _ => Bool) (fun _ _ => Nat) (fun _ => exportFamily)
    (withLeaf emptySpec middleLeaf firstFragment) secondVerifier

/-- The prover retains a private result and offers both possible suffix shapes. -/
def nativeProver : Prover.Strategy emptySpec combined.tree combined.roles (fun _ => Nat) := by
  refine pure ⟨(7 : Nat), ?_⟩
  intro b
  cases b
  · exact pure (pure ⟨(99 : Nat), (73 : Nat)⟩)
  · exact pure (pure ⟨(), (41 : Nat)⟩)

/-- Close only the claim returned by the same native execution. -/
def closedExecution : OracleComp emptySpec
    ((_path : combined.tree.ExecutionPath) × Nat × Option (ClosedClaim Bool exportFamily)) :=
  (fun result => ⟨result.1, result.2.1, result.2.2.map (fun claim => claim.closeWith
    (result.1.closingImpl combined.oracles initial inputImpl))⟩) <$>
    executeStrategies emptySpec combined.tree combined.roles combined.oracles initial inputImpl
      nativeProver compositeVerifier

/-- Read the concrete path, private output, and already closed claim. -/
def observeResult (result :
    (_path : combined.tree.ExecutionPath) × Nat × Option (ClosedClaim Bool exportFamily)) :
    Nat × Bool × Nat × Option (Bool × Nat) :=
  (show Nat from result.1.1, result.1.2.1, result.2.1,
    result.2.2.map (fun claim => (claim.stmt, show Nat from claim.oracles ⟨(), ()⟩)))

def observed : OracleComp emptySpec (Nat × Bool × Nat × Option (Bool × Nat)) :=
  observeResult <$> closedExecution

example : observed = pure (7, true, 41, some (true, 7)) := by
  unfold observed closedExecution compositeVerifier
  rw [executeStrategies_appendExported_close emptySpec tree suffixTree roles suffixRoles
    oracles suffixOracles initial inputImpl (fun _ => Bool) (fun _ _ => Nat)
    (fun _ => exportFamily) (fun _ => Bool) (fun _ _ => Nat) (fun _ => exportFamily)
    (fun _ => Nat) nativeProver (withLeaf emptySpec middleLeaf firstFragment) secondVerifier]
  rfl

#eval evalWithAnswerFn (fun q => nomatch q) observed

def handler : QueryImpl emptySpec ProbComp := fun q => nomatch q

theorem first_fresh : SamplesChallenges emptySpec handler tree roles oracles initial inputImpl
    _ firstFragment firstCertificate.challenges := by
  intro message after supported
  simp only [firstFragment, simulateQ_pure, MonadAttach.support_pure,
    Set.mem_singleton_iff] at supported
  subst after
  constructor
  · intro event
    simp only [simulateQ_pure]
    rfl
  · intro chosen supported
    trivial

theorem second_fresh (path : tree.ExecutionPath) :
    SamplesChallenges emptySpec handler (suffixTree path.toBranchPath)
      (suffixRoles path.toBranchPath) (suffixOracles path.toBranchPath)
      exportFamily.spec.toPFunctor (closedMid path).oracles _
      (secondVerifier path.toBranchPath (closedMid path).stmt)
      (secondCertificate path).challenges := by
  unfold secondVerifier withOutput
  apply samplesChallenges_withLeaf
  rcases path with ⟨message, b, terminal⟩
  cases b
  · intro message after supported
    trivial
  · intro move after supported
    trivial

theorem composite_fresh :
    SamplesChallenges emptySpec handler combined.tree combined.roles combined.oracles
      initial inputImpl _ compositeVerifier compositeCertificate.challenges := by
  unfold compositeVerifier
  exact samplesChallenges_appendExported_withLeaf emptySpec handler tree suffixTree
    roles suffixRoles oracles suffixOracles initial inputImpl (fun _ => Unit)
    (fun _ => Bool) (fun _ _ => Nat) (fun _ => exportFamily)
    (fun _ => Bool) (fun _ _ => Nat) (fun _ => exportFamily) middleLeaf firstFragment
    secondVerifier firstCertificate.challenges (fun path => (secondCertificate path).challenges)
    first_fresh second_fresh

def truePath : combined.tree.ExecutionPath :=
  PathAlong.append TypeTree.runtimeLens tree suffixTree
    ⟨(7 : Nat), true, PUnit.unit⟩ ⟨(), PUnit.unit⟩

def falsePath : combined.tree.ExecutionPath :=
  PathAlong.append TypeTree.runtimeLens tree suffixTree
    ⟨(7 : Nat), false, PUnit.unit⟩ ⟨(99 : Nat), PUnit.unit⟩

example : compositeCertificate.extractor.extractWitness truePath
    (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit) = (6 : Nat) := rfl

example : compositeCertificate.extractor.extractWitness falsePath
    (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit) = (6 : Nat) := rfl

#eval compositeCertificate.extractor.extractWitness truePath
    (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit)
#eval compositeCertificate.extractor.extractWitness falsePath
    (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit)

def finalProblem : Problem (ClaimFamily.closedOracle combined.tree.BranchPath (fun _ => Bool)
    (fun _ => exportFamily)) where
  Witness := fun _ claim => Fin ((show Nat from claim.oracles ⟨(), ()⟩) + 1) × Unit
  admissible := fun _ _ => True
  rel := fun _ claim _ => claim.stmt = true
  rel_admissible := fun _ _ _ _ => trivial

def finalClosed (path : tree.ExecutionPath) (rest : (suffixTree path.toBranchPath).ExecutionPath) :
    ClosedClaim Bool exportFamily :=
  (suffixClaim path.toBranchPath (closedMid path).stmt rest.toBranchPath).closeWith
    (rest.closingImpl (suffixOracles path.toBranchPath) exportFamily.spec.toPFunctor
      (closedMid path).oracles)

def finalEndpoint (path : tree.ExecutionPath) :
    TerminalRelation (secondCertificate path).extractor finalProblem
      (fun rest => Path.append tree suffixTree path.toBranchPath rest.toBranchPath)
      (finalClosed path) where
  witnessEquiv rest := by
    rcases path with ⟨message, b, terminal⟩
    cases b <;> exact Equiv.refl _
  knowledge_iff rest witness := by
    rcases path with ⟨message, b, terminal⟩
    cases b <;> rfl

def compositeEndpoint := firstCertificate.sequentialTerminalRelation suffixTree suffixRoles
  middleProblem (fun path => path.toBranchPath) closedMid middleEndpoint secondCertificate
  finalProblem (fun path rest => Path.append tree suffixTree path.toBranchPath rest.toBranchPath)
  finalClosed finalEndpoint

example : (compositeEndpoint.witnessEquiv truePath
    (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit)).1.val = 6 := rfl

/-- Empty message carriers and empty witnesses require no fabricated message or witness. -/
def emptyExtractor : RoundExtractor (.public Empty (fun _ => .done))
    (⟨Empty, fun _ => False⟩ : KnowledgeState) := Empty.elim

/-- Structural extraction supports larger universes and payload-dependent witness carriers. -/
def largeState : KnowledgeState.{2} := ⟨ULift.{2} Nat, fun _ => True⟩

def largeExtractor : RoundExtractor (.oracle (ULift.{1} Nat) (fun _ => .done)) largeState :=
  fun message => ⟨⟨ULift.{2} (Fin (message.down + 1)), fun _ => True⟩,
    (fun witness => ⟨witness.down.val⟩), PUnit.unit⟩

example : (largeExtractor.extractWitness ⟨(⟨7⟩ : ULift.{1} Nat), PUnit.unit⟩
    (⟨⟨6, by decide⟩⟩ : ULift.{2} (Fin 8))).down = 6 := rfl

end Interaction.Oracle.Security.KnowledgeCompositionTest
