/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Sequential

/-!
# Oracle-execution acceptance client

The verifier computes its public challenge by querying an initial resource and a previously sent
oracle. A second oracle is sent immediately before termination; the terminal action must query it.
An ambient stateful logger distinguishes the exact effect schedule from reordered or duplicated
execution. The non-faithful interface reveals only one coordinate of each concrete message.
-/

namespace Interaction.Oracle.ExecutionExample

open OracleComp OracleSpec TwoParty

/-- Ambient operations are tagged so a stateful interpreter can observe order and multiplicity. -/
abbrev ambient : OracleSpec Nat := Nat →ₒ Nat

/-- Pure input behavior is deliberately supplied without an honest input object. -/
abbrev inputSpec : OracleSpec Unit := Unit →ₒ Nat

/-- The fixed input handler. -/
def inputImpl : QueryImpl inputSpec Id := fun _ => 7

/-- Only the first coordinate of a concrete message is queryable. -/
@[reducible]
def firstInterface : OracleInterface (Nat × Nat) where
  Query := Unit
  toOC.spec := Unit →ₒ Nat
  toOC.impl _ := do return (← read).1

/-- Both public roles and two oracle messages; the final send has no later protocol node. -/
abbrev protocol : Oracle.Protocol :=
  .public .sender Bool fun _ =>
    .oracleWith (Nat × Nat) firstInterface <|
      .public .receiver Nat fun _ =>
        .oracleWith (Nat × Nat) firstInterface .done

/-- Access after the first oracle send. -/
abbrev firstAccess : PFunctor := Access.extend inputSpec.toPFunctor firstInterface

/-- Access after the second oracle send. -/
abbrev finalAccess : PFunctor := Access.extend firstAccess firstInterface

/-- The terminal action queries the final message and performs a tagged ambient operation. -/
def terminal (announced : Bool) (challenge : Nat) :
    OracleComp (ambient + OracleSpec.ofPFunctor finalAccess) Nat := do
  let _ ← liftM ((ambient + OracleSpec.ofPFunctor finalAccess).query (.inl 3))
  let latest : Nat ← liftM
    ((ambient + OracleSpec.ofPFunctor finalAccess).query (.inr (.inr ())))
  return if announced then latest + challenge else 0

/-- No concrete message is an argument to either oracle-node verifier continuation. -/
def verifier : Verifier.Strategy ambient protocol.tree protocol.roles protocol.oracles
    inputSpec.toPFunctor (fun _ => Nat) := by
  -- Expose the four phase types before elaborating query lifts. The protocol constructors
  -- remain opaque to instance search; this is a definitional change, not a cast or assumption.
  change Bool → OracleComp (ambient + inputSpec)
    (OracleComp (ambient + OracleSpec.ofPFunctor firstAccess)
      (OracleComp (ambient + OracleSpec.ofPFunctor firstAccess)
        (Σ _ : Nat, OracleComp (ambient + OracleSpec.ofPFunctor finalAccess)
          (OracleComp (ambient + OracleSpec.ofPFunctor finalAccess) Nat))))
  exact fun announced => do
    let _ ← liftM ((ambient + inputSpec).query (.inl 0))
    return (do
      let _ ← liftM ((ambient + OracleSpec.ofPFunctor firstAccess).query (.inl 5))
      let sent : Nat ← liftM
        ((ambient + OracleSpec.ofPFunctor firstAccess).query (.inr (.inr ())))
      return (do
        let _ ← liftM ((ambient + OracleSpec.ofPFunctor firstAccess).query (.inl 2))
        let old : Nat ← liftM
          ((ambient + OracleSpec.ofPFunctor firstAccess).query (.inr (.inl ())))
        let challenge := old + sent
        return ⟨challenge, pure (terminal announced challenge)⟩))

/-- The prover retains the unobservable coordinate as private output. -/
def prover (hidden : Nat) : Prover.Strategy ambient protocol.tree protocol.roles
    (fun _ => Nat × Nat) :=
  pure ⟨true, do
    let _ ← liftM (ambient.query 1)
    return ⟨(11, hidden), fun (challenge : Nat) => pure <| do
      let _ ← liftM (ambient.query 4)
      return ⟨(challenge + 1, 99), (777, hidden)⟩⟩⟩

/-- The actual statement/witness package, not a separate example-specific runner. -/
def reduction : Oracle.Reduction ambient protocol inputSpec.toPFunctor Unit Nat
    (fun _ => Nat × Nat) (fun _ => Nat) where
  prover := fun _ hidden => pure (prover hidden)
  verifier := fun _ => verifier

/-- Record each ambient query exactly when it executes. -/
def logImpl : QueryImpl ambient (StateM (List Nat)) := fun tag => do
  let log ← get
  set (log ++ [tag])
  return tag

/-- Run the exported reduction under the noncommutative logger. -/
def observed (hidden : Nat) :=
  (simulateQ logImpl (reduction.execute inputImpl () hidden)).run []

/-- The challenge is 7 + 11; the last oracle answer is 19; terminal output is 19 + 18. -/
example (hidden : Nat) : (observed hidden).1.2.2 = 37 := rfl

/-- Public-receive, oracle-receive, challenge, and terminal effects keep their exact order. -/
example (hidden : Nat) : (observed hidden).2 = [0, 1, 5, 2, 4, 3] := rfl

/-- Private prover output survives unchanged and is not forced to equal verifier output. -/
example (hidden : Nat) : (observed hidden).1.2.1 = (777, hidden) := rfl

/-- Only public choices, not the pair payloads, occur in the projected public result. -/
example (hidden : Nat) :
    (publicResult (tree := protocol.tree) (OutP := fun _ => Nat × Nat)
      (OutV := fun _ => Nat) (observed hidden).1).1 =
      ⟨true, PUnit.unit, 18, PUnit.unit, PUnit.unit⟩ :=
  rfl

/-- Normalize one public result before comparing two executions. -/
theorem publicResult_eq (hidden : Nat) :
    publicResult (tree := protocol.tree) (OutP := fun _ => Nat × Nat)
      (OutV := fun _ => Nat) (observed hidden).1 =
      ⟨⟨true, PUnit.unit, 18, PUnit.unit, PUnit.unit⟩, 37⟩ := rfl

/-- Hidden representation data can vary without changing this client's public result. -/
example (hidden₁ hidden₂ : Nat) :
    publicResult (tree := protocol.tree) (OutP := fun _ => Nat × Nat)
      (OutV := fun _ => Nat) (observed hidden₁).1 =
    publicResult (tree := protocol.tree) (OutP := fun _ => Nat × Nat)
      (OutV := fun _ => Nat) (observed hidden₂).1 := by
  rw [publicResult_eq, publicResult_eq]

/-- A one-oracle tree used to test opacity without a preceding public node. -/
abbrev opaqueProtocol : Oracle.Protocol :=
  .oracleWith (Nat × Nat) firstInterface .done

/-- The oracle-node authoring type does not accept a function receiving its opaque payload. -/
example : True := by
  fail_if_success
    have _ : Verifier.Strategy ambient opaqueProtocol.tree opaqueProtocol.roles
        opaqueProtocol.oracles inputSpec.toPFunctor (fun _ => Nat) :=
      fun (message : Nat × Nat) => pure message.2
  trivial

/-- Its positive counterpart queries only the observable coordinate after the oracle receive. -/
example : Verifier.Strategy ambient opaqueProtocol.tree opaqueProtocol.roles
    opaqueProtocol.oracles inputSpec.toPFunctor (fun _ => Nat) := by
  change OracleComp (ambient + OracleSpec.ofPFunctor firstAccess)
    (OracleComp (ambient + OracleSpec.ofPFunctor firstAccess) Nat)
  exact do
    let answer : Nat ← liftM
      ((ambient + OracleSpec.ofPFunctor firstAccess).query (.inr (.inr ())))
    return pure answer

/-- The receiver node cannot prematurely run a query requiring the second oracle. -/
example : True := by
  fail_if_success
    have _ : OracleComp (ambient + OracleSpec.ofPFunctor firstAccess) Nat := terminal true 18
  trivial

/-- The public open-program erasure equation applies to the very strategies tested above. -/
example (hidden : Nat) :
    executeStrategies ambient protocol.tree protocol.roles protocol.oracles inputSpec.toPFunctor
      inputImpl (prover hidden) verifier = (do
        let result ← TwoParty.run protocol.tree.toTypeTree
          (TypeTree.RoleDecoration.toTypeTreeRoles protocol.tree protocol.roles) (prover hidden)
          (Verifier.toCounterpart ambient protocol.tree protocol.roles protocol.oracles
            inputSpec.toPFunctor inputImpl (fun _ => Nat) verifier)
        let out ← result.2.2
        return ⟨TypeTree.ExecutionPath.ofTypeTreePath result.1, result.2.1, out⟩) :=
  executeStrategies_eq_run ambient protocol.tree protocol.roles protocol.oracles
    inputSpec.toPFunctor inputImpl (prover hidden) verifier

/-! Kernel dependency reports for the public structural and execution laws. The build and
zero-warning gates must pass before these reports are interpreted as validation evidence. -/

#print axioms Interaction.Oracle.TypeTree.accessAt_comp
#print axioms Interaction.Oracle.TypeTree.AccessDecoration.restrict_build
#print axioms Interaction.Oracle.Verifier.decorate_access
#print axioms Interaction.Oracle.Verifier.toCounterpart_oracle_eq_of_answer_eq
#print axioms Interaction.Oracle.executeStrategies_eq_run
#print axioms Interaction.Oracle.Reduction.execute

end Interaction.Oracle.ExecutionExample


namespace Interaction.Oracle.ExecutionExample.Append

open OracleComp OracleSpec TwoParty
open PFunctor.FreeM.Displayed (Decoration)

/-- The prefix sends one oracle, then publicly challenges or aborts. -/
abbrev firstProtocol : Oracle.Protocol :=
  .oracleWith (Nat × Nat) firstInterface <|
    .public .receiver (Option Nat) fun _ => .done

/-- Only the successful public branch has a second oracle send. -/
def secondProtocol (path : firstProtocol.tree.BranchPath) : Oracle.Protocol :=
  match path.2.1 with
  | none => .done
  | some _ => .oracleWith (Nat × Nat) firstInterface .done

abbrev combined : Oracle.Protocol :=
  ⟨PFunctor.FreeM.append firstProtocol.tree (fun path => (secondProtocol path).tree),
    Decoration.append firstProtocol.roles (fun path => (secondProtocol path).roles),
    Decoration.append firstProtocol.oracles (fun path => (secondProtocol path).oracles)⟩

/-- The leaf returns the observed answer directly, without a pending terminal action. -/
def firstVerifier (proceed : Bool) : Verifier.Fragment ambient firstProtocol.tree
    firstProtocol.roles firstProtocol.oracles inputSpec.toPFunctor (fun _ => Nat) := by
  change OracleComp (ambient + OracleSpec.ofPFunctor firstAccess)
    (OracleComp (ambient + OracleSpec.ofPFunctor firstAccess) ((choice : Option Nat) × Nat))
  exact do
    let _ ← liftM ((ambient + OracleSpec.ofPFunctor firstAccess).query (.inl 11))
    let sent : Nat ← liftM
      ((ambient + OracleSpec.ofPFunctor firstAccess).query (.inr (.inr ())))
    return do
      let _ ← liftM ((ambient + OracleSpec.ofPFunctor firstAccess).query (.inl 12))
      let old : Nat ← liftM
        ((ambient + OracleSpec.ofPFunctor firstAccess).query (.inr (.inl ())))
      return ⟨if proceed then some (old + sent) else none, sent⟩

/-- Both branches finish once. The successful branch checks its new oracle before finishing. -/
def secondVerifier (path : firstProtocol.tree.BranchPath) (mid : Nat) :
    Verifier.Strategy ambient (secondProtocol path).tree (secondProtocol path).roles
      (secondProtocol path).oracles
      (TypeTree.accessAfter firstProtocol.tree firstProtocol.oracles inputSpec.toPFunctor path)
      (fun _ => Option Nat) := by
  rcases path with ⟨_, choice, _⟩
  cases choice with
  | none =>
      change OracleComp (ambient + OracleSpec.ofPFunctor firstAccess) (Option Nat)
      exact do
        let _ ← liftM ((ambient + OracleSpec.ofPFunctor firstAccess).query (.inl 17))
        return none
  | some challenge =>
      change OracleComp (ambient + OracleSpec.ofPFunctor finalAccess)
        (OracleComp (ambient + OracleSpec.ofPFunctor finalAccess) (Option Nat))
      exact do
        let _ ← liftM ((ambient + OracleSpec.ofPFunctor finalAccess).query (.inl 16))
        return do
          let _ ← liftM ((ambient + OracleSpec.ofPFunctor finalAccess).query (.inl 17))
          let latest : Nat ← liftM
            ((ambient + OracleSpec.ofPFunctor finalAccess).query (.inr (.inr ())))
          return some (latest + mid)

/-- The combined verifier is built using the public composition API. -/
def verifier (proceed : Bool) : Verifier.Strategy ambient combined.tree combined.roles
    combined.oracles inputSpec.toPFunctor (fun _ => Option Nat) :=
  Verifier.append ambient firstProtocol.tree (fun path => (secondProtocol path).tree)
    firstProtocol.roles (fun path => (secondProtocol path).roles)
    firstProtocol.oracles (fun path => (secondProtocol path).oracles)
    inputSpec.toPFunctor (fun _ => Nat) (fun _ => Option Nat)
    (firstVerifier proceed) secondVerifier

/-- The challenge response updates private memory before handing back the actual suffix strategy.
Abort still runs that response; it omits only the subsequent send. -/
def prover (hidden : Nat) : Prover.Strategy ambient combined.tree combined.roles
    (fun _ => Nat) := by
  refine do
    let _ ← liftM (ambient.query 10)
    return ⟨(11, hidden), ?_⟩
  intro choice
  cases choice with
  | none => exact do
      let response ← liftM (ambient.query 14)
      return hidden + response
  | some challenge => exact do
      let response ← liftM (ambient.query 14)
      return do
        let _ ← liftM (ambient.query 15)
        return ⟨(challenge + 1, hidden + response), hidden + response⟩

/- Ordinary-import elaboration check: the exported split law accepts this whole prover,
publicly selected suffix family, and restricted verifiers without a prover wrapper. -/
#check executeStrategies_append ambient firstProtocol.tree (fun path => (secondProtocol path).tree)
  firstProtocol.roles (fun path => (secondProtocol path).roles)
  firstProtocol.oracles (fun path => (secondProtocol path).oracles)
  inputSpec.toPFunctor inputImpl (fun _ => Nat) (fun _ => Nat) (fun _ => Option Nat)
  (prover 5) (firstVerifier true) secondVerifier

#print axioms executeStrategies_append

def observed (proceed : Bool) (hidden : Nat) :=
  (simulateQ logImpl (executeStrategies ambient combined.tree combined.roles combined.oracles
    inputSpec.toPFunctor inputImpl (prover hidden) (verifier proceed))).run []

/-- The suffix uses both the prefix value 11 and its newly sent answer 19. -/
example (hidden : Nat) : (observed true hidden).1.2.2 = some 30 := rfl

/-- Prover response, suffix send, suffix check, and final action retain this exact order. -/
example (hidden : Nat) : (observed true hidden).2 = [10, 11, 12, 14, 15, 16, 17] := rfl

/-- The returned private state includes the ambient answer read after the public challenge. -/
example (hidden : Nat) : (observed true hidden).1.2.1 = hidden + 14 := rfl

example (hidden : Nat) : (observed false hidden).1.2.2 = none := rfl

/-- Public abort preserves the prover's response and runs the one final action. -/
example (hidden : Nat) : (observed false hidden).2 = [10, 11, 12, 14, 17] := rfl

example (hidden : Nat) : (observed false hidden).1.2.1 = hidden + 14 := rfl

/-! A completed prefix can have a terminal effect. Moving it after the next prover send changes
execution, even when both fragments have the same final values. This tests the boundary restriction.
The moved version also exercises append with an empty prefix. -/

private def completedFirst : Verifier.Strategy ambient TypeTree.done PUnit.unit PUnit.unit
    inputSpec.toPFunctor (fun _ => Unit) := by
  change OracleComp (ambient + inputSpec) Unit
  exact do
    let _ ← liftM ((ambient + inputSpec).query (.inl 40))
    return ()

private def nextProver : Prover.Strategy ambient opaqueProtocol.tree opaqueProtocol.roles
    (fun _ => Unit) := do
  let _ ← liftM (ambient.query 41)
  return ⟨(11, 0), ()⟩

private def quietVerifier : Verifier.Strategy ambient opaqueProtocol.tree opaqueProtocol.roles
    opaqueProtocol.oracles inputSpec.toPFunctor (fun _ => Unit) := pure (pure ())

private def afterReceive : Verifier.Strategy ambient opaqueProtocol.tree opaqueProtocol.roles
    opaqueProtocol.oracles inputSpec.toPFunctor (fun _ => Unit) := by
  change OracleComp (ambient + OracleSpec.ofPFunctor firstAccess)
    (OracleComp (ambient + OracleSpec.ofPFunctor firstAccess) Unit)
  exact do
    let _ ← liftM ((ambient + OracleSpec.ofPFunctor firstAccess).query (.inl 40))
    return pure ()

private def movedVerifier : Verifier.Strategy ambient opaqueProtocol.tree opaqueProtocol.roles
    opaqueProtocol.oracles inputSpec.toPFunctor (fun _ => Unit) :=
  Verifier.append ambient TypeTree.done (fun _ => opaqueProtocol.tree)
    PUnit.unit (fun _ => opaqueProtocol.roles) PUnit.unit (fun _ => opaqueProtocol.oracles)
    inputSpec.toPFunctor (fun _ => Unit) (fun _ => Unit) () (fun _ _ => afterReceive)

private def completedThen : OracleComp ambient Unit := do
  let _ ← executeStrategies ambient TypeTree.done PUnit.unit PUnit.unit inputSpec.toPFunctor
    inputImpl (OutP := fun _ => Unit) () completedFirst
  let _ ← executeStrategies ambient opaqueProtocol.tree opaqueProtocol.roles opaqueProtocol.oracles
    inputSpec.toPFunctor inputImpl nextProver quietVerifier
  return ()

private def movedThen : OracleComp ambient Unit := do
  let _ ← executeStrategies ambient opaqueProtocol.tree opaqueProtocol.roles opaqueProtocol.oracles
    inputSpec.toPFunctor inputImpl nextProver movedVerifier
  return ()

example : ((simulateQ logImpl completedThen).run []).2 = [40, 41] := rfl

example : ((simulateQ logImpl movedThen).run []).2 = [41, 40] := rfl

/-- Equality after arbitrary effect reordering would contradict these actual execution logs. -/
example : ((simulateQ logImpl completedThen).run []).2 ≠
    ((simulateQ logImpl movedThen).run []).2 := by
  change [40, 41] ≠ [41, 40]
  decide

/-! A verifier-owned first suffix move follows the prefix and precedes the prover response. -/

private abbrev firstPublic : Oracle.Protocol := .public .sender Unit fun _ => .done
private abbrev secondPublic : Oracle.Protocol := .public .receiver Nat fun _ => .done

private abbrev combinedPublic : Oracle.Protocol :=
  ⟨PFunctor.FreeM.append firstPublic.tree (fun _ => secondPublic.tree),
    Decoration.append firstPublic.roles (fun _ => secondPublic.roles),
    Decoration.append firstPublic.oracles (fun _ => secondPublic.oracles)⟩

private def firstPublicVerifier : Verifier.Fragment ambient firstPublic.tree firstPublic.roles
    firstPublic.oracles inputSpec.toPFunctor (fun _ => Nat) := by
  change Unit → OracleComp (ambient + inputSpec) Nat
  exact fun _ => do
    let _ ← liftM ((ambient + inputSpec).query (.inl 49))
    return 9

private def secondPublicVerifier (path : firstPublic.tree.BranchPath) (mid : Nat) :
    Verifier.Strategy ambient secondPublic.tree secondPublic.roles secondPublic.oracles
      (TypeTree.accessAfter firstPublic.tree firstPublic.oracles inputSpec.toPFunctor path)
      (fun _ => Nat) := by
  change OracleComp (ambient + inputSpec) ((challenge : Nat) × OracleComp (ambient + inputSpec) Nat)
  exact do
    let answer : Nat ← liftM ((ambient + inputSpec).query (.inl 50))
    return ⟨answer + mid, do
      let _ ← liftM ((ambient + inputSpec).query (.inl 52))
      return answer + mid⟩

private def publicProver (hidden : Nat) : Prover.Strategy ambient combinedPublic.tree
    combinedPublic.roles (fun _ => Nat) := by
  change OracleComp ambient ((choice : Unit) × (Nat → OracleComp ambient Nat))
  exact do
    let _ ← liftM (ambient.query 48)
    return ⟨(), fun challenge => do
      let response : Nat ← liftM (ambient.query 51)
      return hidden + challenge + response⟩

private def observedPublic (hidden : Nat) :=
  (simulateQ logImpl (executeStrategies ambient combinedPublic.tree combinedPublic.roles
    combinedPublic.oracles inputSpec.toPFunctor inputImpl (publicProver hidden)
    (Verifier.append ambient firstPublic.tree (fun _ => secondPublic.tree)
      firstPublic.roles (fun _ => secondPublic.roles) firstPublic.oracles
      (fun _ => secondPublic.oracles) inputSpec.toPFunctor (fun _ => Nat) (fun _ => Nat)
      firstPublicVerifier secondPublicVerifier))).run []

example (hidden : Nat) : (observedPublic hidden).2 = [48, 49, 50, 51, 52] := rfl

example (hidden : Nat) : (observedPublic hidden).1.2.1 = hidden + 59 + 51 := rfl

example (hidden : Nat) : (observedPublic hidden).1.2.2 = 59 := rfl

end Interaction.Oracle.ExecutionExample.Append
