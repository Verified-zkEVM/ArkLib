/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Execution

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
def protocol : Oracle.Protocol :=
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
    inputSpec.toPFunctor (fun _ => Nat) :=
  fun announced => do
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
    return ⟨(11, hidden), fun challenge => pure <| do
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
    (publicResult (observed hidden).1).1 =
      ⟨true, PUnit.unit, 18, PUnit.unit, PUnit.unit⟩ :=
  rfl

/-- Hidden representation data can vary without changing this client's public result. -/
example (hidden₁ hidden₂ : Nat) :
    publicResult (observed hidden₁).1 = publicResult (observed hidden₂).1 := rfl

/-- A one-oracle tree used to test opacity without a preceding public node. -/
def opaqueProtocol : Oracle.Protocol :=
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
    opaqueProtocol.oracles inputSpec.toPFunctor (fun _ => Nat) :=
  do
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

end Interaction.Oracle.ExecutionExample
