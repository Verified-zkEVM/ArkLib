/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.SourceRouting
import ArkLib.Interaction.Oracle.CoreRun

/-!
# Exported-interface execution client

The prefix exports the sum of one input answer and its freshly sent oracle. It hides another
input slot. The suffix sees only that exported interface and its own newly received oracle.
Actual execution preserves private prover memory, ambient effect order, and the final closed claim.
-/

namespace Interaction.Oracle.SourceRoutingExample

open OracleComp OracleSpec TwoParty
open PFunctor.FreeM.Displayed (Decoration)

abbrev ambient : OracleSpec Nat := Nat →ₒ Nat
abbrev inputSpec : OracleSpec (Fin 2) := Fin 2 →ₒ Nat

/-- The second input is deliberately absent from the exported query program. -/
def inputImpl (hidden : Nat) : QueryImpl inputSpec Id :=
  fun q => if q = 0 then 7 else hidden

/-- Only the first coordinate of a sent pair is queryable. -/
@[reducible]
def firstInterface : OracleInterface (Nat × Nat) where
  Query := Unit
  toOC.spec := Unit →ₒ Nat
  toOC.impl _ := do return (← read).1

abbrev family : OracleFamily Unit (fun _ => Nat × Nat) := ⟨fun _ => firstInterface⟩
abbrev firstProtocol : Protocol := .oracleWith (Nat × Nat) firstInterface .done
abbrev secondProtocol : Protocol :=
  .oracleWith (Nat × Nat) firstInterface (.public .receiver Nat fun _ => .done)

abbrev combined : Protocol :=
  ⟨PFunctor.FreeM.append firstProtocol.tree (fun _ => secondProtocol.tree),
    Decoration.append firstProtocol.roles (fun _ => secondProtocol.roles),
    Decoration.append firstProtocol.oracles (fun _ => secondProtocol.oracles)⟩

abbrev prefixAccess : PFunctor := Access.extend inputSpec.toPFunctor firstInterface
abbrev suffixAccess : PFunctor := Access.extend family.spec.toPFunctor firstInterface

/-- One exported query expands into two source queries, omitting the hidden input slot. -/
def exportView : VirtualOracle (ofPFunctor prefixAccess) family := ⟨fun _ => do
  let old : Nat ← liftM ((ofPFunctor prefixAccess).query (.inl (0 : Fin 2)))
  let sent : Nat ← liftM ((ofPFunctor prefixAccess).query (.inr ()))
  return old + sent⟩

/-- The suffix's final view combines its exported input with its own oracle message. -/
def finalView : VirtualOracle (ofPFunctor suffixAccess) family := ⟨fun _ => do
  let old : Nat ← liftM ((ofPFunctor suffixAccess).query (.inl ⟨(), ()⟩))
  let sent : Nat ← liftM ((ofPFunctor suffixAccess).query (.inr ()))
  return old + sent⟩

/-- A value boundary exports query programs, without running a terminal action. -/
def firstVerifier : Verifier.Fragment ambient firstProtocol.tree firstProtocol.roles
    firstProtocol.oracles inputSpec.toPFunctor (fun p =>
      OpenClaim (ofPFunctor (TypeTree.accessAfter firstProtocol.tree firstProtocol.oracles
        inputSpec.toPFunctor p)) Unit family) := by
  change OracleComp (ambient + ofPFunctor prefixAccess)
    (OpenClaim (ofPFunctor prefixAccess) Unit family)
  exact do
    let _ ← liftM ((ambient + ofPFunctor prefixAccess).query (.inl 10))
    return ⟨(), exportView⟩

/-- The suffix receives only a statement and the exported interface, not the raw prefix handler. -/
def secondVerifier (_ : firstProtocol.tree.BranchPath) (_ : Unit) :
    Verifier.Strategy ambient secondProtocol.tree secondProtocol.roles secondProtocol.oracles
      family.spec.toPFunctor (fun p => Option (OpenClaim
        (ofPFunctor (TypeTree.accessAfter secondProtocol.tree secondProtocol.oracles
          family.spec.toPFunctor p)) Nat family)) := by
  change OracleComp (ambient + ofPFunctor suffixAccess)
    (OracleComp (ambient + ofPFunctor suffixAccess)
      ((challenge : Nat) × OracleComp (ambient + ofPFunctor suffixAccess)
        (Option (OpenClaim (ofPFunctor suffixAccess) Nat family))))
  exact do
    let _ ← liftM ((ambient + ofPFunctor suffixAccess).query (.inl 30))
    let exported : Nat ← liftM
      ((ambient + ofPFunctor suffixAccess).query (.inr (.inl ⟨(), ()⟩)))
    let fresh : Nat ← liftM ((ambient + ofPFunctor suffixAccess).query (.inr (.inr ())))
    return do
      let _ ← liftM ((ambient + ofPFunctor suffixAccess).query (.inl 40))
      let challenge := exported + fresh
      return ⟨challenge, do
        let _ ← liftM ((ambient + ofPFunctor suffixAccess).query (.inl 60))
        return some ⟨challenge, finalView⟩⟩

def verifier : Verifier.Strategy ambient combined.tree combined.roles combined.oracles
    inputSpec.toPFunctor (TerminalClaim combined inputSpec.toPFunctor
      (fun _ => Nat) (fun _ => family)) :=
  Verifier.appendExported ambient firstProtocol.tree (fun _ => secondProtocol.tree)
    firstProtocol.roles (fun _ => secondProtocol.roles)
    firstProtocol.oracles (fun _ => secondProtocol.oracles) inputSpec.toPFunctor
    (fun _ => Unit) (fun _ _ => Nat × Nat) (fun _ => family)
    (fun _ => Nat) (fun _ _ => Nat × Nat) (fun _ => family)
    firstVerifier secondVerifier

/-- Ordinary continuations retain private data and perform effects on both sides of the join. -/
def prover (secret : Nat) :
    Prover.Strategy ambient combined.tree combined.roles (fun _ => Nat) := by
  change OracleComp ambient ((first : Nat × Nat) × OracleComp ambient
    ((second : Nat × Nat) × (Nat → OracleComp ambient Nat)))
  exact do
    let _ ← liftM (ambient.query 1)
    return ⟨(11, secret), do
      let _ ← liftM (ambient.query 20)
      return ⟨(5, secret), fun challenge => do
        let answer : Nat ← liftM (ambient.query 50)
        return secret + challenge + answer⟩⟩

/-- Ambient answers also record the complete operation order. -/
def logImpl : QueryImpl ambient (StateM (List Nat)) := fun tag => do
  let history ← get
  set (history ++ [tag])
  return tag

/-- Close the returned claim with the input and messages from the actual composed run. -/
def observed (hidden secret : Nat) :=
  (simulateQ logImpl ((fun result =>
    (⟨result.1, result.2.1, result.2.2.map (fun claim => claim.closeWith
      (result.1.closingImpl combined.oracles inputSpec.toPFunctor (inputImpl hidden)))⟩ :
      (_ : combined.tree.ExecutionPath) × Nat × Option (ClosedClaim Nat family))) <$>
    executeStrategies ambient combined.tree combined.roles combined.oracles inputSpec.toPFunctor
      (inputImpl hidden) (prover secret) verifier)).run []

/-- Observe the private output, closed statement/answer, and ambient history together. -/
def resultSummary (hidden secret : Nat) : Nat × Option (Nat × Nat) × List Nat :=
  let result := observed hidden secret
  (result.1.2.1,
    result.1.2.2.map (fun claim => (claim.stmt, claim.oracles ⟨(), ()⟩)), result.2)

/-- Actual composition yields 7 + 11 + 5, retains private state, and finishes exactly once.
The omitted initial slot and hidden coordinates remain arbitrary. -/
example (hidden secret : Nat) : resultSummary hidden secret =
    (secret + 23 + 50, some (23, 23), [1, 10, 20, 30, 40, 50, 60]) := by
  unfold resultSummary observed verifier
  rw [executeStrategies_appendExported_close ambient firstProtocol.tree
    (fun _ => secondProtocol.tree) firstProtocol.roles (fun _ => secondProtocol.roles)
    firstProtocol.oracles (fun _ => secondProtocol.oracles) inputSpec.toPFunctor (inputImpl hidden)
    (fun _ => Unit) (fun _ _ => Nat × Nat) (fun _ => family)
    (fun _ => Nat) (fun _ _ => Nat × Nat) (fun _ => family)
    (fun _ => Nat) (prover secret) firstVerifier secondVerifier]
  rfl

/-- Log the raw source calls of one exported query. -/
def sourceLogImpl (hidden secret : Nat) :
    QueryImpl (ofPFunctor prefixAccess) (StateM (List Nat)) := fun q => do
  let history ← get
  let label := match q with
    | .inl i => i.val
    | .inr _ => 2
  set (history ++ [label])
  return Access.extendImpl inputSpec.toPFunctor firstInterface (inputImpl hidden) (11, secret) q

/-- A single exported query makes two raw queries; it never touches hidden source slot 1. -/
example (hidden secret : Nat) :
    (simulateQ (sourceLogImpl hidden secret) (exportView.query ⟨(), ()⟩)).run [] =
      ((18 : Nat), [0, 2]) := rfl

/- The exported theorem accepts the ordinary whole prover and these actual source resources. -/
#check executeStrategies_appendExported_close ambient firstProtocol.tree
  (fun _ => secondProtocol.tree) firstProtocol.roles (fun _ => secondProtocol.roles)
  firstProtocol.oracles (fun _ => secondProtocol.oracles) inputSpec.toPFunctor (inputImpl 99)
  (fun _ => Unit) (fun _ _ => Nat × Nat) (fun _ => family)
  (fun _ => Nat) (fun _ _ => Nat × Nat) (fun _ => family)
  (fun _ => Nat) (prover 42) firstVerifier secondVerifier

#print axioms executeStrategies_appendExported_close

end Interaction.Oracle.SourceRoutingExample
