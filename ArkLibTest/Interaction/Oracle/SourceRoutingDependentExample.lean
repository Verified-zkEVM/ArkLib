/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.SourceRouting
import ArkLib.Interaction.Oracle.CoreRun

/-!
# Public branches may change the final claim type

A suffix queries its exported input and announces whether the answer is zero. That public choice
changes both the final statement type and the realization type of the final oracle family.
-/

namespace Interaction.Oracle.SourceRoutingDependentExample

open OracleComp OracleSpec TwoParty
open PFunctor.FreeM.Displayed (Decoration)

abbrev ambient : OracleSpec Empty := Empty →ₒ Nat
abbrev inputSpec : OracleSpec Unit := Unit →ₒ Nat

@[reducible]
def natInterface : OracleInterface Nat where
  Query := Unit
  toOC.spec := Unit →ₒ Nat
  toOC.impl _ := read

@[reducible]
def pairInterface : OracleInterface (Nat × Nat) where
  Query := Unit
  toOC.spec := Unit →ₒ Nat
  toOC.impl _ := do return (← read).1

abbrev inputFamily : OracleFamily Unit (fun _ => Nat) := ⟨fun _ => natInterface⟩
abbrev firstProtocol : Protocol := .done
abbrev suffix : Protocol := .public .receiver Bool fun _ => .done

abbrev combined : Protocol :=
  ⟨PFunctor.FreeM.append firstProtocol.tree (fun _ => suffix.tree),
    Decoration.append firstProtocol.roles (fun _ => suffix.roles),
    Decoration.append firstProtocol.oracles (fun _ => suffix.oracles)⟩

def finalStmt (p : combined.tree.BranchPath) : Type :=
  if p.1 then Unit else Nat

def finalData (p : combined.tree.BranchPath) (_ : Unit) : Type :=
  if p.1 then Nat else Nat × Nat

def finalFamily (p : combined.tree.BranchPath) : OracleFamily Unit (finalData p) := by
  match h : p.1 with
  | true => exact ⟨fun _ => by simpa [finalData, h] using natInterface⟩
  | false => exact ⟨fun _ => by simpa [finalData, h] using pairInterface⟩

/-- The prefix exports its input through the declared interface. -/
def firstVerifier : Verifier.Fragment ambient firstProtocol.tree firstProtocol.roles
    firstProtocol.oracles inputSpec.toPFunctor (fun _ =>
      OpenClaim inputSpec Unit inputFamily) :=
  ⟨(), ⟨fun _ => liftM (inputSpec.query ())⟩⟩

/-- The public Boolean selects two different final claim types. -/
def secondVerifier (_ : firstProtocol.tree.BranchPath) (_ : Unit) :
    Verifier.Strategy ambient suffix.tree suffix.roles suffix.oracles
      inputFamily.spec.toPFunctor (fun p => Option (OpenClaim inputFamily.spec
        (finalStmt p) (finalFamily p))) := do
  let answer : Nat ← liftM ((ambient + inputFamily.spec).query (.inr ⟨(), ()⟩))
  if answer = 0 then
    return ⟨true, pure (some ⟨(), ⟨fun _ => liftM (inputFamily.spec.query ⟨(), ()⟩)⟩⟩)⟩
  else
    return ⟨false, pure (some ⟨answer, ⟨fun _ => liftM (inputFamily.spec.query ⟨(), ()⟩)⟩⟩)⟩

def verifier : Verifier.Strategy ambient combined.tree combined.roles combined.oracles
    inputSpec.toPFunctor (TerminalClaim combined inputSpec.toPFunctor finalStmt finalFamily) :=
  Verifier.appendExported ambient firstProtocol.tree (fun _ => suffix.tree)
    firstProtocol.roles (fun _ => suffix.roles)
    firstProtocol.oracles (fun _ => suffix.oracles) inputSpec.toPFunctor
    (fun _ => Unit) (fun _ _ => Nat) (fun _ => inputFamily)
    finalStmt finalData finalFamily firstVerifier secondVerifier

/-- The private result depends on the verifier's public choice. -/
def prover : Prover.Strategy ambient combined.tree combined.roles (fun _ => Nat) := by
  change Bool → OracleComp ambient Nat
  exact fun choice => pure (if choice then 13 else 29)

/-- Read an answer through the family selected by the actual public branch. -/
def closedAnswer {p : combined.tree.BranchPath}
    (claim : ClosedClaim (finalStmt p) (finalFamily p)) : Nat := by
  rcases p with ⟨choice, rest⟩
  cases choice <;> exact claim.oracles ⟨(), ()⟩

/-- Unit statements use zero; the other branch retains its natural-number statement. -/
def statementValue {p : combined.tree.BranchPath}
    (claim : ClosedClaim (finalStmt p) (finalFamily p)) : Nat := by
  rcases p with ⟨choice, rest⟩
  cases choice
  · exact claim.stmt
  · exact 0

/-- Retain the actual path and private output, closing with the resources of the same run. -/
def closedExecution (answer : Nat) :=
  (fun result => (⟨result.1, result.2.1, result.2.2.map (fun claim => claim.closeWith
    (result.1.closingImpl combined.oracles inputSpec.toPFunctor (fun _ => answer)))⟩ :
      (path : combined.tree.ExecutionPath) × Nat ×
        Option (ClosedClaim (finalStmt path.toBranchPath) (finalFamily path.toBranchPath)))) <$>
    executeStrategies ambient combined.tree combined.roles combined.oracles inputSpec.toPFunctor
      (fun _ => answer) prover verifier

/-- Observe the public branch, private result, and closed statement and oracle answer. -/
def observed (answer : Nat) : OracleComp ambient (Bool × Nat × Option (Nat × Nat)) :=
  (fun result => (result.1.toBranchPath.1, result.2.1,
    result.2.2.map (fun claim => (statementValue claim, closedAnswer claim)))) <$>
    closedExecution answer

/-- Zero selects a unit statement and a natural-number oracle realization. -/
example : observed 0 = pure (true, 13, some (0, 0)) := by
  unfold observed closedExecution verifier
  rw [executeStrategies_appendExported_close ambient firstProtocol.tree (fun _ => suffix.tree)
    firstProtocol.roles (fun _ => suffix.roles) firstProtocol.oracles (fun _ => suffix.oracles)
    inputSpec.toPFunctor (fun _ => (0 : Nat)) (fun _ => Unit) (fun _ _ => Nat)
    (fun _ => inputFamily) finalStmt finalData finalFamily (fun _ => Nat)
    prover firstVerifier secondVerifier]
  rfl

/-- A nonzero answer selects a natural-number statement and a pair realization. -/
example : observed 7 = pure (false, 29, some (7, 7)) := by
  unfold observed closedExecution verifier
  rw [executeStrategies_appendExported_close ambient firstProtocol.tree (fun _ => suffix.tree)
    firstProtocol.roles (fun _ => suffix.roles) firstProtocol.oracles (fun _ => suffix.oracles)
    inputSpec.toPFunctor (fun _ => (7 : Nat)) (fun _ => Unit) (fun _ _ => Nat)
    (fun _ => inputFamily) finalStmt finalData finalFamily (fun _ => Nat)
    prover firstVerifier secondVerifier]
  rfl

/- The main theorem accepts final statements and oracle families that change with the branch. -/
#check executeStrategies_appendExported_close ambient firstProtocol.tree (fun _ => suffix.tree)
  firstProtocol.roles (fun _ => suffix.roles) firstProtocol.oracles (fun _ => suffix.oracles)
  inputSpec.toPFunctor (fun _ => (7 : Nat)) (fun _ => Unit) (fun _ _ => Nat)
  (fun _ => inputFamily) finalStmt finalData finalFamily (fun _ => Nat)
  prover firstVerifier secondVerifier

end Interaction.Oracle.SourceRoutingDependentExample
