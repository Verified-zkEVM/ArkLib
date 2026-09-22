/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Access

/-!
# Accumulated-access acceptance client

Public branches select different message types. Rejection tests attempt unavailable queries, with
positive counterparts after the send. Terminal access, cursor composition, repeated signatures,
and a non-faithful oracle interface exercise the semantic boundaries, not just tuple projections.
-/

namespace Interaction.Oracle.TypeTree.AccessExample

open OracleComp OracleSpec

/-- One input resource available from the start. -/
abbrev baseSpec : OracleSpec Unit := Unit →ₒ Nat

/-- Input behavior is supplied directly, not assumed to come from an honest representation. -/
def baseImpl : QueryImpl baseSpec Id := fun _ => 7

/-- A public choice changes the next oracle message type. -/
def accessTree : Oracle.TypeTree :=
  .public Bool fun
    | false => .oracle Bool fun _ => .public (Fin 2) fun _ => .done
    | true => .oracle (Fin 3) fun _ => .public Bool fun _ => .done

/-- Explicit interfaces for the branch-dependent messages. -/
def accessOracles : accessTree.OracleDecoration :=
  ⟨PUnit.unit, fun
    | false => ⟨OracleInterface.instDefault, fun _ => ⟨PUnit.unit, fun _ => ⟨⟩⟩⟩
    | true => ⟨OracleInterface.instDefault, fun _ => ⟨PUnit.unit, fun _ => ⟨⟩⟩⟩⟩

/-- The derived presentation of access before each node. -/
def access : accessTree.AccessDecoration :=
  AccessDecoration.build accessTree accessOracles baseSpec

example : (access.2 false).1.A = Unit := rfl

example : (access.2 true).1.A = Unit := rfl

/-- This actually attempts to type a query for the unsent message. -/
example : True := by
  fail_if_success
    have _ : (access.2 false).1.A := Sum.inr ()
  trivial

/-- The identical query constructor is accepted after the send. -/
example : ((access.2 false).2 PUnit.unit).1.A := Sum.inr ()

example : ((access.2 false).2 PUnit.unit).1.B (.inr ()) = Bool := rfl

example : ((access.2 true).2 PUnit.unit).1.B (.inr ()) = Fin 3 := rfl

/-- Cursor stopping after the false-branch oracle send. -/
def afterSend : PFunctor.FreeM.Cursor accessTree :=
  .down false (.down PUnit.unit
    (.root (Oracle.TypeTree.public (Fin 2) fun _ => Oracle.TypeTree.done)))

example : (accessAt afterSend accessOracles baseSpec.toPFunctor).A = (Unit ⊕ Unit) := rfl

/-- The public future can be selected without any concrete Boolean oracle payload. -/
example : AccessDecoration.restrict afterSend access =
    AccessDecoration.build afterSend.residual
      (OracleDecoration.restrict afterSend accessOracles)
      (OracleSpec.ofPFunctor (accessAt afterSend accessOracles baseSpec.toPFunctor)) :=
  AccessDecoration.restrict_build afterSend accessOracles baseSpec.toPFunctor

/-- Distinct oracle payloads leave the structural projection unchanged. -/
def leftPath : ExecutionPath accessTree := ⟨false, false, (0 : Fin 2), PUnit.unit⟩

/-- Same public choices, different concrete oracle payload. -/
def rightPath : ExecutionPath accessTree := ⟨false, true, (0 : Fin 2), PUnit.unit⟩

example : leftPath ≠ rightPath := by
  intro h
  have impossible : false = true := congrArg
    (fun p : ExecutionPath accessTree => match p with
      | ⟨false, message, _⟩ => message
      | ⟨true, _, _⟩ => false) h
  cases impossible

example : accessAfter accessTree accessOracles baseSpec.toPFunctor leftPath.toBranchPath =
    accessAfter accessTree accessOracles baseSpec.toPFunctor rightPath.toBranchPath :=
  accessAfter_eq_of_toBranchPath_eq accessOracles baseSpec.toPFunctor rfl

/-- A deliberately non-faithful interface: only the first coordinate is observable. -/
@[reducible]
def firstInterface : OracleInterface (Nat × Nat) where
  Query := Unit
  toOC.spec := Unit →ₒ Nat
  toOC.impl _ := do return (← read).1

/-- A send immediately followed by a terminal leaf. -/
def terminalTree : Oracle.TypeTree := .oracle (Nat × Nat) fun _ => .done

/-- Oracle decoration for the terminal-send regression. -/
def terminalOracles : terminalTree.OracleDecoration :=
  ⟨firstInterface, fun _ => ⟨⟩⟩

/-- Complete cursor; node decorations alone have only unit at this residual. -/
def terminalCursor : PFunctor.FreeM.Cursor terminalTree :=
  .down PUnit.unit (.root Oracle.TypeTree.done)

example : (accessAt terminalCursor terminalOracles baseSpec.toPFunctor).A = (Unit ⊕ Unit) := rfl

example :
    (accessAt terminalCursor terminalOracles baseSpec.toPFunctor).B (Sum.inr ()) = Nat := rfl

/-- Two same-signature sources are still explicitly routed to different slots. -/
def derivedQuery : OracleComp
    (OracleSpec.ofPFunctor (Access.extend baseSpec.toPFunctor firstInterface)) Nat := do
  let old : Nat ← Access.queryPrior baseSpec.toPFunctor firstInterface ()
  let fresh : Nat ← Access.queryLatest baseSpec.toPFunctor firstInterface ()
  return old + fresh

example : simulateQ
    (Access.extendImpl baseSpec.toPFunctor firstInterface baseImpl (11, 42)) derivedQuery = 18 :=
  rfl

/-- Hidden representation data do not leak through the handler. -/
example (visible hidden₁ hidden₂ : Nat) :
    Access.extendImpl baseSpec.toPFunctor firstInterface baseImpl (visible, hidden₁) =
      Access.extendImpl baseSpec.toPFunctor firstInterface baseImpl (visible, hidden₂) := by
  funext q
  cases q <;> rfl

/-- A second oracle is not available after only the first send. -/
example : True := by
  fail_if_success
    have _ : OracleComp
        (OracleSpec.ofPFunctor (Access.extend baseSpec.toPFunctor firstInterface)) Nat :=
      Access.queryLatest (Access.extend baseSpec.toPFunctor firstInterface) firstInterface ()
  trivial

/-- The same second-slot query is well typed after the second extension. -/
example : OracleComp
    (OracleSpec.ofPFunctor
      (Access.extend (Access.extend baseSpec.toPFunctor firstInterface) firstInterface)) Nat :=
  Access.queryLatest (Access.extend baseSpec.toPFunctor firstInterface) firstInterface ()

/-- Message/response universe above the query universe. -/
example (Messages : Type 1) (interface : OracleInterface.{1, 0} Messages)
    (initial : PFunctor.{0, 1}) : PFunctor.{0, 1} :=
  Access.extend initial interface

/-- Query universe above the message/response universe. -/
example (Messages : Type) (interface : OracleInterface.{0, 1} Messages)
    (initial : PFunctor.{1, 0}) : PFunctor.{1, 0} :=
  Access.extend initial interface

end Interaction.Oracle.TypeTree.AccessExample
