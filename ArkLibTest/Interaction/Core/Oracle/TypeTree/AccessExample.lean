/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.OracleVerifier
import PolyFun.PFunctor.Free.Cursor

/-! Oracle access as typing. A decision on a completed shape path queries the input family and
the oracle family of that path, `pathResources inputs s p`. A public bit selects message
types; an oracle slot exists only on paths that cross its send. Same-signature input and message
slots stay distinct, and a non-faithful interface hides representation data. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle OracleComp OracleSpec

namespace Interaction.Core.AccessExampleTests

/-- One scalar input slot. -/
@[instance_reducible] def inputs : OracleFamily Unit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- The input data: the single slot holds 7. -/
def seven : ∀ _ : Unit, Nat := fun _ => 7

/-- The part of `accessTree` before its oracle send: the public bit. -/
@[instance_reducible] def before : OracleProtocol :=
  .liftBind (.message Bool) (fun _ => .pure ⟨⟩)

/-- The part of `accessTree` after the public bit: a branch-dependent oracle send, then a public
message. -/
@[instance_reducible] def after : Path before → OracleProtocol
  | ⟨false, ⟨⟩⟩ => .liftBind (.oracle Bool OracleInterface.instDefault)
      (fun _ => .liftBind (.message (Fin 2)) (fun _ => .pure ⟨⟩))
  | ⟨true, ⟨⟩⟩ => .liftBind (.oracle (Fin 3) OracleInterface.instDefault)
      (fun _ => .liftBind (.message Bool) (fun _ => .pure ⟨⟩))

/-- A public bit selects the type of the next oracle message. -/
abbrev accessTree : OracleProtocol := before.append after

/-- The `false` branch, with payload `false`. -/
def leftPath : PathAlong oracleSig accessTree := ⟨false, false, (0 : Fin 2), ⟨⟩⟩

/-- The same public choices, with payload `true`. -/
def rightPath : PathAlong oracleSig accessTree := ⟨false, true, (0 : Fin 2), ⟨⟩⟩

/-- The `true` branch, with payload `2 : Fin 3`. -/
def finPath : PathAlong oracleSig accessTree := ⟨true, (2 : Fin 3), false, ⟨⟩⟩

-- AccessExample 1, restated: a decision stopped before the send is a decision on `before`, the
-- prefix of `accessTree`. Its resources are the inputs and the oracles of `before`, which has
-- none on the `false` path.
/-- Before the `false`-branch send there are no oracle slots. -/
example : oracleIdx before ⟨false, ⟨⟩⟩ = PEmpty := rfl

example : IsEmpty (oracleIdx before ⟨false, ⟨⟩⟩) := inferInstanceAs (IsEmpty PEmpty)

-- AccessExample 2, restated as row 1 for the `true` branch.
example : oracleIdx before ⟨true, ⟨⟩⟩ = PEmpty := rfl

example : IsEmpty (oracleIdx before ⟨true, ⟨⟩⟩) := inferInstanceAs (IsEmpty PEmpty)

-- AccessExample 3, restated: a query naming the unsent message does not typecheck in the
-- resources of a decision stopped before the send.
example : True := by
  fail_if_success
    have _ : (pathResources inputs before ⟨false, ⟨⟩⟩).spec.Domain :=
      (.inr ⟨.inl ⟨⟩, ()⟩)
  trivial

-- AccessExample 4, restated: the same query constructor typechecks for a decision on a completed
-- path through the send.
/-- A decision on the completed `false` path can query the sent message. -/
example : (pathResources inputs accessTree
    (projectPathAlong oracleSig accessTree leftPath)).spec.Domain := (.inr ⟨.inl ⟨⟩, ()⟩)

-- AccessExample 5, restated: the response type of the `false`-branch message.
example : (oracles accessTree (projectPathAlong oracleSig accessTree leftPath)).Range
    ⟨.inl ⟨⟩, ()⟩ = Bool := rfl

-- AccessExample 6, restated: the response type of the `true`-branch message.
example : (oracles accessTree (projectPathAlong oracleSig accessTree finPath)).Range
    ⟨.inl ⟨⟩, ()⟩ = Fin 3 := rfl

-- AccessExample 7, restated: after the send, the decision's resource index is the input slot
-- and the one sent slot.
example : (Unit ⊕ oracleIdx accessTree (projectPathAlong oracleSig accessTree leftPath)) =
    (Unit ⊕ (PUnit ⊕ PEmpty)) := rfl

-- AccessExample 8, restated: decoration restriction is retired. The future after the oracle send
-- is selected by a cursor whose oracle edge carries only a unit marker, and the projected shape of
-- that future is independent of the payload (`oracle_payload_shape`).
/-- The public future after the `false`-branch send, selected without a payload. -/
def afterSend : Cursor.Spine accessTree (.liftBind (.message (Fin 2)) (fun _ => .pure ⟨⟩)) :=
  .down false (.down ⟨⟩ (.root _))

example (x y : Bool) (tr : PathAlong oracleSig (.liftBind (.message (Fin 2))
    (fun _ => .pure ⟨⟩) : OracleProtocol)) :
    projectPathAlong oracleSig (after ⟨false, ⟨⟩⟩) ⟨x, tr⟩ =
      projectPathAlong oracleSig (after ⟨false, ⟨⟩⟩) ⟨y, tr⟩ :=
  oracle_payload_shape Bool OracleInterface.instDefault _ x y tr

-- AccessExample 9, restated: execution paths are full transcripts.
/-- Distinct payloads give distinct full transcripts. -/
example : leftPath ≠ rightPath := by
  intro h
  cases h

-- AccessExample 10, restated: equal shape paths give the same oracle family, by `rfl`.
example : projectPathAlong oracleSig accessTree leftPath =
    projectPathAlong oracleSig accessTree rightPath := rfl

example : oracles accessTree (projectPathAlong oracleSig accessTree leftPath) =
    oracles accessTree (projectPathAlong oracleSig accessTree rightPath) := rfl

/-- Only the first coordinate of a sent pair is observable. -/
@[reducible] def firstInterface : OracleInterface (Nat × Nat) where
  Query := Unit
  toOC.spec := fun _ => Nat
  toOC.impl _ := do return (← read).1

/-- One pair send followed by the leaf. -/
@[instance_reducible] def terminalTree : OracleProtocol :=
  .liftBind (.oracle (Nat × Nat) firstInterface) (fun _ => .pure ⟨⟩)

/-- The only shape path of `terminalTree`. -/
abbrev terminalPath : Path terminalTree := ⟨⟨⟩, ⟨⟩⟩

/-- The decision resources on `terminalTree`. -/
abbrev terminalResources := pathResources inputs terminalTree terminalPath

-- AccessExample 11, restated: on `terminalTree`, the decision's resource index includes the
-- terminal send.
example : (Unit ⊕ oracleIdx terminalTree terminalPath) = (Unit ⊕ (PUnit ⊕ PEmpty)) := rfl

-- AccessExample 12, restated: the terminal send answers `Nat`, through the non-faithful
-- interface.
example : (oracles terminalTree terminalPath).Range ⟨.inl ⟨⟩, ()⟩ = Nat := rfl

/-- Read the input slot and the sent slot; both have the same signature `Unit → Nat`. -/
def derivedQuery : OracleComp terminalResources.spec Nat := do
  let old : Nat ← liftM (terminalResources.spec.query (.inl ⟨(), ()⟩))
  let fresh : Nat ← liftM (terminalResources.spec.query (.inr ⟨.inl ⟨⟩, ()⟩))
  pure (old + fresh)

-- AccessExample 13, restated: input behaviour is the input data 7, and the message is the sent
-- payload. The two same-signature slots are answered from their own data: `7 + 11 = 18`, for every
-- hidden coordinate.
example (hidden : Nat) : simulateQ (terminalResources.answer
    (seven, payloads terminalTree ⟨(11, hidden), ⟨⟩⟩)) derivedQuery = (18 : Nat) := rfl

-- AccessExample 14, restated: the handler of the run's payloads does not depend on the hidden
-- coordinate.
example (visible hidden₁ hidden₂ : Nat) :
    payloadImpl terminalTree ⟨(visible, hidden₁), ⟨⟩⟩ =
      payloadImpl terminalTree ⟨(visible, hidden₂), ⟨⟩⟩ := by
  funext q
  rcases q with ⟨i | i, q⟩
  · rfl
  · exact i.elim

-- AccessExample 15, restated: a one-send protocol has exactly one oracle slot; naming a second
-- slot does not typecheck.
example (i j : oracleIdx terminalTree terminalPath) : i = j := by
  rcases i with ⟨⟩ | i
  · rcases j with ⟨⟩ | j
    · rfl
    · exact j.elim
  · exact i.elim

example : True := by
  fail_if_success
    have _ : oracleIdx terminalTree terminalPath := .inr (.inl ⟨⟩)
  trivial

/-- Two pair sends. -/
@[instance_reducible] def twoSends : OracleProtocol :=
  .liftBind (.oracle (Nat × Nat) firstInterface)
    (fun _ => .liftBind (.oracle (Nat × Nat) firstInterface) (fun _ => .pure ⟨⟩))

-- AccessExample 16, restated: after the second send the decision can query the second slot.
/-- Query the second sent slot. -/
def secondQuery : OracleComp (oracles twoSends ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩) Nat :=
  liftM ((oracles twoSends ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩).query ⟨.inr (.inl ⟨⟩), ()⟩)

/-- It is answered from the second payload. -/
example (first second : Nat × Nat) :
    simulateQ (payloadImpl twoSends ⟨first, second, ⟨⟩⟩) secondQuery = second.1 := rfl

/-- Message and response types may lie above the query type when extending resources. -/
example (Messages : Type 1) (interface : OracleInterface.{1, 0} Messages)
    (initial : PFunctor.{0, 1}) : PFunctor.{0, 1} :=
  let prior : Resources.{1, 0, 1} :=
    ⟨initial.A, OracleSpec.ofPFunctor initial,
      QueryImpl (OracleSpec.ofPFunctor initial) Id, id⟩
  let latest : Resources.{1, 0, 1} :=
    ⟨interface.Query, interface.toOC.spec, Messages,
      fun message query => (interface.toOC.impl query).run message⟩
  (prior.sum latest).spec.toPFunctor

/-- Query types may lie above the message and response types when extending resources. -/
example (Messages : Type) (interface : OracleInterface.{0, 1} Messages)
    (initial : PFunctor.{1, 0}) : PFunctor.{1, 0} :=
  let prior : Resources.{0, 1, 1} :=
    ⟨initial.A, OracleSpec.ofPFunctor initial,
      QueryImpl (OracleSpec.ofPFunctor initial) Id, id⟩
  let latest : Resources.{0, 1, 0} :=
    ⟨interface.Query, interface.toOC.spec, Messages,
      fun message query => (interface.toOC.impl query).run message⟩
  (prior.sum latest).spec.toPFunctor

end Interaction.Core.AccessExampleTests
