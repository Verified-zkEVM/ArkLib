/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.OracleVerifier
import PolyFun.PFunctor.Free.Cursor

/-! Oracle access as typing. A decision on a completed path queries the input family and the
oracle family of that path, `pathBundle inputs s p`. A public bit selects message types. An
oracle exists only on paths that cross its send. Input oracles and oracle messages with the same
signature stay distinct, and a non-faithful interface hides representation data. -/

open PFunctor PFunctor.FreeM Interaction Interaction.Oracle OracleComp OracleSpec

namespace Interaction.AccessTypingTests

/-- One scalar input oracle. -/
def inputs : OracleFamily Unit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- The input data: the single input oracle holds 7. -/
def seven : ∀ _ : Unit, Nat := fun _ => 7

/-- The part of `accessTree` before its oracle send: the public bit. -/
def before : OracleProtocol :=
  .liftBind (.message Bool) (fun _ => .pure ⟨⟩)

/-- The part of `accessTree` after the public bit: a branch-dependent oracle send, then a public
message. -/
def after : Path before → OracleProtocol
  | ⟨false, ⟨⟩⟩ => .liftBind (.oracle Bool OracleInterface.instDefault)
      (fun _ => .liftBind (.message (Fin 2)) (fun _ => .pure ⟨⟩))
  | ⟨true, ⟨⟩⟩ => .liftBind (.oracle (Fin 3) OracleInterface.instDefault)
      (fun _ => .liftBind (.message Bool) (fun _ => .pure ⟨⟩))

/-- A public bit selects the type of the next oracle message. -/
abbrev accessTree : OracleProtocol := before.append after

/-- The `false` branch, with oracle message `false`. -/
def leftPath : Transcript oracleSig accessTree := ⟨false, false, (0 : Fin 2), ⟨⟩⟩

/-- The same public choices, with oracle message `true`. -/
def rightPath : Transcript oracleSig accessTree := ⟨false, true, (0 : Fin 2), ⟨⟩⟩

/-- The `true` branch, with oracle message `2 : Fin 3`. -/
def finPath : Transcript oracleSig accessTree := ⟨true, (2 : Fin 3), false, ⟨⟩⟩

-- AccessExample 1, restated: a decision stopped before the send is a decision on `before`, the
-- prefix of `accessTree`. Its bundle holds the inputs and the oracles of `before`, which has
-- none on the `false` path.
/-- Before the `false`-branch send there are no sent oracles. -/
example : OracleMessageIndex before ⟨false, ⟨⟩⟩ = PEmpty := rfl

example : IsEmpty (OracleMessageIndex before ⟨false, ⟨⟩⟩) := inferInstanceAs (IsEmpty PEmpty)

-- AccessExample 2, restated as row 1 for the `true` branch.
example : OracleMessageIndex before ⟨true, ⟨⟩⟩ = PEmpty := rfl

example : IsEmpty (OracleMessageIndex before ⟨true, ⟨⟩⟩) := inferInstanceAs (IsEmpty PEmpty)

-- AccessExample 3, restated: a query naming the unsent message does not typecheck in the
-- bundle of a decision stopped before the send.
example : True := by
  fail_if_success
    have _ : (pathBundle inputs before ⟨false, ⟨⟩⟩).spec.Domain :=
      (.inr ⟨.inl ⟨⟩, ()⟩)
  trivial

-- AccessExample 4, restated: the same query constructor typechecks for a decision on a completed
-- path through the send.
/-- A decision on the completed `false` path can query the sent message. -/
example : (pathBundle inputs accessTree
    leftPath.path).spec.Domain := (.inr ⟨.inl ⟨⟩, ()⟩)

-- AccessExample 5, restated: the response type of the `false`-branch message.
example : (oracleMessageSpec accessTree leftPath.path).Range
    ⟨.inl ⟨⟩, ()⟩ = Bool := rfl

-- AccessExample 6, restated: the response type of the `true`-branch message.
example : (oracleMessageSpec accessTree finPath.path).Range
    ⟨.inl ⟨⟩, ()⟩ = Fin 3 := rfl

-- AccessExample 7, restated: after the send, the decision's bundle index is the input oracle
-- and the one sent oracle.
example : (Unit ⊕ OracleMessageIndex accessTree leftPath.path) =
    (Unit ⊕ (PUnit ⊕ PEmpty)) := rfl

-- AccessExample 8, restated: decoration restriction is removed. A cursor whose oracle edge
-- carries only a unit marker selects the future after the oracle send. The projected shape of that
-- future is independent of the oracle message (`oracle_payload_shape`).
/-- The public future after the `false`-branch send, selected without an oracle message. -/
def afterSend : Cursor.Spine accessTree (.liftBind (.message (Fin 2)) (fun _ => .pure ⟨⟩)) :=
  .down false (.down ⟨⟩ (.root _))

example (x y : Bool) (tr : Transcript oracleSig (.liftBind (.message (Fin 2))
    (fun _ => .pure ⟨⟩) : OracleProtocol)) :
    Transcript.path (l := oracleSig) (s := (after ⟨false, ⟨⟩⟩)) ⟨x, tr⟩ =
      Transcript.path (l := oracleSig) (s := (after ⟨false, ⟨⟩⟩)) ⟨y, tr⟩ :=
  oracle_payload_shape Bool OracleInterface.instDefault _ x y tr

-- AccessExample 9, restated: execution paths are full transcripts.
/-- Distinct oracle messages give distinct full transcripts. -/
example : leftPath ≠ rightPath := by
  intro h
  cases h

-- AccessExample 10, restated: equal paths give the same oracle family, by `rfl`.
example : leftPath.path =
    rightPath.path := rfl

example : oracleMessageSpec accessTree leftPath.path =
    oracleMessageSpec accessTree rightPath.path := rfl

/-- Only the first coordinate of a sent pair is observable. -/
@[instance_reducible] def firstInterface : OracleInterface (Nat × Nat) where
  Query := Unit
  toOC.spec := fun _ => Nat
  toOC.impl _ := do return (← read).1

/-- One pair send followed by the leaf. -/
def terminalTree : OracleProtocol :=
  .liftBind (.oracle (Nat × Nat) firstInterface) (fun _ => .pure ⟨⟩)

/-- The only path of `terminalTree`. -/
abbrev terminalPath : Path terminalTree := ⟨⟨⟩, ⟨⟩⟩

/-- The decision bundle on `terminalTree`. -/
abbrev terminalBundle := pathBundle inputs terminalTree terminalPath

-- AccessExample 11, restated: on `terminalTree`, the decision's bundle index includes the
-- terminal send.
example : (Unit ⊕ OracleMessageIndex terminalTree terminalPath) = (Unit ⊕ (PUnit ⊕ PEmpty)) := rfl

-- AccessExample 12, restated: the terminal send answers `Nat`, through the non-faithful
-- interface.
example : (oracleMessageSpec terminalTree terminalPath).Range ⟨.inl ⟨⟩, ()⟩ = Nat := rfl

/-- Read the input oracle and the sent oracle. Both have the same signature `Unit → Nat`. -/
def derivedQuery : OracleComp terminalBundle.spec Nat := do
  let old : Nat ← liftM (terminalBundle.spec.query (.inl ⟨(), ()⟩))
  let fresh : Nat ← liftM (terminalBundle.spec.query (.inr ⟨.inl ⟨⟩, ()⟩))
  pure (old + fresh)

-- AccessExample 13, restated: input behaviour is the input data 7, and the message is the sent
-- oracle message. The two oracles with the same signature are answered from their own data:
-- `7 + 11 = 18`, for every hidden coordinate.
example (hidden : Nat) : simulateQ (terminalBundle.answer
    (seven, oracleMessages terminalTree ⟨(11, hidden), ⟨⟩⟩)) derivedQuery = (18 : Nat) := rfl

-- AccessExample 14, restated: the handler of the run's oracle messages does not depend on the
-- hidden coordinate.
example (visible hidden₁ hidden₂ : Nat) :
    oracleMessageImpl terminalTree ⟨(visible, hidden₁), ⟨⟩⟩ =
      oracleMessageImpl terminalTree ⟨(visible, hidden₂), ⟨⟩⟩ := by
  funext q
  rcases q with ⟨i | i, q⟩
  · rfl
  · exact i.elim

-- AccessExample 15, restated: a one-send protocol has exactly one oracle. Naming a second oracle
-- does not typecheck.
example (i j : OracleMessageIndex terminalTree terminalPath) : i = j := by
  rcases i with ⟨⟩ | i
  · rcases j with ⟨⟩ | j
    · rfl
    · exact j.elim
  · exact i.elim

example : True := by
  fail_if_success
    have _ : OracleMessageIndex terminalTree terminalPath := .inr (.inl ⟨⟩)
  trivial

/-- Two pair sends. -/
def twoSends : OracleProtocol :=
  .liftBind (.oracle (Nat × Nat) firstInterface)
    (fun _ => .liftBind (.oracle (Nat × Nat) firstInterface) (fun _ => .pure ⟨⟩))

-- AccessExample 16, restated: after the second send the decision can query the second oracle.
/-- Query the second sent oracle. -/
def secondQuery : OracleComp (oracleMessageSpec twoSends ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩) Nat :=
  liftM ((oracleMessageSpec twoSends ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩).query ⟨.inr (.inl ⟨⟩), ()⟩)

/-- It is answered from the second oracle message. -/
example (first second : Nat × Nat) :
    simulateQ (oracleMessageImpl twoSends ⟨first, second, ⟨⟩⟩) secondQuery = second.1 := rfl

/-- Extend a bundle with message and response carriers in `Type`. -/
example (Messages : Type) (interface : OracleInterface.{0, 0} Messages)
    (initial : PFunctor.{0, 0}) : PFunctor.{0, 0} :=
  let prior : OracleBundle :=
    ⟨initial.A, OracleSpec.ofPFunctor initial,
      QueryImpl (OracleSpec.ofPFunctor initial) Id, id⟩
  let latest : OracleBundle :=
    ⟨interface.Query, interface.toOC.spec, Messages,
      fun message query => (interface.toOC.impl query).run message⟩
  (prior.sum latest).spec.toPFunctor

/-- Extend a bundle with query carriers in `Type`. -/
example (Messages : Type) (interface : OracleInterface.{0, 0} Messages)
    (initial : PFunctor.{0, 0}) : PFunctor.{0, 0} :=
  let prior : OracleBundle :=
    ⟨initial.A, OracleSpec.ofPFunctor initial,
      QueryImpl (OracleSpec.ofPFunctor initial) Id, id⟩
  let latest : OracleBundle :=
    ⟨interface.Query, interface.toOC.spec, Messages,
      fun message query => (interface.toOC.impl query).run message⟩
  (prior.sum latest).spec.toPFunctor

end Interaction.AccessTypingTests
