/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Security.RoundByRound

/-! Transcript prefixes. A prefix is a structural cursor spine decorated with full moves,
`PrefixMoves oracleSig sp`, so hidden oracle payloads stay in the prefix while the spine records
only shape branches. Oracle slots are typed by the completed shape path. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.TwoParty.Lens OracleComp

namespace Interaction.Core.PrefixTests

-- Prefix fixture: the frozen tree's public node is re-authored as a prover message.
/-- One hidden `Bool` payload followed by a public `Fin 3` message. -/
def mixed : OracleProtocol :=
  .liftBind (.oracle Bool OracleInterface.instDefault)
    (fun _ => .liftBind (.message (Fin 3)) (fun _ => .pure ⟨⟩))

/-- The cursor stopping right after the oracle send. Its oracle edge carries only a marker. -/
def afterSend : Cursor.Spine mixed (.liftBind (.message (Fin 3)) (fun _ => .pure ⟨⟩)) :=
  .down ⟨⟩ (.root _)

/-- The prefix stopping after the oracle send, with its payload. -/
def sent (message : Bool) : PrefixMoves oracleSig afterSend := ⟨⟨message, rfl⟩, ⟨⟩⟩

/-- A prefix of `mixed` packaged with its cursor. -/
abbrev MixedPrefix := (t : OracleProtocol) × (sp : Cursor.Spine mixed t) × PrefixMoves oracleSig sp

/-- The packaged prefix after sending `message`. -/
def sentPrefix (message : Bool) : MixedPrefix := ⟨_, afterSend, sent message⟩

-- Prefix 1, restated: the prefixes with payloads `true` and `false` decorate the same spine.
example : (sentPrefix true).2.1 = (sentPrefix false).2.1 := rfl

-- Prefix 2, restated: the two prefixes differ.
example : sent true ≠ sent false := by
  intro h
  exact Bool.noConfusion (congrArg (fun moves : PrefixMoves oracleSig afterSend => moves.1.1) h)

example : sentPrefix true ≠ sentPrefix false := by
  intro h
  cases h

-- Prefix 3, restated: on every completed path the send has an oracle slot, which the run's
-- payloads answer.
/-- Every completed shape path of `mixed` has the sent slot. -/
def sentSlot : (p : Path mixed) → oracleIdx mixed p
  | ⟨⟨⟩, _, ⟨⟩⟩ => .inl ⟨⟩

example (message : Bool) (choice : Fin 3) :
    payloads mixed ⟨message, choice, ⟨⟩⟩ (sentSlot _) = message := rfl

-- Prefix 4, restated: a decision at the root is a decision on the empty prefix of
-- `mixed = (.pure ⟨⟩).append (fun _ => mixed)`, which has no oracle slot.
example : (FreeM.pure ⟨⟩ : OracleProtocol).append (fun _ => mixed) = mixed := rfl

example : IsEmpty (oracleIdx (.pure ⟨⟩) ⟨⟩) := inferInstanceAs (IsEmpty PEmpty)

/-- One send of an `Empty` payload. -/
def emptySend : OracleProtocol :=
  .liftBind (.oracle Empty OracleInterface.instDefault) (fun _ => .pure ⟨⟩)

-- Prefix 5, restated: the root prefix exists for an `Empty` payload type, and so does the shape
-- path through the send.
example : PrefixMoves oracleSig (Cursor.Spine.root emptySend) := ⟨⟩

example : Path emptySend := ⟨⟨⟩, ⟨⟩⟩

-- Prefix 6, restated: no prefix crosses the `Empty` send, and no full transcript exists.
example (moves : PrefixMoves oracleSig
    (.down ⟨⟩ (.root _) : Cursor.Spine emptySend (.pure ⟨⟩))) : False :=
  moves.1.1.elim

example (tr : PathAlong oracleSig emptySend) : False := tr.1.elim

/-- The complete cursor through `mixed`, choosing `2`. -/
def full : Cursor.Spine mixed (.pure ⟨⟩) := .down ⟨⟩ (.down (2 : Fin 3) (.root _))

/-- The complete prefix with payload `true` and public choice `2`. -/
def fullMoves : PrefixMoves oracleSig full := ⟨⟨true, rfl⟩, ⟨⟨(2 : Fin 3), rfl⟩, ⟨⟩⟩⟩

-- Prefix 7, restated: the complete prefix has length 2 and completes to the full transcript
-- `⟨true, 2⟩`.
example : full.length = 2 := rfl

example : PrefixMoves.complete oracleSig full fullMoves = ⟨true, (2 : Fin 3), ⟨⟩⟩ := rfl

-- Prefix 8, restated: the first entry of the complete prefix is the hidden payload `true`.
example : fullMoves.1.1 = true := rfl

/-- The actual prefix ending immediately after the oracle send, before the public choice. -/
def oraclePrefix : OracleProtocol :=
  .liftBind (.oracle Bool OracleInterface.instDefault) (fun _ => .pure ⟨⟩)

/-- The crossed-send prefix followed by the public future is exactly the original protocol. -/
theorem oraclePrefix_append :
    oraclePrefix.append (fun _ => .liftBind (.message (Fin 3)) (fun _ => .pure ⟨⟩)) = mixed := rfl

/-- A decision at the crossed-send boundary can query the oracle without choosing a future. -/
def prefixQuery : OracleComp (oracles oraclePrefix ⟨⟨⟩, ⟨⟩⟩) Bool :=
  liftM ((oracles oraclePrefix ⟨⟨⟩, ⟨⟩⟩).query ⟨.inl ⟨⟩, ()⟩)

/-- The oracle available at the crossed-send boundary answers from that prefix's own payload. -/
theorem crossed_send_answer (message : Bool) :
    simulateQ (payloadImpl oraclePrefix ⟨message, ⟨⟩⟩) prefixQuery = message := rfl

end Interaction.Core.PrefixTests
