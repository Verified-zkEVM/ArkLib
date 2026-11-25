/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Oracle.SentOracles
import ArkLib.Interaction.Security.RoundByRound

/-! Partial transcripts. A partial transcript is a structural cursor spine decorated with full
moves, `PartialTranscriptAt oracleSig sp`. Hidden oracle messages stay in it, while the spine
records only branch choices. The type of oracle indices depends on the completed path. -/

open PFunctor PFunctor.FreeM Interaction Interaction.TwoParty.Lens OracleComp

namespace Interaction.PartialTranscriptsTests

-- Prefix fixture: the old layer's public node is re-authored as a prover message.
/-- One hidden `Bool` oracle message followed by a public `Fin 3` message. -/
def mixed : OracleProtocol :=
  .liftBind (.oracle Bool OracleInterface.instDefault)
    (fun _ => .liftBind (.message (Fin 3)) (fun _ => .pure ⟨⟩))

/-- The cursor stopping right after the oracle send. Its oracle edge carries only a marker. -/
def afterSend : Cursor.Spine mixed (.liftBind (.message (Fin 3)) (fun _ => .pure ⟨⟩)) :=
  .down ⟨⟩ (.root _)

/-- The partial transcript that stops after the oracle send, with its oracle message. -/
def sent (message : Bool) : PartialTranscriptAt oracleSig afterSend := ⟨⟨message, rfl⟩, ⟨⟩⟩

/-- A partial transcript of `mixed` packaged with its cursor. -/
abbrev MixedPrefix :=
  (t : OracleProtocol) × (sp : Cursor.Spine mixed t) × PartialTranscriptAt oracleSig sp

/-- The packaged partial transcript after sending `message`. -/
def sentPrefix (message : Bool) : MixedPrefix := ⟨_, afterSend, sent message⟩

-- Prefix 1, restated: the partial transcripts for `true` and `false` decorate the same spine.
example : (sentPrefix true).2.1 = (sentPrefix false).2.1 := rfl

-- Prefix 2, restated: the two partial transcripts differ.
example : sent true ≠ sent false := by
  intro h
  exact Bool.noConfusion
    (congrArg (fun moves : PartialTranscriptAt oracleSig afterSend => moves.1.1) h)

example : sentPrefix true ≠ sentPrefix false := by
  intro h
  cases h

-- Prefix 3, additional check: on every completed path the send has an oracle, which the run's
-- oracle messages answer.
/-- Every completed path of `mixed` has the sent oracle. -/
def sentSlot : (p : Path mixed) → OracleMessageIndex mixed p
  | ⟨⟨⟩, _, ⟨⟩⟩ => .inl ⟨⟩

example (message : Bool) (choice : Fin 3) :
    oracleMessages mixed ⟨message, choice, ⟨⟩⟩ (sentSlot _) = message := rfl

-- Prefix 3 and 4, availability on `mixed` itself: the root oracle node is not sent at the empty
-- partial transcript, and it is sent once the Boolean has been sent.
/-- The root oracle node of `mixed` is not sent before any move. -/
theorem root_not_sent_empty :
    ¬ (PartialTranscript.empty : PartialTranscript oracleSig mixed).IsSent (.inl ⟨⟩) := by
  rintro ⟨i, _⟩
  exact i.elim

/-- After the Boolean `message` is sent, the root oracle node of `mixed` is sent. -/
theorem root_sent_after_send (message : Bool) :
    PartialTranscript.IsSent (s := mixed) (some ⟨message, none⟩) (.inl ⟨⟩) :=
  ⟨.inl ⟨⟩, rfl⟩

-- Prefix 4, additional check: a decision at the root is a decision on the empty prefix of
-- `mixed = (.pure ⟨⟩).append (fun _ => mixed)`, which has no oracle.
example : (FreeM.pure ⟨⟩ : OracleProtocol).append (fun _ => mixed) = mixed := rfl

example : IsEmpty (OracleMessageIndex (.pure ⟨⟩) ⟨⟩) := inferInstanceAs (IsEmpty PEmpty)

/-- One send of an oracle message of type `Empty`. -/
def emptySend : OracleProtocol :=
  .liftBind (.oracle Empty OracleInterface.instDefault) (fun _ => .pure ⟨⟩)

-- Prefix 5, restated: the root partial transcript exists for the oracle message type `Empty`, and
-- so does the path through the send.
example : PartialTranscriptAt oracleSig (Cursor.Spine.root emptySend) := ⟨⟩

example : Path emptySend := ⟨⟨⟩, ⟨⟩⟩

-- Prefix 6, restated: no partial transcript crosses the `Empty` send; no full transcript exists.
example (moves : PartialTranscriptAt oracleSig
    (.down ⟨⟩ (.root _) : Cursor.Spine emptySend (.pure ⟨⟩))) : False :=
  moves.1.1.elim

example (tr : Transcript oracleSig emptySend) : False := tr.1.elim

/-- The complete cursor through `mixed`, choosing `2`. -/
def full : Cursor.Spine mixed (.pure ⟨⟩) := .down ⟨⟩ (.down (2 : Fin 3) (.root _))

/-- The complete partial transcript with oracle message `true` and public choice `2`. -/
def fullMoves : PartialTranscriptAt oracleSig full := ⟨⟨true, rfl⟩, ⟨⟨(2 : Fin 3), rfl⟩, ⟨⟩⟩⟩

-- Prefix 7, restated: the complete partial transcript has length 2 and completes to the full
-- transcript `⟨true, 2⟩`.
example : full.length = 2 := rfl

example : PartialTranscriptAt.complete oracleSig full fullMoves = ⟨true, (2 : Fin 3), ⟨⟩⟩ := rfl

-- Prefix 8, restated: the complete partial transcript starts with the hidden oracle message `true`.
example : fullMoves.1.1 = true := rfl

/-- The prefix protocol that ends immediately after the oracle send, before the public choice. -/
def oraclePrefix : OracleProtocol :=
  .liftBind (.oracle Bool OracleInterface.instDefault) (fun _ => .pure ⟨⟩)

/-- The crossed-send prefix followed by the public future is exactly the original protocol. -/
theorem oraclePrefix_append :
    oraclePrefix.append (fun _ => .liftBind (.message (Fin 3)) (fun _ => .pure ⟨⟩)) = mixed := rfl

/-- A decision at the crossed-send boundary can query the oracle without choosing a future. -/
def prefixQuery : OracleComp (oracleMessageSpec oraclePrefix ⟨⟨⟩, ⟨⟩⟩) Bool :=
  liftM ((oracleMessageSpec oraclePrefix ⟨⟨⟩, ⟨⟩⟩).query ⟨.inl ⟨⟩, ()⟩)

/-- At the crossed-send boundary, the oracle answers from that prefix's own oracle message. -/
theorem crossed_send_answer (message : Bool) :
    simulateQ (oracleMessageImpl oraclePrefix ⟨message, ⟨⟩⟩) prefixQuery = message := rfl

end Interaction.PartialTranscriptsTests
