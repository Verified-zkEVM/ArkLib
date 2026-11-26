/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.OracleVerifier
import ArkLibTest.Interaction.Oracle.LoggedExecution

/-! One run of a public message, a challenge and a hidden oracle send. The full transcript of the
run keeps the hidden oracle message. The oracle message family returns it, and the verifier view
erases it. A rejecting decision returns an explicit `none` that keeps the transcript, the private
output and the ambient history. -/

open PFunctor PFunctor.FreeM Interaction Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp

namespace Interaction.HiddenSendRunTests

/-- Ambient events carry tags and need no meaningful response. -/
abbrev ambient : OracleSpec Nat := Nat →ₒ Unit

/-- No input oracles. -/
def noInputs : OracleBundle :=
  OracleBundle.ofIndexed (fun i : PEmpty => PEmpty.elim i) fun i => i.elim

/-- The empty input data. -/
def noData : ∀ i : PEmpty, PEmpty.elim i := fun i => i.elim

/-- The prover sends a public bit, receives a challenge bit, then sends a hidden scalar. -/
def phased : OracleProtocol :=
  .liftBind (.message Bool) (fun _ => .liftBind (.challenge Bool) (fun _ =>
    .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ => .pure ⟨⟩)))

/-- The prover records 9, 9 and 1, sends `true`, records 4, receives the challenge, records 5,
then sends `payload` and keeps `hidden` as private output. -/
def prover (payload hidden : Nat) : Prover oracleSig ambient phased (fun _ => Nat) := do
  for t in [9, 9, 1] do let _ ← liftM (ambient.query t)
  pure ⟨true, do
    let _ ← liftM (ambient.query 4)
    pure fun _ => do
      let _ ← liftM (ambient.query 5)
      pure ⟨payload, pure hidden⟩⟩

/-- The decision records 2 and 3, reads the sent oracle, records 6 and 7, then accepts with the
sent value or rejects. -/
def verifier (accept : Bool) :
    OracleVerifier ambient phased Unit (fun _ => Nat)
      noInputs
      (fun _ => noInputs) where
  decide _ p _ := by
    rcases p with ⟨b, c, ⟨⟩, ⟨⟩⟩
    exact OptionT.mk do
      for t in [2, 3] do
        let _ ← liftM (OracleSpec.query (spec :=
          ambient + (pathBundle noInputs phased ⟨b, c, ⟨⟩, ⟨⟩⟩).spec) (.inl t))
      let sent : Nat ← liftM (OracleSpec.query (spec :=
        ambient + (pathBundle noInputs phased ⟨b, c, ⟨⟩, ⟨⟩⟩).spec)
        (.inr (.inr (.inl ()))))
      for t in [6, 7] do
        let _ ← liftM (OracleSpec.query (spec :=
          ambient + (pathBundle noInputs phased ⟨b, c, ⟨⟩, ⟨⟩⟩).spec) (.inl t))
      pure (if accept then some sent else none)
  outputMap _ _ _ :=
    { f := fun _ i => i.elim
      impl := fun q => q.1.elim
      law := fun _ q => q.1.elim }

/-- Record each ambient tag and answer the challenge with `bit`. -/
def logger (bit : Bool) : QueryImpl (ambient + challengeSpec oracleSig phased) (StateM (List Nat))
  | .inl n => modify (· ++ [n])
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inl _⟩, _⟩ => pure bit
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inl _⟩⟩, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inr ⟨_, n⟩⟩⟩, _⟩ => n.elim


/-- Full transcript, private output, verdict and ambient history of one run. All indices and data
lie in `Type`. -/
def summary (accept : Bool) (payload hidden : Nat) (bit : Bool) :
    Transcript oracleSig phased × Nat × Option Nat × List Nat :=
  let z := (simulateQ (logger bit) ((verifier accept).run () noData
    (prover payload hidden))).run []
  (z.1.1, z.1.2.1, z.1.2.2.map Prod.fst, z.2)

-- PhasedRun 4: for every oracle message `payload`, private output and challenge, the run's full
-- transcript is `⟨true, bit, payload⟩`. Its `oracleMessages` returns `payload`, and its
-- verifier view erases it. The decision reads the oracle message and accepts with it.
example (payload hidden : Nat) (bit : Bool) : summary true payload hidden bit =
    (⟨true, bit, payload, ⟨⟩⟩, hidden, some payload, [9, 9, 1, 4, 5, 2, 3, 6, 7]) := rfl

example (payload : Nat) (bit : Bool) :
    (oracleMessages phased ⟨true, bit, payload, ⟨⟩⟩).1 = payload := rfl

example (payload : Nat) (bit : Bool) :
    (toView phased ⟨true, bit, payload, ⟨⟩⟩).val = ⟨true, bit, ⟨⟩, ⟨⟩⟩ := rfl

-- PhasedRun 6: the passive decision returns `none`, the final rejection. For every oracle
-- message, private output and challenge, the run keeps the transcript, the private output and the
-- full ambient history.
example (payload hidden : Nat) (bit : Bool) : summary false payload hidden bit =
    (⟨true, bit, payload, ⟨⟩⟩, hidden, none, [9, 9, 1, 4, 5, 2, 3, 6, 7]) := rfl

end Interaction.HiddenSendRunTests

namespace Interaction.HiddenSendRunClosingTests

open Interaction.LoggedExecutionTests OracleSpec

/-- Execute the actual closing prover, then interpret its final decision under `handler`, which
may fail with a label. Retain the transcript, private output, prover log, decision log and ambient
history. -/
def closingRun (handler : QueryImpl ambient (ExceptT Nat (StateM (List Nat))))
    (mode old message hidden : Nat) :
    (Transcript oracleSig pairSend × Nat × Except Nat (Option (Nat × Nat)) ×
      QueryLog ambient × List (String × Nat)) × List Nat :=
  (do
    let full := ambient + challengeSpec oracleSig pairSend
    let ⟨⟨tr, out, _⟩, proveLog⟩ ← simulateQ (logger pairChallenges)
      (OracleComp.withQueryLog (spec := full) (TwoParty.Lens.run pairSend
        ((pairProver [9] message hidden).simulate (fun q => liftM (full.query (.inl q))))
        (sampler oracleSig pairSend (fun c => liftM (full.query (.inr c))))))
    let p := Transcript.path tr
    let data : (pathBundle inputs pairSend p).Data := (fun _ => old, oracleMessages pairSend tr)
    let (verdict, log) ← (decisionVerifier mode).decideCatching handler () p
      (toView pairSend tr) data
    pure (tr, out, verdict.map (Option.map fun t =>
      (t, ((decisionVerifier mode).outputMap () p (toView pairSend tr)).f data ())),
      proveLog.fst, describePair p log) : StateM (List Nat) _).run []

/-- The closing run under `decisionHandler`, which throws on requests 17 and 23. -/
def decisionObserved (mode old message hidden : Nat) :=
  closingRun decisionHandler mode old message hidden

/-- Under handler failure, the run keeps the label 17, the transcript, the private output, the
prover log and the queries answered before the failure. The failed request has no answer, so it
adds no entry to the log of answered queries. Rejection and acceptance keep the same observations.
The verifier itself returns only an optional verdict: label 17 comes from `decisionHandler`. -/
theorem decision_outcomes (old message hidden : Nat) :
    decisionObserved 1 old message hidden =
      ((⟨(message, hidden), ⟨⟩⟩, hidden, .error 17,
        [⟨9, (9 : Nat)⟩, ⟨0, (0 : Nat)⟩],
        [("tag", 1), ("tag", 2), ("sent", message)]), [9, 0, 1, 2]) ∧
    decisionObserved 0 old message hidden =
      ((⟨(message, hidden), ⟨⟩⟩, hidden, .ok none,
        [⟨9, (9 : Nat)⟩, ⟨0, (0 : Nat)⟩],
        [("tag", 1), ("tag", 2), ("sent", message)]), [9, 0, 1, 2]) ∧
    decisionObserved 3 old message hidden =
      ((⟨(message, hidden), ⟨⟩⟩, hidden, .ok (some (message, old + message)),
        [⟨9, (9 : Nat)⟩, ⟨0, (0 : Nat)⟩],
        [("tag", 1), ("tag", 2), ("sent", message)]), [9, 0, 1, 2]) := by
  exact ⟨rfl, rfl, rfl⟩

/-- A handler that answers every request, including 17, and records it. -/
def answerAll : QueryImpl ambient (ExceptT Nat (StateM (List Nat))) := fun tag => do
  modify (· ++ [tag]); pure tag

/-- When the handler answers every request, mode 1 rejects: the verifier cannot return a fault
itself. The history records request 17 after the queries answered before it. -/
theorem answerAll_rejects (old message hidden : Nat) :
    (closingRun answerAll 1 old message hidden).1.2.2.1 = .ok none ∧
      (closingRun answerAll 1 old message hidden).2 = [9, 0, 1, 2, 17] := ⟨rfl, rfl⟩

end Interaction.HiddenSendRunClosingTests
