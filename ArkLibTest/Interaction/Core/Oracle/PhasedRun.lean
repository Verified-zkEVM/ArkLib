/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.OracleVerifier
import ArkLibTest.Interaction.Core.Oracle.LoggedExecution

/-! One run of a public message, a challenge and a hidden oracle send. The full transcript of the
run keeps the hidden payload, which the payload family returns and the verifier view erases. A
rejecting decision returns an explicit `none` that keeps the transcript, the private output and
the ambient history. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp

namespace Interaction.Core.PhasedRunTests

/-- Ambient events carry tags and need no meaningful response. -/
abbrev ambient : OracleSpec Nat := Nat →ₒ Unit

/-- No input oracles. -/
def noInputs : OracleFamily PEmpty (fun i => PEmpty.elim i) :=
  ⟨fun i => i.elim⟩

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
def verifier.{uI, uJ, wI, wJ} (accept : Bool) :
    OracleVerifier ambient phased Unit (fun _ => Nat)
      (noInputs : OracleFamily.{uI, 0, wI} _ _)
      (fun _ => (noInputs : OracleFamily.{uJ, 0, wJ} _ _)) where
  decide _ p _ := by
    rcases p with ⟨b, c, ⟨⟩, ⟨⟩⟩
    exact OptionT.mk do
      for t in [2, 3] do
        let _ ← liftM (OracleSpec.query (spec :=
          ambient + (pathResources noInputs phased ⟨b, c, ⟨⟩, ⟨⟩⟩).spec) (.inl t))
      let sent : Nat ← liftM (OracleSpec.query (spec :=
        ambient + (pathResources noInputs phased ⟨b, c, ⟨⟩, ⟨⟩⟩).spec)
        (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
      for t in [6, 7] do
        let _ ← liftM (OracleSpec.query (spec :=
          ambient + (pathResources noInputs phased ⟨b, c, ⟨⟩, ⟨⟩⟩).spec) (.inl t))
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

universe uI wI wJ

/-- Full transcript, private output, verdict and ambient history of one run. The empty input
index and the input and output query universes are independent. -/
def summary.{vI, qI, qJ} (accept : Bool) (payload hidden : Nat) (bit : Bool) :
    PathAlong oracleSig phased × Nat × Option Nat × List Nat :=
  let z := (simulateQ (logger bit) ((verifier.{vI, 0, qI, qJ} accept).run () noData
    (prover payload hidden))).run []
  (z.1.1, z.1.2.1, z.1.2.2.map Prod.fst, z.2)

-- PhasedRun 4: for every payload, private output and challenge,
-- the run's full transcript is `⟨true, bit, payload⟩`; its payload family returns `payload` and its
-- verifier view erases it. The decision reads the payload and accepts with it.
example (payload hidden : Nat) (bit : Bool) : summary.{uI, wI, wJ} true payload hidden bit =
    (⟨true, bit, payload, ⟨⟩⟩, hidden, some payload, [9, 9, 1, 4, 5, 2, 3, 6, 7]) := rfl

example (payload : Nat) (bit : Bool) :
    payloads phased ⟨true, bit, payload, ⟨⟩⟩ (.inl ⟨⟩) = payload := rfl

example (payload : Nat) (bit : Bool) :
    (toView phased ⟨true, bit, payload, ⟨⟩⟩).val = ⟨true, bit, ⟨⟩, ⟨⟩⟩ := rfl

-- PhasedRun 6: the passive decision returns `none`, the terminal
-- rejection. For every payload, private output and challenge, the run keeps the transcript, the
-- private output and the full ambient history.
example (payload hidden : Nat) (bit : Bool) : summary.{uI, wI, wJ} false payload hidden bit =
    (⟨true, bit, payload, ⟨⟩⟩, hidden, none, [9, 9, 1, 4, 5, 2, 3, 6, 7]) := rfl

end Interaction.Core.PhasedRunTests

namespace Interaction.Core.PhasedRunClosingTests

open Interaction.Core.LoggedExecutionTests OracleSpec

/-- Execute the actual closing prover before interpreting its final decision with labelled
failure. Retain its transcript, private output, prover log, decision log and ambient history. -/
def terminalObserved (mode old message hidden : Nat) :
    (PathAlong oracleSig pairSend × Nat × Except Nat (Option (Nat × Nat)) ×
      QueryLog ambient × List (String × Nat)) × List Nat :=
  (do
    let full := ambient + challengeSpec oracleSig pairSend
    let ⟨⟨tr, out, _⟩, proveLog⟩ ← simulateQ (logger pairChallenges)
      (OracleComp.withQueryLog (spec := full) (TwoParty.Lens.run pairSend
        ((pairProver [9] message hidden).simulate (fun q => liftM (full.query (.inl q))))
        (sampler oracleSig pairSend (fun c => liftM (full.query (.inr c))))))
    let p := projectPathAlong oracleSig pairSend tr
    let data : (pathResources inputs pairSend p).Data := (fun _ => old, payloads pairSend tr)
    let (verdict, log) ← (terminalVerifier mode).decideWithFailureLog terminalHandler () p
      (toView pairSend tr) data
    pure (tr, out, verdict.map (Option.map fun t =>
      (t, ((terminalVerifier mode).outputMap () p (toView pairSend tr)).f data ())),
      proveLog.fst, describePair p log) : StateM (List Nat) _).run []

/-- Fault 17, rejection and acceptance retain the same actual transcript, private output and
answered-query logs. Failure is returned by the handler and is neither rejection nor acceptance.
The failed request has no answer, so it adds no query-answer entry. -/
theorem terminal_outcomes (old message hidden : Nat) :
    terminalObserved 1 old message hidden =
      ((⟨(message, hidden), ⟨⟩⟩, hidden, .error 17,
        [⟨9, (9 : Nat)⟩, ⟨0, (0 : Nat)⟩],
        [("tag", 1), ("tag", 2), ("sent", message)]), [9, 0, 1, 2]) ∧
    terminalObserved 0 old message hidden =
      ((⟨(message, hidden), ⟨⟩⟩, hidden, .ok none,
        [⟨9, (9 : Nat)⟩, ⟨0, (0 : Nat)⟩],
        [("tag", 1), ("tag", 2), ("sent", message)]), [9, 0, 1, 2]) ∧
    terminalObserved 3 old message hidden =
      ((⟨(message, hidden), ⟨⟩⟩, hidden, .ok (some (message, old + message)),
        [⟨9, (9 : Nat)⟩, ⟨0, (0 : Nat)⟩],
        [("tag", 1), ("tag", 2), ("sent", message)]), [9, 0, 1, 2]) := by
  exact ⟨rfl, rfl, rfl⟩

end Interaction.Core.PhasedRunClosingTests
