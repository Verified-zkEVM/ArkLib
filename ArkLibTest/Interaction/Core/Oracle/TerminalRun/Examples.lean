/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.OracleVerifier

/-!
# Accepted output data comes from the same run

The prover sends one pair oracle; the decision records 1, reads the observable coordinate of the
sent pair, records 2 and accepts with it. The output data is `input + sent.1`, computed from the
input data and the payload of the same run, so two runs with different inputs and messages close
to different values.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp

namespace Interaction.Core.TerminalRunTests

/-- Ambient queries carry tags; the logger records each tag and answers with it. -/
abbrev ambient : OracleSpec Nat := Nat →ₒ Nat

/-- One scalar input slot. -/
@[instance_reducible] def inputs : OracleFamily Unit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- One scalar output oracle. -/
@[instance_reducible] def output : OracleFamily Unit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- Only the first coordinate of a sent pair is observable. -/
@[reducible] def firstInterface : OracleInterface (Nat × Nat) where
  Query := Unit
  toOC.spec := fun _ => Nat
  toOC.impl _ := do return (← read).1

/-- The prover sends one pair oracle. -/
@[instance_reducible] def protocol : OracleProtocol :=
  .liftBind (.oracle (Nat × Nat) firstInterface) (fun _ => .pure ⟨⟩)

/-- The decision resources on the only path of `protocol`. -/
abbrev resources := pathResources inputs protocol ⟨⟨⟩, ⟨⟩⟩

/-- Output data: the input plus the observable coordinate of the sent pair. -/
def outputOracle : OracleMap resources output where
  f x _ := x.1 () + (x.2 (.inl ⟨⟩)).1
  impl _ := do
    let a : Nat ← liftM (resources.spec.query (.inl ⟨(), ()⟩))
    let b : Nat ← liftM (resources.spec.query (.inr ⟨.inl ⟨⟩, ()⟩))
    pure (a + b)
  law _ _ := by
    simp only [simulateQ_bind]
    rfl

/-- The decision records 1, reads the sent oracle, records 2, and accepts with the sent value. -/
def verifier : OracleVerifier ambient protocol Unit (fun _ => Nat) inputs (fun _ => output) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact do
      let _ ← liftM ((ambient + resources.spec).query (.inl 1))
      let sent : Nat ← liftM ((ambient + resources.spec).query (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
      let _ ← liftM ((ambient + resources.spec).query (.inl 2))
      pure sent
  outputMap _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact outputOracle

/-- The prover makes setup query 9 and query 0, sends `(message, hidden)` and keeps `hidden`. -/
def prover (message hidden : Nat) : Prover oracleSig ambient protocol (fun _ => Nat) := do
  let _ ← liftM (ambient.query 9)
  let _ ← liftM (ambient.query 0)
  pure ⟨(message, hidden), pure hidden⟩

/-- Record each ambient tag and answer it with itself; `protocol` has no challenges. -/
def logger : QueryImpl (ambient + challengeSpec oracleSig protocol) (StateM (List Nat))
  | .inl n => do modify (· ++ [n]); pure n
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, n⟩, _⟩ => n.elim

/-- The private output, the claim with its output data, and the ambient history of one run. -/
def summary (old message hidden : Nat) : Nat × Option (Nat × Nat) × List Nat :=
  let z := (simulateQ logger (verifier.run () (fun _ => old) (prover message hidden))).run []
  (z.1.2.1, z.1.2.2.map (fun r => (r.1, r.2 ())), z.2)

-- TerminalRun TR5 (two examples), restated: the frozen accepted terminal claim closed with the
-- run's sources becomes the accepted result of `OracleVerifier.run`, whose output data is the
-- output map applied to the input data and the payloads of the same run. Input 7 and message 11
-- close to 18; input 13 and message 19 close to 32. Holds for every hidden value; the result also
-- keeps the private output and the full ambient history.
example (hidden : Nat) : summary 7 11 hidden = (hidden, some (11, 18), [9, 0, 1, 2]) := rfl

example (hidden : Nat) : summary 13 19 hidden = (hidden, some (19, 32), [9, 0, 1, 2]) := rfl

-- Executable samples of the two runs.
run_cmd do
  for hidden in [0, 42] do
    unless summary 7 11 hidden == (hidden, some (11, 18), [9, 0, 1, 2]) do
      throwError "the first accepted run is wrong: {summary 7 11 hidden}"
    unless summary 13 19 hidden == (hidden, some (19, 32), [9, 0, 1, 2]) do
      throwError "the second accepted run is wrong: {summary 13 19 hidden}"

end Interaction.Core.TerminalRunTests
