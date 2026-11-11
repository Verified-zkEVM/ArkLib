/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibTest.Interaction.Core.Oracle.LoggedExecution

/-!
# Closing the verifier's output with the same run's data

The prover sends one pair oracle whose interface exposes only the first coordinate, and keeps the
second coordinate as private output. The passive decision reads the sent oracle by query. The
output data is the input plus the sent coordinate, materialized from the input and the payloads of
the same run. A stateful logger exposes the exact effect order.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp
open Interaction.Core.LoggedExecutionTests (inputs seven pairSend pairResources)

namespace Interaction.Core.CoreRunExampleTests

/-- Observable ambient events. -/
abbrev ambient : OracleSpec Nat := Nat →ₒ Unit

/-- The output data adds the input to the observable coordinate of the sent pair. -/
def outputMap : OracleMap pairResources inputs where
  f x _ := (show Nat from x.1 ()) + (show Nat × Nat from x.2 (.inl ⟨⟩)).1
  impl _ := do
    let old : Nat ← liftM (pairResources.spec.query (.inl ⟨(), ()⟩))
    let sent : Nat ← liftM (pairResources.spec.query (.inr ⟨.inl ⟨⟩, ()⟩))
    pure (old + sent)
  law _ _ := by
    simp only [simulateQ_bind]
    rfl

/-- The decision records 1, records 2, reads the sent oracle, and accepts with it or rejects. -/
def verifier (accept : Bool) : OracleVerifier ambient pairSend Unit (fun _ => Nat) inputs
    (fun _ => inputs) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact OptionT.mk do
      let _ ← liftM ((ambient + pairResources.spec).query (.inl 1))
      let _ ← liftM ((ambient + pairResources.spec).query (.inl 2))
      let sent : Nat ← liftM ((ambient + pairResources.spec).query (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
      pure (if accept then some sent else none)
  outputMap _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact outputMap

/-- The prover makes the `setup` events and event 0, sends `(message, hidden)`, and keeps
`hidden` as private output. -/
def prover (setup : List Nat) (message hidden : Nat) :
    Prover oracleSig ambient pairSend (fun _ => Nat) := do
  for t in setup ++ [0] do liftM (ambient.query t)
  pure ⟨(message, hidden), pure hidden⟩

/-- Log each ambient event without assuming effect commutativity; `pairSend` has no challenges. -/
def logger : QueryImpl (ambient + challengeSpec oracleSig pairSend) (StateM (List Nat))
  | .inl tag => modify (· ++ [tag])
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, n⟩, _⟩ => n.elim

/-- The run under the logger. -/
def observed (accept : Bool) (setup : List Nat) (message hidden : Nat) :=
  (simulateQ logger ((verifier accept).run () seven (prover setup message hidden))).run []

/-- Private output, the claim with its output data, and the ambient history of one run. -/
def summary (accept : Bool) (setup : List Nat) (message hidden : Nat) :
    Nat × Option (Nat × Nat) × List Nat :=
  let z := observed accept setup message hidden
  (z.1.2.1, z.1.2.2.map (fun r => (r.1, r.2 ())), z.2)

-- CoreRunExample 1, restated: the frozen verifier's reception event 1 moves into the passive
-- decision, which runs after the prover's event 0. For every hidden value the history is
-- `[0, 1, 2]`, each event once.
example (hidden : Nat) : (summary true [] 11 hidden).2.2 = [0, 1, 2] := rfl

-- CoreRunExample 2: the hidden coordinate is the private prover output, for every hidden value.
example (hidden : Nat) : (summary true [] 11 hidden).1 = hidden := rfl

-- CoreRunExample 3, restated: the accepted statement is the queried first coordinate 11.
example (hidden : Nat) : (summary true [] 11 hidden).2.1.map Prod.fst = some 11 := rfl

-- CoreRunExample 4, restated: the output data is the input 7 plus the sent 11, materialized from
-- this run's input and payloads.
example (hidden : Nat) : (summary true [] 11 hidden).2.1.map Prod.snd = some 18 := rfl

-- CoreRunExample 5, restated: a different run closes with its own message 19.
example (hidden : Nat) : (summary true [] 19 hidden).2.1.map Prod.snd = some 26 := rfl

-- The complete summary of the accepted run, for every message and hidden value.
example (message hidden : Nat) :
    summary true [] message hidden = (hidden, some (message, 7 + message), [0, 1, 2]) := rfl

-- CoreRunExample 6: a rejecting decision yields no claim, for every message and hidden value.
example (message hidden : Nat) : (observed false [] message hidden).1.2.2 = none := rfl

-- CoreRunExample 7, restated: the frozen setup runs before the strategies; here it is the prover's
-- first slot. Setup event 3 runs once, before the same send and decision events, and the
-- observation is the same as without setup.
example (accept : Bool) (message hidden : Nat) :
    observed accept [3] message hidden =
      ((observed accept [] message hidden).1, [3, 0, 1, 2]) := by
  cases accept <;> rfl

run_cmd do
  for hidden in [0, 5] do
    unless summary true [3] 11 hidden == (hidden, some (11, 18), [3, 0, 1, 2]) do
      throwError "the accepted run with setup is wrong: {summary true [3] 11 hidden}"
    unless summary false [] 19 hidden == (hidden, none, [0, 1, 2]) do
      throwError "the rejected run is wrong: {summary false [] 19 hidden}"

end Interaction.Core.CoreRunExampleTests
