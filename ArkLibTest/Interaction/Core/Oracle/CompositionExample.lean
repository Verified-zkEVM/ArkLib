/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Oracle.Routing
import ArkLibTest.Interaction.Core.Oracle.CoreRunExample

/-!
# Heterogeneous composed oracle execution

The intermediate statement is `Bool`, the final statement is `Nat`, and the final oracle answers
`Bool` rather than `Nat`. The prefix has no interaction nodes; its decision reads the input
oracle, and its output map exports the input plus 11. The suffix starts with a prover `Bool`
message that selects a `Nat` or a `Bool` second message. The suffix decision reads the exported
oracle; the final output map exports its parity. A stateful logger detects reordered, duplicated
or skipped effects.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp
open Interaction.Core.LoggedExecutionTests (inputs)
open Interaction.Core.DependentRoutingTests (done)

universe uX dX

namespace Interaction.Core.CompositionExampleTests

/-- Tagged ambient events. -/
abbrev ambient : OracleSpec Nat := Nat →ₒ Unit

/-- A distinct scalar Boolean oracle. -/
@[instance_reducible] def booleans : OracleFamily.{0, 0, 0} Unit (fun _ => Bool) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- Export the scalar input plus 11, next to any message resources. -/
def addEleven (messages : Resources.{0, uX, dX}) :
    OracleMap (Resources.sum inputs messages) inputs where
  f x _ := (show Nat from x.1 ()) + 11
  impl _ := do
    let old : Nat ← liftM ((Resources.sum inputs messages).spec.query (.inl ⟨(), ()⟩))
    pure (old + 11)
  law _ _ := by
    simp only [simulateQ_bind]
    rfl

/-- Export the parity of the scalar input, next to any message resources. -/
def isEven (messages : Resources.{0, uX, dX}) :
    OracleMap (Resources.sum inputs messages) booleans where
  f x _ := (show Nat from x.1 ()) % 2 == 0
  impl _ := do
    let value : Nat ← liftM ((Resources.sum inputs messages).spec.query (.inl ⟨(), ()⟩))
    pure (value % 2 == 0)
  law _ _ := by
    simp only [simulateQ_bind]
    rfl

/-- The prefix decision records 1, reads the input and decides its parity, or rejects. -/
def firstVerifier (accept : Bool) :
    OracleVerifier ambient done Unit (fun _ => Bool) inputs (fun _ => inputs) where
  decide _ p _ := OptionT.mk do
    let _ ← liftM ((ambient + (pathResources inputs done p).spec).query (.inl 1))
    let old : Nat ← liftM ((ambient + (pathResources inputs done p).spec).query
      (.inr (.inl ⟨(), ()⟩)))
    pure (if accept then some (old % 2 == 0) else none)
  outputMap _ p _ := addEleven (pathFamily done p)

/-- The second message type depends on the first message. -/
@[instance_reducible] def branchNext : Bool → OracleProtocol
  | true => .liftBind (.message Nat) (fun _ => .pure ⟨⟩)
  | false => .liftBind (.message Bool) (fun _ => .pure ⟨⟩)

/-- A true choice sends a natural number; a false choice sends a Boolean. -/
@[instance_reducible] def branchProtocol : OracleProtocol :=
  .liftBind (.message Bool) branchNext

/-- The numeric value of the second message on either branch. -/
def messageValue : Path branchProtocol → Nat
  | ⟨true, m, ⟨⟩⟩ => show Nat from m
  | ⟨false, b, ⟨⟩⟩ => if show Bool from b then 100 else 200

/-- The suffix decision records 3, reads the exported oracle, and adds the message value. -/
def secondVerifier :
    OracleVerifier ambient branchProtocol Bool (fun _ => Nat) inputs (fun _ => booleans) where
  decide _ p _ := do
    let _ ← liftM ((ambient + (pathResources inputs branchProtocol p).spec).query
      (.inl 3))
    let value : Nat ← liftM
      ((ambient + (pathResources inputs branchProtocol p).spec).query
        (.inr (.inl ⟨(), ()⟩)))
    pure (messageValue p + value)
  outputMap _ p _ := isEven (pathFamily branchProtocol p)

/-- The interaction-free prefix followed by the branching suffix. -/
abbrev composedProtocol : OracleProtocol := done.append (fun _ => branchProtocol)

/-- The suffix output map ignores the intermediate statement. -/
def compatible (accept : Bool) :
    OracleVerifier.OutputCompatibility (firstVerifier accept) (fun _ => secondVerifier) where
  outputMap stmt p v :=
    (secondVerifier.outputMap false (Path.split done (fun _ => branchProtocol) p).2
      (View.split done (fun _ => branchProtocol) p v).2).comp
      (OracleVerifier.suffixRoute (firstVerifier accept) stmt p v)
  agrees _ _ _ _ _ _ := rfl

/-- The composed oracle verifier. -/
def composed (accept : Bool) :=
  (firstVerifier accept).append (fun _ => secondVerifier) (compatible accept)

/-- The prefix prover records 0, and passes on `hidden + 1` and its branch choice. -/
def firstProver (choice : Bool) (hidden : Nat) :
    Prover oracleSig ambient done (fun _ => Nat × Bool) := do
  liftM (ambient.query 0)
  pure (hidden + 1, choice)

/-- The suffix prover sends its choice, then a message of the chosen type. It carries its hidden
input through either branch, as private output distinct from the verifier's statement. -/
def secondProver : (choice : Bool) → (hidden : Nat) →
    Prover oracleSig ambient branchProtocol (fun _ => Nat × Nat)
  | true, memory => pure ⟨true, (pure ⟨memory, pure (memory, memory + 1)⟩ :
      Prover oracleSig ambient (branchNext true) (fun _ => Nat × Nat))⟩
  | false, memory => pure ⟨false, (pure ⟨decide (memory > 0), pure (memory, memory + 1)⟩ :
      Prover oracleSig ambient (branchNext false) (fun _ => Nat × Nat))⟩

/-- The seam records 2, then hands over the suffix prover. -/
def seam (mid : Nat × Bool) :
    OracleComp ambient (Prover oracleSig ambient branchProtocol (fun _ => Nat × Nat)) := do
  liftM (ambient.query 2)
  pure (secondProver mid.2 mid.1)

/-- The whole prover with an explicit branch choice. -/
def proverWith (choice : Bool) (hidden : Nat) :
    Prover oracleSig ambient composedProtocol (fun _ => Nat × Nat) :=
  Prover.append (firstProver choice hidden) (fun _ mid => seam mid)

/-- The honest prover knows the input and chooses the branch by its parity. -/
def prover (answer hidden : Nat) := proverWith (answer % 2 == 0) hidden

/-- The composed protocol has only message nodes. -/
theorem noChallenge : ChallengeNode oracleSig composedProtocol → False := by
  rintro ⟨n, h⟩
  rcases n with _ | ⟨b, n⟩
  · exact nomatch h
  · cases b <;> rcases n with _ | ⟨_, n⟩
    all_goals exact nomatch h

/-- Log each ambient event. -/
def logger : QueryImpl (ambient + challengeSpec oracleSig composedProtocol) (StateM (List Nat))
  | .inl tag => modify (· ++ [tag])
  | .inr c => (noChallenge c).elim

/-- The final statement with the final oracle's answer, the private output, and the history. -/
def summaryWith (choice accept : Bool) (answer hidden : Nat) :
    Option (Nat × Bool) × (Nat × Nat) × List Nat :=
  let z := (simulateQ logger ((composed accept).run () (fun _ => answer)
    (proverWith choice hidden))).run []
  (z.1.2.2.map (fun r => (r.1, r.2 ())), z.1.2.1, z.2)

/-- The summary of the honest prover's run. -/
def summary (accept : Bool) (answer hidden : Nat) :=
  summaryWith (answer % 2 == 0) accept answer hidden

-- CompositionExample 1, the first stage on its own: the prefix verifier's run against the prefix
-- prover is the prover's event 0, then the decision's event 1; the statement is the input's parity,
-- and the output data is the input plus 11. Stated for every verdict, input, choice and hidden
-- value.
example (accept choice : Bool) (answer hidden : Nat) :
    (firstVerifier accept).run () (fun _ => answer) (firstProver choice hidden) = (do
      liftM ((ambient + challengeSpec oracleSig done).query (.inl 0))
      liftM ((ambient + challengeSpec oracleSig done).query (.inl 1))
      pure ⟨⟨⟩, (hidden + 1, choice),
        if accept then some (answer % 2 == 0, fun _ => answer + 11) else none⟩) := by
  cases accept <;> rfl

-- CompositionExample 2, the second stage on its own, on both message types. The frozen stage's
-- setup event 2 is the seam action, here the suffix prover's first slot; the branch is chosen by
-- the prover's `Bool` message. Stated for every input statement, exported value and hidden value.
example (mid : Bool) (value hidden : Nat) :
    secondVerifier.run mid (fun _ => value) (Strategy.joinSlot (seam (hidden, true))) = (do
      liftM ((ambient + challengeSpec oracleSig branchProtocol).query (.inl 2))
      liftM ((ambient + challengeSpec oracleSig branchProtocol).query (.inl 3))
      pure ⟨⟨true, hidden, ⟨⟩⟩, (hidden, hidden + 1),
        some (hidden + value, fun _ => value % 2 == 0)⟩) := rfl

example (mid : Bool) (value hidden : Nat) :
    secondVerifier.run mid (fun _ => value) (Strategy.joinSlot (seam (hidden, false))) = (do
      liftM ((ambient + challengeSpec oracleSig branchProtocol).query (.inl 2))
      liftM ((ambient + challengeSpec oracleSig branchProtocol).query (.inl 3))
      pure ⟨⟨false, decide (hidden > 0), ⟨⟩⟩, (hidden, hidden + 1),
        some ((if decide (hidden > 0) then 100 else 200) + value, fun _ => value % 2 == 0)⟩) :=
  rfl

-- CompositionExample 3 to 5: the same two stages as a chain are `StagesExample.twoStages`, whose
-- run is this binary composition (`Stages.run_cons`). Both run both interactions, then the prefix
-- decision, then the suffix decision only after prefix acceptance. This is
-- `OracleVerifier.run_append` at this fixture and the ordinary whole prover.
example (accept : Bool) (answer hidden : Nat) :=
  OracleVerifier.run_append (firstVerifier accept) (fun _ => secondVerifier) (compatible accept) ()
    (fun _ => answer) (prover answer hidden)

-- CompositionExample 6 to 13 are also ported for the stage chain in `StagesExample`, with a third
-- stage. Here, the same rows for the binary composition. CompositionExample 6: the normal form of
-- the accepted run, for every branch choice, input and hidden value. The history becomes
-- `[0, 2, 1, 3]`: the prover's events, then the decisions, because both decisions are passive and
-- run after the whole interaction.
/-- The accepted run for every branch choice, input and hidden value. -/
theorem summaryWith_true (choice : Bool) (answer hidden : Nat) :
    summaryWith choice true answer hidden =
      (some ((if choice then hidden + 1 else 100) +
          (answer + 11), (answer + 11) % 2 == 0),
        (hidden + 1, hidden + 1 + 1), [0, 2, 1, 3]) := by
  unfold summaryWith composed
  rw [OracleVerifier.run_append]
  cases choice <;> rfl

/-- The accepted run of the honest prover, for every input and hidden value. -/
theorem summary_true (answer hidden : Nat) :
    summary true answer hidden =
      (some ((if answer % 2 == 0 then hidden + 1 else 100) + (answer + 11),
          (answer + 11) % 2 == 0),
        (hidden + 1, hidden + 1 + 1), [0, 2, 1, 3]) :=
  summaryWith_true _ answer hidden

-- CompositionExample 7, restated: every effect runs exactly once, in the order `[0, 2, 1, 3]`.
example : (summary true 7 40).2.2 = [0, 2, 1, 3] := by rw [summary_true]

-- CompositionExample 8: the odd input selects the `Bool` branch; the exported oracle answers
-- 7 + 11.
example : (summary true 7 40).1.map Prod.fst = some 118 := by
  rw [summary_true]
  rfl

-- CompositionExample 9: the even input selects the `Nat` branch; the exported oracle answers
-- 20 + 11.
example : (summary true 20 40).1.map Prod.fst = some 72 := by
  rw [summary_true]
  rfl

-- CompositionExample 10, restated: the final Boolean oracle is the parity of the exported
-- behavior, materialized by the composite output map from the same run.
example : (summary true 7 40).1.map Prod.snd = some true := by
  rw [summary_true]
  rfl

-- CompositionExample 11: changing the input changes the final oracle.
example : (summary true 20 40).1.map Prod.snd = some false := by
  rw [summary_true]
  rfl

-- CompositionExample 12, restated: the private outputs cross the handoff through the prover's
-- leaf memory, distinct from the public statements.
example : (summary true 7 40).2.1 = (41, 42) := by
  rw [summary_true]

-- CompositionExample 13, restated for the binary composition: a rejecting prefix decision yields
-- no claim and skips the suffix decision's event 3. The suffix interaction and its seam event 2
-- still run, because the composition decides after the whole interaction. Stated for every branch
-- choice, input and hidden value.
example (choice : Bool) (answer hidden : Nat) :
    summaryWith choice false answer hidden = (none, (hidden + 1, hidden + 1 + 1), [0, 2, 1]) := by
  unfold summaryWith composed
  rw [OracleVerifier.run_append]
  cases choice <;> rfl

-- CompositionExample 14, restated: the frozen lower adapter keeps the oracle output and the
-- hidden prover output of an oracle message. Here the oracle verifier's run of the one-send
-- fixture keeps both: output data 18 and private output `hidden`, for every hidden value.
example (hidden : Nat) :
    ((CoreRunExampleTests.observed true [] 11 hidden).1.2.2.map (fun r => r.2 ()),
      (CoreRunExampleTests.observed true [] 11 hidden).1.2.1) = (some 18, hidden) := rfl

run_cmd do
  for hidden in [0, 40] do
    unless summary true 7 hidden ==
        (some (100 + 18, true), (hidden + 1, hidden + 2), [0, 2, 1, 3]) do
      throwError "the accepted odd-input run is wrong: {summary true 7 hidden}"
    unless summary true 20 hidden ==
        (some (hidden + 1 + 31, false), (hidden + 1, hidden + 2), [0, 2, 1, 3]) do
      throwError "the accepted even-input run is wrong: {summary true 20 hidden}"
    unless summary false 7 hidden == (none, (hidden + 1, hidden + 2), [0, 2, 1]) do
      throwError "the rejected run is wrong: {summary false 7 hidden}"

end Interaction.Core.CompositionExampleTests
