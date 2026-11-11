/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Stages
import ArkLibTest.Interaction.Core.Oracle.CompositionExample

/-!
# Passive composition of heterogeneous oracle stages

The first two stages are the prefix and suffix verifiers of the composition example. The first
stage reads the input oracle, decides its parity and exports the input plus 11. The second stage
takes the `Bool` statement, receives a `Nat` or a `Bool` message chosen by the prover, and exports
the parity of what it read. The third stage takes the `Nat` statement and the `Bool` oracle, draws
a challenge through an ambient event, checks the prover's response, and exports the negation of
the `Bool` oracle. The statement type changes at every stage: `Unit`, then `Bool`, then `Nat`,
then `Bool × Nat`. The oracle data changes from `Nat` to `Bool` at the second stage. The prover's
private output changes from `Nat` to a pair at the second stage and to a triple at the third.

A stateful logger detects reordered, duplicated or skipped effects. The composition runs every
interaction before any decision: the prover's events 0, 2 and 4 and the draw 5, then the decisions
1, 3 and 6. A rejecting first decision skips the later decisions 3 and 6, but none of the later
interactions.

The last section composes two stages whose second stage is selected by a message of the first.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp Interaction.Core.CompositionExampleTests
open Interaction.Core.LoggedExecutionTests (inputs)
open Interaction.Core.DependentRoutingTests (done)

namespace Interaction.Core.StagesExampleTests

/-- The second stage has only message nodes. -/
theorem branchProtocol_noChallenge : ChallengeNode oracleSig branchProtocol → False := by
  rintro ⟨n, h⟩
  rcases n with _ | ⟨b, n⟩
  · exact nomatch h
  · cases b <;> rcases n with _ | ⟨_, n⟩
    all_goals exact nomatch h

/-- A challenge, then the prover's response. -/
@[instance_reducible] def responseProtocol : OracleProtocol :=
  .liftBind (.challenge Nat) (fun _ => .liftBind (.message Nat) (fun _ => .pure ⟨⟩))

/-- The challenge draw records 5 and answers 9. -/
def responseDraw : (c : ChallengeNode oracleSig responseProtocol) →
    OracleComp ambient (challengeSpec oracleSig responseProtocol c)
  | ⟨.inl _, _⟩ => do
    liftM (ambient.query 5)
    pure (9 : Nat)
  | ⟨.inr ⟨_, .inl _⟩, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, _⟩ => n.elim

/-- The decision resources on a path of `responseProtocol`. -/
abbrev responseResources (p : Path responseProtocol) :=
  pathResources booleans responseProtocol p

/-- Export the negation of the `Bool` input oracle. -/
def negate (p : Path responseProtocol) : OracleMap (responseResources p) booleans where
  f x _ := !(show Bool from x.1 ())
  impl _ := do
    let b : Bool ← liftM ((responseResources p).spec.query (.inl ⟨(), ()⟩))
    pure !b
  law _ _ := by
    simp only [simulateQ_bind]
    rfl

/-- The decision records 6, reads the input oracle, and accepts the oracle answer with the
statement plus the response if the response is the challenge plus 1. -/
def responseVerifier : OracleVerifier ambient responseProtocol Nat (fun _ => Bool × Nat) booleans
    (fun _ => booleans) where
  decide stmt p v := OptionT.mk do
    let _ ← liftM ((ambient + (responseResources p).spec).query (.inl 6))
    let b : Bool ← liftM ((ambient + (responseResources p).spec).query (.inr (.inl ⟨(), ()⟩)))
    let challenge : Nat := v.val.1
    let response : Nat := v.val.2.1
    pure (if response = challenge + 1 then some (b, stmt + response) else none)
  outputMap _ p _ := negate p

/-- The prover records 4, answers the challenge with its successor, and adds the challenge to its
private memory. -/
def responseProver (memory : Nat × Nat) :
    Prover oracleSig ambient responseProtocol (fun _ => Nat × Nat × Nat) := do
  liftM (ambient.query 4)
  pure fun (challenge : Nat) => pure ⟨challenge + 1, pure (memory.1, memory.2, challenge)⟩

/-- A prover of `s` followed by the empty chain's protocol, which returns the prover's output. -/
def close {s : OracleProtocol} {Out : Type} (prover : Prover oracleSig ambient s (fun _ => Out)) :
    Prover oracleSig ambient (s.append fun _ => (.pure ⟨⟩ : OracleProtocol)) (fun _ => Out) :=
  Prover.append prover fun _ out => pure (pure out)

/-! ## Three heterogeneous stages -/

/-- The third stage alone, closed by the empty chain. -/
def thirdStages : Stages ambient Nat booleans :=
  .cons responseProtocol responseVerifier (responseVerifier.outputMap 0) (fun _ => rfl)
    responseDraw fun _ => .nil booleans

/-- The second and third stages. -/
def lastStages : Stages ambient Bool inputs :=
  .cons branchProtocol secondVerifier (secondVerifier.outputMap false) (fun _ => rfl)
    (fun c => (branchProtocol_noChallenge c).elim) fun _ => thirdStages

/-- The three stages. The first decision accepts if `accept` holds. -/
def stages (accept : Bool) : Stages ambient Unit inputs :=
  .cons done (firstVerifier accept) ((firstVerifier accept).outputMap ()) (fun _ => rfl)
    (fun c => c.val.elim) fun _ => lastStages

/-- The composed protocol of the three stages, written out. -/
abbrev threeProtocol : OracleProtocol :=
  done.append fun _ => branchProtocol.append fun _ =>
    responseProtocol.append fun _ => (.pure ⟨⟩ : OracleProtocol)

/-- The composed protocol of the stages is the written-out protocol. -/
example (accept : Bool) : (stages accept).protocol = threeProtocol := rfl

/-- The composed verifier of the stages is the binary append of the first verifier and the
composed verifier of the other two. -/
example (accept : Bool) :
    (stages accept).verifier = (firstVerifier accept).append (fun _ => lastStages.verifier)
      (Stages.compatible done (firstVerifier accept) _ (fun _ => rfl) fun _ => lastStages) :=
  Stages.verifier_cons _ _ _ _ _ _

/-- The honest prover: the first prover records 0 and passes on `hidden + 1` with the parity of
the input; the seam records 2 and starts the second prover on the chosen branch; the third prover
records 4 and answers the challenge. -/
def prover (answer hidden : Nat) : Prover oracleSig ambient threeProtocol
    (fun _ => Nat × Nat × Nat) :=
  Prover.append (firstProver (answer % 2 == 0) hidden) fun _ mid => do
    liftM (ambient.query 2)
    pure (Prover.append (secondProver mid.2 mid.1) fun _ memory =>
      pure (close (responseProver memory)))

/-- Log each ambient event. -/
def logger : QueryImpl ambient (StateM (List Nat))
  | tag => modify (· ++ [tag])

/-- The composed run of the three stages under the logger. -/
def observed (accept : Bool) (answer hidden : Nat) :=
  (simulateQ logger ((stages accept).run () (fun _ => answer) (prover answer hidden))).run []

/-- The final statement, the final oracle's answer, the private output, and the history. -/
def summary (accept : Bool) (answer hidden : Nat) :
    Option ((Bool × Nat) × Bool) × (Nat × Nat × Nat) × List Nat :=
  let z := observed accept answer hidden
  (z.1.2.2.map fun r => (r.1, r.2 ()), z.1.2.1, z.2)

-- The run of the three stages is the run of the binary append of the first stage and the other
-- two, with the challenges answered by the combined draws.
example (accept : Bool) (answer hidden : Nat) :=
  Stages.run_cons done (firstVerifier accept) _ (fun _ => rfl) (fun c => c.val.elim)
    (fun _ => lastStages) () (fun _ => answer) (prover answer hidden)

-- Every effect runs once: the prover's events 0, 2 and 4 and the draw 5, then the decisions 1, 3
-- and 6. On the odd input the second statement is 100 plus the exported 18, and the third stage
-- adds the response 10. The final oracle negates the parity of 18.
example : summary true 7 40 = (some ((true, 128), false), (41, 42, 9), [0, 2, 4, 5, 1, 3, 6]) :=
  rfl

-- On the even input the second statement is the hidden value 41 plus the exported 31.
example : summary true 20 40 = (some ((false, 82), true), (41, 42, 9), [0, 2, 4, 5, 1, 3, 6]) :=
  rfl

-- A rejecting first decision yields no claim and skips the decisions 3 and 6. The interactions of
-- the second and third stages still run: the seam event 2, the prover event 4 and the draw 5.
example : summary false 7 40 = (none, (41, 42, 9), [0, 2, 4, 5, 1]) := rfl

run_cmd do
  for hidden in [0, 40] do
    unless summary true 7 hidden ==
        (some ((true, 100 + 18 + 10), false), (hidden + 1, hidden + 2, 9),
          [0, 2, 4, 5, 1, 3, 6]) do
      throwError "the accepted odd-input run is wrong: {summary true 7 hidden}"
    unless summary true 20 hidden ==
        (some ((false, hidden + 1 + 31 + 10), true), (hidden + 1, hidden + 2, 9),
          [0, 2, 4, 5, 1, 3, 6]) do
      throwError "the accepted even-input run is wrong: {summary true 20 hidden}"
    unless summary false 7 hidden == (none, (hidden + 1, hidden + 2, 9), [0, 2, 4, 5, 1]) do
      throwError "the rejected run is wrong: {summary false 7 hidden}"

/-! ## The frozen two-stage family

The frozen ordered execution of the first two stages, ported to their passive composition. -/

/-- The second stage alone, closed by the empty chain. -/
def secondStages : Stages ambient Bool inputs :=
  .cons branchProtocol secondVerifier (secondVerifier.outputMap false) (fun _ => rfl)
    (fun c => (branchProtocol_noChallenge c).elim) fun _ => .nil booleans

/-- The first two stages. -/
def twoStages (accept : Bool) : Stages ambient Unit inputs :=
  .cons done (firstVerifier accept) ((firstVerifier accept).outputMap ()) (fun _ => rfl)
    (fun c => c.val.elim) fun _ => secondStages

/-- The composed protocol of the two stages, written out. -/
abbrev twoProtocol : OracleProtocol :=
  done.append fun _ => branchProtocol.append fun _ => (.pure ⟨⟩ : OracleProtocol)

/-- The prover of the two stages with an explicit branch choice. -/
def twoProverWith (choice : Bool) (hidden : Nat) :
    Prover oracleSig ambient twoProtocol (fun _ => Nat × Nat) :=
  Prover.append (firstProver choice hidden) fun _ mid => do
    liftM (ambient.query 2)
    pure (close (secondProver mid.2 mid.1))

/-- The honest prover knows the input and chooses the branch by its parity. -/
def twoProver (answer hidden : Nat) := twoProverWith (answer % 2 == 0) hidden

/-- The final statement with the final oracle's answer, the private output, and the history. -/
def summaryTwoWith (choice accept : Bool) (answer hidden : Nat) :
    Option (Nat × Bool) × (Nat × Nat) × List Nat :=
  let z := (simulateQ logger
    ((twoStages accept).run () (fun _ => answer) (twoProverWith choice hidden))).run []
  (z.1.2.2.map fun r => (r.1, r.2 ()), z.1.2.1, z.2)

/-- The summary of the honest prover's run. -/
def summaryTwo (accept : Bool) (answer hidden : Nat) :=
  summaryTwoWith (answer % 2 == 0) accept answer hidden

-- CompositionExample 3 to 5, restated: the chain lists its two stages in order, and its run is
-- the run of the binary append of the first stage and the composed second stage.
-- `OracleVerifier.run_append` splits that run into both interactions, then the first decision
-- and, after its acceptance only, the second decision.
example (accept : Bool) (answer hidden : Nat) :=
  Stages.run_cons done (firstVerifier accept) _ (fun _ => rfl) (fun c => c.val.elim)
    (fun _ => secondStages) () (fun _ => answer) (twoProver answer hidden)

-- CompositionExample 6, restated: the normal form of the accepted run, for every branch choice,
-- input and hidden value. Both interactions run before either decision.
/-- The accepted run of the two stages for every branch choice, input and hidden value. -/
theorem summaryTwoWith_true (choice : Bool) (answer hidden : Nat) :
    summaryTwoWith choice true answer hidden =
      (some ((if choice then hidden + 1 else 100) + (answer + 11), (answer + 11) % 2 == 0),
        (hidden + 1, hidden + 1 + 1), [0, 2, 1, 3]) := by
  have h : (twoStages true).run () (fun _ => answer) (twoProverWith choice hidden) = _ :=
    (Stages.run_cons done (firstVerifier true) _ (fun _ => rfl) (fun c => c.val.elim)
      (fun _ => secondStages) () (fun _ => answer) (twoProverWith choice hidden)).trans
      (congrArg _ (OracleVerifier.run_append (firstVerifier true) (fun _ => secondStages.verifier)
        (Stages.compatible done (firstVerifier true) _ (fun _ => rfl) fun _ => secondStages) ()
        (fun _ => answer) (twoProverWith choice hidden)))
  unfold summaryTwoWith
  rw [h]
  cases choice <;> rfl

/-- The accepted run of the honest prover, for every input and hidden value. -/
theorem summaryTwo_true (answer hidden : Nat) :
    summaryTwo true answer hidden =
      (some ((if answer % 2 == 0 then hidden + 1 else 100) + (answer + 11),
          (answer + 11) % 2 == 0),
        (hidden + 1, hidden + 1 + 1), [0, 2, 1, 3]) :=
  summaryTwoWith_true _ _ _

-- CompositionExample 7, restated: every effect runs exactly once, in the order `[0, 2, 1, 3]`.
example : (summaryTwo true 7 40).2.2 = [0, 2, 1, 3] := by rw [summaryTwo_true]

-- CompositionExample 8: the odd input selects the `Bool` branch; the statement is 100 plus the
-- exported 7 + 11.
example : (summaryTwo true 7 40).1.map Prod.fst = some 118 := by
  rw [summaryTwo_true]
  rfl

-- CompositionExample 9: the even input selects the `Nat` branch; the statement is the hidden
-- value 41 plus the exported 20 + 11.
example : (summaryTwo true 20 40).1.map Prod.fst = some 72 := by
  rw [summaryTwo_true]
  rfl

-- CompositionExample 10: the exported Boolean oracle is the parity of the exported 18.
example : (summaryTwo true 7 40).1.map Prod.snd = some true := by
  rw [summaryTwo_true]
  rfl

-- CompositionExample 11: changing the input changes the final oracle.
example : (summaryTwo true 20 40).1.map Prod.snd = some false := by
  rw [summaryTwo_true]
  rfl

-- CompositionExample 12: the private outputs cross the seam through the prover, distinct from the
-- public statements.
example : (summaryTwo true 7 40).2.1 = (41, 42) := by rw [summaryTwo_true]

-- CompositionExample 13, restated: a rejecting first decision yields no claim and skips the second
-- decision's event 3. The second stage's interaction and its seam event 2 still run. Stated for
-- every branch choice, input and hidden value.
example (choice : Bool) (answer hidden : Nat) :
    summaryTwoWith choice false answer hidden =
      (none, (hidden + 1, hidden + 1 + 1), [0, 2, 1]) := by
  have h : (twoStages false).run () (fun _ => answer) (twoProverWith choice hidden) = _ :=
    (Stages.run_cons done (firstVerifier false) _ (fun _ => rfl) (fun c => c.val.elim)
      (fun _ => secondStages) () (fun _ => answer) (twoProverWith choice hidden)).trans
      (congrArg _ (OracleVerifier.run_append (firstVerifier false) (fun _ => secondStages.verifier)
        (Stages.compatible done (firstVerifier false) _ (fun _ => rfl) fun _ => secondStages) ()
        (fun _ => answer) (twoProverWith choice hidden)))
  unfold summaryTwoWith
  rw [h]
  cases choice <;> rfl

example : summaryTwo false 7 40 = (none, (41, 42), [0, 2, 1]) := rfl

/-! ## A later stage selected by an earlier prover message

The first stage receives a `Bool` from the prover and accepts its input statement. The second
stage is selected by that message: on `true` it is the third stage above, which draws a challenge;
on `false` it receives one `Nat` and has no challenge. -/

/-- The prover sends one `Bool`. -/
@[instance_reducible] def pick : OracleProtocol :=
  .liftBind (.message Bool) fun _ => .pure ⟨⟩

/-- The first decision records 20 and accepts its input statement. It forwards the input oracle. -/
def pickVerifier :
    OracleVerifier ambient pick Nat (fun _ => Nat) booleans (fun _ => booleans) where
  decide stmt p _ := OptionT.mk do
    let _ ← liftM ((ambient + (pathResources booleans pick p).spec).query (.inl 20))
    pure (some stmt)
  outputMap _ _ _ := OracleMap.fst _ _

/-- The prover sends one `Nat`. -/
@[instance_reducible] def reply : OracleProtocol :=
  .liftBind (.message Nat) fun _ => .pure ⟨⟩

/-- The decision records 22, reads the input oracle, and accepts its answer with the statement
plus the message. It forwards the input oracle. -/
def replyVerifier :
    OracleVerifier ambient reply Nat (fun _ => Bool × Nat) booleans (fun _ => booleans) where
  decide stmt p v := OptionT.mk do
    let _ ← liftM ((ambient + (pathResources booleans reply p).spec).query (.inl 22))
    let b : Bool ← liftM ((ambient + (pathResources booleans reply p).spec).query
      (.inr (.inl ⟨(), ()⟩)))
    pure (some (b, stmt + (show Nat from v.val.1)))
  outputMap _ _ _ := OracleMap.fst _ _

/-- A single message has no challenges. -/
theorem reply_noChallenge : ChallengeNode oracleSig reply → False := by
  rintro ⟨_ | ⟨_, n⟩, h⟩
  · exact nomatch h
  · exact n.elim

/-- The second stage, selected by the first stage's message. -/
def selected : (p : Path pick) → Stages ambient Nat booleans
  | ⟨true, _⟩ => thirdStages
  | ⟨false, _⟩ =>
    .cons reply replyVerifier (replyVerifier.outputMap 0) (fun _ => rfl)
      (fun c => (reply_noChallenge c).elim) fun _ => .nil booleans

/-- A single `Bool` message has no challenges. -/
theorem pick_noChallenge : ChallengeNode oracleSig pick → False := by
  rintro ⟨_ | ⟨_, n⟩, h⟩
  · exact nomatch h
  · exact n.elim

/-- The first stage, then the stage its message selects. -/
def shapeStages : Stages ambient Nat booleans :=
  .cons pick pickVerifier (pickVerifier.outputMap 0) (fun _ => rfl)
    (fun c => (pick_noChallenge c).elim) selected

/-- The prover on the selected branch: on `true` it answers the challenge, on `false` it records
33 and sends 5. -/
def selectedProver : (b : Bool) → (memory : Nat × Nat) →
    Prover oracleSig ambient (selected ⟨b, ⟨⟩⟩).protocol (fun _ => Nat × Nat × Nat)
  | true, memory => close (responseProver memory)
  | false, memory => close (do
      liftM (ambient.query 33)
      pure ⟨(5 : Nat), pure (memory.1, memory.2, 0)⟩ :
        Prover oracleSig ambient reply (fun _ => Nat × Nat × Nat))

/-- The prover records 30, sends `choice`, and continues on the branch it selected. -/
def shapeProver (choice : Bool) (memory : Nat × Nat) :
    Prover oracleSig ambient shapeStages.protocol (fun _ => Nat × Nat × Nat) := do
  liftM (ambient.query 30)
  pure ⟨choice, selectedProver choice memory⟩

/-- The composed run under the logger, on the statement 7 and the `true` input oracle. -/
def shapeObserved (choice : Bool) :=
  (simulateQ logger (shapeStages.run 7 (fun _ => true) (shapeProver choice (1, 2)))).run []

/-- The shape path's message, the final statement, the private output, and the history. The type
of the final statement is computed from the shape path. -/
def shapeSummary (choice : Bool) :=
  let z := shapeObserved choice
  ((projectPathAlong oracleSig shapeStages.protocol z.1.1).1, z.1.2.2.map (·.1), z.1.2.1, z.2)

-- The prover's `true` selects the stage with a challenge: the prover event 4 and the draw 5 run,
-- the response is 10, and the second decision 6 accepts the statement 7 plus 10.
example : shapeSummary true = (true, some (true, 17), (1, 2, 9), [30, 4, 5, 20, 6]) := rfl

-- The prover's `false` selects the stage without a challenge: no draw runs, the prover records 33
-- and sends 5, and the second decision 22 accepts the statement 7 plus 5.
example : shapeSummary false = (false, some (true, 12), (1, 2, 0), [30, 33, 20, 22]) := rfl

end Interaction.Core.StagesExampleTests
