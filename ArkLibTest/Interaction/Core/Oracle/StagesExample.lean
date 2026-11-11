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

The chains above have output maps that do not read their input statements, which
`Stages.StatementFree` records. A later section composes stages whose output maps read the input
statement, with the general compatibility certificates. Another composes stages whose oracle
families have their queries in different universes, and another derives a property of a
three-stage decision from one hypothesis per stage boundary. The section on shape selection
composes two stages whose second stage is selected by a message of the first.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp Interaction.Core.CompositionExampleTests
open Interaction.Core.LoggedExecutionTests (inputs)
open Interaction.Core.DependentRoutingTests (done)

namespace Interaction.Core.StagesExampleTests

universe uX dX

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
  .cons responseProtocol responseVerifier responseDraw fun _ => .nil booleans

/-- The third stage's output map does not read its input statement. -/
def thirdMaps : thirdStages.StatementFree :=
  ⟨responseVerifier.outputMap 0, fun _ => rfl, fun _ => ⟨⟩⟩

/-- The second and third stages. -/
def lastStages : Stages ambient Bool inputs :=
  .cons branchProtocol secondVerifier (fun c => (branchProtocol_noChallenge c).elim)
    fun _ => thirdStages

/-- The output maps of the second and third stages do not read their input statements. -/
def lastMaps : lastStages.StatementFree :=
  ⟨secondVerifier.outputMap false, fun _ => rfl, fun _ => thirdMaps⟩

/-- The three stages. The first decision accepts if `accept` holds. -/
def stages (accept : Bool) : Stages ambient Unit inputs :=
  .cons done (firstVerifier accept) (fun c => c.val.elim) fun _ => lastStages

/-- No output map of the three stages reads its input statement. -/
def stagesMaps (accept : Bool) : (stages accept).StatementFree :=
  ⟨(firstVerifier accept).outputMap (), fun _ => rfl, fun _ => lastMaps⟩

/-- The composed protocol of the three stages, written out. -/
abbrev threeProtocol : OracleProtocol :=
  done.append fun _ => branchProtocol.append fun _ =>
    responseProtocol.append fun _ => (.pure ⟨⟩ : OracleProtocol)

/-- The composed protocol of the stages is the written-out protocol. -/
example (accept : Bool) : (stages accept).protocol = threeProtocol := rfl

/-- The composed verifier of the stages is the binary append of the first verifier and the
composed verifier of the other two. -/
example (accept : Bool) :
    (stages accept).verifier (stagesMaps accept).compatibility =
      (firstVerifier accept).append (fun _ => lastStages.verifier lastMaps.compatibility)
        (OracleVerifier.OutputCompatibility.ofStatementFree (firstVerifier accept) _ _
          (fun _ => rfl) (fun _ => Stages.StatementFree.map lastStages lastMaps)
          fun _ => lastMaps.outputMap_eq) :=
  rfl

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
  (simulateQ logger ((stages accept).run (stagesMaps accept).compatibility () (fun _ => answer)
    (prover answer hidden))).run []

/-- The final statement, the final oracle's answer, the private output, and the history. -/
def summary (accept : Bool) (answer hidden : Nat) :
    Option ((Bool × Nat) × Bool) × (Nat × Nat × Nat) × List Nat :=
  let z := observed accept answer hidden
  (z.1.2.2.map fun r => (r.1, r.2 ()), z.1.2.1, z.2)

-- The run of the three stages is the run of the binary append of the first stage and the other
-- two, with the challenges answered by the combined draws.
example (accept : Bool) (answer hidden : Nat) :=
  Stages.run_cons done (firstVerifier accept) (fun c => c.val.elim) (fun _ => lastStages)
    (stagesMaps accept).compatibility.1 (stagesMaps accept).compatibility.2 () (fun _ => answer)
    (prover answer hidden)

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
  .cons branchProtocol secondVerifier (fun c => (branchProtocol_noChallenge c).elim)
    fun _ => .nil booleans

/-- The second stage's output map does not read its input statement. -/
def secondMaps : secondStages.StatementFree :=
  ⟨secondVerifier.outputMap false, fun _ => rfl, fun _ => ⟨⟩⟩

/-- The first two stages. -/
def twoStages (accept : Bool) : Stages ambient Unit inputs :=
  .cons done (firstVerifier accept) (fun c => c.val.elim) fun _ => secondStages

/-- No output map of the two stages reads its input statement. -/
def twoMaps (accept : Bool) : (twoStages accept).StatementFree :=
  ⟨(firstVerifier accept).outputMap (), fun _ => rfl, fun _ => secondMaps⟩

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
    ((twoStages accept).run (twoMaps accept).compatibility () (fun _ => answer)
      (twoProverWith choice hidden))).run []
  (z.1.2.2.map fun r => (r.1, r.2 ()), z.1.2.1, z.2)

/-- The summary of the honest prover's run. -/
def summaryTwo (accept : Bool) (answer hidden : Nat) :=
  summaryTwoWith (answer % 2 == 0) accept answer hidden

-- CompositionExample 3 to 5, restated: the chain lists its two stages in order, and its run is
-- the run of the binary append of the first stage and the composed second stage.
-- `OracleVerifier.run_append` splits that run into both interactions, then the first decision
-- and, after its acceptance only, the second decision.
example (accept : Bool) (answer hidden : Nat) :=
  Stages.run_cons done (firstVerifier accept) (fun c => c.val.elim) (fun _ => secondStages)
    (twoMaps accept).compatibility.1 (twoMaps accept).compatibility.2 () (fun _ => answer)
    (twoProver answer hidden)

-- CompositionExample 6, restated: the normal form of the accepted run, for every branch choice,
-- input and hidden value. Both interactions run before either decision.
/-- The accepted run of the two stages for every branch choice, input and hidden value. -/
theorem summaryTwoWith_true (choice : Bool) (answer hidden : Nat) :
    summaryTwoWith choice true answer hidden =
      (some ((if choice then hidden + 1 else 100) + (answer + 11), (answer + 11) % 2 == 0),
        (hidden + 1, hidden + 1 + 1), [0, 2, 1, 3]) := by
  have h : (twoStages true).run (twoMaps true).compatibility () (fun _ => answer)
      (twoProverWith choice hidden) = _ :=
    (Stages.run_cons done (firstVerifier true) (fun c => c.val.elim) (fun _ => secondStages)
      (twoMaps true).compatibility.1 (twoMaps true).compatibility.2 () (fun _ => answer)
      (twoProverWith choice hidden)).trans
      (congrArg _ (OracleVerifier.run_append (firstVerifier true)
        (fun p => secondStages.verifier ((twoMaps true).compatibility.1 p))
        (twoMaps true).compatibility.2 () (fun _ => answer) (twoProverWith choice hidden)))
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
  have h : (twoStages false).run (twoMaps false).compatibility () (fun _ => answer)
      (twoProverWith choice hidden) = _ :=
    (Stages.run_cons done (firstVerifier false) (fun c => c.val.elim) (fun _ => secondStages)
      (twoMaps false).compatibility.1 (twoMaps false).compatibility.2 () (fun _ => answer)
      (twoProverWith choice hidden)).trans
      (congrArg _ (OracleVerifier.run_append (firstVerifier false)
        (fun p => secondStages.verifier ((twoMaps false).compatibility.1 p))
        (twoMaps false).compatibility.2 () (fun _ => answer) (twoProverWith choice hidden)))
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
      .cons reply replyVerifier (fun c => (reply_noChallenge c).elim) fun _ => .nil booleans

/-- A single `Bool` message has no challenges. -/
theorem pick_noChallenge : ChallengeNode oracleSig pick → False := by
  rintro ⟨_ | ⟨_, n⟩, h⟩
  · exact nomatch h
  · exact n.elim

/-- The first stage, then the stage its message selects. -/
def shapeStages : Stages ambient Nat booleans :=
  .cons pick pickVerifier (fun c => (pick_noChallenge c).elim) selected

/-- No output map of the selected stages reads its input statement. -/
def selectedMaps : (p : Path pick) → (selected p).StatementFree
  | ⟨true, _⟩ => thirdMaps
  | ⟨false, _⟩ => ⟨replyVerifier.outputMap 0, fun _ => rfl, fun _ => ⟨⟩⟩

/-- No output map of the shape-selected chain reads its input statement. -/
def shapeMaps : shapeStages.StatementFree :=
  ⟨pickVerifier.outputMap 0, fun _ => rfl, selectedMaps⟩

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
  (simulateQ logger (shapeStages.run shapeMaps.compatibility 7 (fun _ => true)
    (shapeProver choice (1, 2)))).run []

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

/-! ## Output maps that read the input statement

An interaction-free stage accepts its `Nat` statement and exports a scalar oracle whose data is
that statement and whose query answers it. Its output map reads the input statement, so no
statement-free map exists for it, even in a chain of one stage. The general certificate
`OutputCompatibility.ofStatement` composes it, because the accepted statement is the public input
statement. -/

/-- The scalar oracle with data `n`, whose one query answers `n`, from any resources. -/
def statementOracle (n : Nat) (R : Resources.{0, uX, dX}) : OracleMap R inputs where
  f _ _ := n
  impl _ := pure n
  law _ _ := rfl

/-- Accept the input statement and export it as a scalar oracle. -/
def echoVerifier : OracleVerifier ambient done Nat (fun _ => Nat) inputs (fun _ => inputs) where
  decide stmt _ _ := pure stmt
  outputMap stmt p _ := statementOracle stmt (pathResources inputs done p)

/-- The echo decision accepts its input statement. -/
theorem echo_decideWith (stmt : Nat) (p : Path done) (v : View done p)
    (data : (pathResources inputs done p).Data) :
    echoVerifier.decideWith stmt p v data = pure (some stmt) :=
  simulateQ_pure _ _

/-- The only statement the echo decision can accept is its input statement. -/
theorem echo_accepted (stmt t : Nat) (p : Path done) (v : View done p)
    (data : (pathResources inputs done p).Data)
    (h : some t ∈ support (echoVerifier.decideWith stmt p v data)) : t = stmt := by
  rw [echo_decideWith] at h
  simpa using h

/-- The echo stage alone, closed by the empty chain. -/
def echoStages : Stages ambient Nat inputs :=
  .cons done echoVerifier (fun c => c.val.elim) fun _ => .nil inputs

/-- The echo stage composed with the empty chain: the intermediate statement is the input. -/
def echoEvidence : echoStages.Compatibility :=
  ⟨fun _ => ⟨⟩, OracleVerifier.OutputCompatibility.ofStatement echoVerifier _
    (fun stmt _ _ => stmt) fun stmt p _ data t h =>
      echo_accepted stmt t _ _ ((OracleVerifier.prefixRoute p).f data) h⟩

/-- The input data of a run of the echo stage: the input oracle holds 3. -/
def echoData : (pathResources inputs echoStages.protocol ⟨⟩).Data :=
  (fun _ => 3, fun i => i.elim)

-- The composed output data is the input statement, whatever the input oracle holds.
example :
    ((echoStages.verifier echoEvidence).outputMap 5 ⟨⟩ ⟨⟨⟩, rfl⟩).f echoData () = (5 : Nat) :=
  rfl
example :
    ((echoStages.verifier echoEvidence).outputMap 6 ⟨⟩ ⟨⟨⟩, rfl⟩).f echoData () = (6 : Nat) :=
  rfl

/-- No statement-free output map describes the echo stage: inputs 0 and 1 export different
data. -/
theorem echoStages_not_statementFree : echoStages.StatementFree → False := fun m => by
  have h := congrArg (fun map => (map ⟨⟩ ⟨⟨⟩, rfl⟩).f (fun _ => 3, fun i => i.elim) ())
    ((m.2.1 0).trans (m.2.1 1).symm)
  exact Nat.zero_ne_one (h : (0 : Nat) = 1)

/-- Read the input oracle, accept the input statement if the oracle answers it, and export twice
the input statement. -/
def checkVerifier : OracleVerifier ambient done Nat (fun _ => Nat) inputs (fun _ => inputs) where
  decide stmt p _ := OptionT.mk do
    let value : Nat ← liftM ((ambient + (pathResources inputs done p).spec).query
      (.inr (.inl ⟨(), ()⟩)))
    pure (if value = stmt then some stmt else none)
  outputMap stmt p _ := statementOracle (2 * stmt) (pathResources inputs done p)

/-- The check stage alone, closed by the empty chain. -/
def checkStages : Stages ambient Nat inputs :=
  .cons done checkVerifier (fun c => c.val.elim) fun _ => .nil inputs

/-- The check stage composed with the empty chain, whose output map ignores the statement. -/
def checkEvidence : checkStages.Compatibility :=
  ⟨fun _ => ⟨⟩,
    { outputMap := fun stmt p v =>
        (OracleMap.fst _ _).comp (OracleVerifier.suffixRoute checkVerifier stmt p v)
      agrees := fun _ _ _ _ _ _ => rfl }⟩

/-- The echo stage, then the check stage, which reads the echoed statement. -/
def echoCheck : Stages ambient Nat inputs :=
  .cons done echoVerifier (fun c => c.val.elim) fun _ => checkStages

/-- The echo stage passes its input statement to the check stage. -/
def echoCheckEvidence : echoCheck.Compatibility :=
  ⟨fun _ => checkEvidence, OracleVerifier.OutputCompatibility.ofStatement echoVerifier _
    (fun stmt _ _ => stmt) fun stmt p _ data t h =>
      echo_accepted stmt t _ _ ((OracleVerifier.prefixRoute p).f data) h⟩

/-- The prover of the interaction-free stages returns nothing. -/
def echoCheckProver : Prover oracleSig ambient echoCheck.protocol (fun _ => Unit) := pure ()

/-- The verdict of the two stages on the input statement, with the final oracle's answer. -/
def echoCheckSummary (stmt : Nat) : Option (Nat × Nat) :=
  let z := (simulateQ logger (echoCheck.run echoCheckEvidence stmt (fun _ => 3)
    echoCheckProver)).run []
  z.1.2.2.map fun r => (r.1, r.2 ())

-- The check stage reads the echoed statement and accepts it; the final oracle answers twice the
-- statement. The input oracle's 3 is not read.
example : echoCheckSummary 5 = some (5, 10) := rfl
example : echoCheckSummary 6 = some (6, 12) := rfl

/-! ## Query universes at the chain boundaries

The input family has its query in `Type 0`; `wideBooleans` has its query in `Type 1`. The first
stage reads the small input family and exports a wide family directly. The chain's families have
their queries in `Type 1`: the input family enters through `liftQueries`. A second stage reads the
wide family and exports the small `booleans`, which enters the chain lifted and leaves it through
`lowerOutputs`. -/

/-- A Boolean answers its one query, which lies in `Type 1`, with itself. -/
@[reducible]
def wideInterface : OracleInterface.{0, 1} Bool where
  Query := ULift.{1} Unit
  toOC.spec := ULift.{1} Unit →ₒ Bool
  toOC.impl _ := read

/-- One Boolean oracle whose query lies in `Type 1`. -/
@[instance_reducible]
def wideBooleans : OracleFamily.{0, 0, 1} Unit (fun _ => Bool) := ⟨fun _ => wideInterface⟩

/-- Export the parity of the scalar input as a wide oracle. -/
def wideParity (messages : Resources.{0, uX, dX}) :
    OracleMap (Resources.sum inputs messages) wideBooleans where
  f x _ := (show Nat from x.1 ()) % 2 == 0
  impl _ := do
    let value : Nat ← liftM ((Resources.sum inputs messages).spec.query (.inl ⟨(), ()⟩))
    pure (value % 2 == 0)
  law _ _ := by
    simp only [simulateQ_bind]
    rfl

/-- Read the small input oracle, accept its parity, and export it as a wide oracle. The input
query lies in `Type 0` and the output query in `Type 1`. -/
def wideVerifier :
    OracleVerifier ambient done Unit (fun _ => Bool) inputs (fun _ => wideBooleans) where
  decide _ p _ := OptionT.mk do
    let value : Nat ← liftM ((ambient + (pathResources inputs done p).spec).query
      (.inr (.inl ⟨(), ()⟩)))
    pure (some (value % 2 == 0))
  outputMap _ p _ := wideParity (pathFamily done p)

/-- Read the wide oracle, accept its answer with the statement, and export the answer as a small
oracle. -/
def narrowVerifier :
    OracleVerifier ambient done Bool (fun _ => Bool) wideBooleans (fun _ => booleans) where
  decide stmt p _ := OptionT.mk do
    let b : Bool ← liftM ((ambient + (pathResources wideBooleans done p).spec).query
      (.inr (.inl ⟨(), ⟨()⟩⟩)))
    pure (some (b && stmt))
  outputMap _ p _ :=
    { f := fun x _ => x.1 ()
      impl := fun _ => liftM ((pathResources wideBooleans done p).spec.query (.inl ⟨(), ⟨()⟩⟩))
      law := fun _ _ => rfl }

/-- The small input family with its query lifted to `Type 1`. -/
abbrev liftedInputs : OracleFamily.{0, 0, 1} Unit (fun _ => Nat) := inputs.liftQueries.{0, 1}

/-- The first stage alone: small-query inputs, larger-query outputs. -/
def wideStages : Stages.{0, 1} ambient Unit liftedInputs :=
  .cons done wideVerifier.liftInputs (fun c => c.val.elim) fun _ => .nil wideBooleans

/-- The first stage's output map does not read its input statement. -/
def wideMaps : wideStages.StatementFree :=
  ⟨wideVerifier.liftInputs.outputMap (), fun _ => rfl, fun _ => ⟨⟩⟩

/-- The one-stage chain decides as the original first stage on the original input data. -/
example (p : Path wideStages.protocol) (v : View _ p)
    (data : (pathResources liftedInputs wideStages.protocol p).Data) :
    (wideStages.verifier wideMaps.compatibility).decideWith () p v data =
      wideVerifier.decideWith () (Path.split done _ p).1 (View.split done _ p v).1
        ((OracleVerifier.prefixRoute (inputs := liftedInputs) p).f data) :=
  (Stages.decideWith_one done _ _ _ _ () p v data).trans
    (wideVerifier.liftInputs_decideWith () _ _ _)

/-- Both stages: the input query lies in `Type 0`, the middle query in `Type 1`, and the output
query, lifted inside the chain, in `Type 0`. -/
def wideNarrow : Stages.{0, 1} ambient Unit liftedInputs :=
  .cons done wideVerifier.liftInputs (fun c => c.val.elim) fun _ =>
    .cons done narrowVerifier.liftOutputs (fun c => c.val.elim) fun _ =>
      .nil booleans.liftQueries.{0, 1}

/-- No output map of the two stages reads its input statement. -/
def wideNarrowMaps : wideNarrow.StatementFree :=
  ⟨wideVerifier.liftInputs.outputMap (), fun _ => rfl, fun _ =>
    ⟨narrowVerifier.liftOutputs.outputMap false, fun _ => rfl, fun _ => ⟨⟩⟩⟩

/-- The composed verifier, exporting the original small family. -/
def wideNarrowVerifier :
    OracleVerifier ambient wideNarrow.protocol Unit wideNarrow.Out liftedInputs
      (fun _ => booleans) :=
  OracleVerifier.lowerOutputs (outputs := fun _ => booleans)
    (wideNarrow.verifier wideNarrowMaps.compatibility)

/-- Lowering the output family keeps the decision. -/
example : wideNarrowVerifier.decideWith =
    (wideNarrow.verifier wideNarrowMaps.compatibility).decideWith := rfl

/-- The prover of the interaction-free stages returns nothing. -/
def wideNarrowProver : Prover oracleSig ambient wideNarrow.protocol (fun _ => Unit) := pure ()

/-- The verdict and the final oracle's answer on the input data `answer`. -/
def wideNarrowSummary (answer : Nat) : Option (Bool × Bool) :=
  let z := (simulateQ logger (wideNarrow.run wideNarrowMaps.compatibility () (fun _ => answer)
    wideNarrowProver)).run []
  z.1.2.2.map fun r => (r.1, r.2 ())

-- The first stage accepts the parity of the input; the second reads it through the wide oracle
-- and exports it as the small oracle.
example : wideNarrowSummary 4 = some (true, true) := rfl
example : wideNarrowSummary 7 = some (false, false) := rfl

/-! ## A chain law from one hypothesis per boundary

Three stages: the first adds its message to a `Nat` statement, the second pairs the statement with
its message, and the third, without interaction, adds the pair. The predicate at each boundary
depends on the messages of the stages up to it. One hypothesis per stage gives the property of the
composed decision. -/

/-- Accept the statement plus the message. -/
def addVerifier : OracleVerifier ambient reply Nat (fun _ => Nat) inputs (fun _ => inputs) where
  decide stmt p _ := pure (stmt + (show Nat from p.1))
  outputMap _ _ _ := OracleMap.fst _ _

/-- Accept the statement paired with the message. -/
def pairVerifier :
    OracleVerifier ambient reply Nat (fun _ => Nat × Nat) inputs (fun _ => inputs) where
  decide stmt p _ := pure (stmt, (show Nat from p.1))
  outputMap _ _ _ := OracleMap.fst _ _

/-- Accept the sum of the pair. -/
def sumVerifier :
    OracleVerifier ambient done (Nat × Nat) (fun _ => Nat) inputs (fun _ => inputs) where
  decide r _ _ := pure (r.1 + r.2)
  outputMap _ _ _ := OracleMap.fst _ _

/-- The three stages. -/
def sumStages : Stages ambient Nat inputs :=
  .cons reply addVerifier (fun c => (reply_noChallenge c).elim) fun _ =>
    .cons reply pairVerifier (fun c => (reply_noChallenge c).elim) fun _ =>
      .cons done sumVerifier (fun c => c.val.elim) fun _ => .nil inputs

/-- No output map of the three stages reads its input statement. -/
def sumMaps : sumStages.StatementFree :=
  ⟨fun _ _ => OracleMap.fst _ _, fun _ => rfl, fun _ =>
    ⟨fun _ _ => OracleMap.fst _ _, fun _ => rfl, fun _ =>
      ⟨fun _ _ => OracleMap.fst _ _, fun _ => rfl, fun _ => ⟨⟩⟩⟩⟩

/-- The predicates after each stage, for a first message `a` and a second message `b`: at least
`1 + a`; a pair whose first entry is at least `1 + a` and whose second entry is `b`; at least
`1 + a + b`. -/
def sumBounds : sumStages.Boundaries (· → Prop) :=
  ⟨fun pa n => 1 + (show Nat from pa.1) ≤ n, fun pa =>
    ⟨fun pb r => 1 + (show Nat from pa.1) ≤ r.1 ∧ r.2 = (show Nat from pb.1), fun pb =>
      ⟨fun _ n => 1 + (show Nat from pa.1) + (show Nat from pb.1) ≤ n, fun _ => ⟨⟩⟩⟩⟩

/-- Each stage, separately, accepts deterministically a statement satisfying its predicate from a
statement satisfying the predicate before it. -/
theorem sumSteps : sumStages.DeterministicSteps (1 ≤ ·) sumBounds :=
  ⟨fun stmt h pa _ _ => ⟨stmt + (show Nat from pa.1), simulateQ_pure _ _, by
      change 1 + _ ≤ _
      omega⟩,
    fun pa => ⟨fun stmt h pb _ _ => ⟨(stmt, (show Nat from pb.1)), simulateQ_pure _ _, h, rfl⟩,
      fun pb => ⟨fun r h _ _ _ => ⟨r.1 + r.2, simulateQ_pure _ _, by
          obtain ⟨h₁, h₂⟩ := h
          change 1 + _ + _ ≤ _
          omega⟩,
        fun _ => trivial⟩⟩⟩

/-- The composed decision, the fold of the three decisions after all interactions, accepts a
statement at least `1 + a + b` deterministically, from every statement at least 1, where `a` and
`b` are the first two messages. -/
theorem sumStages_accepts (stmt : Nat) (h : 1 ≤ stmt) (a b : Nat)
    (v : View sumStages.protocol ⟨a, b, ⟨⟩⟩)
    (data : (pathResources inputs sumStages.protocol ⟨a, b, ⟨⟩⟩).Data) :
    ∃ out, (sumStages.verifier sumMaps.compatibility).decideWith stmt ⟨a, b, ⟨⟩⟩ v data =
      pure (some out) ∧ 1 + a + b ≤ out :=
  Stages.decideWith_accepts sumStages _ _ sumBounds sumSteps stmt h _ v data

/-- Each stage, separately, accepts only statements satisfying its predicate. -/
theorem sumSupportSteps : sumStages.SupportSteps (1 ≤ ·) sumBounds := by
  refine ⟨fun stmt h pa v data r hr => ?_, fun pa => ⟨fun stmt h pb v data r hr => ?_,
    fun pb => ⟨fun s h _ v data r hr => ?_, fun _ => trivial⟩⟩⟩
  · obtain ⟨mid, hmid, hp⟩ := sumSteps.1 stmt h pa v data
    rw [hmid] at hr
    exact ⟨mid, by simpa using hr, hp⟩
  · obtain ⟨mid, hmid, hp⟩ := (sumSteps.2 pa).1 stmt h pb v data
    rw [hmid] at hr
    exact ⟨mid, by simpa using hr, hp⟩
  · obtain ⟨mid, hmid, hp⟩ := ((sumSteps.2 pa).2 pb).1 s h _ v data
    rw [hmid] at hr
    exact ⟨mid, by simpa using hr, hp⟩

/-- Every possible result of the composed decision is an accepted statement at least `1 + a + b`.
-/
theorem sumStages_support (stmt : Nat) (h : 1 ≤ stmt) (a b : Nat)
    (v : View sumStages.protocol ⟨a, b, ⟨⟩⟩)
    (data : (pathResources inputs sumStages.protocol ⟨a, b, ⟨⟩⟩).Data) :
    ∀ r ∈ support ((sumStages.verifier sumMaps.compatibility).decideWith stmt ⟨a, b, ⟨⟩⟩ v data),
      ∃ out, r = some out ∧ 1 + a + b ≤ out :=
  Stages.decideWith_preserves_support sumStages _ _ sumBounds sumSupportSteps stmt h _ v data

end Interaction.Core.StagesExampleTests
