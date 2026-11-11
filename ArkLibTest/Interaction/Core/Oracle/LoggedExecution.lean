/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Oracle.LoggedExecution
import ArkLib.Interaction.Core.Oracle.Routing
import ArkLibTest.Interaction.Core.Oracle.DependentRouting
import VCVio.OracleComp.Runtime
import ArkLibTest.Interaction.Core.Support
import ArkLibTest.Interaction.Core.Oracle.HiddenBitFixture

/-! Logged and runtime execution of passive oracle verifiers. The decision log records ambient
queries and queries to the input and message oracles, in order and with repeats, before routing.
A persistent runtime executes the logged run once as `runtime.run (V.runWithLog …)` and returns
the final state and the ordered surface trace of queries and answers. A composed verifier logs the
raw input and message queries that its routes make. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp OracleSpec

namespace Interaction.Core.LoggedExecutionTests

/-- Ambient queries carry tags. Loggers answer a tag with itself; counters answer with the
updated count. -/
abbrev ambient : OracleSpec Nat := Nat →ₒ Nat

/-- One scalar input slot. -/
@[instance_reducible] def inputs : OracleFamily.{0, 0, 0} Unit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- One exported scalar oracle. -/
@[instance_reducible] def exported : OracleFamily.{0, 0, 0} Unit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- The input data: the single slot holds 7. -/
def seven : ∀ _ : Unit, Nat := fun _ => 7

/-- Record each ambient tag and answer it with itself; answer challenges with `draw`. -/
def logger {s : OracleProtocol} (draw : QueryImpl (challengeSpec oracleSig s) Id) :
    QueryImpl (ambient + challengeSpec oracleSig s) (StateM (List Nat))
  | .inl n => do modify (· ++ [n]); pure n
  | .inr c => pure (draw c)

/-- A runtime counting ambient queries from `start`; each answer is the updated count. Challenges
are answered with `draw` and leave the count alone. -/
abbrev counter {s : OracleProtocol} (start : Nat)
    (draw : QueryImpl (challengeSpec oracleSig s) Id) :
    OracleRuntime []ₒ (ambient + challengeSpec oracleSig s) where
  State := Nat
  setup := pure start
  handler
    | .inl _ => do
      let count ← get
      set (count + 1)
      pure (count + 1)
    | .inr c => pure (draw c)

/-- Evaluate a computation with no imports. -/
def runImport {α : Type} (program : OracleComp []ₒ α) : α :=
  simulateQ (fun q => q.elim : QueryImpl []ₒ Id) program

/-! ## One pair send: the scheduling fixture

The prover makes its setup queries and query 0, then sends `(message, hidden)`. Only the first
coordinate is observable. The decision records 1, reads the sent oracle, records 2, and accepts
with the sent value or rejects. The output data closes to `input + sent.1`. -/

/-- Only the first coordinate of a sent pair is observable. -/
@[reducible] def firstInterface : OracleInterface (Nat × Nat) where
  Query := Unit
  toOC.spec := fun _ => Nat
  toOC.impl _ := do return (← read).1

/-- The prover sends one pair oracle. -/
@[instance_reducible] def pairSend : OracleProtocol :=
  .liftBind (.oracle (Nat × Nat) firstInterface) (fun _ => .pure ⟨⟩)

/-- The decision resources on the only path of `pairSend`. -/
abbrev pairResources := sumFamily inputs (pathFamily pairSend ⟨⟨⟩, ⟨⟩⟩)

/-- Close to the input plus the observable coordinate of the sent pair. -/
def closeMap : OracleMap pairResources exported where
  f x _ := (show Nat from x (.inl ())) + (show Nat × Nat from x (.inr (.inl ⟨⟩))).1
  impl _ := do
    let a : Nat ← liftM (pairResources.spec.query ⟨.inl (), ()⟩)
    let b : Nat ← liftM (pairResources.spec.query ⟨.inr (.inl ⟨⟩), ()⟩)
    pure (a + b)
  law _ _ := by
    simp only [simulateQ_bind]
    rfl

/-- The decision records 1, reads the sent oracle, records 2, and accepts or rejects. -/
def pairVerifier (accept : Bool) :
    OracleVerifier ambient pairSend Unit (fun _ => Nat) inputs (fun _ => exported) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact OptionT.mk do
      let _ ← liftM ((ambient + pairResources.spec).query (.inl 1))
      let sent : Nat ← liftM ((ambient + pairResources.spec).query (.inr ⟨.inr (.inl ⟨⟩), ()⟩))
      let _ ← liftM ((ambient + pairResources.spec).query (.inl 2))
      pure (if accept then some sent else none)
  outputMap _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact closeMap

/-- The prover makes the `setup` queries and query 0, sends `(message, hidden)` and keeps
`hidden` as private output. -/
def pairProver (setup : List Nat) (message hidden : Nat) :
    Prover oracleSig ambient pairSend (fun _ => Nat) := do
  for t in setup ++ [0] do let _ ← liftM (ambient.query t)
  pure ⟨(message, hidden), pure hidden⟩

/-- `pairSend` has no challenges. -/
def pairChallenges : QueryImpl (challengeSpec oracleSig pairSend) Id
  | ⟨.inl _, h⟩ => nomatch h
  | ⟨.inr ⟨_, n⟩, _⟩ => n.elim

/-- Name and answer of each decision log entry on `pairSend`. -/
def describePair (p : FreeM.Path pairSend) :
    QueryLog (ambient + (sumFamily inputs (pathFamily pairSend p)).spec) →
      List (String × Nat) := by
  rcases p with ⟨⟨⟩, ⟨⟩⟩
  exact List.map fun
    | ⟨.inl n, _⟩ => ("tag", n)
    | ⟨.inr ⟨.inl _, _⟩, a⟩ => ("input", show Nat from a)
    | ⟨.inr ⟨.inr (.inl _), _⟩, a⟩ => ("sent", show Nat from a)
    | ⟨.inr ⟨.inr (.inr n), _⟩, _⟩ => n.elim

/-- The logged run under the tag logger. -/
def observed (accept : Bool) (old message hidden : Nat) (setup : List Nat) :=
  (simulateQ (logger pairChallenges)
    ((pairVerifier accept).runWithLog () (fun _ => old) (pairProver setup message hidden))).run []

/-- Private output, claim with output data, decision log and ambient history of a logged run. -/
def summary (accept : Bool) (old message hidden : Nat) (setup : List Nat) :
    Nat × Option (Nat × Nat) × List (String × Nat) × List Nat :=
  let z := observed accept old message hidden setup
  (z.1.1.2.1, z.1.1.2.2.map (fun r => (r.1, r.2 ())), describePair _ z.1.2.2, z.2)

/-! LoggedExecutionExample 1, restated: the frozen row checks the trace of a verifier with
effects between the sends. The decision is passive, so its effects come after the prover's. For
every verdict, input, message, hidden value and setup, logging keeps the ambient history of the
unlogged run; this follows from `runWithLog_erase`. The schedule is `[0, 1, 2]` for every hidden
value. -/
example (accept : Bool) (old message hidden : Nat) (setup : List Nat) :
    (observed accept old message hidden setup).2 =
      ((simulateQ (logger pairChallenges) ((pairVerifier accept).run () (fun _ => old)
        (pairProver setup message hidden))).run []).2 := by
  rw [observed, ← OracleVerifier.runWithLog_erase, simulateQ_map]
  rfl

example (hidden : Nat) : (observed true 7 11 hidden []).2 = [0, 1, 2] := rfl

/-! LoggedExecutionExample 3 and 4, restated: for every hidden value, the log holds the decision's
queries only; computing the output data does not query anything. The output data closes to
`7 + 11 = 18` with this run's input and message. -/
example (hidden : Nat) : summary true 7 11 hidden [] =
    (hidden, some (11, 18), [("tag", 1), ("sent", 11), ("tag", 2)], [0, 1, 2]) := rfl

/-! LoggedExecutionExample 5 and TerminalRun TR4, restated: the frozen rows reject in a terminal
phase. Here the end decision rejects with `none` for every hidden value, and the log keeps its
queries, including the resource query that answered 19. -/
example (hidden : Nat) :
    (summary false 7 19 hidden []).2 = (none, [("tag", 1), ("sent", 19), ("tag", 2)], [0, 1, 2]) :=
  rfl

/-! TerminalRun TR1 and TR2, restated: the frozen rows run to a fault. The decisions have no fault
outcome, and these runs instead end in rejection. The setup query 9 becomes the prover's first
query,
and the frozen reception query 1 moves into the decision. For every hidden value the history keeps
the prover and decision effects `[9, 0, 1, 2]`, and the result keeps the private output and the
decision log, whose resource query answered the sent value 11.

PhasedRun 5, restated: phase grouping is dropped. For every hidden value, the accepting decision
on input 7 and sent 11 has the same history and log, and its output data closes to 18. -/
example (hidden : Nat) : summary false 7 11 hidden [9] =
    (hidden, none, [("tag", 1), ("sent", 11), ("tag", 2)], [9, 0, 1, 2]) := rfl

example (hidden : Nat) : summary true 7 11 hidden [9] =
    (hidden, some (11, 18), [("tag", 1), ("sent", 11), ("tag", 2)], [9, 0, 1, 2]) := rfl

-- Executable samples of the rows above.
run_cmd do
  for hidden in [0, 42] do
    unless summary true 7 11 hidden [9] ==
        (hidden, some (11, 18), [("tag", 1), ("sent", 11), ("tag", 2)], [9, 0, 1, 2]) do
      throwError "the accepted logged run is wrong: {summary true 7 11 hidden [9]}"
    unless summary false 7 19 hidden [] ==
        (hidden, none, [("tag", 1), ("sent", 19), ("tag", 2)], [0, 1, 2]) do
      throwError "the rejected logged run is wrong: {summary false 7 19 hidden []}"

/-! RuntimeExample 1, restated: the frozen verifier's reception query 1 moves into the decision,
so the request order `[0, 1, 2]` is unchanged. For every hidden value, a counter starting at 7
answers 8, 9 and 10, ends at 10, and the private output is the hidden value. -/
example (hidden : Nat) :
    (fun result => (result.output.1.2.1, result.state, result.trace)) <$>
      (counter 7 pairChallenges).run
        ((pairVerifier true).runWithLog () (fun _ => 7) (pairProver [] 11 hidden)) =
    pure (hidden, 10, [⟨.inl 0, (8 : Nat)⟩, ⟨.inl 1, (9 : Nat)⟩, ⟨.inl 2, (10 : Nat)⟩]) := rfl

/-! ## Two scalar sends from counter answers -/

/-- The prover sends two scalar oracles. -/
@[instance_reducible] def sendTwice : OracleProtocol :=
  .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ =>
    .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ => .pure ⟨⟩))

/-- The decision resources on the only path of `sendTwice`. -/
abbrev twiceResources := sumFamily inputs (pathFamily sendTwice ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩)

/-- Decision programs over the ambient and the resources of `sendTwice`. -/
abbrev Decision := OptionT (OracleComp (ambient + twiceResources.spec)) (List Nat)

/-- Read the scalar input oracle. -/
def readInput : OracleComp (ambient + twiceResources.spec) Nat :=
  liftM ((ambient + twiceResources.spec).query (.inr ⟨.inl (), ()⟩))

/-- Read the first scalar message oracle. -/
def readFirst : OracleComp (ambient + twiceResources.spec) Nat :=
  liftM ((ambient + twiceResources.spec).query (.inr ⟨.inr (.inl ⟨⟩), ()⟩))

/-- Read the second scalar message oracle. -/
def readSecond : OracleComp (ambient + twiceResources.spec) Nat :=
  liftM ((ambient + twiceResources.spec).query (.inr ⟨.inr (.inr (.inl ⟨⟩)), ()⟩))

/-- A verifier on `sendTwice` running a fixed decision program; its outputs are its inputs. -/
def twiceVerifier (program : Decision) :
    OracleVerifier ambient sendTwice Unit (fun _ => List Nat) inputs (fun _ => inputs) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    exact program
  outputMap _ p _ := OracleMap.embedding (sumFamily inputs (pathFamily sendTwice p)) .inl

/-- `sendTwice` has no challenges. -/
def twiceChallenges : QueryImpl (challengeSpec oracleSig sendTwice) Id
  | ⟨.inl _, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inl _⟩, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, _⟩ => n.elim

/-- Name and answer of each decision log entry on `sendTwice`. -/
def describeTwice (p : FreeM.Path sendTwice) :
    QueryLog (ambient + (sumFamily inputs (pathFamily sendTwice p)).spec) →
      List (String × Nat) := by
  rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
  exact List.map fun
    | ⟨.inl n, _⟩ => ("tag", n)
    | ⟨.inr ⟨.inl _, _⟩, a⟩ => ("input", show Nat from a)
    | ⟨.inr ⟨.inr (.inl _), _⟩, a⟩ => ("first", show Nat from a)
    | ⟨.inr ⟨.inr (.inr (.inl _)), _⟩, a⟩ => ("second", show Nat from a)
    | ⟨.inr ⟨.inr (.inr (.inr n)), _⟩, _⟩ => n.elim

/-- The decision reads the first message, the input, then the second message twice. -/
def readAll : Decision := do
  let first ← readFirst
  let input ← readInput
  let second ← readSecond
  let again ← readSecond
  pure [first, input, second, again]

/-- A prover sending 11 and 19. -/
def constantProver : Prover oracleSig ambient sendTwice (fun _ => Unit) :=
  pure ⟨(11 : Nat), pure ⟨(19 : Nat), pure ()⟩⟩

/-! LoggedExecutionExample 2, restated: the frozen row logs resource queries made between the
sends and re-indexes old slots when the context grows. The decision is passive and its log is over
`oracleIdx` of the whole path, so the check is the order and repeats of its end queries:
first 11, input 7, second 19, second 19. -/
example : describeTwice _ ((simulateQ (logger twiceChallenges)
    ((twiceVerifier readAll).runWithLog () seven constantProver)).run []).1.2.2 =
    [("first", 11), ("input", 7), ("second", 19), ("second", 19)] := rfl

/-- A private output whose type depends on the first message actually sent. -/
abbrev firstOut (tr : PathAlong oracleSig sendTwice) := Fin (Nat.succ (show Nat from tr.1))

/-- The prover makes the `setup` queries, then sends the counter's answers to queries 1 and 2.
Its private output is `0 : Fin (first + 1)`. -/
def counterProver (setup : List Nat) : Prover oracleSig ambient sendTwice firstOut := do
  for t in setup do let _ ← liftM (ambient.query t)
  let first : Nat ← liftM (ambient.query 1)
  pure ⟨first, do
    let second : Nat ← liftM (ambient.query 2)
    pure ⟨second, pure ⟨0, Nat.zero_lt_succ first⟩⟩⟩

/-- The decision reads both messages in order. -/
def readBoth : Decision := do
  let first ← readFirst
  let second ← readSecond
  pure [first, second]

/-- Claim, private output, decision log, final count and full trace of a counter execution. -/
def counterSummary (setup : List Nat) :=
  (fun result => (result.output.1.2.2.map (·.1), result.output.1.2.1.val,
      describeTwice _ result.output.2.2, result.state, result.trace)) <$>
    (counter 0 twiceChallenges).run
      ((twiceVerifier readBoth).runWithLog () seven (counterProver setup))

/-! `NativeRuntime.lean` example 1, restated: the frozen runtime's setup query 0 becomes the
prover's first query, and the input slot is an `OracleFamily` slot. The prover sends the counter's
actual answers 2 and 3, and its private output lives in `Fin (2 + 1)`. One runtime execution
returns the claim `[2, 3]`, the private output 0, the decision log `[first 2, second 3]`, the
final count 3 and the full surface trace with answers. Example 2 there: with no setup query the
sends are 1 and 2, the count 2 and the trace has two entries. -/
example : counterSummary [0] = pure (some [2, 3], 0, [("first", 2), ("second", 3)], 3,
    [⟨.inl 0, (1 : Nat)⟩, ⟨.inl 1, (2 : Nat)⟩, ⟨.inl 2, (3 : Nat)⟩]) := rfl

example : counterSummary [] = pure (some [1, 2], 0, [("first", 1), ("second", 2)], 2,
    [⟨.inl 1, (1 : Nat)⟩, ⟨.inl 2, (2 : Nat)⟩]) := rfl

-- Executable samples: the sends are the counter's answers, as the trace shows.
run_cmd do
  let (claim, out, log, state, trace) := runImport (counterSummary [0])
  unless claim == some [2, 3] && out == 0 && log == [("first", 2), ("second", 3)] && state == 3 do
    throwError "the counter execution is wrong"
  unless trace.fst.map (fun e => (e.1, show Nat from e.2)) == [(0, 1), (1, 2), (2, 3)] do
    throwError "the counter trace is wrong"

/-! ## A public message, a challenge and an oracle send -/

/-- The prover sends a public bit, receives a challenge bit, then sends a scalar oracle. -/
@[instance_reducible] def phased : OracleProtocol :=
  .liftBind (.message Bool) (fun _ => .liftBind (.challenge Bool) (fun _ =>
    .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ => .pure ⟨⟩)))

/-- The prover records 9, 9 and 1 before the message, 4 before the challenge and 5 after it. -/
def phasedProver : Prover oracleSig ambient phased (fun _ => Nat) := do
  for t in [9, 9, 1] do let _ ← liftM (ambient.query t)
  pure ⟨true, do
    let _ ← liftM (ambient.query 4)
    pure fun c => do
      let _ ← liftM (ambient.query 5)
      pure ⟨(if (show Bool from c) then 11 else 0 : Nat), pure 0⟩⟩

/-- The decision records 2 and 3, reads the oracle, then records 6 and 7. -/
def phasedVerifier :
    OracleVerifier ambient phased Unit (fun _ => List Nat) inputs (fun _ => inputs) where
  decide _ p _ := by
    rcases p with ⟨b, c, ⟨⟩, ⟨⟩⟩
    exact do
      for t in [2, 3] do
        let _ ← liftM (OracleSpec.query (spec :=
          ambient + (sumFamily inputs (pathFamily phased ⟨b, c, ⟨⟩, ⟨⟩⟩)).spec) (.inl t))
      let sent : Nat ← liftM (OracleSpec.query (spec :=
        ambient + (sumFamily inputs (pathFamily phased ⟨b, c, ⟨⟩, ⟨⟩⟩)).spec)
        (.inr ⟨.inr (.inl ⟨⟩), ()⟩))
      for t in [6, 7] do
        let _ ← liftM (OracleSpec.query (spec :=
          ambient + (sumFamily inputs (pathFamily phased ⟨b, c, ⟨⟩, ⟨⟩⟩)).spec) (.inl t))
      pure [sent]
  outputMap _ p _ := OracleMap.embedding (sumFamily inputs (pathFamily phased p)) .inl

/-- The challenge bit is `true`. -/
def phasedChallenges : QueryImpl (challengeSpec oracleSig phased) Id
  | ⟨.inl _, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inl _⟩, _⟩ => pure true
  | ⟨.inr ⟨_, .inr ⟨_, .inl _⟩⟩, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inr ⟨_, .inr ⟨_, n⟩⟩⟩, _⟩ => n.elim

/-- A runtime whose state appends the digit `tag + 1` for each ambient query, answering with the
tag. -/
abbrev digits (draw : QueryImpl (challengeSpec oracleSig phased) Id) :
    OracleRuntime []ₒ (ambient + challengeSpec oracleSig phased) where
  State := Nat
  setup := pure 1
  handler
    | .inl n => do modify (· * 10 + n + 1); pure n
    | .inr c => pure (draw c)

/-! PhasedRun 2, restated: the frozen setup query 9 becomes the prover's first query, the frozen
mid-run verifier queries move into the end decision, and the phase summary is dropped. One state
sees the prover's queries `[9, 9, 1, 4, 5]` and then the decision's `[2, 3, 6, 7]`; the challenge
draw is part of the surface trace but leaves the state alone. -/
run_cmd do
  let result := runImport ((digits phasedChallenges).run
    (phasedVerifier.runWithLog () seven phasedProver))
  unless result.trace.fst.map (·.1) == [9, 9, 1, 4, 5, 2, 3, 6, 7] do
    throwError "the surface trace is wrong: {result.trace.fst.map (·.1)}"
  unless result.trace.length == 10 do throwError "the challenge draw is missing from the trace"
  unless (show Nat from result.state) == 2102563478 do
    throwError "the runtime state is wrong: {(show Nat from result.state)}"
  unless result.output.1.2.2.map (·.1) == some [11] do
    throwError "the decision did not read the oracle sent after the challenge"

/-! ## Composition -/

/-- The prover sends one scalar oracle. -/
@[instance_reducible] def single : OracleProtocol :=
  .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ => .pure ⟨⟩)

/-- Two consecutive scalar oracle sends. -/
abbrev pair : OracleProtocol := single.append (fun _ => single)

/-- The prefix resources on the only path of `single`. -/
abbrev prefixResources := sumFamily inputs (pathFamily single ⟨⟨⟩, ⟨⟩⟩)

/-- Export the input plus the prefix message. -/
def sumExport : OracleMap prefixResources exported where
  f x _ := (show Nat from x (.inl ())) + (show Nat from x (.inr (.inl ⟨⟩)))
  impl _ := do
    let a : Nat ← liftM (prefixResources.spec.query ⟨.inl (), ()⟩)
    let b : Nat ← liftM (prefixResources.spec.query ⟨.inr (.inl ⟨⟩), ()⟩)
    pure (a + b)
  law _ _ := by
    simp only [simulateQ_bind]
    rfl

/-- Export the prefix message. -/
def messageExport : OracleMap prefixResources exported where
  f x _ := show Nat from x (.inr (.inl ⟨⟩))
  impl _ := liftM (prefixResources.spec.query ⟨.inr (.inl ⟨⟩), ()⟩)
  law _ _ := rfl

/-- A prefix verifier with a fixed decision program and export. -/
def prefixVerifier (program : OptionT (OracleComp (ambient + prefixResources.spec)) Nat)
    (exportMap : OracleMap prefixResources exported) :
    OracleVerifier ambient single Unit (fun _ => Nat) inputs (fun _ => exported) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact program
  outputMap _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact exportMap

/-- The prefix decision reads its message. -/
def readPrefix : OptionT (OracleComp (ambient + prefixResources.spec)) Nat :=
  liftM ((ambient + prefixResources.spec).query (.inr ⟨.inr (.inl ⟨⟩), ()⟩))

/-- The suffix resources on the only path of `single`. -/
abbrev suffixResources := sumFamily exported (pathFamily single ⟨⟨⟩, ⟨⟩⟩)

/-- The suffix records 3, reads the export and its own message, and claims their sum plus the
statement. -/
def suffixVerifier :
    OracleVerifier ambient single Nat (fun _ => Nat) exported (fun _ => exported) where
  decide stmt p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact do
      let _ ← liftM ((ambient + suffixResources.spec).query (.inl 3))
      let e : Nat ← liftM ((ambient + suffixResources.spec).query (.inr ⟨.inl (), ()⟩))
      let m : Nat ← liftM ((ambient + suffixResources.spec).query (.inr ⟨.inr (.inl ⟨⟩), ()⟩))
      pure (stmt + e + m)
  outputMap _ p _ := OracleMap.embedding (sumFamily exported (pathFamily single p)) .inl

/-- The composite output map is the suffix output map after `suffixRoute`. -/
def compatible (V : OracleVerifier ambient single Unit (fun _ => Nat) inputs (fun _ => exported)) :
    OracleVerifier.OutputCompatibility V (fun _ => suffixVerifier) where
  outputMap stmt p v :=
    (suffixVerifier.outputMap 0 (Path.split single (fun _ => single) p).2
      (View.split single (fun _ => single) p v).2).comp (OracleVerifier.suffixRoute V stmt p v)
  agrees _ _ _ _ _ _ := rfl

/-- Append the suffix verifier using its routed output map. -/
def composed (V : OracleVerifier ambient single Unit (fun _ => Nat) inputs (fun _ => exported)) :=
  V.append (fun _ => suffixVerifier) (compatible V)

/-- The prover sends the counter's answers to queries 1 and 2, keeping `out` as private output. -/
def appendProver (out : Nat) : Prover oracleSig ambient pair (fun _ => Nat) :=
  Prover.append (s₂ := fun _ => single)
    (do let first : Nat ← liftM (ambient.query 1); pure ⟨first, pure out⟩)
    (fun _ memory => pure do
      let second : Nat ← liftM (ambient.query 2)
      pure ⟨second, pure memory⟩)

/-- `pair` has no challenges. -/
def appendChallenges : QueryImpl (challengeSpec oracleSig pair) Id
  | ⟨.inl _, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inl _⟩, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, _⟩ => n.elim

/-- Name and answer of each composite decision log entry. -/
def describeAppend (p : FreeM.Path pair) :
    QueryLog (ambient + (sumFamily inputs (pathFamily pair p)).spec) →
      List (String × Nat) := by
  rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
  exact List.map fun
    | ⟨.inl n, _⟩ => ("tag", n)
    | ⟨.inr ⟨.inl _, _⟩, a⟩ => ("input", show Nat from a)
    | ⟨.inr ⟨.inr (.inl _), _⟩, a⟩ => ("prefix", show Nat from a)
    | ⟨.inr ⟨.inr (.inr (.inl _)), _⟩, a⟩ => ("suffix", show Nat from a)
    | ⟨.inr ⟨.inr (.inr (.inr n)), _⟩, _⟩ => n.elim

/-- Private output, claim with output data, decision log, final count and full trace. -/
def appendSummary
    (V : OracleVerifier ambient single Unit (fun _ => Nat) inputs (fun _ => exported))
    (out : Nat) :=
  (fun result => (result.output.1.2.1, result.output.1.2.2.map (fun r => (r.1, r.2 ())),
      describeAppend _ result.output.2.2, result.state, result.trace)) <$>
    (counter 0 appendChallenges).run ((composed V).runWithLog () seven (appendProver out))

/-! `NativeRuntime.lean` example 4, restated: the exported view is an `OracleMap` whose `impl`
reads the input and the prefix message, composition is `OracleVerifier.append`, and the input is
an `OracleFamily` slot. The prover sends the counter's answers 1 and 2; the suffix decision makes
the counter request 3. The suffix's one export query logs as the two raw queries made by its
route, then the suffix reads its own message: `[tag 3, input 7, prefix 1, suffix 2]`. For every
secret, the claim is `0 + 8 + 2 = 10`, the private output is the secret, the count is 3 and the
full trace answers 1, 2 and 3.

QueryBounds 8, restated: the output data, computed by the composite output map `f` on this run's
resources, is the export 8, alongside the same log. -/
example (secret : Nat) : appendSummary (prefixVerifier (pure 0) sumExport) secret =
    pure (secret, some (10, 8), [("tag", 3), ("input", 7), ("prefix", 1), ("suffix", 2)], 3,
      [⟨.inl 1, (1 : Nat)⟩, ⟨.inl 2, (2 : Nat)⟩, ⟨.inl 3, (3 : Nat)⟩]) := by
  kernel_rfl

/-! QueryBounds 5, restated: the input is an `OracleFamily` slot and composition is
`OracleVerifier.append`. The prefix reads its message and exports it; the suffix's export query
reads the prefix message again. The log keeps the repeat: `[prefix 1, tag 3, prefix 1, suffix 2]`,
the claim is `1 + 1 + 2 = 4` and the private output is 3. -/
example : appendSummary (prefixVerifier readPrefix messageExport) 3 =
    pure (3, some (4, 1), [("prefix", 1), ("tag", 3), ("prefix", 1), ("suffix", 2)], 3,
      [⟨.inl 1, (1 : Nat)⟩, ⟨.inl 2, (2 : Nat)⟩, ⟨.inl 3, (3 : Nat)⟩]) := rfl

-- Executable samples of the composed rows.
run_cmd do
  for secret in [0, 13] do
    let (out, claim, log, state, _) := runImport (appendSummary (prefixVerifier (pure 0) sumExport)
      secret)
    unless out == secret && claim == some (10, 8) && state == 3 &&
        log == [("tag", 3), ("input", 7), ("prefix", 1), ("suffix", 2)] do
      throwError "the composed counter execution is wrong: {log}"

/-- Realizations of the prefix resources: input 7 and message 1. -/
def prefixData : ∀ i, prefixResources.Realization i :=
  sumData seven (payloads single ⟨(1 : Nat), ⟨⟩⟩)

/-- One query to the export, routed by the export's `impl`. -/
def exportQuery : OracleComp exported.spec Nat := liftM (exported.spec.query ⟨(), ()⟩)

/-- Answer prefix resource queries from `prefixData`. -/
def answerPrefix : QueryImpl prefixResources.spec Id :=
  fun q => pure (prefixResources.behaviorOfRealizations prefixData q)

/-- Name and answer of a prefix resource log entry. -/
def nameEntry : (z : (i : prefixResources.spec.Domain) × prefixResources.spec.Range i) →
    String × Nat
  | ⟨⟨.inl _, _⟩, a⟩ => ("input", show Nat from a)
  | ⟨⟨.inr (.inl _), _⟩, a⟩ => ("prefix", show Nat from a)
  | ⟨⟨.inr (.inr n), _⟩, _⟩ => n.elim

/-! `NativeRuntime.lean` example 5, restated: the route is the `impl` of the exported
`OracleMap`, answered by the prefix realizations. The logging handler of `withQueryLog_simulateQ`
records the two raw queries `[input 7, prefix 1]` of the one export query, which answers 8. -/
example : (fun z => (z.1, z.2.map nameEntry)) (simulateQ answerPrefix
    (simulateQ (QueryImpl.compose prefixResources.spec.loggingOracle sumExport.impl)
      exportQuery).run) = (8, [("input", 7), ("prefix", 1)]) := by
  rw [← OracleComp.withQueryLog_simulateQ]
  rfl

/-! ## The hidden-bit runtime

The fixture is `ArkLibTest.Interaction.Core.Oracle.HiddenBitFixture`. -/

open Interaction.Core.HiddenBitFixture

/-! RuntimeQueryBounds 13, restated: the logged run executes directly in the runtime. The guess
prover leaves the state at `(hidden, 2)`; the trace is the challenge, the prefix decision's dummy
request and the suffix decision's reveal, with charge 4. -/
example (guess : Bool) (secret : Nat) :
    (fun result => (result.state, result.trace, bitCharge result.trace.fst)) <$>
      bitRuntime.run (bitVerifier.runWithLog () falseData (guessProver guess secret)) =
    (fun hidden => ((hidden, 2),
      ([⟨challengeEntry, ()⟩, ⟨.inl false, false⟩, ⟨.inl true, hidden⟩] : QueryLog bitFull), 4))
      <$> (coinSpec.query () : OracleComp coinSpec Bool) := by
  kernel_rfl

/-! RuntimeQueryBounds 14, restated: the informed prover's reveal comes first, from the seam
slot, so the trace is `[challenge, true ↦ hidden, false ↦ false, true ↦ hidden]`, the state is
`(hidden, 3)` and the charge is 7. -/
example (secret : Nat) :
    (fun result => (result.state, result.trace, bitCharge result.trace.fst)) <$>
      bitRuntime.run (bitVerifier.runWithLog () falseData (informedProver secret)) =
    (fun hidden => ((hidden, 3),
      ([⟨challengeEntry, ()⟩, ⟨.inl true, hidden⟩, ⟨.inl false, false⟩, ⟨.inl true, hidden⟩] :
        QueryLog bitFull), 7)) <$> (coinSpec.query () : OracleComp coinSpec Bool) := by
  kernel_rfl

/-- Ambient requests of the composed run, as full-surface queries. -/
def toFull : QueryImpl bitAmbient (OracleComp bitFull) := fun q => liftM (bitFull.query (.inl q))

/-- Challenge draws of the composed run, as full-surface queries. -/
def fullDraw : (c : ChallengeNode oracleSig bitCombined) →
    OracleComp bitFull (challengeSpec oracleSig bitCombined c) :=
  fun c => liftM (bitFull.query (.inr c))

/-- The prefix stage of `OracleVerifier.run_append`: the prefix interaction, ending after the
seam slot. -/
def boundary (prover : Prover oracleSig bitAmbient bitCombined (fun _ => Nat)) :=
  TwoParty.Lens.run bitFirst (Focal.splitPrefix (prover.simulate toFull))
    (sampler oracleSig bitFirst (prefixDraw oracleSig bitFirst (fun _ => bitSecond) fullDraw))

/-! RuntimeQueryBounds 9, restated: the composed run, split by `OracleVerifier.run_append` into
the two interaction stages and the two decisions, has the row-13 history. -/
example (guess : Bool) (secret : Nat) :
    (fun result => (result.state, result.trace, bitCharge result.trace.fst)) <$>
      bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret)) =
    (fun hidden => ((hidden, 2),
      ([⟨challengeEntry, ()⟩, ⟨.inl false, false⟩, ⟨.inl true, hidden⟩] : QueryLog bitFull), 4))
      <$> (coinSpec.query () : OracleComp coinSpec Bool) := by
  unfold bitVerifier
  rw [OracleVerifier.run_append]
  kernel_rfl

/-! RuntimeQueryBounds 10, restated: the split informed run has the row-14 history. -/
example (secret : Nat) :
    (fun result => (result.state, result.trace, bitCharge result.trace.fst)) <$>
      bitRuntime.run (bitVerifier.run () falseData (informedProver secret)) =
    (fun hidden => ((hidden, 3),
      ([⟨challengeEntry, ()⟩, ⟨.inl true, hidden⟩, ⟨.inl false, false⟩, ⟨.inl true, hidden⟩] :
        QueryLog bitFull), 7)) <$> (coinSpec.query () : OracleComp coinSpec Bool) := by
  unfold bitVerifier
  rw [OracleVerifier.run_append]
  kernel_rfl

/-! The reveal sits in the seam slot, which `Focal.splitPrefix` places in the prefix stage: at the
boundary the informed run has state `(hidden, 1)` and trace `[challenge, true ↦ hidden]`, while
the guess run has state `(hidden, 0)` and only the challenge. -/
example (secret : Nat) :
    (fun result => (result.state, result.trace)) <$>
      bitRuntime.run (boundary (informedProver secret)) =
    (fun hidden => ((hidden, 1),
      ([⟨challengeEntry, ()⟩, ⟨.inl true, hidden⟩] : QueryLog bitFull))) <$>
      (coinSpec.query () : OracleComp coinSpec Bool) := by
  kernel_rfl

example (guess : Bool) (secret : Nat) :
    (fun result => (result.state, result.trace)) <$>
      bitRuntime.run (boundary (guessProver guess secret)) =
    (fun hidden => ((hidden, 0), ([⟨challengeEntry, ()⟩] : QueryLog bitFull))) <$>
      (coinSpec.query () : OracleComp coinSpec Bool) := by
  kernel_rfl

/-! ## Erasure under a runtime -/

/-- Erasure commutes with handlers whose lawful target monad has a larger universe. -/
example {m : Type → Type 1} [Monad m] [LawfulMonad m]
    (handler : QueryImpl bitFull m) (guess : Bool) (secret : Nat) :
    Sigma.fst <$> simulateQ handler
        (bitVerifier.runWithLog () falseData (guessProver guess secret)) =
      simulateQ handler (bitVerifier.run () falseData (guessProver guess secret)) :=
  OracleVerifier.simulateQ_runWithLog_erase bitVerifier handler () falseData
    (guessProver guess secret)

/-- The hidden-bit runtime satisfies logged-run erasure for every guess and secret. -/
example (guess : Bool) (secret : Nat) :
    (fun result => (result.output.1, result.state)) <$>
        bitRuntime.run (bitVerifier.runWithLog () falseData (guessProver guess secret)) =
      bitRuntime.setup >>= fun state =>
        bitRuntime.handler.runState state
          (bitVerifier.run () falseData (guessProver guess secret)) :=
  OracleVerifier.runtime_runWithLog_erase bitVerifier bitRuntime () falseData
    (guessProver guess secret)

end Interaction.Core.LoggedExecutionTests

/-! LoggedExecutionExample 6 and 7, `NativeRuntime.lean` rows 7, 8 and 9, and TerminalRun TR6:
the erasure laws, runtime erasure and logging after substitution stay axiom-clean. Row 8 guards
the composition of VCVio's runtime erasure law with `runWithLog_erase`. TR6 restated: the frozen
row guards the terminal erase law; the decisions have no terminal layer, so it guards
`runWithLog_fst` and `runWithLog_erase`. -/
run_cmd do
  for decl in [``Interaction.Core.OracleVerifier.runWithLog_fst,
      ``Interaction.Core.OracleVerifier.runWithLog_erase,
      ``Interaction.Core.OracleVerifier.runtime_runWithLog_erase,
      ``Interaction.Core.OracleVerifier.simulateQ_runWithLog_erase,
      ``OracleComp.withQueryLog_simulateQ] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"

namespace Interaction.Core.DependentRoutingTests

/-- Observe the logged run with the statement and output oracle selected by its public Boolean.
The dependent claim is read through that selected oracle interface. -/
def loggedObserved (input : Nat) : Bool × Nat × Option (Nat × Nat) :=
  let obs := (simulateQ noQueries (composite.runWithLog () (fun _ => input) (prover input))).1
  ((projectPathAlong oracleSig combined obs.1).1, obs.2.1,
    obs.2.2.map (readClaim (projectPathAlong oracleSig combined obs.1)))

/-- Logging retains the unit statement and scalar realization of the zero branch. -/
example : loggedObserved 0 = (true, 13, some (0, 0)) := rfl

/-- Logging retains the natural statement and pair realization of the nonzero branch. -/
example : loggedObserved 7 = (false, 29, some (7, 7)) := rfl

/-- Erasing a logged run retains the dependent observation for every input. -/
example (input : Nat) : loggedObserved input = observed input := by
  have h := OracleVerifier.simulateQ_runWithLog_erase composite noQueries ()
    (fun _ => input) (prover input)
  exact congrArg (fun obs => ((projectPathAlong oracleSig combined obs.1).1, obs.2.1,
    obs.2.2.map (readClaim (projectPathAlong oracleSig combined obs.1)))) h

end Interaction.Core.DependentRoutingTests
