/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Oracle.LoggedExecution
import ArkLib.Interaction.Core.Oracle.PrefixResources
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
abbrev pairResources := pathResources inputs pairSend ⟨⟨⟩, ⟨⟩⟩

/-- Close to the input plus the observable coordinate of the sent pair. -/
def closeMap : OracleMap pairResources exported where
  f x _ := (show Nat from x.1 ()) + (show Nat × Nat from x.2 (.inl ⟨⟩)).1
  impl _ := do
    let a : Nat ← liftM (pairResources.spec.query (.inl ⟨(), ()⟩))
    let b : Nat ← liftM (pairResources.spec.query (.inr ⟨.inl ⟨⟩, ()⟩))
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
      let sent : Nat ← liftM ((ambient + pairResources.spec).query (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
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
    QueryLog (ambient + (pathResources inputs pairSend p).spec) →
      List (String × Nat) := by
  rcases p with ⟨⟨⟩, ⟨⟩⟩
  exact List.map fun
    | ⟨.inl n, _⟩ => ("tag", n)
    | ⟨.inr (.inl ⟨_, _⟩), a⟩ => ("input", show Nat from a)
    | ⟨.inr (.inr ⟨.inl _, _⟩), a⟩ => ("sent", show Nat from a)
    | ⟨.inr (.inr ⟨.inr n, _⟩), _⟩ => n.elim

/-- The logged run under the tag logger. -/
def observed (accept : Bool) (old message hidden : Nat) (setup : List Nat) :=
  (simulateQ (logger pairChallenges)
    ((pairVerifier accept).runWithLog () (fun _ => old) (pairProver setup message hidden))).run []

/-- Private output, claim with output data, decision log and ambient history of a logged run. -/
def summary (accept : Bool) (old message hidden : Nat) (setup : List Nat) :
    Nat × Option (Nat × Nat) × List (String × Nat) × List Nat :=
  let z := observed accept old message hidden setup
  (z.1.1.2.1, z.1.1.2.2.map (fun r => (r.1, r.2 ())), describePair _ z.1.2.2, z.2)

/-! Additional passive coverage of erasure and the one-send schedule. The disposition inventory
separates these from the full public-message and challenge trace tested by `full_schedule`. -/
example (accept : Bool) (old message hidden : Nat) (setup : List Nat) :
    (observed accept old message hidden setup).2 =
      ((simulateQ (logger pairChallenges) ((pairVerifier accept).run () (fun _ => old)
        (pairProver setup message hidden))).run []).2 := by
  rw [observed, ← OracleVerifier.map_fst_runWithLog, simulateQ_map]
  rfl

example (hidden : Nat) : (observed true 7 11 hidden []).2 = [0, 1, 2] := rfl

/-! For every hidden value, the decision log contains one oracle read. Computing the
output data from this run's input and sent message adds no queries. -/
example (hidden : Nat) : summary true 7 11 hidden [] =
    (hidden, some (11, 18), [("tag", 1), ("sent", 11), ("tag", 2)], [0, 1, 2]) := by
  kernel_rfl

/-! A rejecting decision retains all earlier query answers, including the oracle answer 19. -/
example (hidden : Nat) :
    (summary false 7 19 hidden []).2 = (none, [("tag", 1), ("sent", 19), ("tag", 2)], [0, 1, 2]) :=
  rfl

/-! Additional passive accepting and rejecting executions with a setup query. Labelled terminal
failures are tested separately below; rejection is never used as a substitute for failure. -/
example (hidden : Nat) : summary false 7 11 hidden [9] =
    (hidden, none, [("tag", 1), ("sent", 11), ("tag", 2)], [9, 0, 1, 2]) := by
  kernel_rfl

example (hidden : Nat) : summary true 7 11 hidden [9] =
    (hidden, some (11, 18), [("tag", 1), ("sent", 11), ("tag", 2)], [9, 0, 1, 2]) := by
  kernel_rfl

/-- A final decision reads the message before accepting, rejecting, or requesting a failure. -/
def terminalVerifier (mode : Nat) :
    OracleVerifier ambient pairSend Unit (fun _ => Nat) inputs (fun _ => exported) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact OptionT.mk do
      let _ ← liftM ((ambient + pairResources.spec).query (.inl 1))
      let _ ← liftM ((ambient + pairResources.spec).query (.inl 2))
      let sent : Nat ← liftM ((ambient + pairResources.spec).query
        (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
      if mode = 1 then
        let _ ← liftM ((ambient + pairResources.spec).query (.inl 17))
        pure none
      else if mode = 2 then
        let _ ← liftM ((ambient + pairResources.spec).query (.inl 23))
        pure none
      else pure (if mode = 0 then none else some sent)
  outputMap _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact closeMap

/-- Answered ambient requests update a persistent history; two requests fail with distinct labels.
An unanswered failing request has no query-answer entry. -/
def terminalHandler : QueryImpl ambient (ExceptT Nat (StateM (List Nat))) := fun tag => do
  if tag = 17 ∨ tag = 23 then throw tag
  modify (· ++ [tag])
  pure tag

/-- Execute the actual prover, then interpret its final decision with recoverable labelled
failure. The private output and transcript are captured before interpreting that decision. -/
def terminalObserved (mode old message hidden : Nat) :=
  (do
    let ⟨tr, out, _⟩ ← simulateQ (logger pairChallenges) (TwoParty.Lens.run pairSend
      ((pairProver [9] message hidden).simulate
        (fun q => liftM ((ambient + challengeSpec oracleSig pairSend).query (.inl q))))
      (sampler oracleSig pairSend (fun c =>
        liftM ((ambient + challengeSpec oracleSig pairSend).query (.inr c)))))
    let p := projectPathAlong oracleSig pairSend tr
    let data : (pathResources inputs pairSend p).Data := (fun _ => old, payloads pairSend tr)
    let (verdict, log) ← (terminalVerifier mode).decideWithFailureLog terminalHandler () p
      (toView pairSend tr) data
    pure (out, verdict.map (Option.map fun t =>
      (t, ((terminalVerifier mode).outputMap () p (toView pairSend tr)).f data ())),
      describePair p log) : StateM (List Nat) _).run []

/-- Both failures retain their distinct labels, all earlier effects, the source answer and the
actual private output. Rejection and acceptance use the same execution and the same resources. -/
theorem terminal_outcomes (old message hidden : Nat) :
    terminalObserved 1 old message hidden =
      ((hidden, .error 17, [("tag", 1), ("tag", 2), ("sent", message)]), [9, 0, 1, 2]) ∧
    terminalObserved 2 old message hidden =
      ((hidden, .error 23, [("tag", 1), ("tag", 2), ("sent", message)]), [9, 0, 1, 2]) ∧
    terminalObserved 0 old message hidden =
      ((hidden, .ok none, [("tag", 1), ("tag", 2), ("sent", message)]), [9, 0, 1, 2]) ∧
    terminalObserved 3 old message hidden =
      ((hidden, .ok (some (message, old + message)),
        [("tag", 1), ("tag", 2), ("sent", message)]), [9, 0, 1, 2]) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Closing uses the actual input and observable message, including the second accepted example. -/
theorem terminal_closing_examples (hidden : Nat) :
    (terminalObserved 3 7 11 hidden).1.2.1 = .ok (some (11, 18)) ∧
    (terminalObserved 3 13 19 hidden).1.2.1 = .ok (some (19, 32)) := ⟨rfl, rfl⟩

-- Executable samples of the rows above.
run_cmd do
  for hidden in [0, 42] do
    unless summary true 7 11 hidden [9] ==
        (hidden, some (11, 18), [("tag", 1), ("sent", 11), ("tag", 2)], [9, 0, 1, 2]) do
      throwError "the accepted logged run is wrong: {summary true 7 11 hidden [9]}"
    unless summary false 7 19 hidden [] ==
        (hidden, none, [("tag", 1), ("sent", 19), ("tag", 2)], [0, 1, 2]) do
      throwError "the rejected logged run is wrong: {summary false 7 19 hidden []}"

/-! A persistent counter starting at 7 records three requests and ends at 10. The actual
private output remains arbitrary and is retained by the logged observation. -/
example (hidden : Nat) :
    (fun result => (result.output.1.2.1, result.state, result.trace)) <$>
      (counter 7 pairChallenges).run
        ((pairVerifier true).runWithLog () (fun _ => 7) (pairProver [] 11 hidden)) =
    pure (hidden, 10, [⟨.inl 0, (8 : Nat)⟩, ⟨.inl 1, (9 : Nat)⟩, ⟨.inl 2, (10 : Nat)⟩]) := by
  rw [OracleVerifier.runWithLog_eq]
  rfl

/-- Tagged ambient requests with a unique unit response. -/
abbrev unitAmbient : OracleSpec Nat := Nat →ₒ Unit

/-- The prover makes request 0, sends the pair, and retains its arbitrary private output. -/
def unitProver (hidden : Nat) : Prover oracleSig unitAmbient pairSend (fun _ => Nat) := do
  let _ ← liftM (unitAmbient.query 0)
  pure ⟨(11, hidden), pure hidden⟩

/-- Both verifier effects occur in the final decision, which reads the actual sent oracle. -/
def unitVerifier :
    OracleVerifier unitAmbient pairSend Unit (fun _ => Nat) inputs (fun _ => exported) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact do
      let _ ← liftM ((unitAmbient + pairResources.spec).query (.inl 1))
      let sent : Nat ← liftM ((unitAmbient + pairResources.spec).query
        (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
      let _ ← liftM ((unitAmbient + pairResources.spec).query (.inl 2))
      pure sent
  outputMap _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact closeMap

/-- A persistent counter starts at 7 and increments on each unit-response ambient request. -/
abbrev unitCounter : OracleRuntime []ₒ (unitAmbient + challengeSpec oracleSig pairSend) where
  State := Nat
  setup := pure 7
  handler
    | .inl _ => do
      modify (· + 1)
      pure ()
    | .inr c => pure (pairChallenges c)

/-- One runtime execution retains the private output, final count 10 and all three unit answers
in chronological order. -/
theorem unit_runtime_trace (hidden : Nat) :
    (fun result => (result.output.1.2.1, result.state, result.trace)) <$>
      unitCounter.run (unitVerifier.runWithLog () seven (unitProver hidden)) =
    pure (hidden, 10, [⟨.inl 0, ()⟩, ⟨.inl 1, ()⟩, ⟨.inl 2, ()⟩]) := by
  rw [OracleVerifier.runWithLog_eq]
  rfl

run_cmd do
  for hidden in [0, 42] do
    let result := runImport (unitCounter.run (unitVerifier.runWithLog () seven (unitProver hidden)))
    unless result.output.1.2.1 == hidden && (show Nat from result.state) == 10 do
      throwError "the unit-response runtime lost the private output or final state"
    unless result.trace.fst.map (fun e => (e.1, show Unit from e.2)) ==
        [(0, ()), (1, ()), (2, ())] do
      throwError "the unit-response runtime changed its requests or answers"

/-! ## Two scalar sends from counter answers -/

/-- The prover sends two scalar oracles. -/
@[instance_reducible] def sendTwice : OracleProtocol :=
  .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ =>
    .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ => .pure ⟨⟩))

/-- The decision resources on the only path of `sendTwice`. -/
abbrev twiceResources := pathResources inputs sendTwice ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩

/-- Decision programs over the ambient and the resources of `sendTwice`. -/
abbrev Decision := OptionT (OracleComp (ambient + twiceResources.spec)) (List Nat)

/-- Read the scalar input oracle. -/
def readInput : OracleComp (ambient + twiceResources.spec) Nat :=
  liftM ((ambient + twiceResources.spec).query (.inr (.inl ⟨(), ()⟩)))

/-- Read the first scalar message oracle. -/
def readFirst : OracleComp (ambient + twiceResources.spec) Nat :=
  liftM ((ambient + twiceResources.spec).query (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))

/-- Read the second scalar message oracle. -/
def readSecond : OracleComp (ambient + twiceResources.spec) Nat :=
  liftM ((ambient + twiceResources.spec).query (.inr (.inr ⟨.inr (.inl ⟨⟩), ()⟩)))

/-- A verifier on `sendTwice` running a fixed decision program; its outputs are its inputs. -/
def twiceVerifier (program : Decision) :
    OracleVerifier ambient sendTwice Unit (fun _ => List Nat) inputs (fun _ => inputs) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    exact program
  outputMap _ p _ := OracleMap.fst _ _

/-- `sendTwice` has no challenges. -/
def twiceChallenges : QueryImpl (challengeSpec oracleSig sendTwice) Id
  | ⟨.inl _, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inl _⟩, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, _⟩ => n.elim

/-- Name and answer of each decision log entry on `sendTwice`. -/
def describeTwice (p : FreeM.Path sendTwice) :
    QueryLog (ambient + (pathResources inputs sendTwice p).spec) →
      List (String × Nat) := by
  rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
  exact List.map fun
    | ⟨.inl n, _⟩ => ("tag", n)
    | ⟨.inr (.inl ⟨_, _⟩), a⟩ => ("input", show Nat from a)
    | ⟨.inr (.inr ⟨.inl _, _⟩), a⟩ => ("first", show Nat from a)
    | ⟨.inr (.inr ⟨.inr (.inl _), _⟩), a⟩ => ("second", show Nat from a)
    | ⟨.inr (.inr ⟨.inr (.inr n), _⟩), _⟩ => n.elim

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

/-! The final decision queries the first send, input, and second send twice, in that order.
This does not assert a source query between the sends. -/
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

/-! Setup and two sends share one persistent counter. The sends are its actual answers, and
the private output type depends on the first send. Omitting setup removes exactly one request. -/
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
          ambient + (pathResources inputs phased ⟨b, c, ⟨⟩, ⟨⟩⟩).spec) (.inl t))
      let sent : Nat ← liftM (OracleSpec.query (spec :=
        ambient + (pathResources inputs phased ⟨b, c, ⟨⟩, ⟨⟩⟩).spec)
        (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
      for t in [6, 7] do
        let _ ← liftM (OracleSpec.query (spec :=
          ambient + (pathResources inputs phased ⟨b, c, ⟨⟩, ⟨⟩⟩).spec) (.inl t))
      pure [sent]
  outputMap _ p _ := OracleMap.fst _ _

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

/-! Additional passive scheduling coverage. The produced trace distinguishes the challenge
from ambient requests, and the state records the order of all ambient effects. -/
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

/-- The public announcement, challenge receive, oracle send and private terminal output all
remain present when the verifier is passive. Equal setup requests remain separate effects. -/
def phaseProver : Prover oracleSig ambient phased (fun _ => Nat) := do
  let _ ← liftM (ambient.query 9)
  let _ ← liftM (ambient.query 9)
  let _ ← liftM (ambient.query 1)
  pure ⟨true, do
    let _ ← liftM (ambient.query 4)
    pure fun _ => do
      let _ ← liftM (ambient.query 5)
      pure ⟨(17 : Nat), pure 23⟩⟩

/-- The decision retains both former reception effects at the terminal boundary. -/
def phaseVerifier :
    OracleVerifier ambient phased Unit (fun _ => Nat) inputs (fun _ => exported) where
  decide _ _ _ := do
    for tag in [2, 3, 6, 7] do
      let _ ← liftM (ambient.query tag)
    pure 31
  outputMap _ _ _ := OracleMap.fst _ _

/-- The phase observer reads both produced owner logs, the completed prefix, private output and
verdict, together with the noncommutative runtime state. No replacement owner is an argument. -/
def phaseSummary :=
  (fun result =>
    let tr := result.output.1.1
    (result.output.2.1.map (·.1), result.output.2.2.fst.map (·.1),
      tr.1, tr.2.1, tr.2.2.1, result.output.1.2.1,
      result.output.1.2.2.map (·.1), result.state)) <$>
    (digits phasedChallenges).run (phaseVerifier.runWithLog () seven phaseProver)

/-- The available owner logs retain setup multiplicity and all actions; the full prefix retains
both public directions and the final oracle payload. The accumulator witnesses their effect
order. -/
theorem phase_log_contract : phaseSummary =
    pure ([9, 9, 1, 4, 5], [2, 3, 6, 7], true, true, (17 : Nat), 23, some 31, 2102563478) := by
  kernel_rfl

/-- A public announcement, an oracle send, a challenge and a final oracle send. -/
@[instance_reducible] def schedule : OracleProtocol :=
  .liftBind (.message Bool) (fun _ =>
    .liftBind (.oracle (Nat × Nat) firstInterface) (fun _ =>
      .liftBind (.challenge Nat) (fun _ =>
        .liftBind (.oracle (Nat × Nat) firstInterface) (fun _ => .pure ⟨⟩))))

/-- The prover preserves the concrete sends and private output across the sampled challenge. -/
def scheduleProver (hidden : Nat) : Prover oracleSig ambient schedule (fun _ => Nat × Nat) := do
  let _ ← liftM (ambient.query 0)
  pure ⟨true, do
    let _ ← liftM (ambient.query 1)
    pure ⟨(11, hidden), pure fun challenge => do
      let _ ← liftM (ambient.query 4)
      pure ⟨((show Nat from challenge) + 1, 99), pure (777, hidden)⟩⟩⟩

/-- The final decision reads the last message, after all sends and challenge receives. -/
def scheduleVerifier : OracleVerifier ambient schedule Unit (fun _ => Nat) inputs
    (fun _ => exported) where
  decide _ p view := by
    rcases p with ⟨b, ⟨⟨⟩, ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩⟩⟩
    exact do
      let _ ← liftM (ambient.query 3)
      let last : Nat ← liftM ((ambient + (pathResources inputs schedule
        ⟨b, ⟨⟨⟩, ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩⟩⟩).spec).query
          (.inr (.inr ⟨.inr (.inl ⟨⟩), ()⟩)))
      pure (if (show Bool from b) then last + (show Nat from view.val.2.2.1) else 0)
  outputMap _ _ _ := OracleMap.fst _ _

/-- The challenge service records both parts of its draw, without reading any resource. -/
def scheduleHandler : QueryImpl (ambient + challengeSpec oracleSig schedule)
    (StateM (List Nat))
  | .inl tag => do modify (· ++ [tag]); pure tag
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inl _⟩, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inl _⟩⟩, _⟩ => do
    modify (· ++ [5, 2])
    pure (18 : Nat)
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inr ⟨_, .inl _⟩⟩⟩, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inr ⟨_, .inr ⟨_, n⟩⟩⟩⟩, _⟩ => n.elim

/-- The full passive action trace includes public send, oracle send, draw, receive continuation
and final decision. It also retains the private output and the terminal answer. -/
theorem full_schedule (hidden : Nat) :
    (fun z => (z.1.1.2.1, z.1.1.2.2.map (·.1), z.2))
      ((simulateQ scheduleHandler (scheduleVerifier.runWithLog () seven
        (scheduleProver hidden))).run []) =
      ((777, hidden), some 37, [0, 1, 5, 2, 4, 3]) := by
  kernel_rfl

/-! ## Composition -/

/-- The prover sends one scalar oracle. -/
@[instance_reducible] def single : OracleProtocol :=
  .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ => .pure ⟨⟩)

/-- Two consecutive scalar oracle sends. -/
abbrev pair : OracleProtocol := single.append (fun _ => single)

/-- The prefix resources on the only path of `single`. -/
abbrev prefixResources := pathResources inputs single ⟨⟨⟩, ⟨⟩⟩

/-- Export the input plus the prefix message. -/
def sumExport : OracleMap prefixResources exported where
  f x _ := (show Nat from x.1 ()) + (show Nat from x.2 (.inl ⟨⟩))
  impl _ := do
    let a : Nat ← liftM (prefixResources.spec.query (.inl ⟨(), ()⟩))
    let b : Nat ← liftM (prefixResources.spec.query (.inr ⟨.inl ⟨⟩, ()⟩))
    pure (a + b)
  law _ _ := by
    simp only [simulateQ_bind]
    rfl

/-- Export the prefix message. -/
def messageExport : OracleMap prefixResources exported where
  f x _ := show Nat from x.2 (.inl ⟨⟩)
  impl _ := liftM (prefixResources.spec.query (.inr ⟨.inl ⟨⟩, ()⟩))
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
  liftM ((ambient + prefixResources.spec).query (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))

/-- The suffix resources on the only path of `single`. -/
abbrev suffixResources := pathResources exported single ⟨⟨⟩, ⟨⟩⟩

/-- The suffix records 3, reads the export and its own message, and claims their sum plus the
statement. -/
def suffixVerifier :
    OracleVerifier ambient single Nat (fun _ => Nat) exported (fun _ => exported) where
  decide stmt p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact do
      let _ ← liftM ((ambient + suffixResources.spec).query (.inl 3))
      let e : Nat ← liftM ((ambient + suffixResources.spec).query (.inr (.inl ⟨(), ()⟩)))
      let m : Nat ← liftM ((ambient + suffixResources.spec).query (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
      pure (stmt + e + m)
  outputMap _ p _ := OracleMap.fst _ _

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
    QueryLog (ambient + (pathResources inputs pair p).spec) →
      List (String × Nat) := by
  rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
  exact List.map fun
    | ⟨.inl n, _⟩ => ("tag", n)
    | ⟨.inr (.inl ⟨_, _⟩), a⟩ => ("input", show Nat from a)
    | ⟨.inr (.inr ⟨.inl _, _⟩), a⟩ => ("prefix", show Nat from a)
    | ⟨.inr (.inr ⟨.inr (.inl _), _⟩), a⟩ => ("suffix", show Nat from a)
    | ⟨.inr (.inr ⟨.inr (.inr n), _⟩), _⟩ => n.elim

/-- Private output, claim with output data, decision log, final count and full trace. -/
def appendSummary
    (V : OracleVerifier ambient single Unit (fun _ => Nat) inputs (fun _ => exported))
    (out : Nat) :=
  (fun result => (result.output.1.2.1, result.output.1.2.2.map (fun r => (r.1, r.2 ())),
      describeAppend _ result.output.2.2, result.state, result.trace)) <$>
    (counter 0 appendChallenges).run ((composed V).runWithLog () seven (appendProver out))

/-! The composite decision reads the exported input and prefix message, followed by the
suffix message. The returned data is the export of those same resources. -/
example (secret : Nat) : appendSummary (prefixVerifier (pure 0) sumExport) secret =
    pure (secret, some (10, 8), [("tag", 3), ("input", 7), ("prefix", 1), ("suffix", 2)], 3,
      [⟨.inl 1, (1 : Nat)⟩, ⟨.inl 2, (2 : Nat)⟩, ⟨.inl 3, (3 : Nat)⟩]) := by
  kernel_rfl

/-! Additional QueryBounds execution coverage: the input is an `OracleFamily` slot. Composition is
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
def prefixData : prefixResources.Data :=
  (seven, payloads single ⟨(1 : Nat), ⟨⟩⟩)

/-- One query to the export, routed by the export's `impl`. -/
def exportQuery : OracleComp exported.spec Nat := liftM (exported.spec.query ⟨(), ()⟩)

/-- Answer prefix resource queries from `prefixData`. -/
def answerPrefix : QueryImpl prefixResources.spec Id :=
  fun q => pure (prefixResources.answer prefixData q)

/-- Name and answer of a prefix resource log entry. -/
def nameEntry : (z : (i : prefixResources.spec.Domain) × prefixResources.spec.Range i) →
    String × Nat
  | ⟨.inl ⟨_, _⟩, a⟩ => ("input", show Nat from a)
  | ⟨.inr ⟨.inl _, _⟩, a⟩ => ("prefix", show Nat from a)
  | ⟨.inr ⟨.inr n, _⟩, _⟩ => n.elim

/-! Logging after substitution records both raw requests and answers of one exported query. -/
example : (fun z => (z.1, z.2.map nameEntry)) (simulateQ answerPrefix
    (simulateQ (QueryImpl.compose prefixResources.spec.loggingOracle sumExport.impl)
      exportQuery).run) = (8, [("input", 7), ("prefix", 1)]) := by
  rw [← OracleComp.withQueryLog_simulateQ]
  rfl

/-! ## The hidden-bit runtime

The fixture is `ArkLibTest.Interaction.Core.Oracle.HiddenBitFixture`. -/

open Interaction.Core.HiddenBitFixture

/-! The logged guessing run retains the actual ambient history and charge, with the
challenge recorded separately in the full surface trace. -/
example (guess : Bool) (secret : Nat) :
    (fun result => (result.state, result.trace, bitCharge result.trace.fst)) <$>
      bitRuntime.run (bitVerifier.runWithLog () falseData (guessProver guess secret)) =
    (fun hidden => ((hidden, 2),
      ([⟨challengeEntry, ()⟩, ⟨.inl false, false⟩, ⟨.inl true, hidden⟩] : QueryLog bitFull), 4))
      <$> (coinSpec.query () : OracleComp coinSpec Bool) := by
  kernel_rfl

/-! The informed prover reveals the hidden bit at the seam, before the final decisions.
Its actual ordered history has charge 7 and is not a dummy-before-reveal history. -/
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

/-! The split guessing run has the same charged history as the unsplit run. -/
example (guess : Bool) (secret : Nat) :
    (fun result => (result.state, result.trace, bitCharge result.trace.fst)) <$>
      bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret)) =
    (fun hidden => ((hidden, 2),
      ([⟨challengeEntry, ()⟩, ⟨.inl false, false⟩, ⟨.inl true, hidden⟩] : QueryLog bitFull), 4))
      <$> (coinSpec.query () : OracleComp coinSpec Bool) := by
  unfold bitVerifier
  rw [OracleVerifier.run_append]
  kernel_rfl

/-! The split informed run retains the seam revelation before both decisions. -/
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

/-! The erasure laws, runtime erasure, recoverable terminal decision and logging after
substitution use only the permitted kernel axioms. -/
run_cmd do
  for decl in [``Interaction.Core.OracleVerifier.runWithLog_fst,
      ``Interaction.Core.OracleVerifier.map_fst_runWithLog,
      ``Interaction.Core.OracleVerifier.decideWithFailureLog,
      ``Interaction.Core.OracleVerifier.close_optional_ok,
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
  change (simulateQ noQueries (composite.runWithLog () (fun _ => input) (prover input))).1 =
    simulateQ noQueries (composite.run () (fun _ => input) (prover input)) at h
  dsimp only [loggedObserved, observed]
  exact congrArg (fun (obs : Observation oracleSig combined (fun _ => Nat)
    (OracleVerifier.Output finalStmt finalData)) =>
      ((projectPathAlong oracleSig combined obs.1).1, obs.2.1,
    obs.2.2.map (readClaim (projectPathAlong oracleSig combined obs.1)))) h

end Interaction.Core.DependentRoutingTests


universe uS wJ v

/-- Log erasure permits large input statements and output query types in a lawful target monad.
The input queries stay small because the decision log returns them. -/
example {ι I : Type} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol}
    {T : FreeM.Path s → Type} {A : I → Type} {J : FreeM.Path s → Type}
    {B : (p : FreeM.Path s) → J p → Type} {inputs : OracleFamily.{0, 0, 0} I A}
    {outputs : (p : FreeM.Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
    {Out : PathAlong oracleSig s → Type} {m : Type → Type v} [Monad m] [LawfulMonad m]
    (V : OracleVerifier ambient s S T inputs outputs)
    (handler : QueryImpl (ambient + challengeSpec oracleSig s) m) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient s Out) :
    Sigma.fst <$> simulateQ handler (V.runWithLog stmt data prover) =
      simulateQ handler (V.run stmt data prover) :=
  OracleVerifier.simulateQ_runWithLog_erase V handler stmt data prover

namespace Interaction.Core.LoggedExecutionTests

/-- Read per-slot provenance from the same stateful scheduling fixture as the aggregate test. -/
def tracedPhaseSummary :=
  (fun result =>
    (result.output.phases.map (fun phase =>
      (phase.prefix.length, phase.party, phase.queries.map (·.1))),
      result.output.observation.2.1, result.output.observation.2.2.map (·.1), result.state)) <$>
    (digits phasedChallenges).run (phaseVerifier.runWithTrace () seven phaseProver)

/-- The passive schedule retains every prover boundary and gives the decision its own phase. -/
theorem phase_trace_contract : tracedPhaseSummary = pure
    ([(0, .sender, [9, 9, 1]), (0, .receiver, []), (1, .sender, [4]), (1, .receiver, []),
      (2, .sender, [5]), (2, .receiver, []), (3, .sender, []), (3, .receiver, []),
      (3, .receiver, [2, 3, 6, 7])], 23, some 31, 2102563478) := by
  kernel_rfl

/-- Answer ambient requests by their tags and use the designated challenge interpreter. -/
def answerTags {s : OracleProtocol} (draw : QueryImpl (challengeSpec oracleSig s) Id) :
    QueryImpl (ambient + challengeSpec oracleSig s) Id
  | .inl n => n
  | .inr c => draw c

/-- The produced scheduling trace retains actual public challenges and hidden payloads. -/
def actualPhaseTrace : OracleVerifier.TracedRun phaseVerifier (fun _ => Nat) :=
  simulateQ (answerTags phasedChallenges)
  (phaseVerifier.runWithTrace () seven phaseProver)

/-- Reading actual prefixes observes the sampled bit and the concrete sent payload. -/
theorem actual_phase_prefixes :
    (actualPhaseTrace.phases[4]'(by decide)).prefix =
      (some ⟨true, some ⟨true, none⟩⟩ : FullPrefix phased) ∧
    actualPhaseTrace.terminalPhase.prefix =
      (some ⟨true, some ⟨true, some ⟨(17 : Nat), none⟩⟩⟩ : FullPrefix phased) := by
  constructor <;> kernel_rfl

/-- An explicit setup retains its own slot before the same sends and terminal output. -/
def phaseSetup : OracleComp ambient (Prover oracleSig ambient phased (fun _ => Nat)) := do
  let _ ← liftM (ambient.query 9)
  let _ ← liftM (ambient.query 9)
  pure (do
    let _ ← liftM (ambient.query 1)
    pure ⟨true, do
      let _ ← liftM (ambient.query 4)
      pure fun _ => do
        let _ ← liftM (ambient.query 5)
        pure ⟨(17 : Nat), pure 23⟩⟩)

/-- Execute the explicitly separate setup and interaction in the same ambient world. -/
def setupPhaseTrace : OracleVerifier.TracedRun phaseVerifier (fun _ => Nat) :=
  simulateQ (answerTags phasedChallenges)
  (phaseVerifier.runWithSetupTrace () seven phaseSetup)

/-- Setup and first-send query groups stay separate, at the same actual empty prefix. -/
theorem setup_phase_trace_contract : setupPhaseTrace.phases.map (fun phase =>
    (phase.prefix.length, phase.party, phase.queries.map (·.1))) =
      [(0, .sender, [9, 9]), (0, .sender, [1]), (0, .receiver, []),
        (1, .sender, [4]), (1, .receiver, []), (2, .sender, [5]), (2, .receiver, []),
        (3, .sender, []), (3, .receiver, []), (3, .receiver, [2, 3, 6, 7])] := by
  kernel_rfl

/-- A fixed public announcement followed by a terminal prover slot. -/
@[instance_reducible] def fixedMessage : OracleProtocol :=
  .liftBind (.message Unit) (fun _ => .pure ⟨⟩)

/-- Place the same ambient request either before the message or in the terminal prover slot. -/
def moveQuery (early : Bool) : Prover oracleSig ambient fixedMessage (fun _ => Nat) := do
  if early then let _ ← liftM (ambient.query 5)
  pure ⟨(), do
    if !early then let _ ← liftM (ambient.query 5)
    pure 7⟩

/-- The decision makes no queries and exports the unchanged input. -/
def fixedVerifier :
    OracleVerifier ambient fixedMessage Unit (fun _ => Nat) inputs (fun _ => exported) where
  decide _ _ _ := pure 31
  outputMap _ _ _ := OracleMap.fst _ _

/-- Ordinary observations, including the whole transcript and private output, are identical. -/
theorem moved_query_same_run :
    fixedVerifier.run () seven (moveQuery true) = fixedVerifier.run () seven (moveQuery false) := by
  kernel_rfl

/-- Aggregate logs cannot distinguish which prefix contained the query. -/
theorem moved_query_same_log :
    fixedVerifier.runWithLog () seven (moveQuery true) =
      fixedVerifier.runWithLog () seven (moveQuery false) := by
  kernel_rfl

/-- The fixed-message protocol has no receiver nodes. -/
def fixedDraw : QueryImpl (challengeSpec oracleSig fixedMessage) Id
  | ⟨.inl _, h⟩ => nomatch h
  | ⟨.inr ⟨_, n⟩, _⟩ => n.elim

/-- Interpret a trace using the tag as its answer; this protocol has no challenge nodes. -/
def movedQueryTrace (early : Bool) : OracleVerifier.TracedRun fixedVerifier (fun _ => Nat) :=
  simulateQ (answerTags fixedDraw) (fixedVerifier.runWithTrace () seven (moveQuery early))

/-- The actual query prefixes differ even though all aggregate observations coincide. -/
theorem moved_query_different_prefixes :
    ((movedQueryTrace true).phases.filter (fun phase => !phase.queries.isEmpty)).map
        (fun phase => phase.prefix.length) = [0] ∧
    ((movedQueryTrace false).phases.filter (fun phase => !phase.queries.isEmpty)).map
        (fun phase => phase.prefix.length) = [1] := by
  constructor <;> kernel_rfl

/-- Two oracle sends with a fixed shape provide actual join and terminal boundaries. -/
@[instance_reducible] def twoOracles : OracleProtocol :=
  .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ =>
    .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ => .pure ⟨⟩))

/-- The sent payloads and private result are distinct. -/
def twoOracleProver : Prover oracleSig ambient twoOracles (fun _ => Nat) :=
  pure ⟨(1 : Nat), pure ⟨(2 : Nat), pure 3⟩⟩

/-- Read the old payload twice and then the fresh payload, retaining the full decision log. -/
def twoOracleVerifier :
    OracleVerifier ambient twoOracles Unit (fun _ => Nat) inputs (fun _ => exported) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    let spec := ambient + (pathResources inputs twoOracles ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩).spec
    exact do
      let a : Nat ← liftM (spec.query (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
      let b : Nat ← liftM (spec.query (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
      let c : Nat ← liftM (spec.query (.inr (.inr ⟨.inr (.inl ⟨⟩), ()⟩)))
      pure (a + b + c)
  outputMap _ _ _ := OracleMap.fst _ _

/-- This fixed two-send protocol has no challenge draws. -/
def twoOracleDraw : QueryImpl (challengeSpec oracleSig twoOracles) Id
  | ⟨.inl _, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inl _⟩, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, _⟩ => n.elim

/-- Execute the strategies once to obtain the phase artifacts and their raw source log. -/
def twoOracleTrace : OracleVerifier.TracedRun twoOracleVerifier (fun _ => Nat) :=
  simulateQ (answerTags twoOracleDraw)
  (twoOracleVerifier.runWithTrace () seven twoOracleProver)

/-- The first suffix prover slot is the passive join phase. -/
def joinPhase : SlotPhase ambient twoOracles := twoOracleTrace.phases[2]'(by decide)

/-- The final decision is its own terminal phase under P1. -/
def terminalPhase : SlotPhase ambient twoOracles := twoOracleTrace.terminalPhase

/-- The selected join is an actual phase of the produced execution. -/
theorem joinPhase_mem : joinPhase ∈ twoOracleTrace.phases := List.getElem_mem _

/-- The final verifier phase belongs to the same produced execution. -/
theorem terminalPhase_mem : terminalPhase ∈ twoOracleTrace.phases :=
  twoOracleTrace.terminalPhase_mem

/-- The actual join prefix contains the first sent payload and stops before the second. -/
theorem joinPhase_prefix : joinPhase.prefix = (some ⟨(1 : Nat), none⟩ : FullPrefix twoOracles) := by
  kernel_rfl

/-- The actual terminal prefix contains both concrete payloads. -/
theorem terminalPhase_prefix : terminalPhase.prefix =
    (some ⟨(1 : Nat), some ⟨(2 : Nat), none⟩⟩ : FullPrefix twoOracles) := by
  kernel_rfl

/-- Join ownership is prover ownership; the terminal action is the verifier's decision slot. -/
theorem phase_intrinsic_owners : joinPhase.slot = .prover ∧ terminalPhase.slot = .decision := by
  constructor <;> kernel_rfl

/-- The actual join includes into the actual terminal context. -/
def producedInclusion : FullPrefix.Extends (s := twoOracles)
    joinPhase.prefix terminalPhase.prefix := by
  rw [joinPhase_prefix, terminalPhase_prefix]
  exact FullPrefix.Extends.cons (a := .oracle Nat OracleInterface.instDefault)
    (next := fun _ => .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ => .pure ⟨⟩))
    (1 : Nat) (.here _)

/-- The old canonical name remains unchanged by the actual join-to-terminal inclusion. -/
theorem joinPhase_name : terminalPhase.prefix.name
    (FullPrefix.includeIndex producedInclusion (.inl ⟨⟩)) =
      joinPhase.prefix.name (.inl ⟨⟩) := FullPrefix.includeIndex_name _ _

/-- The already sent oracle is available at the join, and the second oracle is still unavailable. -/
theorem joinPhase_availability :
    joinPhase.prefix.Available (.inl ⟨⟩) ∧
      ¬ joinPhase.prefix.Available (.inr ⟨⟨⟩, .inl ⟨⟩⟩) := by
  constructor
  · exact ⟨.inl ⟨⟩, rfl⟩
  · rintro ⟨i, hi⟩
    rcases i with _ | impossible
    · cases hi
    · exact impossible.elim

/-- The terminal context makes the newly sent oracle available under a distinct name. -/
theorem terminalPhase_availability :
    terminalPhase.prefix.Available (.inr ⟨⟨⟩, .inl ⟨⟩⟩) ∧
      terminalPhase.prefix.name (.inl ⟨⟩) ≠
        terminalPhase.prefix.name (.inr (.inl ⟨⟩)) := by
  constructor
  · exact ⟨.inr (.inl ⟨⟩), rfl⟩
  · intro equal
    cases equal

/-- The phase artifact retains the exact old/old/fresh log, private result and closed verdict. -/
theorem phase_source_log_contract :
    twoOracleTrace.decisionQueries.snd =
      [⟨.inr ⟨.inl ⟨⟩, ()⟩, (1 : Nat)⟩, ⟨.inr ⟨.inl ⟨⟩, ()⟩, (1 : Nat)⟩,
        ⟨.inr ⟨.inr (.inl ⟨⟩), ()⟩, (2 : Nat)⟩] ∧
    twoOracleTrace.observation.2.1 = 3 ∧
      twoOracleTrace.observation.2.2.map (·.1) = some 4 := by
  constructor
  · kernel_rfl
  · constructor <;> kernel_rfl

/-- The phase projection is the existing logged execution, including its raw source queries. -/
example : OracleVerifier.TracedRun.logView <$>
    twoOracleVerifier.runWithTrace () seven twoOracleProver =
    twoOracleVerifier.runWithLog () seven twoOracleProver :=
  twoOracleVerifier.runWithTrace_logView () seven twoOracleProver

#print axioms OracleVerifier.runWithTrace_erase
#print axioms OracleVerifier.runWithTrace_logView
#print axioms OracleVerifier.runWithTrace_prefixes
#print axioms FullPrefix.familyInclusion_query
#print axioms FullPrefix.contextInclusion_name

end Interaction.Core.LoggedExecutionTests

universe uQuery uInput uData

/-- Ambient provenance preserves the parent verifier's independent resource universes. -/
example {ι : Type} {S : Type uS} {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, uQuery}} {T J : FreeM.Path s → Type}
    {B : (p : FreeM.Path s) → J p → Type} {inputs : Resources.{0, uInput, uData}}
    {outputs : (p : FreeM.Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
    {Out : PathAlong oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (prover : Prover oracleSig ambient s Out) :
    OracleVerifier.AmbientTracedRun.observation <$> V.runWithAmbientTrace stmt data prover =
      V.run stmt data prover := V.runWithAmbientTrace_erase stmt data prover

namespace Interaction.Core.LoggedExecutionTests

/-- A small payload has genuinely larger query indices. -/
@[reducible] def liftedQueries : OracleInterface.{0, 1} Nat where
  Query := ULift.{1, 0} Unit
  toOC.spec _ := Nat
  toOC.impl _ := do return (← read)

/-- Attach the larger query interface to an actual small-move oracle node. -/
@[instance_reducible] def liftedNode : OracleProtocol.{0, 1} :=
  .liftBind (.oracle Nat liftedQueries) (fun _ => .pure ⟨⟩)

/-- The final decision queries the actual large-index oracle sent by the prover. -/
def liftedVerifier : OracleVerifier ambient liftedNode Unit (fun _ => Nat) inputs
    (fun _ => exported) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact do
      let sent : Nat ← liftM ((ambient + (pathResources inputs liftedNode ⟨⟨⟩, ⟨⟩⟩).spec).query
        (.inr (.inr ⟨.inl ⟨⟩, ⟨()⟩⟩)))
      pure sent
  outputMap _ _ _ := OracleMap.fst _ _

/-- No receiver node occurs in this larger-query protocol. -/
def liftedDraw : QueryImpl (challengeSpec oracleSig liftedNode) Id
  | ⟨.inl _, h⟩ => nomatch h
  | ⟨.inr ⟨_, n⟩, _⟩ => n.elim

/-- Ambient tracing runs a genuinely larger-query oracle node without returning resource indices. -/
def liftedTrace : OracleVerifier.AmbientTracedRun liftedVerifier (fun _ => Nat) :=
  simulateQ (show QueryImpl (ambient + challengeSpec oracleSig liftedNode) Id from
    fun q => match q with | .inl n => n | .inr c => liftedDraw c)
    (liftedVerifier.runWithAmbientTrace () seven (pure ⟨(17 : Nat), pure 23⟩))

/-- The same larger-query execution returns its payload, private output and actual terminal
prefix. -/
theorem lifted_trace_contract : liftedTrace.observation.2.1 = 23 ∧
    liftedTrace.observation.2.2.map (·.1) = some 17 ∧
    liftedTrace.terminalPhase.prefix = (some ⟨(17 : Nat), none⟩ : FullPrefix liftedNode) := by
  constructor
  · kernel_rfl
  · constructor <;> kernel_rfl

end Interaction.Core.LoggedExecutionTests
