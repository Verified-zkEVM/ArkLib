/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Oracle.LoggedExecution
import ArkLib.Interaction.Oracle.SentOracles
import ArkLib.Interaction.Oracle.Routing
import ArkLibTest.Interaction.Oracle.DependentRouting
import VCVio.OracleComp.Runtime
import ArkLibTest.Interaction.Support
import ArkLibTest.Interaction.Oracle.HiddenBitFixture

/-! Logged and runtime execution of passive oracle verifiers. The decision log records ambient
queries and queries to the input and message oracles, in order and with repeats, before routing.
A persistent runtime executes the logged run once as `runtime.run (V.runWithLog …)` and returns
the final state and the ordered surface trace of queries and answers. A composed verifier logs the
raw input and message queries that its routes make. -/

open PFunctor PFunctor.FreeM Interaction Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp OracleSpec

namespace Interaction.LoggedExecutionTests

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

/-- The decision's bundle on the only path of `pairSend`. -/
abbrev pairBundle := pathBundle inputs pairSend ⟨⟨⟩, ⟨⟩⟩

/-- Close to the input plus the observable coordinate of the sent pair. -/
def closeMap : OracleMap pairBundle exported where
  f x _ := (show Nat from x.1 ()) + (show Nat × Nat from x.2 (.inl ⟨⟩)).1
  impl _ := do
    let a : Nat ← (OracleMap.fst inputs (oracleMessageFamily pairSend ⟨⟨⟩, ⟨⟩⟩)).impl ⟨(), ()⟩
    let b : Nat ← (OracleMap.snd inputs (oracleMessageFamily pairSend ⟨⟨⟩, ⟨⟩⟩)).impl ⟨.inl ⟨⟩, ()⟩
    pure (a + b)
  law _ _ := rfl

/-- The decision records 1, reads the sent oracle, records 2, and accepts or rejects. -/
def pairVerifier (accept : Bool) :
    OracleVerifier ambient pairSend Unit (fun _ => Nat) inputs (fun _ => exported) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact OptionT.mk do
      let _ ← liftM ((ambient + pairBundle.spec).query (.inl 1))
      let sent : Nat ← pathLift ambient inputs (s := pairSend) ⟨⟨⟩, ⟨⟩⟩ ⟨.inl ⟨⟩, ()⟩
      let _ ← liftM ((ambient + pairBundle.spec).query (.inl 2))
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
    QueryLog (ambient + (pathBundle inputs pairSend p).spec) →
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

/-! Additional passive coverage of erasure and the one-send schedule. The port table
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

/-! Additional passive accepting and rejecting executions with a setup query. Labelled failures of
the final decision are tested separately below. Rejection is never used as a substitute for
failure. -/
example (hidden : Nat) : summary false 7 11 hidden [9] =
    (hidden, none, [("tag", 1), ("sent", 11), ("tag", 2)], [9, 0, 1, 2]) := by
  kernel_rfl

example (hidden : Nat) : summary true 7 11 hidden [9] =
    (hidden, some (11, 18), [("tag", 1), ("sent", 11), ("tag", 2)], [9, 0, 1, 2]) := by
  kernel_rfl

/-- A final decision reads the message before accepting, rejecting, or requesting a failure. -/
def decisionVerifier (mode : Nat) :
    OracleVerifier ambient pairSend Unit (fun _ => Nat) inputs (fun _ => exported) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact OptionT.mk do
      let _ ← liftM ((ambient + pairBundle.spec).query (.inl 1))
      let _ ← liftM ((ambient + pairBundle.spec).query (.inl 2))
      let sent : Nat ← pathLift ambient inputs (s := pairSend) ⟨⟨⟩, ⟨⟩⟩ ⟨.inl ⟨⟩, ()⟩
      if mode = 1 then
        let _ ← liftM ((ambient + pairBundle.spec).query (.inl 17))
        pure none
      else if mode = 2 then
        let _ ← liftM ((ambient + pairBundle.spec).query (.inl 23))
        pure none
      else pure (if mode = 0 then none else some sent)
  outputMap _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact closeMap

/-- Answered ambient requests update a persistent history; two requests fail with distinct labels.
An unanswered failing request has no query-answer entry. -/
def decisionHandler : QueryImpl ambient (ExceptT Nat (StateM (List Nat))) := fun tag => do
  if tag = 17 ∨ tag = 23 then throw tag
  modify (· ++ [tag])
  pure tag

/-- Execute the actual prover, then interpret its final decision with recoverable labelled
failure from `handler`. The private output and transcript are captured before interpreting that
decision. -/
def observedWith (handler : QueryImpl ambient (ExceptT Nat (StateM (List Nat))))
    (mode old message hidden : Nat) :=
  (do
    let ⟨tr, out, _⟩ ← simulateQ (logger pairChallenges) (TwoParty.Lens.run pairSend
      ((pairProver [9] message hidden).simulate
        ((QueryImpl.id' (ambient + challengeSpec oracleSig pairSend)).restrictLeft))
      (sampler oracleSig pairSend
        ((QueryImpl.id' (ambient + challengeSpec oracleSig pairSend)).restrictRight)))
    let p := Transcript.path tr
    let data : (pathBundle inputs pairSend p).Data := (fun _ => old, oracleMessages pairSend tr)
    let (verdict, log) ← (decisionVerifier mode).decideCatching handler () p
      (toView pairSend tr) data
    pure (out, verdict.map (Option.map fun t =>
      (t, ((decisionVerifier mode).outputMap () p (toView pairSend tr)).f data ())),
      describePair p log) : StateM (List Nat) _).run []

/-- The run of `observedWith` under the failing handler `decisionHandler`. -/
def decisionObserved (mode old message hidden : Nat) :=
  observedWith decisionHandler mode old message hidden

/-- Both failures retain their distinct labels, all earlier effects, the source answer and the
actual private output. Rejection and acceptance use the same execution and the same bundle. -/
theorem decision_outcomes (old message hidden : Nat) :
    decisionObserved 1 old message hidden =
      ((hidden, .error 17, [("tag", 1), ("tag", 2), ("sent", message)]), [9, 0, 1, 2]) ∧
    decisionObserved 2 old message hidden =
      ((hidden, .error 23, [("tag", 1), ("tag", 2), ("sent", message)]), [9, 0, 1, 2]) ∧
    decisionObserved 0 old message hidden =
      ((hidden, .ok none, [("tag", 1), ("tag", 2), ("sent", message)]), [9, 0, 1, 2]) ∧
    decisionObserved 3 old message hidden =
      ((hidden, .ok (some (message, old + message)),
        [("tag", 1), ("tag", 2), ("sent", message)]), [9, 0, 1, 2]) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Closing uses the actual input and observable message, including the second accepted example. -/
theorem decision_closing_examples (hidden : Nat) :
    (decisionObserved 3 7 11 hidden).1.2.1 = .ok (some (11, 18)) ∧
    (decisionObserved 3 13 19 hidden).1.2.1 = .ok (some (19, 32)) := ⟨rfl, rfl⟩

/-- A total handler answers every request, including 17 and 23, and records each one. -/
def totalHandler : QueryImpl ambient (ExceptT Nat (StateM (List Nat))) := fun tag => do
  modify (· ++ [tag]); pure tag

/-- The run of `observedWith` under the total handler `totalHandler`. -/
def totalObserved (mode old message hidden : Nat) :=
  observedWith totalHandler mode old message hidden

/-- Under a total handler, modes 1 and 2 reject exactly like mode 0. A core verdict is an
`Option`, so the verifier cannot return a fault itself. The labels 17 and 23 in
`decision_outcomes` come from `decisionHandler` failing. -/
theorem total_handler_faults_reject (old message hidden : Nat) :
    (totalObserved 1 old message hidden).1.2.1 = .ok none ∧
    (totalObserved 2 old message hidden).1.2.1 = .ok none ∧
    (totalObserved 0 old message hidden).1.2.1 = .ok none := ⟨rfl, rfl, rfl⟩

section CloseOptional

universe v dI uI wJ

/-- For the closing map `close` of any completed transcript, `Except.ok outcome` mapped by
`Option.map close` equals `Except.ok (outcome.map close)`. This is an equation about `Except.map`
alone and mentions no actual run. An absent verdict stays a rejection and creates no failure.
`decision_outcomes` checks the closed output of actual runs. -/
theorem close_optional_ok {ε : Type v} {ι : Type} {S : Type}
    {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}} {T : Path s → Type}
    {J : Path s → Type} {B : (p : Path s) → J p → Type}
    {inputs : OracleBundle.{0, uI, dI}}
    {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (tr : Transcript oracleSig s) (outcome : Option (T tr.path)) :
    let p := tr.path
    let pathData : (pathBundle inputs s p).Data := (data, oracleMessages s tr)
    let close := fun t => (t, (V.outputMap stmt p (toView s tr)).f pathData)
    (Except.ok outcome : Except ε (Option (T p))).map (Option.map close) =
      Except.ok (outcome.map close) := rfl

end CloseOptional

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
private output remains arbitrary and is retained by the logged outcome. -/
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
      let _ ← liftM ((unitAmbient + pairBundle.spec).query (.inl 1))
      let sent : Nat ← pathLift unitAmbient inputs (s := pairSend) ⟨⟨⟩, ⟨⟩⟩ ⟨.inl ⟨⟩, ()⟩
      let _ ← liftM ((unitAmbient + pairBundle.spec).query (.inl 2))
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

/-- The decision's bundle on the only path of `sendTwice`. -/
abbrev twiceBundle := pathBundle inputs sendTwice ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩

/-- Decision programs over the ambient and the bundle of `sendTwice`. -/
abbrev Decision := OptionT (OracleComp (ambient + twiceBundle.spec)) (List Nat)

/-- Read the scalar input oracle. -/
def readInput : OracleComp (ambient + twiceBundle.spec) Nat :=
  liftM ((ambient + twiceBundle.spec).query (.inr (.inl ⟨(), ()⟩)))

/-- Read the first scalar message oracle. -/
def readFirst : OracleComp (ambient + twiceBundle.spec) Nat :=
  pathLift ambient inputs (s := sendTwice) ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩ ⟨.inl ⟨⟩, ()⟩

/-- Read the second scalar message oracle. -/
def readSecond : OracleComp (ambient + twiceBundle.spec) Nat :=
  pathLift ambient inputs (s := sendTwice) ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩ ⟨.inr (.inl ⟨⟩), ()⟩

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
    QueryLog (ambient + (pathBundle inputs sendTwice p).spec) →
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
abbrev firstOut (tr : Transcript oracleSig sendTwice) := Fin (Nat.succ (show Nat from tr.1))

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
@[instance_reducible] def mixed : OracleProtocol :=
  .liftBind (.message Bool) (fun _ => .liftBind (.challenge Bool) (fun _ =>
    .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ => .pure ⟨⟩)))

/-- The prover records 9, 9 and 1 before the message, 4 before the challenge and 5 after it. -/
def mixedProver : Prover oracleSig ambient mixed (fun _ => Nat) := do
  for t in [9, 9, 1] do let _ ← liftM (ambient.query t)
  pure ⟨true, do
    let _ ← liftM (ambient.query 4)
    pure fun c => do
      let _ ← liftM (ambient.query 5)
      pure ⟨(if (show Bool from c) then 11 else 0 : Nat), pure 0⟩⟩

/-- The decision records 2 and 3, reads the oracle, then records 6 and 7. -/
def mixedVerifier :
    OracleVerifier ambient mixed Unit (fun _ => List Nat) inputs (fun _ => inputs) where
  decide _ p _ := by
    rcases p with ⟨b, c, ⟨⟩, ⟨⟩⟩
    exact do
      for t in [2, 3] do
        let _ ← liftM (OracleSpec.query (spec :=
          ambient + (pathBundle inputs mixed ⟨b, c, ⟨⟩, ⟨⟩⟩).spec) (.inl t))
      let sent : Nat ← pathLift ambient inputs (s := mixed) ⟨b, c, ⟨⟩, ⟨⟩⟩ ⟨.inl ⟨⟩, ()⟩
      for t in [6, 7] do
        let _ ← liftM (OracleSpec.query (spec :=
          ambient + (pathBundle inputs mixed ⟨b, c, ⟨⟩, ⟨⟩⟩).spec) (.inl t))
      pure [sent]
  outputMap _ p _ := OracleMap.fst _ _

/-- The challenge bit is `true`. -/
def mixedChallenges : QueryImpl (challengeSpec oracleSig mixed) Id
  | ⟨.inl _, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inl _⟩, _⟩ => pure true
  | ⟨.inr ⟨_, .inr ⟨_, .inl _⟩⟩, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inr ⟨_, .inr ⟨_, n⟩⟩⟩, _⟩ => n.elim

/-- A runtime whose state appends the digit `tag + 1` for each ambient query, answering with the
tag. -/
abbrev digits (draw : QueryImpl (challengeSpec oracleSig mixed) Id) :
    OracleRuntime []ₒ (ambient + challengeSpec oracleSig mixed) where
  State := Nat
  setup := pure 1
  handler
    | .inl n => do modify (· * 10 + n + 1); pure n
    | .inr c => pure (draw c)

/-! Additional passive scheduling coverage. The produced trace distinguishes the challenge
from ambient requests, and the state records the order of all ambient effects. -/
run_cmd do
  let result := runImport ((digits mixedChallenges).run
    (mixedVerifier.runWithLog () seven mixedProver))
  unless result.trace.fst.map (·.1) == [9, 9, 1, 4, 5, 2, 3, 6, 7] do
    throwError "the surface trace is wrong: {result.trace.fst.map (·.1)}"
  unless result.trace.length == 10 do throwError "the challenge draw is missing from the trace"
  unless (show Nat from result.state) == 2102563478 do
    throwError "the runtime state is wrong: {(show Nat from result.state)}"
  unless result.output.1.2.2.map (·.1) == some [11] do
    throwError "the decision did not read the oracle sent after the challenge"

/-- The public announcement, challenge receive, oracle send and private final output all
remain present when the verifier is passive. Equal setup requests remain separate effects. -/
def moveProver : Prover oracleSig ambient mixed (fun _ => Nat) := do
  let _ ← liftM (ambient.query 9)
  let _ ← liftM (ambient.query 9)
  let _ ← liftM (ambient.query 1)
  pure ⟨true, do
    let _ ← liftM (ambient.query 4)
    pure fun _ => do
      let _ ← liftM (ambient.query 5)
      pure ⟨(17 : Nat), pure 23⟩⟩

/-- The decision keeps both former reception effects at the decision entry. -/
def moveVerifier :
    OracleVerifier ambient mixed Unit (fun _ => Nat) inputs (fun _ => exported) where
  decide _ _ _ := do
    for tag in [2, 3, 6, 7] do
      let _ ← liftM (ambient.query tag)
    pure 31
  outputMap _ _ _ := OracleMap.fst _ _

/-- The summary reads the prover's and the verifier's query logs, the whole transcript, the
private output and the verdict, together with the noncommutative runtime state. No querier is
passed as an argument. -/
def moveSummary :=
  (fun result =>
    let tr := result.output.1.1
    (result.output.2.1.map (·.1), result.output.2.2.fst.map (·.1),
      tr.1, tr.2.1, tr.2.2.1, result.output.1.2.1,
      result.output.1.2.2.map (·.1), result.state)) <$>
    (digits mixedChallenges).run (moveVerifier.runWithLog () seven moveProver)

/-- The prover's and the verifier's logs keep the multiplicity of setup queries and all actions.
The transcript keeps both public directions and the final oracle message. The accumulator shows the
order of their effects. -/
theorem move_summary_contract : moveSummary =
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
      let last : Nat ← pathLift ambient inputs (s := schedule)
        ⟨b, ⟨⟨⟩, ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩⟩⟩ ⟨.inr (.inl ⟨⟩), ()⟩
      pure (if (show Bool from b) then last + (show Nat from view.val.2.2.1) else 0)
  outputMap _ _ _ := OracleMap.fst _ _

/-- The challenge service records both parts of its draw, without reading the bundle. -/
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

/-- The six-tag passive trace covers a public send, an oracle send, one challenge draw, the
receive continuation and the final decision. Tags 5 and 2 both come from that one draw. The test
also checks the private output and the final answer. -/
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

/-- The prefix bundle on the only path of `single`. -/
abbrev prefixBundle := pathBundle inputs single ⟨⟨⟩, ⟨⟩⟩

/-- Export the input plus the prefix message. -/
def sumExport : OracleMap prefixBundle exported where
  f x _ := (show Nat from x.1 ()) + (show Nat from x.2 (.inl ⟨⟩))
  impl _ := do
    let a : Nat ← (OracleMap.fst inputs (oracleMessageFamily single ⟨⟨⟩, ⟨⟩⟩)).impl ⟨(), ()⟩
    let b : Nat ← (OracleMap.snd inputs (oracleMessageFamily single ⟨⟨⟩, ⟨⟩⟩)).impl ⟨.inl ⟨⟩, ()⟩
    pure (a + b)
  law _ _ := rfl

/-- Export the prefix message. -/
def messageExport : OracleMap prefixBundle exported :=
  (OracleMap.embedding (oracleMessageFamily single ⟨⟨⟩, ⟨⟩⟩)
    (fun _ : Unit => Sum.inl PUnit.unit)).comp
    (OracleMap.snd inputs (oracleMessageFamily single ⟨⟨⟩, ⟨⟩⟩))

/-- A prefix verifier with a fixed decision program and export. -/
def prefixVerifier (program : OptionT (OracleComp (ambient + prefixBundle.spec)) Nat)
    (exportMap : OracleMap prefixBundle exported) :
    OracleVerifier ambient single Unit (fun _ => Nat) inputs (fun _ => exported) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact program
  outputMap _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact exportMap

/-- The prefix decision reads its message. -/
def readPrefix : OptionT (OracleComp (ambient + prefixBundle.spec)) Nat :=
  liftM (pathLift ambient inputs (s := single) ⟨⟨⟩, ⟨⟩⟩ ⟨.inl ⟨⟩, ()⟩)

/-- The suffix bundle on the only path of `single`. -/
abbrev suffixBundle := pathBundle exported single ⟨⟨⟩, ⟨⟩⟩

/-- The suffix records 3, reads the export and its own message, and claims their sum plus the
statement. -/
def suffixVerifier :
    OracleVerifier ambient single Nat (fun _ => Nat) exported (fun _ => exported) where
  decide stmt p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact do
      let _ ← liftM ((ambient + suffixBundle.spec).query (.inl 3))
      let e : Nat ← liftM ((ambient + suffixBundle.spec).query (.inr (.inl ⟨(), ()⟩)))
      let m : Nat ← pathLift ambient exported (s := single) ⟨⟨⟩, ⟨⟩⟩ ⟨.inl ⟨⟩, ()⟩
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
    QueryLog (ambient + (pathBundle inputs pair p).spec) →
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
suffix message. The returned data is the export of those same bundles. -/
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

/-- Realizations of the prefix bundle: input 7 and message 1. -/
def prefixData : prefixBundle.Data :=
  (seven, oracleMessages single ⟨(1 : Nat), ⟨⟩⟩)

/-- One query to the export, routed by the export's `impl`. -/
def exportQuery : OracleComp exported.spec Nat := liftM (exported.spec.query ⟨(), ()⟩)

/-- Answer prefix bundle queries from `prefixData`. -/
def answerPrefix : QueryImpl prefixBundle.spec Id :=
  fun q => pure (prefixBundle.answer prefixData q)

/-- Name and answer of a log entry for a prefix bundle query. -/
def nameEntry : (z : (i : prefixBundle.spec.Domain) × prefixBundle.spec.Range i) →
    String × Nat
  | ⟨.inl ⟨_, _⟩, a⟩ => ("input", show Nat from a)
  | ⟨.inr ⟨.inl _, _⟩, a⟩ => ("prefix", show Nat from a)
  | ⟨.inr ⟨.inr n, _⟩, _⟩ => n.elim

/-! Logging after substitution records both raw requests and answers of one exported query. -/
example : (fun z => (z.1, z.2.map nameEntry)) (simulateQ answerPrefix
    (simulateQ (QueryImpl.compose prefixBundle.spec.loggingOracle sumExport.impl)
      exportQuery).run) = (8, [("input", 7), ("prefix", 1)]) := by
  rw [← OracleComp.withQueryLog_simulateQ]
  rfl

/-! ## The hidden-bit runtime

The fixture is `ArkLibTest.Interaction.Oracle.HiddenBitFixture`. -/

open Interaction.HiddenBitFixture

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
def toFull : QueryImpl bitAmbient (OracleComp bitFull) := (QueryImpl.id' bitFull).restrictLeft

/-- Challenge draws of the composed run, as full-surface queries. -/
def fullDraw : (c : ChallengeNode oracleSig bitCombined) →
    OracleComp bitFull (challengeSpec oracleSig bitCombined c) :=
  (QueryImpl.id' bitFull).restrictRight

/-- The prefix stage of `OracleVerifier.run_append`: the prefix interaction, ending after the
seam move. -/
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

/-! The reveal sits in the seam move, which `Focal.splitPrefix` places in the prefix stage. At the
boundary the informed run has state `(hidden, 1)` and trace `[challenge, true ↦ hidden]`. The
guess run has state `(hidden, 0)` and only the challenge. -/
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

end Interaction.LoggedExecutionTests

/-! The erasure laws, runtime erasure, recoverable final decision, logging after substitution
and the laws of the queries by move and sent oracles use only the permitted kernel axioms. -/
run_cmd do
  for decl in [``Interaction.OracleVerifier.runWithLog_fst,
      ``Interaction.OracleVerifier.map_fst_runWithLog,
      ``Interaction.OracleVerifier.decideCatching,
      ``Interaction.LoggedExecutionTests.close_optional_ok,
      ``Interaction.OracleVerifier.runtime_runWithLog_erase,
      ``Interaction.OracleVerifier.simulateQ_runWithLog_erase,
      ``Interaction.OracleVerifier.map_fst_runWithQueriesByMove,
      ``Interaction.OracleVerifier.toLog_runWithQueriesByMove,
      ``Interaction.OracleVerifier.runWithQueriesByMove_before_le,
      ``Interaction.PartialTranscript.sentOracleMessageMap_query,
      ``Interaction.PartialTranscript.availableMap_node,
      ``OracleComp.withQueryLog_simulateQ] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"

namespace Interaction.DependentRoutingTests

/-- Observe the logged run with the statement and output oracle selected by its public Boolean.
The dependent claim is read through that selected oracle interface. -/
def loggedObserved (input : Nat) : Bool × Nat × Option (Nat × Nat) :=
  let obs := (simulateQ noQueries (composite.runWithLog () (fun _ => input) (prover input))).1
  ((Transcript.path obs.1).1, obs.2.1,
    obs.2.2.map (readClaim (Transcript.path obs.1)))

/-- Logging retains the unit statement and scalar realization of the zero branch. -/
example : loggedObserved 0 = (true, 13, some (0, 0)) := rfl

/-- Logging retains the natural statement and pair realization of the nonzero branch. -/
example : loggedObserved 7 = (false, 29, some (7, 7)) := rfl

/-- Erasing a logged run retains the dependent outcome for every input. -/
example (input : Nat) : loggedObserved input = observed input := by
  have h := OracleVerifier.simulateQ_runWithLog_erase composite noQueries ()
    (fun _ => input) (prover input)
  change (simulateQ noQueries (composite.runWithLog () (fun _ => input) (prover input))).1 =
    simulateQ noQueries (composite.run () (fun _ => input) (prover input)) at h
  dsimp only [loggedObserved, observed]
  exact congrArg (fun (obs : Outcome oracleSig combined (fun _ => Nat)
    (OracleVerifier.Output finalStmt finalData)) =>
      ((Transcript.path obs.1).1, obs.2.1,
    obs.2.2.map (readClaim (Transcript.path obs.1)))) h

end Interaction.DependentRoutingTests


universe v

/-- Log erasure holds in a lawful target monad with any result universe. -/
example {ι I : Type} {S : Type} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}}
    {T : FreeM.Path s → Type} {A : I → Type} {J : FreeM.Path s → Type}
    {B : (p : FreeM.Path s) → J p → Type} {inputs : OracleFamily.{0, 0, 0} I A}
    {outputs : (p : FreeM.Path s) → OracleFamily.{0, 0, 0} (J p) (B p)}
    {Out : Transcript oracleSig s → Type} {m : Type → Type v} [Monad m] [LawfulMonad m]
    (V : OracleVerifier ambient s S T inputs outputs)
    (handler : QueryImpl (ambient + challengeSpec oracleSig s) m) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient s Out) :
    Sigma.fst <$> simulateQ handler (V.runWithLog stmt data prover) =
      simulateQ handler (V.run stmt data prover) :=
  OracleVerifier.simulateQ_runWithLog_erase V handler stmt data prover

namespace Interaction.LoggedExecutionTests

/-- Read the queries by move from the same stateful scheduling fixture as the aggregate test. -/
def queriesByMoveSummary :=
  (fun result =>
    (result.output.withDecision.map (fun entry =>
      (entry.before.length, entry.role, entry.queries.map (·.1))),
      result.output.outcome.2.1, result.output.outcome.2.2.map (·.1), result.state)) <$>
    (digits mixedChallenges).run (moveVerifier.runWithQueriesByMove () seven moveProver)

/-- The passive schedule keeps every move boundary and gives the decision its own entry. -/
theorem queries_by_move_contract : queriesByMoveSummary = pure
    ([(0, .sender, [9, 9, 1]), (0, .receiver, []), (1, .sender, [4]), (1, .receiver, []),
      (2, .sender, [5]), (2, .receiver, []), (3, .sender, []), (3, .receiver, []),
      (3, .receiver, [2, 3, 6, 7])], 23, some 31, 2102563478) := by
  kernel_rfl

/-- Answer ambient requests by their tags and use the designated challenge interpreter. -/
def answerTags {s : OracleProtocol} (draw : QueryImpl (challengeSpec oracleSig s) Id) :
    QueryImpl (ambient + challengeSpec oracleSig s) Id
  | .inl n => n
  | .inr c => draw c

/-- The queries by move keep the public challenges that were drawn and the hidden oracle messages
that were sent. -/
def actualQueriesByMove : OracleVerifier.QueriesByMove moveVerifier (fun _ => Nat) :=
  simulateQ (answerTags mixedChallenges)
  (moveVerifier.runWithQueriesByMove () seven moveProver)

/-- The partial transcript of an entry shows the sampled bit and the concrete sent oracle
message. -/
theorem actual_partial_transcripts :
    (actualQueriesByMove.withDecision[4]'(by decide)).before =
      (some ⟨true, some ⟨true, none⟩⟩ : PartialTranscript oracleSig mixed) ∧
    actualQueriesByMove.decision.before =
      (some ⟨true, some ⟨true, some ⟨(17 : Nat), none⟩⟩⟩ : PartialTranscript oracleSig mixed) := by
  constructor <;> kernel_rfl

/-- An explicit setup keeps its own entry in front of the same sends and the final output. -/
def moveSetup : OracleComp ambient (Prover oracleSig ambient mixed (fun _ => Nat)) := do
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
def setupQueriesByMove : OracleVerifier.QueriesByMove moveVerifier (fun _ => Nat) :=
  simulateQ (answerTags mixedChallenges)
  (moveVerifier.runWithProverSetup () seven moveSetup)

/-- The setup entry and the first send entry stay separate, and both start from the empty partial
transcript. -/
theorem setup_queries_by_move_contract : setupQueriesByMove.withDecision.map (fun entry =>
    (entry.before.length, entry.role, entry.queries.map (·.1))) =
      [(0, .sender, [9, 9]), (0, .sender, [1]), (0, .receiver, []),
        (1, .sender, [4]), (1, .receiver, []), (2, .sender, [5]), (2, .receiver, []),
        (3, .sender, []), (3, .receiver, []), (3, .receiver, [2, 3, 6, 7])] := by
  kernel_rfl

/-- A fixed public announcement followed by a final prover move. -/
@[instance_reducible] def fixedMessage : OracleProtocol :=
  .liftBind (.message Unit) (fun _ => .pure ⟨⟩)

/-- Place the same ambient request either before the message or in the final prover move. -/
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

/-- Ordinary outcomes, including the whole transcript and private output, are identical. -/
theorem moved_query_same_run :
    fixedVerifier.run () seven (moveQuery true) = fixedVerifier.run () seven (moveQuery false) := by
  kernel_rfl

/-- Aggregate logs cannot tell which move made the query. -/
theorem moved_query_same_log :
    fixedVerifier.runWithLog () seven (moveQuery true) =
      fixedVerifier.runWithLog () seven (moveQuery false) := by
  kernel_rfl

/-- The fixed-message protocol has no receiver nodes. -/
def fixedDraw : QueryImpl (challengeSpec oracleSig fixedMessage) Id
  | ⟨.inl _, h⟩ => nomatch h
  | ⟨.inr ⟨_, n⟩, _⟩ => n.elim

/-- Log the entries of a run that answers each query with its tag; this protocol has no challenge
nodes. -/
def movedQueryByMove (early : Bool) : OracleVerifier.QueriesByMove fixedVerifier (fun _ => Nat) :=
  simulateQ (answerTags fixedDraw) (fixedVerifier.runWithQueriesByMove () seven (moveQuery early))

/-- The entries that make queries have different partial transcripts, although all aggregate
outcomes coincide. -/
theorem moved_query_different_partial_transcripts :
    ((movedQueryByMove true).withDecision.filter (fun entry => !entry.queries.isEmpty)).map
        (fun entry => entry.before.length) = [0] ∧
    ((movedQueryByMove false).withDecision.filter (fun entry => !entry.queries.isEmpty)).map
        (fun entry => entry.before.length) = [1] := by
  constructor <;> kernel_rfl

/-- Two oracle sends give a join entry and a decision entry with fixed partial transcripts. -/
@[instance_reducible] def twoOracles : OracleProtocol :=
  .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ =>
    .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ => .pure ⟨⟩))

/-- The sent oracle messages and private result are distinct. -/
def twoOracleProver : Prover oracleSig ambient twoOracles (fun _ => Nat) :=
  pure ⟨(1 : Nat), pure ⟨(2 : Nat), pure 3⟩⟩

/-- Read the old oracle message twice and then the fresh one, retaining the full decision log. -/
def twoOracleVerifier :
    OracleVerifier ambient twoOracles Unit (fun _ => Nat) inputs (fun _ => exported) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    exact do
      let a : Nat ← pathLift ambient inputs (s := twoOracles) ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩ ⟨.inl ⟨⟩, ()⟩
      let b : Nat ← pathLift ambient inputs (s := twoOracles) ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩ ⟨.inl ⟨⟩, ()⟩
      let c : Nat ← pathLift ambient inputs (s := twoOracles) ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩ ⟨.inr (.inl ⟨⟩), ()⟩
      pure (a + b + c)
  outputMap _ _ _ := OracleMap.fst _ _

/-- This fixed two-send protocol has no challenge draws. -/
def twoOracleDraw : QueryImpl (challengeSpec oracleSig twoOracles) Id
  | ⟨.inl _, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inl _⟩, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, _⟩ => n.elim

/-- Run the strategies once to obtain the queries by move and their raw source log. -/
def twoOracleQueriesByMove : OracleVerifier.QueriesByMove twoOracleVerifier (fun _ => Nat) :=
  simulateQ (answerTags twoOracleDraw)
  (twoOracleVerifier.runWithQueriesByMove () seven twoOracleProver)

/-- The first prover move of the second protocol gives the passive join entry. -/
def joinEntry : QueriesAt ambient twoOracles := twoOracleQueriesByMove.withDecision[2]'(by decide)

/-- The final decision is its own entry under P1. -/
def decisionEntry : QueriesAt ambient twoOracles := twoOracleQueriesByMove.decision

/-- The join entry is one of the entries of the run. -/
theorem joinEntry_mem : joinEntry ∈ twoOracleQueriesByMove.withDecision := List.getElem_mem _

/-- The decision entry is also one of the entries of the run. -/
theorem decisionEntry_mem : decisionEntry ∈ twoOracleQueriesByMove.withDecision :=
  twoOracleQueriesByMove.decision_mem_withDecision

/-- The join entry's partial transcript contains the first sent oracle message and stops before the
second. -/
theorem joinEntry_before :
    joinEntry.before = (some ⟨(1 : Nat), none⟩ : PartialTranscript oracleSig twoOracles) := by
  kernel_rfl

/-- The decision entry's partial transcript contains both concrete oracle messages. -/
theorem decisionEntry_before : decisionEntry.before =
    (some ⟨(1 : Nat), some ⟨(2 : Nat), none⟩⟩ : PartialTranscript oracleSig twoOracles) := by
  kernel_rfl

/-- The join entry's querier is the prover, and the decision entry's querier is the verifier's
decision. -/
theorem entry_intrinsic_queriers :
    joinEntry.querier = .prover ∧ decisionEntry.querier = .decision := by
  constructor <;> kernel_rfl

/-- The join entry's partial transcript is below the decision entry's. -/
def joinToDecisionLe : PartialTranscript.Le (s := twoOracles)
    joinEntry.before decisionEntry.before := by
  rw [joinEntry_before, decisionEntry_before]
  exact PartialTranscript.Le.cons (a := .oracle Nat OracleInterface.instDefault)
    (next := fun _ => .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ => .pure ⟨⟩))
    (1 : Nat) (.empty _)

/-- The sent oracle message keeps its node name under the inclusion from the join entry to the
decision entry. -/
theorem joinEntry_node : PartialTranscript.SentOracleMessageIndex.node decisionEntry.before
    (PartialTranscript.SentOracleMessageIndex.lift joinToDecisionLe (.inl ⟨⟩)) =
      PartialTranscript.SentOracleMessageIndex.node joinEntry.before (.inl ⟨⟩) :=
  PartialTranscript.SentOracleMessageIndex.node_lift _ _

/-- The first oracle is already sent at the join entry, and the second oracle is not yet sent. -/
theorem joinEntry_isSent :
    joinEntry.before.IsSent (.inl ⟨⟩) ∧
      ¬ joinEntry.before.IsSent (.inr ⟨⟨⟩, .inl ⟨⟩⟩) := by
  constructor
  · exact ⟨.inl ⟨⟩, rfl⟩
  · rintro ⟨i, hi⟩
    rcases i with _ | impossible
    · cases hi
    · exact impossible.elim

/-- At the decision entry the newly sent oracle is sent too, under a different node name. -/
theorem decisionEntry_isSent :
    decisionEntry.before.IsSent (.inr ⟨⟨⟩, .inl ⟨⟩⟩) ∧
      PartialTranscript.SentOracleMessageIndex.node decisionEntry.before (.inl ⟨⟩) ≠
        PartialTranscript.SentOracleMessageIndex.node decisionEntry.before (.inr (.inl ⟨⟩)) := by
  constructor
  · exact ⟨.inr (.inl ⟨⟩), rfl⟩
  · intro equal
    cases equal

/-- The queries by move keep the exact old/old/fresh decision log, the private result and the closed
verdict. -/
theorem queries_by_move_source_log_contract :
    twoOracleQueriesByMove.decisionQueries.snd =
      [⟨.inr ⟨.inl ⟨⟩, ()⟩, (1 : Nat)⟩, ⟨.inr ⟨.inl ⟨⟩, ()⟩, (1 : Nat)⟩,
        ⟨.inr ⟨.inr (.inl ⟨⟩), ()⟩, (2 : Nat)⟩] ∧
    twoOracleQueriesByMove.outcome.2.1 = 3 ∧
      twoOracleQueriesByMove.outcome.2.2.map (·.1) = some 4 := by
  constructor
  · kernel_rfl
  · constructor <;> kernel_rfl

/-- Forgetting the move boundaries gives the existing logged execution, including its raw source
queries. -/
example : OracleVerifier.QueriesByMove.toLog <$>
    twoOracleVerifier.runWithQueriesByMove () seven twoOracleProver =
    twoOracleVerifier.runWithLog () seven twoOracleProver :=
  twoOracleVerifier.toLog_runWithQueriesByMove () seven twoOracleProver

end Interaction.LoggedExecutionTests

/-- Forgetting the ambient queries by move recovers the parent verifier's run. -/
example {ι : Type} {S : Type} {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, 0}} {T J : FreeM.Path s → Type}
    {B : (p : FreeM.Path s) → J p → Type} {inputs : OracleBundle.{0, 0, 0}}
    {outputs : (p : FreeM.Path s) → OracleFamily.{0, 0, 0} (J p) (B p)}
    {Out : Transcript oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (prover : Prover oracleSig ambient s Out) :
    OracleVerifier.AmbientQueriesByMove.outcome <$> V.runWithAmbientQueriesByMove stmt data prover =
      V.run stmt data prover := V.map_fst_runWithAmbientQueriesByMove stmt data prover
