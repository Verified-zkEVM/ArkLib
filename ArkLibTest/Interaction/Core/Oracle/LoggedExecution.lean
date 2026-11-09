/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Oracle.LoggedExecution
import ArkLib.Interaction.Core.Composition

/-! Logged and runtime execution of passive oracle verifiers. The decision log records ambient
queries and queries to the input and message oracles, in order and with repeats, before routing.
A counting runtime executes the logged run once and returns the final state and the ordered
surface trace. A composed verifier logs the raw input and message queries that its routes make. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp OracleSpec

namespace Interaction.Core.LoggedExecutionTests

/-- Ambient queries carry tags, which runtimes and handlers record. -/
abbrev ambient : OracleSpec Nat := Nat →ₒ PUnit

/-- One scalar input slot. -/
@[instance_reducible] def inputs : OracleFamily Unit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- One exported scalar oracle. -/
@[instance_reducible] def exported : OracleFamily Unit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- The input data: the single slot holds 7. -/
def seven : ∀ _ : Unit, Nat := fun _ => 7

/-! ## Two scalar sends -/

/-- The prover sends two scalar oracles. -/
@[instance_reducible] def sendTwice : OracleProtocol :=
  .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ =>
    .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ => .pure ⟨⟩))

/-- The resources of the decision on the only path of `sendTwice`. -/
abbrev twiceResources := sumFamily inputs (pathFamily sendTwice ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩)

/-- Decision programs over the ambient and the resources of `sendTwice`. -/
abbrev Decision := OptionT (OracleComp (ambient + twiceResources.spec)) (List Nat)

def tag (n : Nat) : OracleComp (ambient + twiceResources.spec) Unit :=
  liftM ((ambient + twiceResources.spec).query (.inl n))

def readInput : OracleComp (ambient + twiceResources.spec) Nat :=
  liftM ((ambient + twiceResources.spec).query (.inr ⟨.inl (), ()⟩))

def readFirst : OracleComp (ambient + twiceResources.spec) Nat :=
  liftM ((ambient + twiceResources.spec).query (.inr ⟨.inr (.inl ⟨⟩), ()⟩))

def readSecond : OracleComp (ambient + twiceResources.spec) Nat :=
  liftM ((ambient + twiceResources.spec).query (.inr ⟨.inr (.inr (.inl ⟨⟩)), ()⟩))

/-- Export the input plus the first message. -/
def twiceExport : OracleMap twiceResources exported where
  f x _ := (show Nat from x (.inl ())) + (show Nat from x (.inr (.inl ⟨⟩)))
  impl _ := do
    let a : Nat ← liftM (twiceResources.spec.query ⟨.inl (), ()⟩)
    let b : Nat ← liftM (twiceResources.spec.query ⟨.inr (.inl ⟨⟩), ()⟩)
    pure (a + b)
  law _ _ := by
    simp only [simulateQ_bind]
    rfl

/-- A verifier on `sendTwice` running a fixed decision program and exporting `input + first`. -/
def twiceVerifier (program : Decision) :
    OracleVerifier ambient sendTwice Unit (List Nat) inputs exported where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    exact program
  outputMap _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    exact twiceExport

/-- The prover makes the `before` queries, sends `first`, makes the `between` queries, sends
`second`, and keeps `out` as private output. -/
def twiceProver (before between : List Nat) (first second out : Nat) :
    Prover oracleSig ambient sendTwice (fun _ => Nat) := do
  for t in before do let _ ← liftM (ambient.query t)
  pure ⟨first, do
    for t in between do let _ ← liftM (ambient.query t)
    pure ⟨second, pure out⟩⟩

/-- `sendTwice` has no challenges. -/
def twiceChallenges : QueryImpl (challengeSpec oracleSig sendTwice) Id
  | ⟨.inl _, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inl _⟩, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, _⟩ => n.elim

/-- Name and answer of each decision log entry on `sendTwice`. -/
def describe (p : FreeM.Path sendTwice) :
    QueryLog (ambient + (sumFamily inputs (pathFamily sendTwice p)).spec) →
      List (String × Nat) := by
  rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
  exact List.map fun
    | ⟨.inl n, _⟩ => ("tag", n)
    | ⟨.inr ⟨.inl _, _⟩, a⟩ => ("input", show Nat from a)
    | ⟨.inr ⟨.inr (.inl _), _⟩, a⟩ => ("first", show Nat from a)
    | ⟨.inr ⟨.inr (.inr (.inl _)), _⟩, a⟩ => ("second", show Nat from a)
    | ⟨.inr ⟨.inr (.inr (.inr n)), _⟩, _⟩ => n.elim


/-- Record ambient tags; answer challenges with `draw`. -/
def tagHandler {s : OracleProtocol} (draw : QueryImpl (challengeSpec oracleSig s) Id) :
    QueryImpl (ambient + challengeSpec oracleSig s) (StateM (List Nat))
  | .inl n => modify (· ++ [n])
  | .inr c => pure (draw c)

/-- The decision reads the first message, the input, then the second message twice. -/
def readAll : Decision := do
  let first ← readFirst
  let input ← readInput
  let second ← readSecond
  let again ← readSecond
  pure [first, input, second, again]

def readAllProver := twiceProver [5] [6] 11 19 4

/-! LoggedExecutionExample 1, restated: the frozen row compares two traces of a mid-run verifier
with effects between the sends. The decision is passive, so the check is that logging keeps the
ambient schedule, the verdict and the output of the unlogged run. -/
run_cmd do
  let V := twiceVerifier (do tag 9; readAll)
  let (logged, loggedTrace) :=
    (simulateQ (tagHandler twiceChallenges) (V.runWithLog () seven readAllProver)).run []
  let (plain, plainTrace) :=
    (simulateQ (tagHandler twiceChallenges) (V.run () seven readAllProver)).run []
  unless loggedTrace == [5, 6, 9] && loggedTrace == plainTrace do
    throwError "logging changed the ambient schedule: {loggedTrace} vs {plainTrace}"
  unless logged.1.2.1 == plain.2.1 do throwError "logging changed the private output"
  unless (logged.1.2.2.map (·.1)) == (plain.2.2.map (·.1)) do
    throwError "logging changed the verdict"
  unless logged.2.1.map (·.1) == [5, 6] do
    throwError "the prover log is wrong: {logged.2.1.map (·.1)}"

/-! LoggedExecutionExample 2, restated: the frozen row logs resource queries made between the
sends and re-indexes old slots when the context grows. The decision is passive and its log is over
`oracleIdx` of the whole path, so the check is the order and repeats of its end queries:
first 11, input 7, second 19, second 19. Example 3, restated: the log holds only the decision's
queries; computing the output data does not query anything. Example 4: the output data is
`input + first = 18`. -/
run_cmd do
  let (z, _) := (simulateQ (tagHandler twiceChallenges)
    ((twiceVerifier readAll).runWithLog () seven readAllProver)).run []
  let log := describe _ z.2.2
  unless log == [("first", 11), ("input", 7), ("second", 19), ("second", 19)] do
    throwError "the decision log lost order or repeats: {log}"
  match z.1.2.2 with
  | none => throwError "the decision rejected"
  | some (claim, data) =>
    unless claim == [11, 7, 19, 19] do throwError "the claim is wrong: {claim}"
    unless data () == 18 do throwError "the output data is not input + first"

/-- The decision records 1, reads the first message, records 2, and accepts or rejects. -/
def checkFirst (accept : Bool) : Decision := do
  tag 1
  let first ← readFirst
  tag 2
  if accept then pure [first] else failure

/-! LoggedExecutionExample 5 and TerminalRun TR4, restated: the frozen rows reject in a
terminal phase. Here the end decision rejects with `none`, and the log keeps its queries,
including the resource query that answered 19. -/
run_cmd do
  let (z, trace) := (simulateQ (tagHandler twiceChallenges)
    ((twiceVerifier (checkFirst false)).runWithLog () seven
      (twiceProver [9, 0] [] 19 3 5))).run []
  unless z.1.2.2.isNone do throwError "the decision should reject"
  let log := describe _ z.2.2
  unless log == [("tag", 1), ("first", 19), ("tag", 2)] do
    throwError "rejection lost the decision log: {log}"
  unless trace == [9, 0, 1, 2] do throwError "rejection lost effects: {trace}"


/-! ## Runtime execution -/

/-- A runtime that counts ambient queries from `start` and answers challenges with `draw`. -/
def counter {s : OracleProtocol} (start : Nat) (draw : QueryImpl (challengeSpec oracleSig s) Id) :
    OracleRuntime []ₒ (ambient + challengeSpec oracleSig s) where
  State := Nat
  setup := pure start
  handler
    | .inl _ => modify (· + 1)
    | .inr c => pure (draw c)

/-- Evaluate a computation with no imports. -/
def runImport {α : Type} (program : OracleComp []ₒ α) : α :=
  simulateQ (fun q => q.elim : QueryImpl []ₒ Id) program

/-- Runtime execution of a `sendTwice` verifier from a counter starting at `start`. -/
def twiceRuntimeRun (start : Nat) (program : Decision) (prover : Prover oracleSig ambient sendTwice
    (fun _ => Nat)) :=
  runImport ((twiceVerifier program).runWithRuntime (counter start twiceChallenges) () seven
    prover)

/-- The decision reads both messages in order. -/
def readBoth : Decision := do
  let first ← readFirst
  let second ← readSecond
  pure [first, second]

/-! Frozen `NativeRuntime.lean` example 1, restated: the frozen runtime's setup query 0 becomes the
prover's first query, and the input slot is an `OracleFamily` slot. One runtime execution returns
the claim `[2, 3]`, the private output, the decision log `[first 2, second 3]`, the final count 3
and the surface trace `[0, 1, 2]`. Example 2 there: with no setup query, the claim is `[1, 2]`, the
count 2 and the trace `[1, 2]`. -/
run_cmd do
  let result := twiceRuntimeRun 0 readBoth (twiceProver [0, 1] [2] 2 3 0)
  unless result.output.1.2.1 == 0 do throwError "the private output was lost"
  unless result.output.1.2.2.map (·.1) == some [2, 3] do throwError "the claim is wrong"
  unless describe _ result.output.2.2 == [("first", 2), ("second", 3)] do
    throwError "the decision log is wrong: {describe _ result.output.2.2}"
  unless (show Nat from result.state) == 3 do throwError "the final runtime state is wrong"
  unless result.trace.fst.map (·.1) == [0, 1, 2] do
    throwError "the surface trace is wrong: {result.trace.fst.map (·.1)}"
  let direct := twiceRuntimeRun 0 readBoth (twiceProver [1] [2] 1 2 0)
  unless direct.output.1.2.2.map (·.1) == some [1, 2] do throwError "the claim is wrong"
  unless (show Nat from direct.state) == 2 do throwError "the final runtime state is wrong"
  unless direct.trace.fst.map (·.1) == [1, 2] do throwError "the surface trace is wrong"

/-! RuntimeExample 1, restated: the frozen verifier's reception query 1 moves into the decision,
so the order `[0, 1, 2]` is unchanged. A runtime starting at 7 ends at 10, and the private output
is the hidden value. -/
run_cmd do
  for hidden in [0, 42] do
    let result := twiceRuntimeRun 7 (checkFirst true) (twiceProver [0] [] 11 3 hidden)
    unless result.output.1.2.1 == hidden do throwError "the private output was lost"
    unless (show Nat from result.state) == 10 do throwError "the final runtime state is wrong"
    unless result.trace.fst.map (·.1) == [0, 1, 2] do throwError "the surface trace is wrong"

/-! TerminalRun TR1 and TR2, restated: the frozen rows run to a fault. The decisions here have
no fault outcome, so the rows run to a rejection. The setup query 9 becomes the prover's first
query, and the frozen reception query 1 moves into the decision. The trace keeps the prover and
decision effects `[9, 0, 1, 2]`, and the result keeps the private output 5 and the decision log,
whose resource query answered the sent value 11.

PhasedRun 5, restated: phase grouping is dropped. The accepting decision on input 7 and sent 11
has the same trace and log, and its output data closes to 18. -/
run_cmd do
  let rejected := twiceRuntimeRun 0 (checkFirst false) (twiceProver [9, 0] [] 11 3 5)
  unless rejected.output.1.2.2.isNone do throwError "the decision should reject"
  unless rejected.output.1.2.1 == 5 do throwError "rejection lost the private output"
  unless describe _ rejected.output.2.2 == [("tag", 1), ("first", 11), ("tag", 2)] do
    throwError "rejection lost the decision log"
  unless rejected.trace.fst.map (·.1) == [9, 0, 1, 2] do
    throwError "rejection lost effects: {rejected.trace.fst.map (·.1)}"
  let accepted := twiceRuntimeRun 0 (checkFirst true) (twiceProver [9, 0] [] 11 3 5)
  match accepted.output.1.2.2 with
  | none => throwError "the decision should accept"
  | some (claim, data) =>
    unless claim == [11] && data () == 18 do throwError "the accepted output is wrong"
  unless describe _ accepted.output.2.2 == [("tag", 1), ("first", 11), ("tag", 2)] do
    throwError "the decision log is wrong"
  unless accepted.trace.fst.map (·.1) == [9, 0, 1, 2] do throwError "the surface trace is wrong"


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
def phasedVerifier : OracleVerifier ambient phased Unit (List Nat) inputs inputs where
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

/-- A runtime whose state appends the digit `tag + 1` for each ambient query. -/
def digits (draw : QueryImpl (challengeSpec oracleSig phased) Id) :
    OracleRuntime []ₒ (ambient + challengeSpec oracleSig phased) where
  State := Nat
  setup := pure 1
  handler
    | .inl n => modify (· * 10 + n + 1)
    | .inr c => pure (draw c)

/-! PhasedRun 2, restated: the frozen setup query 9 becomes the prover's first query, the
frozen mid-run verifier queries move into the end decision, and the phase summary is dropped.
One state sees the prover's queries `[9, 9, 1, 4, 5]` and then the decision's `[2, 3, 6, 7]`;
the challenge draw is part of the surface trace but leaves the state alone. -/
run_cmd do
  let result := runImport (phasedVerifier.runWithRuntime (digits phasedChallenges) () seven
    phasedProver)
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
    OracleVerifier ambient single Unit Nat inputs exported where
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

/-- The suffix reads the export and its own message, and claims their sum plus the statement. -/
def suffixVerifier : OracleVerifier ambient single Nat Nat exported exported where
  decide stmt p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact do
      let e : Nat ← liftM ((ambient + suffixResources.spec).query (.inr ⟨.inl (), ()⟩))
      let m : Nat ← liftM ((ambient + suffixResources.spec).query (.inr ⟨.inr (.inl ⟨⟩), ()⟩))
      pure (stmt + e + m)
  outputMap _ p _ := OracleMap.embedding (sumFamily exported (pathFamily single p)) .inl

/-- The composite output map is the suffix output map after `suffixRoute`. -/
def compatible (V : OracleVerifier ambient single Unit Nat inputs exported) :
    OracleVerifier.OutputCompatibility V (fun _ => suffixVerifier) where
  outputMap stmt p v :=
    (suffixVerifier.outputMap 0 (Path.split single (fun _ => single) p).2
      (View.split single (fun _ => single) p v).2).comp (OracleVerifier.suffixRoute V stmt p v)
  agrees _ _ _ _ _ _ := rfl

def composed (V : OracleVerifier ambient single Unit Nat inputs exported) :=
  V.append (fun _ => suffixVerifier) (compatible V)

/-- The prover records 1, sends 1, records 2 at the seam and 3 before sending 2. -/
def pairProver (out : Nat) : Prover oracleSig ambient pair (fun _ => Nat) :=
  Prover.append (s₂ := fun _ => single)
    (do let _ ← liftM (ambient.query 1); pure ⟨(1 : Nat), pure out⟩)
    (fun _ memory => do
      let _ ← liftM (ambient.query 2)
      pure do
        let _ ← liftM (ambient.query 3)
        pure ⟨(2 : Nat), pure memory⟩)

/-- `pair` has no challenges. -/
def pairChallenges : QueryImpl (challengeSpec oracleSig pair) Id
  | ⟨.inl _, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inl _⟩, h⟩ => nomatch h
  | ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, _⟩ => n.elim

/-- Name and answer of each composite decision log entry. -/
def describePair (p : FreeM.Path pair) :
    QueryLog (ambient + (sumFamily inputs (pathFamily pair p)).spec) →
      List (String × Nat) := by
  rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
  exact List.map fun
    | ⟨.inl n, _⟩ => ("tag", n)
    | ⟨.inr ⟨.inl _, _⟩, a⟩ => ("input", show Nat from a)
    | ⟨.inr ⟨.inr (.inl _), _⟩, a⟩ => ("prefix", show Nat from a)
    | ⟨.inr ⟨.inr (.inr (.inl _)), _⟩, a⟩ => ("suffix", show Nat from a)
    | ⟨.inr ⟨.inr (.inr (.inr n)), _⟩, _⟩ => n.elim

def pairRuntimeRun (V : OracleVerifier ambient single Unit Nat inputs exported) (out : Nat) :=
  runImport ((composed V).runWithRuntime (counter 0 pairChallenges) () seven (pairProver out))

/-! Frozen `NativeRuntime.lean` example 4, restated: the exported view is an `OracleMap` whose
`impl` reads the input and the prefix message, composition is `OracleVerifier.append`, and the input
is an `OracleFamily` slot. The suffix's one export query logs as the two raw queries made by its
route, then the suffix reads its own message: `[input 7, prefix 1, suffix 2]`. The claim is
`0 + 8 + 2 = 10`, the private output is kept, the count is 3 and the trace `[1, 2, 3]`.

QueryBounds 8, restated: the output data, computed by the composite output map `f` on this run's
resources, is the export 8, alongside the same log. -/
run_cmd do
  for secret in [0, 13] do
    let result := pairRuntimeRun (prefixVerifier (pure 0) sumExport) secret
    unless describePair _ result.output.2.2 == [("input", 7), ("prefix", 1), ("suffix", 2)] do
      throwError "the composite decision log is wrong: {describePair _ result.output.2.2}"
    unless result.output.1.2.1 == secret do throwError "the private output was lost"
    match result.output.1.2.2 with
    | none => throwError "the composite decision rejected"
    | some (claim, data) =>
      unless claim == 10 do throwError "the claim is wrong: {claim}"
      unless data () == 8 do throwError "the output data is not this run's export"
    unless (show Nat from result.state) == 3 do throwError "the final runtime state is wrong"
    unless result.trace.fst.map (·.1) == [1, 2, 3] do throwError "the surface trace is wrong"

/-! QueryBounds 5, restated: the input is an `OracleFamily` slot and composition is
`OracleVerifier.append`. The prefix reads its message and exports it; the suffix's export query
reads the prefix message again. The log keeps the repeat: `[prefix 1, prefix 1, suffix 2]`, the
claim is `1 + 1 + 2 = 4` and the private output is 3. -/
run_cmd do
  let result := pairRuntimeRun (prefixVerifier readPrefix messageExport) 3
  unless describePair _ result.output.2.2 == [("prefix", 1), ("prefix", 1), ("suffix", 2)] do
    throwError "the composite decision log is wrong: {describePair _ result.output.2.2}"
  unless result.output.1.2.1 == 3 do throwError "the private output was lost"
  unless result.output.1.2.2.map (·.1) == some 4 do throwError "the claim is wrong"

/-- Realizations of the prefix resources: input 7 and message 1. -/
def prefixData : ∀ i, prefixResources.Realization i :=
  sumData seven (payloads single ⟨(1 : Nat), ⟨⟩⟩)

/-- One query to the export, routed by the export's `impl`. -/
def exportQuery : OracleComp exported.spec Nat := liftM (exported.spec.query ⟨(), ()⟩)

/-! Frozen `NativeRuntime.lean` example 5, restated: the route is the `impl` of the exported
`OracleMap`, answered by the prefix realizations. Logging after substitution records the two raw
queries `[input 7, prefix 1]` of the one export query, which answers 8; the logging handler of
`withQueryLog_simulateQ` gives the same answer and log. -/
run_cmd do
  let answer : QueryImpl prefixResources.spec Id :=
    fun q => pure (prefixResources.behaviorOfRealizations prefixData q)
  let name : (z : (i : prefixResources.spec.Domain) × prefixResources.spec.Range i) →
      String × Nat
    | ⟨⟨.inl _, _⟩, a⟩ => ("input", show Nat from a)
    | ⟨⟨.inr (.inl _), _⟩, a⟩ => ("prefix", show Nat from a)
    | ⟨⟨.inr (.inr n), _⟩, _⟩ => n.elim
  let (value, log) := simulateQ answer (simulateQ sumExport.impl exportQuery).withQueryLog
  unless value == 8 && log.map name == [("input", 7), ("prefix", 1)] do
    throwError "logging after routing is wrong: {value}, {log.map name}"
  let (value', log') := simulateQ answer
    (simulateQ (QueryImpl.compose prefixResources.spec.loggingOracle sumExport.impl)
      exportQuery).run
  unless value' == value && log'.map name == log.map name do
    throwError "the logging handler disagrees with logging after substitution"

example : (simulateQ sumExport.impl exportQuery).withQueryLog =
    (simulateQ (QueryImpl.compose prefixResources.spec.loggingOracle sumExport.impl)
      exportQuery).run :=
  OracleComp.withQueryLog_simulateQ sumExport.impl exportQuery

end Interaction.Core.LoggedExecutionTests

/-! LoggedExecutionExample 6 and 7, `NativeRuntime.lean` rows 7, 8 and 9, and TerminalRun TR6: the
erasure laws, the runtime laws and logging after substitution stay axiom-clean. TR6 restated: the
frozen row guards the terminal erase law; the decisions have no terminal layer, so it guards
`runWithLog_fst` and `runWithLog_erase`. -/
run_cmd do
  for decl in [``Interaction.Core.OracleVerifier.runWithLog_fst,
      ``Interaction.Core.OracleVerifier.runWithLog_erase,
      ``Interaction.Core.OracleVerifier.runWithRuntime_eq,
      ``Interaction.Core.OracleVerifier.runWithRuntime_erase,
      ``OracleComp.withQueryLog_simulateQ] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
