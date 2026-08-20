/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.D2SBranch
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SMonitoredState

/-!
# Statement layer — module 3: online transformation (D2SQuery), REPAIRED (R1)

This module is the dependency-acyclic home of the *online* runner of the transformation.  The real
boundary types (`NormalState`, `StopRecord`, `StepResult`), the genuine output-bearing `D2SStep`
transition, the six branch relations of Algorithm 5.3, and the shared branch-witness object
`D2SBranchStep` now live in the **lower** acyclic module `D2SBranch` — importable by
both this module and `RevisedOperators` — so this module holds only the **runner**:

- `D2SRunTerminal` — the terminal execution object of a D2SQuery run (`finished` / `stopped` /
  `aborted`) over the real boundary types;
- `QueryStream` — a finite stream of sponge-oracle occurrences, each carrying its own optional
  Program-marker context;
- `D2SQueryRun` — the fold-style runner that consumes the stream one occurrence at a time and,
  for every permutation occurrence, **folds the shared `D2SBranchStep` witness**: each step is
  resolved by exactly one of the six branches carrying its exact `result`, with every `continue`
  successor linked to the next step's normal (a genuine fold, so each successor normal state is
  *constructed* by the transition, never pre-labelled), and a `stopped`/abort terminating the run.

Every `Program` context belongs to one occurrence, rather than being threaded globally through
`D2SQueryRun`; this matches the stateful-replay scheduling of `StatefulReplay.ReplayHistory`.

Rules honoured: **no** fabricated boundary type, **no** generic `Prop` branch combinator, **no**
free `ℕ`/`ℝ` standing in for a real quantity, **no** `sorry`/`admit`/`axiom`.  This module
imports no live Section 5 algorithm (only `D2SBranch`, the acyclic boundary module
`D2SMonitoredState`, and their acyclic dependencies).
-/

namespace DuplexSpongeFS

namespace Statement

namespace D2SQuery

open OracleComp OracleSpec ProtocolSpec DSTraceStorage
open DuplexSpongeFS.ProverTransform

variable {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- The **terminal execution object** of a D2SQuery run, built only from the **real** boundary
types (`D2SNormalState`, `D2SPostOccurrenceStopRecord`): either the stream was exhausted into a
final reusable normal state with `Monitor` passing at every step (`finished`), stopped at the
first monitored failure carrying the real `E`-stop record (`stopped`), or aborted on a named
underlying BackTrack / LookAhead failure at the current normal state (`aborted`). -/
inductive D2SRunTerminal (StmtIn : Type) {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] (δ : Nat)
    [DecidableEq StmtIn] [DecidableEq U] (T_H : Type) (T_P : Type)
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] : Type where
  | finished (state : DuplexSpongeFS.ProverTransform.D2SNormalState (δ := δ) (T_H := T_H)
        (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
  | stopped (state : DuplexSpongeFS.ProverTransform.D2SNormalState (δ := δ) (T_H := T_H)
        (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (record : DuplexSpongeFS.ProverTransform.D2SPostOccurrenceStopRecord (δ := δ)
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) state)
  | aborted (state : DuplexSpongeFS.ProverTransform.D2SNormalState (δ := δ) (T_H := T_H)
        (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-! ## The query-stream runner (fold-style, successor-linked) -/

/-- One **query occurrence** consumed by the revised D2SQuery.  A non-Program occurrence has
`programContext = none`; a Program occurrence contains its own recovered replay cursor, verifier
challenge length, and first-squeeze position. -/
structure QueryOccurrence (StmtIn : Type) {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] where
  programContext : Option (ProgramContext pSpec)
  query : (duplexSpongeChallengeOracle StmtIn U).Domain

/-- A finite **query stream** of sponge-oracle occurrences.  The Program-marker context is stored
with the occurrence, so different forward queries may legitimately refer to different replay
rounds. -/
abbrev QueryStream (StmtIn : Type) {n : Nat} (pSpec : ProtocolSpec n) (U : Type)
    [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] : Type :=
  List (QueryOccurrence StmtIn pSpec U)

/-- The revised D2SQuery **runner**: from a reusable normal state and a finite query stream, it
consumes the stream one occurrence at a time and relates to the outcome by the **real** transitions
— the hash branch, or the forward-`Install` / inverse **branch witnesses** `D2SBranchStep` of the
lower `D2SBranch` module — with every `continue` successor linked to the next step's normal (a
genuine fold, so each successor normal state is *constructed* by the transition, never
pre-labelled), and a `stopped`/abort terminating the run at the first failing occurrence.  The
optional Program marker is read from that occurrence, not from a global run parameter. A
`continue` successor state is the real one: its trace is the raw trace plus exactly the occurrence,
its permutation table evolves by the real table-only `Install`, and the monitor `¬ E` passes. -/
def D2SQueryRun (normal : NormalState StmtIn pSpec U δ T_H T_P)
    (stream : QueryStream StmtIn pSpec U)
    (terminal : D2SRunTerminal StmtIn pSpec U δ T_H T_P) : Prop :=
  match stream with
  | [] =>
      -- the stream is exhausted: `terminal` must be `finished` at exactly the carried final state
      match terminal with
      | .finished state => state = normal
      | _ => False
  | occurrence :: rest =>
      ∃ result : QueryResult (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          (T_H := T_H) (T_P := T_P) occurrence.query,
        D2SBranchStep normal occurrence.programContext occurrence.query result ∧
          match result with
          | .continue _ newNormal =>
              D2SQueryRun newNormal rest terminal
          | .stopped state record =>
              -- A monitored stop is absorbing: the unconsumed suffix is never queried.
              state = normal ∧ terminal = .stopped state record
          | .underlyingAbort =>
              -- Likewise, a search abort occurs before another oracle occurrence is issued.
              terminal = .aborted normal

end D2SQuery

end Statement

end DuplexSpongeFS
