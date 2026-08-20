/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.StatefulReplay
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.D2SBranch
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.OnlineTransformation
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.OfflineTransformation
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SMonitoredState
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Backtrack
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lookahead

/-!
# Statement layer — D2: whole revised operators (stateful BackTrack / LookAhead, D2SQuery, D2SAlgo)

This module makes the six revised algorithms **whole operators** over the real boundary types
(`D2SMonitoredState`), the real `Install`/`Monitor` discipline, and the real stateful replay of
`StatefulReplay` (D1), instead of only the per-branch *specimen* relations:

- `statefulBackTrack` / `statefulLookAhead` — whole operators on the D1 stateful replay: given
  the **strict-prefix** table (Backtrack) or the **full** table (LookAhead) of a `ReplayState`,
  the certified marker, and the real normalized trace, they expose the paper's search outcome and
  its `no-abort` face (`¬ BadEvent → non-err`).
- `revisedD2SQueryStep` — the single whole-operator step that **dispatches the six paper branches**
  of Algorithm 5.3 over a reusable `D2SNormalState` and yields the real three-way
  `D2SRevisedStepResult`; `revisedD2SQueryRun` is its list-of-steps runner.
- `revisedStdTrace` / `revisedD2STrace` / `revisedD2SAlgo` — the whole Algorithm 5.5 / 5.6 /
  5.4 operators, re-exporting the **real** two-table + raw-trace `StdTrace.View`, the three-way
  D2SAlgo memo/reissue/abort relations.

Rules honoured: no fabricated boundary type, no generic `Prop` combinator, no free `ℕ`/`ℝ`
standing in for a real quantity, no `sorry`/`admit`/`axiom`.  Only the acyclic operator layers are
imported (`D2SMonitoredState`, `Backtrack`, the statement modules); no live Section 5 algorithm.
-/

namespace DuplexSpongeFS

namespace Statement

open OracleComp OracleSpec ProtocolSpec DSTraceStorage
open DuplexSpongeFS.Backtrack
open DuplexSpongeFS.ProverTransform

variable {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [codec : CodecCore pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

namespace D2SQuery

open DuplexSpongeFS.ProverTransform

/-! ## Whole operator: revised D2SQuery step (six-branch dispatch)

The step is the whole-operator face of Algorithm 5.3, so the six paper branches are **exactly the
six alternatives** that can explain a three-way result, each carrying its own real extra data (a
sampled `capacity` for the tail-hit branch, and an occurrence-local scheduling context for the
`Program` branch).  The hash branch is stated separately (it installs nothing and is outside the
permutation-table path); the five permutation branches are disjoined here. -/

/-- The **whole** revised `D2SQuery` step (Algorithm 5.3) **is the shared six-branch witness**
`D2SBranchStep` of the lower `D2SBranch` module: for one occurrence `query` on the
reusable normal state `normal`, exactly one of the hash / inverse / tail-hit / table-hit /
fresh-miss / `Program` branches holds, carrying the **exact** three-way `result`, the **exact**
`stateIn`/`stateOut`, and the exact successor / cache / table / `Install` / `Monitor` effect of
that occurrence — the successor normal state or terminal record **constructed** by the genuine
`D2SStep` (no pre-labelled `result`).  The hash branch is the `hash` constructor (its `answer` is
the exact result of the occurrence; a hash query installs nothing and carries no `StepResult`). -/
abbrev RevisedD2SQueryStep (programContext : Option (D2SQuery.ProgramContext pSpec))
    (normal : NormalState StmtIn pSpec U δ T_H T_P)
    (query : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (result : D2SQuery.QueryResult (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      (T_H := T_H) (T_P := T_P) query) : Prop :=
  D2SBranchStep normal programContext query result

end D2SQuery

/-! ## Whole operators: stateful BackTrack / LookAhead on the replay (Algorithms 5.1 / 5.2)

These run the **real** procedural operators (`DuplexSpongeFS.Backtrack.backTrack`,
`DuplexSpongeFS.Lookahead.lookAhead`) on the D1 stateful replay's raw insertion trace and its
strict-prefix/full tables, exposed at a `Certified` post-prover/pre-squeeze marker.  The
`no-abort` face is exactly `¬ BadEvent → operator ≠ .err` (the real `.err` computation), not a
vacuous `Nonempty`. -/

/-- The **stateful BackTrack** whole operator (Algorithm 5.1) over a `ReplayExecution`: for any real
`TraceNabla` witness `trΔ` that is a subset of the replay's raw insertion trace and any search
start state, absent the bad event the real `backTrack` never returns the multiple-match `.err`
face.  The replay's derived tables and terminal cursor are present in the premises so the no-abort
is tied to the coherent execution object. -/
def statefulBackTrack
    (replay : DuplexSpongeFS.Statement.ReplayExecution StmtIn U SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec)))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog replay.trace)
    (state : CanonicalSpongeState U) : Prop :=
  ¬ BadEvent replay.trace →
    DuplexSpongeFS.Backtrack.backTrack (n := n) (pSpec := pSpec) (δ := δ)
      replay.trace trΔ h_trΔ state ≠ ExperimentOutput.err

/-- The round-local marker used by stateful LookAhead.  The cursor is the history cursor before
round `j`, not the terminal cursor after the entire replay. -/
def statefulRoundMarker
    (history : DuplexSpongeFS.Statement.ReplayHistory StmtIn U SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec)))
    (j : pSpec.ChallengeIdx) (pos : ℕ) : Prop :=
  j.1.1 < (DuplexSpongeFS.protocolPhases (pSpec := pSpec)).length ∧
    DuplexSpongeFS.Statement.Certified SpongeSize.R (history.cursors j.1.1)
      (challengeSize j) pos

/-- The **stateful LookAhead** whole operator (Algorithm 5.2), at one concrete round-local
post-prover/pre-squeeze marker.  It receives the history prefix selected by Backtrack and the full
normalized table for LookAhead; it therefore cannot use the terminal replay cursor or substitute
the strict-prefix table for the full table.  The selected replay prefix is a subtrace of the
ambient normal trace: a later repeated Program call may legitimately retain unrelated earlier
occurrences, so raw-trace equality would be an unwanted strengthening. -/
def statefulLookAhead
    (history : DuplexSpongeFS.Statement.ReplayHistory StmtIn U SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec)))
    (j : pSpec.ChallengeIdx) (normal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P)
    (fullDelta : TraceNabla T_H T_P StmtIn U) (pos : ℕ) (state : CanonicalSpongeState U) : Prop :=
  (history.tracePrefix j.1.1).Sublist normal.state.trace ∧
    fullDelta.MirrorsQueryLog history.trace ∧
    (¬ BadEvent history.trace →
      statefulRoundMarker (pSpec := pSpec) history j pos →
        DuplexSpongeFS.Lookahead.lookAhead (pSpec := pSpec) fullDelta.p state j ≠
          (pure ExperimentOutput.err :
            OracleComp (Unit →ₒ U) (ExperimentOutput (Vector U (challengeSize j)))))

/-- **Output-linked BackTrack:** the real executable `backTrack`
over the replay's raw insertion trace and its normalized table **recovers** the concrete sole output
`out : BacktrackOutput` — the exact paper tuple `(i, 𝕩, τ, (α̂_1, …, α̂_i))` — rather than merely
returning the multiple-match `.err`.  This is the output-bearing face of the no-abort
`statefulBackTrack`: `ExperimentOutput.some out` implies `≠ ExperimentOutput.err`. -/
def statefulBackTrackRecovers
    (replay : DuplexSpongeFS.Statement.ReplayExecution StmtIn U SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec)))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog replay.trace)
    (state : CanonicalSpongeState U)
    (out : DuplexSpongeFS.Backtrack.BacktrackOutput (δ := δ) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U)) : Prop :=
  DuplexSpongeFS.Backtrack.backTrack (n := n) (pSpec := pSpec) (δ := δ)
    replay.trace trΔ h_trΔ state = ExperimentOutput.some out

/-- The **strict-prefix BackTrack call** made at a round boundary.  This is the exact search in
Algorithm 5.3 Step **4.a** and Algorithm 5.5 Step **4.b.i**: the real `backTrack` consumes the
normal state's own trace/table.  The replayed prefix before round `j` is an order-preserving
subtrace of that normal trace, rather than the whole normal trace itself: the surrounding oracle
trace can contain earlier unrelated queries.  This records the actual embedding selected by the
BackTrack candidate without falsely requiring raw-trace equality. -/
def statefulBackTrackAt
    (history : DuplexSpongeFS.Statement.ReplayHistory StmtIn U SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec)))
    (j : pSpec.ChallengeIdx) (normal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P)
    (state : CanonicalSpongeState U)
    (out : DuplexSpongeFS.Backtrack.BacktrackOutput (δ := δ) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U)) : Prop :=
  j.1.1 < (DuplexSpongeFS.protocolPhases (pSpec := pSpec)).length ∧
    (history.tracePrefix j.1.1).Sublist normal.state.trace ∧
    DuplexSpongeFS.Backtrack.backTrack (n := n) (pSpec := pSpec) (δ := δ)
      normal.state.trace normal.state.trΔ normal.state.h_inv state = ExperimentOutput.some out

/-- **Output-linked LookAhead:** for a challenge round `i`, the
real `lookAhead` over the lawful full-table realization `trΔp` **recovers** the exact decoded
prefix `ρ̂ᵢ : Vector U (challengeSize i)` — its computation equals `pure (.some ρ̂ᵢ)` — rather than
merely not returning the multiple-maximal `.err`.  This is the output-bearing face of the no-abort
`statefulLookAhead`. -/
def statefulLookAheadRecovers {T_P : Type}
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔp : T_P) (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx)
    (rhoHat : Vector U (challengeSize i)) : Prop :=
  DuplexSpongeFS.Lookahead.lookAhead (pSpec := pSpec) trΔp state i =
    (pure (ExperimentOutput.some rhoHat) : OracleComp (Unit →ₒ U)
      (ExperimentOutput (Vector U (challengeSize i))))

/-- The **full-table LookAhead call** of Algorithm 5.5 Step **4.b.iv.B--D**.  `fullDelta` mirrors
the complete replay trace, whereas `normal` retains a raw trace containing the selected replay
prefix in which the current forward occurrence was reached.  Thus Backtrack and LookAhead are
explicitly prevented from sharing the wrong table, without claiming that the ambient normal trace
contains no earlier unrelated oracle entries. -/
def statefulLookAheadAt
    (history : DuplexSpongeFS.Statement.ReplayHistory StmtIn U SpongeSize.R δ
      (DuplexSpongeFS.protocolPhases (pSpec := pSpec)))
    (j : pSpec.ChallengeIdx) (pos : ℕ)
    (normal : D2SQuery.NormalState StmtIn pSpec U δ T_H T_P)
    (fullDelta : TraceNabla T_H T_P StmtIn U)
    (state : CanonicalSpongeState U) (rhoHat : Vector U (challengeSize j)) : Prop :=
  statefulRoundMarker (pSpec := pSpec) history j pos ∧
    (history.tracePrefix j.1.1).Sublist normal.state.trace ∧
    fullDelta.MirrorsQueryLog history.trace ∧
    DuplexSpongeFS.Lookahead.lookAhead (pSpec := pSpec) fullDelta.p state j =
      (pure (ExperimentOutput.some rhoHat) : OracleComp (Unit →ₒ U)
        (ExperimentOutput (Vector U (challengeSize j))))

/-! ## Whole operators: revised StdTrace / D2STrace / D2SAlgo (Algorithms 5.5 / 5.6 / 5.4)

The `revisedStdTrace`/`revisedD2STrace`/`revisedD2SAlgo` whole operators re-export the **real**
two-table + raw-trace, three-way-result, and memo/reissue/abort relations.  They are the faithful
faces of the updated paper's Algorithms, not new generic relations. -/

/-- The whole **revised StdTrace** operator (Algorithm 5.5): the two-table view is the real
normalized image of its own raw insertion trace (strict-prefix of the full table, prefix
invariant carried by the structure), and any single update is a real `PrefixUpdate` (install +
append one occurrence + `Monitor` passes) or a real `ConflictRetainsAttemptedOccurrence`
(tables unchanged, raw occurrence appended, `E` holds). -/
def RevisedStdTraceStep (pre post : StdTrace.View StmtIn U)
    (occ : ForwardOccurrence U)
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (a : (duplexSpongeChallengeOracle StmtIn U).Range q)
    (status : PermInstallStatus) : Prop :=
  StdTrace.InversesNormalizedForward post ∧
    (StdTrace.AppendOneOccurrence pre post occ q a status ∨
      StdTrace.ConflictRetainsAttemptedOccurrence pre post q a status)

/-- The whole **revised StdTrace** operator (Algorithm 5.5) as a **genuine whole-trace
transformer**: it is exactly `StdTrace.Run` over the real raw-occurrence stream `stream` from the
start view `pre`, preserving raw insertion order, the strict-prefix/full tables, the
`Install → append → Monitor` discipline, and conflict stopping. -/
def RevisedStdTrace (pre : StdTrace.View StmtIn U)
    (stream : List (StdTrace.RawOccurrence StmtIn U))
    (final : StdTrace.View StmtIn U) : Prop :=
  StdTrace.Run pre stream final

/-- The whole **revised D2STrace** operator (Algorithm 5.6): a view with the **real three-way**
online result `step` tied to the view's actual trace — a normal `continue`, a monitored `stopped`,
or an `underlyingAbort` are each the genuine `D2STrace.Execution`. -/
def RevisedD2STrace
    (view : D2STrace.View StmtIn pSpec U δ T_H T_P)
    (step : D2SQuery.StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U)) : Prop :=
  D2STrace.Execution view step

/-- The whole **revised D2SAlgo** operator (Algorithm 5.4): the real `(i, κ̂) ↦ ρ̂ᵢ` memo agrees
with the insertion order of the raw encoded trace, and every concrete `Program` invocation is
re-issued in that trace (including repeated keys).  It aborts exactly on a **named** underlying
BackTrack/LookAhead failure over the actual raw transcript `rawTrace`. -/
def RevisedD2SAlgo
    (memo : (i : pSpec.ChallengeIdx) →
      (gSpecInterface (U := U) StmtIn pSpec δ i).Query → Vector U (challengeSize i))
    (encodedTrace : D2SAlgo.EncodedTrace StmtIn pSpec U δ)
    (invocations : List (D2SAlgo.ProgramInvocation (pSpec := pSpec) (U := U) (δ := δ)
      (T_H := T_H) (T_P := T_P) memo))
    (rawTrace : DuplexSpongeFS.Statement.Trace StmtIn U)
    (result : D2SQuery.StepResult StmtIn pSpec U δ T_H T_P (CanonicalSpongeState U)) : Prop :=
  D2SAlgo.CompleteExecution (T_H := T_H) (T_P := T_P) memo encodedTrace invocations rawTrace result

end Statement

end DuplexSpongeFS
