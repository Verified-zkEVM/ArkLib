/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SCacheHistory
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventDefs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SPermInstall
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs

/-!
# Monitored D2S boundary types (single source of truth)

The revised Section 5.4 wrapper runs `Monitor` (the trace-only predicate `BadEventDS.E`) after
every trace occurrence.  The three boundary types below — a reusable **normal** state, a
**post-occurrence stop record**, and the **three-way** step result — are the revised return-state
interface.  They sit in their own lower module because they are needed by **both** the live
executable layer (`MonitoredD2SQuery`, `D2SRevisedTransition`, `D2SRevisedInstall`) and by the
Section 5 **statement layer** (`Statement.OnlineTransformation`, `Statement.OfflineTransformation`),
and they are **handler-free**: they depend only on the lower `D2SQueryState` data
(`D2SCacheHistory`), the trace-only `BadEventDS.E` (`BadEventDefs`), and the challenge-oracle /
sponge data (`Defs`).

Do **not** add a second copy of these types under `Statement` — this module is the single source
of truth, imported by both sides.  Anything here must stay handler-free (no `BadEvents`,
`D2SRevisedTransition`, or `ProverTransform` handler import): the two `D2SNormalState.table_*`
functionality lemmas, which cite `BadEvents`, deliberately remain in `MonitoredD2SQuery.lean`.
-/

open OracleComp OracleSpec ProtocolSpec
namespace DuplexSpongeFS.ProverTransform
open DSTraceStorage

variable {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : CodecCore pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- A reusable state of revised `D2SQuery`: by construction its trace has passed `Monitor` and its
normalized permutation table contains no duplicate pair.  The latter is an execution invariant:
the initial table is empty, fresh `Install` adds one pair, `present` preserves the table, and a
conflict never creates a successor.  Keeping it here lets a lookup miss mean actual absence in the
first-event proof, rather than repeatedly carrying a separate table-nodup premise.  The terminal
trace produced by the next conflicting operation has a separate type below, so no later lookup can
accidentally use a malformed table. -/
structure D2SNormalState where
  state : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  monitorPassed : ¬ BadEventDS.E state.trace
  permutationNodup : (LawfulTraceTable.toMultiSet state.trΔ.p).Nodup
  /-- The normalized hash table has no repeated stored pair.  Together with
  `hashInputFunctional`, this makes an `h`-table miss a semantic absence fact, just as
  `permutationNodup` makes a permutation-table miss usable in first-event arguments. -/
  hashNodup : (LawfulTraceTable.toMultiSet state.trΔ.h).Nodup
  /-- A hash statement has at most one stored capacity.  This execution invariant is preserved
  by hash hits and by adding only after an `inlu = none` miss. -/
  hashInputFunctional : TraceTableOps.InputFunctional state.trΔ.h

/-- The initial reusable state of revised `D2SQuery`.  Its empty trace has passed `Monitor`, and
its empty normalized permutation table is duplicate-free.  Making this construction explicit is
what lets the live revised `QueryImpl` start from the same proof-carrying boundary as the
one-step handlers, rather than falling back to the legacy unmonitored `D2SQueryState` default. -/
noncomputable def D2SNormalState.initial : D2SNormalState
    (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) := by
  classical
  refine ⟨default, ?_, ?_, ?_, ?_⟩
  · change ¬ BadEventDS.E ([] : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    simp [BadEventDS.E, BadEventDS.capacitySegmentDup,
      BadEventDS.capacitySegmentDupHash, BadEventDS.capacitySegmentDupPerm,
      BadEventDS.capacitySegmentDupPermInv, BadEventDS.E_func,
      getBaseTrace, getBaseTraceAux]
  · change (LawfulTraceTable.toMultiSet (TraceTableOps.empty : T_P)).Nodup
    rw [LawfulTraceTable.toMultiSet_empty]
    exact Multiset.nodup_zero
  · change (LawfulTraceTable.toMultiSet (TraceTableOps.empty : T_H)).Nodup
    rw [LawfulTraceTable.toMultiSet_empty]
    exact Multiset.nodup_zero
  · change TraceTableOps.InputFunctional (TraceTableOps.empty : T_H)
    intro stmt capacity₁ capacity₂ h₁ _
    simp [LawfulTraceTable.toMultiSet_empty] at h₁

/-- Lift a successful offline `PrefixUpdate` into the reusable normal-state boundary once its
caller has passed `Monitor`.  The raw trace is preserved verbatim and the rate-only cache starts
empty; this is the H₀-side bridge from revised StdTrace tables to the same lookup invariants used
by revised D2SQuery. -/
noncomputable def D2SNormalState.ofPrefixUpdate
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trDelta : TraceNabla T_H T_P StmtIn U)
    (hUpdate : prefixUpdateTrace trace = some trDelta)
    (hMonitor : ¬ BadEventDS.E trace) :
    D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) := by
  let hInvariant := prefixUpdateTrace_invariant hUpdate
  let state : D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
    { trace := trace
      trΔ := trDelta
      h_inv := prefixUpdateTrace_isSubset hUpdate
      h_mirror := hInvariant.mirrors }
  exact ⟨state, hMonitor, hInvariant.permutationNodup, hInvariant.hashNodup,
    hInvariant.hashInputFunctional⟩

/-- Adding a hash-table pair after a genuine input lookup miss preserves the normalized hash
table's pair-nodup invariant. -/
lemma D2SNormalState.hash_add_nodup
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {stmt : StmtIn} {capacity : Vector U SpongeSize.C}
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = none) :
    (LawfulTraceTable.toMultiSet
      (TraceTableOps.add normal.state.trΔ.h stmt capacity)).Nodup := by
  have hFresh :
      ∀ capacity' : Vector U SpongeSize.C,
        (stmt, capacity') ∉ LawfulTraceTable.toMultiSet normal.state.trΔ.h :=
    TraceTableOps.no_mem_of_inlu_eq_none_of_nodup_of_inputFunctional
      normal.hashNodup normal.hashInputFunctional hLookup
  exact TraceTableOps.nodup_add normal.hashNodup (hFresh capacity)

/-- Adding a hash-table pair after a genuine input lookup miss preserves input functionality. -/
lemma D2SNormalState.hash_add_inputFunctional
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {stmt : StmtIn} {capacity : Vector U SpongeSize.C}
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = none) :
    TraceTableOps.InputFunctional
      (TraceTableOps.add normal.state.trΔ.h stmt capacity) := by
  have hFresh :
      ∀ capacity' : Vector U SpongeSize.C,
        (stmt, capacity') ∉ LawfulTraceTable.toMultiSet normal.state.trΔ.h :=
    TraceTableOps.no_mem_of_inlu_eq_none_of_nodup_of_inputFunctional
      normal.hashNodup normal.hashInputFunctional hLookup
  exact TraceTableOps.inputFunctional_add normal.hashInputFunctional hFresh

/-- The post-occurrence stopping object required by the revised paper's
`compute → Install → append one occurrence → Monitor` discipline.  It is deliberately **not**
tied to a specific stop reason (an `Install = conflict`, a fresh `Install`, or any other forced
mapping can each lead to `Monitor` failure): it uniformly records *any* normal state whose next
single occurrence makes `E` hold.  It is indexed by the last reusable normal state, so its
normalized tables and rate-only cache are exactly those of `normal.state`, while its visible
trace is one additional occurrence.  It has **no successor state**: the rate-only cache and
permutation table visible here are definitionally the pre-occurrence ones, and no reuse of the
final occurrence as an installed partial-bijection mapping is claimed. -/
structure D2SPostOccurrenceStopRecord
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) where
  /-- The actual final `h`, `p`, or `p⁻¹` query. -/
  query : (duplexSpongeChallengeOracle StmtIn U).Domain
  /-- Its actual answer, retained for trace multiplicity and first-bad-event witnesses. -/
  answer : (duplexSpongeChallengeOracle StmtIn U).Range query
  /-- `Monitor` fails exactly after this final occurrence is appended.  This is the single
  predicate that ties the stop to `E`: whether the occurrence was added because the `Install`
  was a `conflict` or because it was fresh but a later table/mirror check fails, the stopped
  record is the same object. -/
  monitorFails : BadEventDS.E (normal.state.trace ++ [⟨query, answer⟩])

/-- The insertion trace carried by a post-occurrence stop record. -/
def D2SPostOccurrenceStopRecord.trace
    {normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  normal.state.trace ++ [⟨record.query, record.answer⟩]

@[simp] lemma D2SPostOccurrenceStopRecord.monitorFails_trace
    {normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal) :
    BadEventDS.E record.trace := record.monitorFails

/-- A post-occurrence stop record has exactly one more insertion occurrence than the normal
prefix that created it.  This is the trace-growth fact needed by the first-bad-event coupling; it
does not claim that the final occurrence is represented in the reusable lookup table. -/
@[simp] lemma D2SPostOccurrenceStopRecord.trace_length
    {normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal) :
    record.trace.length = normal.state.trace.length + 1 := by
  simp [D2SPostOccurrenceStopRecord.trace]

/-- The table and cache available at a post-occurrence stop record are *definitionally* those of
its normal prefix.  Keeping this projection explicit prevents a later proof from treating the
final, non-reusable occurrence as a reusable permutation-table mapping: a stopped record retains
the pre-occurrence table/cache **only**, and has no successor state. -/
def D2SPostOccurrenceStopRecord.normalState
    {normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (_record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal) :
    D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) := normal

/-- Result type for the revised transition.  Only `continue` exposes a reusable normal state.
`stopped` retains the first bad occurrence but has no successor state, and `underlyingAbort`
denotes an abort before an occurrence was produced. -/
inductive D2SRevisedStepResult
    (α : Type) where
  | continue (answer : α)
      (state : D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
      D2SRevisedStepResult α
  | stopped (state : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (record : D2SPostOccurrenceStopRecord
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) state) :
      D2SRevisedStepResult α
  | underlyingAbort : D2SRevisedStepResult α

/-- The only reusable state produced by a revised step.  In particular, a stopped result has no
successor state even though its terminal trace is retained for the first-bad-event proof. -/
def D2SRevisedStepResult.reusableState?
    {α : Type}
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) α) :
    Option (D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  match result with
  | .continue _ state => some state
  | .stopped _ _ => none
  | .underlyingAbort => none

/-- The proof-only post-occurrence trace of a revised step.  It is present precisely at a monitor
stop and is never available as the trace of a reusable state. -/
def D2SRevisedStepResult.terminalTrace?
    {α : Type}
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) α) :
    Option (QueryLog (duplexSpongeChallengeOracle StmtIn U)) :=
  match result with
  | .continue _ _ => none
  | .stopped _ record => some record.trace
  | .underlyingAbort => none

/-- Whether a revised step ended at the explicit post-occurrence `Monitor` stop.  This deliberately
distinguishes that event from both a reusable `continue` state and an `underlyingAbort`: the
first-bad-event proof charges only this constructor, whose terminal trace contains the attempted
last occurrence. -/
def D2SRevisedStepResult.isMonitorStop
    {α : Type}
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) α) : Prop :=
  match result with
  | .continue _ _ => False
  | .stopped _ _ => True
  | .underlyingAbort => False

/-- Change only the public answer of a revised step.  The reusable normal state and a possible
post-occurrence stop record are preserved definitionally.  This is the right transport for a
whole-query runner whose proof needs the insertion trace but not the branch-specific answer. -/
def D2SRevisedStepResult.map
    {α β : Type} (f : α → β) :
    D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) α →
      D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) β
  | .continue answer state => .continue (f answer) state
  | .stopped state record => .stopped state record
  | .underlyingAbort => .underlyingAbort

@[simp] lemma D2SRevisedStepResult.map_continue
    {α β : Type} (f : α → β) (answer : α)
    (state : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    (D2SRevisedStepResult.continue answer state).map f = .continue (f answer) state := rfl

@[simp] lemma D2SRevisedStepResult.map_stopped
    {α β : Type} (f : α → β)
    (state : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) state) :
    (D2SRevisedStepResult.stopped (α := α) state record).map f = .stopped state record := rfl

@[simp] lemma D2SRevisedStepResult.map_underlyingAbort
    {α β : Type} (f : α → β) :
    (D2SRevisedStepResult.underlyingAbort
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (α := α)).map f =
      .underlyingAbort := rfl

@[simp] lemma D2SRevisedStepResult.reusableState?_continue
    {α : Type} (answer : α)
    (state : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    (D2SRevisedStepResult.continue answer state).reusableState? = some state := rfl

@[simp] lemma D2SRevisedStepResult.terminalTrace?_stopped
    {α : Type}
    (state : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) state) :
    (D2SRevisedStepResult.stopped (α := α) state record).terminalTrace? = some record.trace := rfl

@[simp] lemma D2SRevisedStepResult.isMonitorStop_continue
    {α : Type} (answer : α)
    (state : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    (D2SRevisedStepResult.continue answer state).isMonitorStop = False := rfl

@[simp] lemma D2SRevisedStepResult.isMonitorStop_stopped
    {α : Type}
    (state : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) state) :
    (D2SRevisedStepResult.stopped (α := α) state record).isMonitorStop = True := rfl

@[simp] lemma D2SRevisedStepResult.isMonitorStop_underlyingAbort
    {α : Type} :
    (D2SRevisedStepResult.underlyingAbort
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (α := α)).isMonitorStop = False := rfl

/-- Erasing or changing a branch answer cannot change whether the branch stopped at `Monitor`.
This lets the whole-query runner use `Unit` answers without losing the first-bad-event stopping
predicate. -/
@[simp] lemma D2SRevisedStepResult.isMonitorStop_map
    {α β : Type} (f : α → β)
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) α) :
    (result.map f).isMonitorStop ↔ result.isMonitorStop := by
  cases result <;> rfl

/-- A stopped result never exposes a reusable normal state.  The terminal trace is retained only
for the first-bad-event proof; it is not a successor state. -/
@[simp] lemma D2SRevisedStepResult.reusableState?_stopped
    {α : Type}
    (state : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) state) :
    (D2SRevisedStepResult.stopped (α := α) state record).reusableState? = none := rfl

end DuplexSpongeFS.ProverTransform
