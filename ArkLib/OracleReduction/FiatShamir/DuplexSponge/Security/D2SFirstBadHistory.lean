/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SFirstBadDispatcher
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Section5Nonempty

/-!
# Terminal-history gateway for revised D2SQuery

The first-bad probability proof needs more than a cardinality bound: a terminal monitored record
must retain the raw trace prefix with which its live D2SQuery step began.  This module proves that
fact at the concrete `simulateQ` boundary, one dispatcher direction at a time.  It is deliberately
separate from the probability and adaptive-run modules so those later proofs only compose a small
support-level contract instead of reopening branch implementations.
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

/-- The raw terminal-history property of one revised D2SQuery step.  It intentionally exposes
only the record trace observed by an absorbing stop; it does not manufacture a reusable state or
assert that the final occurrence belongs to the partial permutation table. -/
def D2SQueryStepStopTraceExtension
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain) : Prop :=
  ∀ (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (stoppedNormal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stoppedNormal),
    .stopped stoppedNormal record ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sQueryStepRevised normal q)) →
      ∃ tail, record.trace = normal.state.trace ++ tail

/-- The Step-2 hash dispatcher retains its input trace in every supported monitor stop.  A hash
hit is deterministic; a miss chooses one capacity and then uses the same append-then-Monitor
transition. -/
lemma d2sQueryStepRevised_hash_stopped_trace_extension
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) :
    D2SQueryStepStopTraceExtension normal (dsHashQuery stmt) := by
  unfold D2SQueryStepStopTraceExtension
  intro gImpl stoppedNormal record hResult
  cases hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt with
  | some capacity =>
      rw [d2sQueryStepRevised_hash,
        d2sHandleHashQueryRevised_hit normal stmt capacity hLookup] at hResult
      change D2SRevisedStepResult.stopped stoppedNormal record ∈
        support (pure (d2sHandleHashPresentRevised normal stmt capacity hLookup)) at hResult
      rw [mem_support_pure_iff] at hResult
      exact d2sHandleHashPresentRevised_stopped_trace_extends normal stmt capacity hLookup
        hResult.symm
  | none =>
      rw [d2sQueryStepRevised_hash,
        d2sHandleHashQueryRevised_miss normal stmt hLookup] at hResult
      change D2SRevisedStepResult.stopped stoppedNormal record ∈ support (simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>=
          fun capacity => pure (d2sHandleHashFreshRevised normal stmt capacity hLookup))) at hResult
      rw [simulateQ_bind, mem_support_bind_iff] at hResult
      obtain ⟨capacity, _hCapacity, hResult⟩ := hResult
      change D2SRevisedStepResult.stopped stoppedNormal record ∈
        support (pure (d2sHandleHashFreshRevised normal stmt capacity hLookup)) at hResult
      rw [mem_support_pure_iff] at hResult
      exact d2sHandleHashFreshRevised_stopped_trace_extends normal stmt capacity hLookup
        hResult.symm

/-- The Step-3 inverse dispatcher retains its input trace in every supported monitor stop.  Both
the table-hit and sampled-preimage cases reduce to the shared resolved-permutation terminal
transition. -/
lemma d2sQueryStepRevised_inverse_stopped_trace_extension
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut : CanonicalSpongeState U) :
    D2SQueryStepStopTraceExtension normal (dsPermInvQuery stateOut) := by
  unfold D2SQueryStepStopTraceExtension
  intro gImpl stoppedNormal record hResult
  cases hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut with
  | some stateIn =>
      rw [d2sQueryStepRevised_inverse,
        d2sHandleInversePermQueryRevised_hit normal stateOut stateIn hLookup] at hResult
      change D2SRevisedStepResult.stopped stoppedNormal record ∈ support
        (pure (d2sPermResolvedStep normal (.inverse stateOut stateIn))) at hResult
      rw [mem_support_pure_iff] at hResult
      exact d2sPermResolvedStep_stopped_trace_extends normal (.inverse stateOut stateIn)
        hResult.symm
  | none =>
      rw [d2sQueryStepRevised_inverse,
        d2sHandleInversePermQueryRevised_miss normal stateOut hLookup] at hResult
      change D2SRevisedStepResult.stopped stoppedNormal record ∈ support (simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>=
          fun stateIn => pure (d2sPermResolvedStep normal (.inverse stateOut stateIn)))) at hResult
      rw [simulateQ_bind, mem_support_bind_iff] at hResult
      obtain ⟨stateIn, _hStateIn, hResult⟩ := hResult
      change D2SRevisedStepResult.stopped stoppedNormal record ∈ support
        (pure (d2sPermResolvedStep normal (.inverse stateOut stateIn))) at hResult
      rw [mem_support_pure_iff] at hResult
      exact d2sPermResolvedStep_stopped_trace_extends normal (.inverse stateOut stateIn)
        hResult.symm

/-- A supported stop while materializing a rate-only tail is rooted at the original normal trace.
The sampled capacity chooses the missing capacity coordinate only; the common resolved action owns
the terminal occurrence. -/
lemma d2sHandlePoppedRateOnlyTailRevised_stopped_trace_extension_of_support
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (stoppedNormal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stoppedNormal)
    (hResult : .stopped stoppedNormal record ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandlePoppedRateOnlyTailRevised normal entry cacheRest))) :
    ∃ tail, record.trace = normal.state.trace ++ tail := by
  rw [d2sHandlePoppedRateOnlyTailRevised_eq normal entry cacheRest] at hResult
  change D2SRevisedStepResult.stopped stoppedNormal record ∈ support (simulateQ
    (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
    (d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>=
      fun capacity => pure (d2sConsumePoppedRateOnlyTailRevised normal entry cacheRest capacity)))
      at hResult
  rw [simulateQ_bind, mem_support_bind_iff] at hResult
  obtain ⟨capacity, _hCapacity, hResult⟩ := hResult
  change D2SRevisedStepResult.stopped stoppedNormal record ∈
    support (pure (d2sConsumePoppedRateOnlyTailRevised normal entry cacheRest capacity)) at hResult
  rw [mem_support_pure_iff] at hResult
  exact d2sConsumePoppedRateOnlyTailRevised_stopped_trace_extends normal entry cacheRest capacity
    hResult.symm

/-- A supported stop at Program's first rate block is rooted at the pre-Program trace.  The later
rate blocks are not pre-sampled or recorded; they remain a continuation-only lazy tail. -/
lemma d2sHandleProgramFirstRateRevised_stopped_trace_extension_of_support
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R))
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (stoppedNormal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stoppedNormal)
    (hResult : .stopped stoppedNormal record ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleProgramFirstRateRevised normal stateIn firstRate remainingRates))) :
    ∃ tail, record.trace = normal.state.trace ++ tail := by
  rw [d2sHandleProgramFirstRateRevised_eq normal stateIn firstRate remainingRates] at hResult
  change D2SRevisedStepResult.stopped stoppedNormal record ∈ support (simulateQ
    (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
    (d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>=
      fun capacity => pure (d2sProgramFirstRateRevised normal stateIn firstRate remainingRates
        capacity))) at hResult
  rw [simulateQ_bind, mem_support_bind_iff] at hResult
  obtain ⟨capacity, _hCapacity, hResult⟩ := hResult
  change D2SRevisedStepResult.stopped stoppedNormal record ∈ support
    (pure (d2sProgramFirstRateRevised normal stateIn firstRate remainingRates capacity)) at hResult
  rw [mem_support_pure_iff] at hResult
  exact d2sProgramFirstRateRevised_stopped_trace_extends normal stateIn firstRate remainingRates
    capacity hResult.symm

/-- Every stopped Step-4.c execution is rooted at its input trace.  This is the precise
stateful ordering: a pending lazy tail wins before either a normalized-table replay or a fresh
full-state sample. -/
lemma d2sHandleForwardNoResultRevised_stopped_trace_extension_of_support
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (stoppedNormal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stoppedNormal)
    (hResult : .stopped stoppedNormal record ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleForwardNoResultRevised normal stateIn))) :
    ∃ tail, record.trace = normal.state.trace ++ tail := by
  cases hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn with
  | some tailAndCache =>
      rcases tailAndCache with ⟨tail, cacheRest⟩
      rw [d2sHandleForwardNoResultRevised_tail normal stateIn tail cacheRest hPop] at hResult
      exact d2sHandlePoppedRateOnlyTailRevised_stopped_trace_extension_of_support normal
        ⟨stateIn, tail⟩ cacheRest gImpl stoppedNormal record hResult
  | none =>
      cases hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn with
      | some stateOut =>
          rw [d2sHandleForwardNoResultRevised_table normal stateIn stateOut hPop hLookup]
            at hResult
          change D2SRevisedStepResult.stopped stoppedNormal record ∈ support
            (pure (d2sPermResolvedStep normal (.forward stateIn stateOut))) at hResult
          rw [mem_support_pure_iff] at hResult
          exact d2sPermResolvedStep_stopped_trace_extends normal (.forward stateIn stateOut)
            hResult.symm
      | none =>
          rw [d2sHandleForwardNoResultRevised_fresh normal stateIn hPop hLookup] at hResult
          change D2SRevisedStepResult.stopped stoppedNormal record ∈ support (simulateQ
            (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
            (d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>=
              fun stateOut => pure (d2sPermResolvedStep normal (.forward stateIn stateOut))))
              at hResult
          rw [simulateQ_bind, mem_support_bind_iff] at hResult
          obtain ⟨stateOut, _hStateOut, hResult⟩ := hResult
          change D2SRevisedStepResult.stopped stoppedNormal record ∈ support
            (pure (d2sPermResolvedStep normal (.forward stateIn stateOut))) at hResult
          rw [mem_support_pure_iff] at hResult
          exact d2sPermResolvedStep_stopped_trace_extends normal (.forward stateIn stateOut)
            hResult.symm

/-- A stopped Program continuation after a reissued `gᵢ` answer still starts from the same normal
trace that entered Step 4.  The `gᵢ` query chooses only the encoded challenge; it has no hidden
D2S trace effect before the selected resolved or Program action. -/
lemma d2sHandleBacktrackAfterGRevised_stopped_trace_extension_of_support
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx))
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (stoppedNormal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stoppedNormal)
    (hResult : .stopped stoppedNormal record ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleBacktrackAfterGRevised normal stateIn backtrackOut rhoHat))) :
    ∃ tail, record.trace = normal.state.trace ++ tail := by
  cases hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn with
  | some stateOut =>
      rw [d2sHandleBacktrackAfterGRevised_hit normal stateIn stateOut backtrackOut rhoHat
        hLookup] at hResult
      change D2SRevisedStepResult.stopped stoppedNormal record ∈ support
        (pure (d2sPermResolvedStep normal (.forward stateIn stateOut))) at hResult
      rw [mem_support_pure_iff] at hResult
      exact d2sPermResolvedStep_stopped_trace_extends normal (.forward stateIn stateOut)
        hResult.symm
  | none =>
      rw [d2sHandleBacktrackAfterGRevised_miss normal stateIn backtrackOut rhoHat hLookup]
        at hResult
      rw [simulateQ_bind, mem_support_bind_iff] at hResult
      obtain ⟨rateBlocks, _hRateBlocks, hResult⟩ := hResult
      cases hBlocks : rateBlocks.toList with
      | nil =>
          rw [hBlocks] at hResult
          simp at hResult
      | cons firstRate remainingRates =>
          rw [hBlocks] at hResult
          exact d2sHandleProgramFirstRateRevised_stopped_trace_extension_of_support normal
            stateIn firstRate remainingRates gImpl stoppedNormal record hResult

/-- In the revised nonempty Section 5 scope, the Program continuation after a successful
`gᵢ` query never returns `underlyingAbort`.  A table hit is a resolved action; on a table miss,
the parser returns a vector whose statically prescribed positive length rules out its legacy
empty-list branch, and the selected first block is a resolved Program action.  Hence the only
live forward abort left for the later Backtrack refinement is a genuine search failure. -/
lemma d2sHandleBacktrackAfterGRevised_no_underlyingAbort_of_support
    [VCVCompatible U] [Nonempty U] [SampleableType U] [Section5Nonempty pSpec]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx))
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (hResult : (.underlyingAbort : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) ∈ support
        (simulateQ (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
          (d2sHandleBacktrackAfterGRevised normal stateIn backtrackOut rhoHat))) : False := by
  cases hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn with
  | some stateOut =>
      rw [d2sHandleBacktrackAfterGRevised_hit normal stateIn stateOut backtrackOut rhoHat
        hLookup] at hResult
      have hEq : (.underlyingAbort : D2SRevisedStepResult
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) =
          d2sPermResolvedStep normal (.forward stateIn stateOut) := by
        simpa only [simulateQ_pure, mem_support_pure_iff] using hResult
      exact d2sPermResolvedStep_ne_underlyingAbort normal (.forward stateIn stateOut)
        hEq.symm
  | none =>
      rw [d2sHandleBacktrackAfterGRevised_miss normal stateIn backtrackOut rhoHat hLookup]
        at hResult
      rw [simulateQ_bind, mem_support_bind_iff] at hResult
      obtain ⟨rateBlocks, _hRateBlocks, hResult⟩ := hResult
      cases hBlocks : rateBlocks.toList with
      | nil =>
          exact (Section5Nonempty.challenge_rateBlocks_toList_ne_nil
            (pSpec := pSpec) (U := U) backtrackOut.roundIdx rateBlocks) hBlocks
      | cons firstRate remainingRates =>
          simp only [hBlocks] at hResult
          rw [d2sHandleProgramFirstRateRevised_eq normal stateIn firstRate remainingRates,
            simulateQ_bind, mem_support_bind_iff] at hResult
          obtain ⟨capacity, _hCapacity, hResult⟩ := hResult
          have hEq : (.underlyingAbort : D2SRevisedStepResult
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) =
              d2sProgramFirstRateRevised normal stateIn firstRate remainingRates capacity := by
            simpa only [simulateQ_pure, mem_support_pure_iff] using hResult
          exact d2sProgramFirstRateRevised_ne_underlyingAbort normal stateIn firstRate
            remainingRates capacity hEq.symm

/-- A recovered Backtrack candidate preserves the input trace at every monitor stop.  This
includes the important priority case where an old rate-only tail is consumed before the candidate
can reissue `gᵢ` or program a new mapping. -/
lemma d2sHandleBacktrackSomeRevised_stopped_trace_extension_of_support
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (stoppedNormal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stoppedNormal)
    (hResult : .stopped stoppedNormal record ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleBacktrackSomeRevised normal stateIn backtrackOut))) :
    ∃ tail, record.trace = normal.state.trace ++ tail := by
  cases hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn with
  | some tailAndCache =>
      rcases tailAndCache with ⟨tail, cacheRest⟩
      rw [d2sHandleBacktrackSomeRevised_tail normal stateIn backtrackOut tail cacheRest hPop]
        at hResult
      exact d2sHandlePoppedRateOnlyTailRevised_stopped_trace_extension_of_support normal
        ⟨stateIn, tail⟩ cacheRest gImpl stoppedNormal record hResult
  | none =>
      by_cases hImage : d2sInCodecImagePredicate
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut
      · by_cases hNonempty : 0 < challengeSize (pSpec := pSpec) backtrackOut.roundIdx
        · rw [d2sHandleBacktrackSomeRevised_nonemptyChallenge normal stateIn backtrackOut hPop
            hImage hNonempty] at hResult
          rw [simulateQ_bind, mem_support_bind_iff] at hResult
          obtain ⟨rhoHat, _hRhoHat, hResult⟩ := hResult
          exact d2sHandleBacktrackAfterGRevised_stopped_trace_extension_of_support normal
            stateIn backtrackOut rhoHat gImpl stoppedNormal record hResult
        · rw [d2sHandleBacktrackSomeRevised_emptyChallenge normal stateIn backtrackOut hPop
            hImage hNonempty] at hResult
          exact d2sHandleForwardNoResultRevised_stopped_trace_extension_of_support normal
            stateIn gImpl stoppedNormal record hResult
      · rw [d2sHandleBacktrackSomeRevised_notInImage normal stateIn backtrackOut hPop hImage]
          at hResult
        exact d2sHandleForwardNoResultRevised_stopped_trace_extension_of_support normal stateIn
          gImpl stoppedNormal record hResult

/-- The complete Step-4 forward dispatcher has no pre-terminal trace discontinuity.  Its only
non-monitor terminal face is the explicit Backtrack/search failure, which cannot inhabit the
stopped-result support in this theorem. -/
lemma d2sHandleForwardPermQueryRevised_stopped_trace_extension_of_support
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (stoppedNormal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stoppedNormal)
    (hResult : .stopped stoppedNormal record ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleForwardPermQueryRevised normal stateIn))) :
    ∃ tail, record.trace = normal.state.trace ++ tail := by
  cases hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn with
  | some tailAndCache =>
      rcases tailAndCache with ⟨tail, cacheRest⟩
      rw [d2sHandleForwardPermQueryRevised_tail normal stateIn tail cacheRest hPop] at hResult
      exact d2sHandlePoppedRateOnlyTailRevised_stopped_trace_extension_of_support normal
        ⟨stateIn, tail⟩ cacheRest gImpl stoppedNormal record hResult
  | none =>
      cases hSearch : Backtrack.backTrack
          (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          normal.state.trace normal.state.trΔ normal.state.h_inv stateIn
          (normal.state.trace.length + 1) with
      | err =>
          rw [d2sHandleForwardPermQueryRevised_err normal stateIn hPop hSearch] at hResult
          change D2SRevisedStepResult.stopped stoppedNormal record ∈ support
            (pure .underlyingAbort) at hResult
          simp at hResult
      | noResult =>
          rw [d2sHandleForwardPermQueryRevised_noResult normal stateIn hPop hSearch] at hResult
          exact d2sHandleForwardNoResultRevised_stopped_trace_extension_of_support normal stateIn
            gImpl stoppedNormal record hResult
      | some backtrackOut =>
          rw [d2sHandleForwardPermQueryRevised_some normal stateIn backtrackOut hPop hSearch]
            at hResult
          exact d2sHandleBacktrackSomeRevised_stopped_trace_extension_of_support normal stateIn
            backtrackOut gImpl stoppedNormal record hResult

/-- Every supported monitored stop of the complete live dispatcher retains the raw trace with
which that dispatcher call began.  This is the stop-side companion to
`d2sQueryStepRevised_continue_trace_extension`; together they give the adaptive runner a literal
global history, not merely a length budget. -/
lemma d2sQueryStepRevised_stopped_trace_extension
    [VCVCompatible U] [Nonempty U] [SampleableType U] :
    ∀ (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (q : (duplexSpongeChallengeOracle StmtIn U).Domain),
      D2SQueryStepStopTraceExtension normal q := by
  intro normal q
  cases q with
  | inl stmt =>
      exact d2sQueryStepRevised_hash_stopped_trace_extension normal stmt
  | inr q =>
      cases q with
      | inl stateIn =>
          unfold D2SQueryStepStopTraceExtension
          intro gImpl stoppedNormal record hResult
          simpa only [d2sQueryStepRevised_forward] using
            d2sHandleForwardPermQueryRevised_stopped_trace_extension_of_support normal stateIn
              gImpl stoppedNormal record hResult
      | inr stateOut =>
          exact d2sQueryStepRevised_inverse_stopped_trace_extension normal stateOut

end DuplexSpongeFS.ProverTransform
