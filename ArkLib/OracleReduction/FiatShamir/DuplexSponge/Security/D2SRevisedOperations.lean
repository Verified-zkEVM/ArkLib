/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SRevisedInstall

/-!
# Stateful branch operations for revised D2SQuery

This module contains the common resolved-permutation tail, rate-only cache materialization,
hash/inverse handlers, and finite action runners built on the core forward/inverse Install
transitions.  Separating it from `D2SRevisedInstall` keeps the table-only transition core small
and lets probability arguments depend on exactly the stateful operations they use.
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


/-! ## Finite resolved-permutation core

The six public D2SQuery branches choose an answer by different mechanisms (hash table, inverse
sampling, lazy rate-only tail, ordinary fresh sampling, or `Program`).  Once a branch has fixed a
*permutation* input/output pair, however, all of them must use the same revised

    Install → append one occurrence → Monitor

transition.  This small deterministic core makes that common tail executable.  It deliberately
does **not** sample a capacity, inspect the rate-only cache, or claim that an arbitrary list of
pairs was produced by D2SQuery.  The branch-refinement theorem is responsible for producing these
resolved actions.  Consequently, probability proofs can reason about sampling once per branch and
use this core for every conflict/terminal-record argument.
-/

/-- A resolved permutation action: a D2SQuery branch has already selected the exact input and
output state, but has not yet performed the common `Install → append → Monitor` tail.  The order
of the inverse constructor matches the queried inverse oracle: `p⁻¹(stateOut) = stateIn`. -/
inductive D2SPermResolvedAction (U : Type) [SpongeUnit U] [SpongeSize] where
  | forward (stateIn stateOut : CanonicalSpongeState U)
  | inverse (stateOut stateIn : CanonicalSpongeState U)

/-- Execute the common revised tail for one already-resolved permutation action.  This is exactly
the forward or inverse restated install transition above; in particular a table conflict returns a
post-occurrence `stopped` record rather than collapsing to legacy `Option.none`. -/
noncomputable def d2sPermResolvedStep
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    D2SPermResolvedAction U →
      D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (CanonicalSpongeState U)
  | .forward stateIn stateOut =>
      d2sInstallPermForwardStateRevised normal stateIn stateOut
  | .inverse stateOut stateIn =>
      d2sInstallPermInverseStateRevised normal stateOut stateIn

@[simp] lemma d2sPermResolvedStep_forward
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U) :
    d2sPermResolvedStep normal (.forward stateIn stateOut) =
      d2sInstallPermForwardStateRevised normal stateIn stateOut := rfl

@[simp] lemma d2sPermResolvedStep_inverse
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U) :
    d2sPermResolvedStep normal (.inverse stateOut stateIn) =
      d2sInstallPermInverseStateRevised normal stateOut stateIn := rfl

/-- The raw query-answer occurrence contributed by a resolved permutation action.  Keeping this
projection beside the common `Install → append → Monitor` executor gives every later branch one
uniform trace-growth contract. -/
def D2SPermResolvedAction.occurrence (StmtIn : Type)
    (action : D2SPermResolvedAction U) : Sigma (duplexSpongeChallengeOracle StmtIn U) :=
  match action with
  | .forward stateIn stateOut => ⟨dsPermQuery stateIn, stateOut⟩
  | .inverse stateOut stateIn => ⟨dsPermInvQuery stateOut, stateIn⟩

/-- A continuing resolved forward or inverse action appends exactly its one attempted
occurrence.  This is the deterministic core behind the global first-bad trace-growth bound. -/
lemma d2sPermResolvedStep_continue_trace
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (action : D2SPermResolvedAction U)
    {answer : CanonicalSpongeState U}
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (h : d2sPermResolvedStep normal action = .continue answer normal') :
    normal'.state.trace = normal.state.trace ++ [action.occurrence StmtIn] := by
  cases action with
  | forward stateIn stateOut =>
      rw [d2sPermResolvedStep_forward] at h
      have hAnswer := d2sInstallPermForwardStateRevised_continue_answer_eq
        normal stateIn stateOut answer normal' h
      subst answer
      simpa [D2SPermResolvedAction.occurrence] using
        d2sInstallPermForwardStateRevised_continue_trace normal stateIn stateOut h
  | inverse stateOut stateIn =>
      rw [d2sPermResolvedStep_inverse] at h
      unfold d2sInstallPermInverseStateRevised at h
      split at h
      · simp_all
      · split at h
        · simp_all
        · rcases h with ⟨hAnswer, hNormal⟩
          rfl
      · split at h
        · simp_all
        · rcases h with ⟨hAnswer, hNormal⟩
          rfl

/-- Resolved permutation actions cannot have an underlying parser abort: their input/output pair
has already been selected by a branch, so the only possible non-continuation is the explicit
post-occurrence monitor stop.  This keeps the first-bad-event induction separate from the
BackTrack/LookAhead search-error analysis. -/
lemma d2sPermResolvedStep_ne_underlyingAbort
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (action : D2SPermResolvedAction U) :
    d2sPermResolvedStep normal action ≠ .underlyingAbort := by
  cases action with
  | forward stateIn stateOut =>
      rw [d2sPermResolvedStep_forward]
      unfold d2sInstallPermForwardStateRevised
      split
      · simp
      · split <;> simp
      · split <;> simp
  | inverse stateOut stateIn =>
      rw [d2sPermResolvedStep_inverse]
      unfold d2sInstallPermInverseStateRevised
      split
      · simp
      · split <;> simp
      · split <;> simp

/-- Every terminal record of a resolved permutation action is indexed by its input normal state.
This packages the fact that `Install → append → Monitor` never exposes a modified cache/table on
the stopping path. -/
lemma d2sPermResolvedStep_stopped_normal_eq
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (action : D2SPermResolvedAction U)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    {record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal'}
    (hStop : d2sPermResolvedStep normal action = .stopped normal' record) :
    normal' = normal := by
  cases action with
  | forward stateIn stateOut =>
      rw [d2sPermResolvedStep_forward] at hStop
      unfold d2sInstallPermForwardStateRevised at hStop
      split at hStop
      · injection hStop with hNormal _
        exact hNormal.symm
      · by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
        · simp [hE] at hStop
          exact hStop.1.symm
        · simp [hE] at hStop
      · by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
        · simp [hE] at hStop
          exact hStop.1.symm
        · simp [hE] at hStop
  | inverse stateOut stateIn =>
      rw [d2sPermResolvedStep_inverse] at hStop
      unfold d2sInstallPermInverseStateRevised at hStop
      split at hStop
      · injection hStop with hNormal _
        exact hNormal.symm
      · by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
        · simp [hE] at hStop
          exact hStop.1.symm
        · simp [hE] at hStop
      · by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
        · simp [hE] at hStop
          exact hStop.1.symm
        · simp [hE] at hStop

/-- A resolved monitor stop exposes a terminal trace extending the action's input trace.  The
record's pre-stop state is the input normal state by the preceding theorem; its own final
occurrence then supplies the suffix.  This deliberately does not claim that the final occurrence
was installed in the reusable table. -/
lemma d2sPermResolvedStep_stopped_trace_extends
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (action : D2SPermResolvedAction U)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    {record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal'}
    (hStop : d2sPermResolvedStep normal action = .stopped normal' record) :
    ∃ tail, record.trace = normal.state.trace ++ tail := by
  have hNormal := d2sPermResolvedStep_stopped_normal_eq normal action hStop
  subst normal'
  exact ⟨[⟨record.query, record.answer⟩], rfl⟩

/-! ## Rate-only tail materialization

The corrected `Cache_p` contains a next *rate* block and no output capacity.  This continuation
is the sole point at which that capacity becomes observable.  Its type makes the order explicit:
one supplied capacity materializes one output, the common forward `Install → append → Monitor`
tail runs, and the residual cache is installed only on a continuing successor.  In particular a
conflict/monitor stop retains the pre-occurrence cache in its stop record.
-/

/-- Replace the rate-only cache of a continuing result.  A stopped record deliberately retains
its own pre-occurrence normal state, so this operation never changes a terminal record. -/
noncomputable def d2sReplaceRateCacheOnContinue
    (rateCacheP : List (RateOnlyCacheEntry (U := U)))
    {α : Type} :
    D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) α →
      D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) α
  | .continue answer normal =>
      .continue answer ⟨{ normal.state with rateCacheP }, normal.monitorPassed,
        normal.permutationNodup, normal.hashNodup, normal.hashInputFunctional⟩
  | .stopped normal record => .stopped normal record
  | .underlyingAbort => .underlyingAbort

@[simp] lemma d2sReplaceRateCacheOnContinue_continue
    (rateCacheP : List (RateOnlyCacheEntry (U := U))) {α : Type} (answer : α)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    d2sReplaceRateCacheOnContinue rateCacheP (.continue answer normal) =
      .continue answer ⟨{ normal.state with rateCacheP }, normal.monitorPassed,
        normal.permutationNodup, normal.hashNodup, normal.hashInputFunctional⟩ := rfl

@[simp] lemma d2sReplaceRateCacheOnContinue_stopped
    (rateCacheP : List (RateOnlyCacheEntry (U := U))) {α : Type}
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal) :
    d2sReplaceRateCacheOnContinue rateCacheP (.stopped normal record : D2SRevisedStepResult α) =
      .stopped normal record := rfl

/-- A continuing cache replacement has a unique continuing source.  The replacement operation
changes only the rate-only cache field of that source; its trace and both oracle tables are
preserved definitionally.  Tail and Program proofs use this to recover the common forward
`Install → append → Monitor` transition underneath their cache-specific successor. -/
lemma d2sReplaceRateCacheOnContinue_continue_source
    (rateCacheP : List (RateOnlyCacheEntry (U := U))) {α : Type}
    (step : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) α)
    {answer : α}
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hContinue : d2sReplaceRateCacheOnContinue rateCacheP step = .continue answer normal') :
    ∃ source : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U),
      step = .continue answer source ∧
        normal'.state.trace = source.state.trace ∧ normal'.state.trΔ = source.state.trΔ := by
  cases step
  next sourceAnswer source =>
      simp only [d2sReplaceRateCacheOnContinue_continue] at hContinue
      cases hContinue
      exact ⟨source, rfl, rfl, rfl⟩
  next source record =>
      simp [d2sReplaceRateCacheOnContinue_stopped] at hContinue
  next =>
      simp [d2sReplaceRateCacheOnContinue] at hContinue

/-- The cache supplied to a continuing replacement is exactly the cache in its successor. -/
lemma d2sReplaceRateCacheOnContinue_continue_cache
    (rateCacheP : List (RateOnlyCacheEntry (U := U))) {α : Type}
    (step : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) α)
    {answer : α}
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hContinue : d2sReplaceRateCacheOnContinue rateCacheP step = .continue answer normal') :
    normal'.state.rateCacheP = rateCacheP := by
  cases step
  next sourceAnswer source =>
      simp only [d2sReplaceRateCacheOnContinue_continue] at hContinue
      cases hContinue
      rfl
  next source record =>
      simp [d2sReplaceRateCacheOnContinue_stopped] at hContinue
  next =>
      simp [d2sReplaceRateCacheOnContinue] at hContinue

/-- The cache after consuming a tail that a caller has already removed from `Cache_p`.  A residual
tail is re-keyed at the just-materialized output; a final tail is discharged. -/
def rateOnlyTailResidualCache
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (capacity : Vector U SpongeSize.C) : List (RateOnlyCacheEntry (U := U)) :=
  match (materializeRateOnlyCacheEntry (U := U) entry capacity).2 with
  | none => cacheRest
  | some successor => successor :: cacheRest

/-- Consume a tail that a caller has already removed from `Cache_p`.  Exactly one capacity is
provided at this point.  The caller supplies `cacheRest` from that pop; if the materialized tail
has a successor it is re-keyed at the just-produced output, otherwise the entry is discharged. -/
noncomputable def d2sConsumePoppedRateOnlyTailRevised
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (capacity : Vector U SpongeSize.C) :
    D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U) :=
  let materialized := materializeRateOnlyCacheEntry (U := U) entry capacity
  d2sReplaceRateCacheOnContinue (rateOnlyTailResidualCache entry cacheRest capacity)
    (d2sPermResolvedStep normal (.forward entry.stateIn materialized.1))

/-- The sampling form of a selected cache-tail branch.  It issues precisely one capacity query;
the capacity is not sampled when the tail is created, and no full state is sampled here. -/
noncomputable def d2sHandlePoppedRateOnlyTailRevised
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U))) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) := do
  let capacity ← d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
  pure (d2sConsumePoppedRateOnlyTailRevised normal entry cacheRest capacity)

/-- The selected-tail handler exposes its sole source of randomness as the one capacity sample.
This equation is the forward lazy-sampling interface used by the first-event proof. -/
@[simp] lemma d2sHandlePoppedRateOnlyTailRevised_eq
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U))) :
    d2sHandlePoppedRateOnlyTailRevised normal entry cacheRest =
      d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>= fun capacity =>
        pure (d2sConsumePoppedRateOnlyTailRevised normal entry cacheRest capacity) := rfl

/-- A continuing lazy-tail materialization appends exactly the one forward occurrence it
materializes.  Replacing the rate-only cache changes no trace coordinate, so this is inherited
directly from the resolved forward action. -/
lemma d2sConsumePoppedRateOnlyTailRevised_continue_trace
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (capacity : Vector U SpongeSize.C)
    {stateOut : CanonicalSpongeState U}
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hContinue : d2sConsumePoppedRateOnlyTailRevised normal entry cacheRest capacity =
      .continue stateOut normal') :
    normal'.state.trace = normal.state.trace ++
      [⟨dsPermQuery entry.stateIn,
        (materializeRateOnlyCacheEntry (U := U) entry capacity).1⟩] := by
  unfold d2sConsumePoppedRateOnlyTailRevised at hContinue
  obtain ⟨source, hSource, hTrace, _⟩ :=
    d2sReplaceRateCacheOnContinue_continue_source
      (rateOnlyTailResidualCache entry cacheRest capacity)
      (d2sPermResolvedStep normal
        (.forward entry.stateIn (materializeRateOnlyCacheEntry (U := U) entry capacity).1))
      hContinue
  rw [hTrace]
  exact d2sPermResolvedStep_continue_trace normal
    (.forward entry.stateIn (materializeRateOnlyCacheEntry (U := U) entry capacity).1) hSource

/-- A stopped lazy-tail materialization retains a terminal trace rooted at the input normal
state.  Updating the residual tail is continuation-only, so it cannot change this fact. -/
lemma d2sConsumePoppedRateOnlyTailRevised_stopped_trace_extends
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (capacity : Vector U SpongeSize.C)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    {record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal'}
    (hStop : d2sConsumePoppedRateOnlyTailRevised normal entry cacheRest capacity =
      .stopped normal' record) :
    ∃ tail, record.trace = normal.state.trace ++ tail := by
  unfold d2sConsumePoppedRateOnlyTailRevised at hStop
  cases hStep : d2sPermResolvedStep normal
      (.forward entry.stateIn (materializeRateOnlyCacheEntry (U := U) entry capacity).1)
  next answer normal'' =>
    simp [hStep] at hStop
  next normal'' record'' =>
    have hInput : normal'' = normal := d2sPermResolvedStep_stopped_normal_eq normal
      (.forward entry.stateIn (materializeRateOnlyCacheEntry (U := U) entry capacity).1) hStep
    subst normal''
    simp [hStep] at hStop
    cases hStop.1
    exact ⟨[⟨record.query, record.answer⟩], rfl⟩
  next =>
    exact False.elim (d2sPermResolvedStep_ne_underlyingAbort normal
      (.forward entry.stateIn (materializeRateOnlyCacheEntry (U := U) entry capacity).1) hStep)

/-! ## Revised forward no-result branch

This is precisely Algorithm 5.3 Step 4.c after BackTrack has returned `.noResult`: consume a
matching rate-only tail if present; otherwise reuse an installed forward mapping; otherwise sample
one full output state.  Every one of those three selections then uses the same revised terminal
discipline.  It is deliberately separate from the BackTrack/Program branch, whose search result
can have an underlying parser abort.
-/

/-- Revised Step 4.c.  The stateful cache lookup comes first, so an unmaterialized tail cannot be
mistaken for an ordinary fresh mapping.  If no tail applies, a normalized table hit makes no random
query; only a true miss samples one full output state. -/
noncomputable def d2sHandleForwardNoResultRevised
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) := do
  match popRateOnlyTailByInput normal.state.rateCacheP stateIn with
  | some (tail, cacheRest) =>
      d2sHandlePoppedRateOnlyTailRevised normal ⟨stateIn, tail⟩ cacheRest
  | none =>
      match TraceTableOps.inlu normal.state.trΔ.p stateIn with
      | some stateOut =>
          pure (d2sPermResolvedStep normal (.forward stateIn stateOut))
      | none =>
          let stateOut ← d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          pure (d2sPermResolvedStep normal (.forward stateIn stateOut))

/-- A forward no-result branch with an already-found cache tail has exactly the one-capacity
tail handler as its continuation. -/
@[simp] lemma d2sHandleForwardNoResultRevised_tail
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = some (tail, cacheRest)) :
    d2sHandleForwardNoResultRevised normal stateIn =
      d2sHandlePoppedRateOnlyTailRevised normal ⟨stateIn, tail⟩ cacheRest := by
  unfold d2sHandleForwardNoResultRevised
  rw [hPop]

/-- With no pending lazy tail, an installed forward table entry is replayed through the common
resolved action without sampling.  This separate equation keeps the table-hit trace contract as
visible as the tail-hit and fresh-miss equations. -/
@[simp] lemma d2sHandleForwardNoResultRevised_table
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = some stateOut) :
    d2sHandleForwardNoResultRevised normal stateIn =
      pure (d2sPermResolvedStep normal (.forward stateIn stateOut)) := by
  unfold d2sHandleForwardNoResultRevised
  simp [hPop, hLookup]

/-- With neither a rate-only tail nor a forward-table mapping, Step 4.c's only random operation
is one full-state sample followed by the common forward transition. -/
@[simp] lemma d2sHandleForwardNoResultRevised_fresh
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none) :
    d2sHandleForwardNoResultRevised normal stateIn =
      d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>= fun stateOut =>
        pure (d2sPermResolvedStep normal (.forward stateIn stateOut)) := by
  unfold d2sHandleForwardNoResultRevised
  simp [hPop, hLookup]

/-! ## Revised Program materialization

After the Program branch has issued its `gᵢ` query and parsed the encoded challenge plus padding,
it has a first rate block and a list of later rate blocks.  The next two definitions isolate the
only capacity sampling in that branch.  They intentionally do not model the preceding `gᵢ` or
padding work: those are codec/oracle concerns; this boundary owns the permutation occurrence,
Monitor call, and initial rate-only-tail installation.
-/

/-- The rate-only cache produced by a continuing fresh Program mapping.  It contains exactly the
post-first blocks and no capacity for them. -/
def programResidualRateCache
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut : CanonicalSpongeState U)
    (remainingRates : List (Vector U SpongeSize.R)) : List (RateOnlyCacheEntry (U := U)) :=
  match RateOnlyTail.ofBlocks? (U := U) remainingRates with
  | none => normal.state.rateCacheP
  | some tail => ⟨stateOut, tail⟩ :: normal.state.rateCacheP

/-- Materialize a fresh Program mapping after its rate blocks have been parsed.  The common
forward action performs `Install → append → Monitor`; only a continuing result receives the
initial residual rate-only cache. -/
noncomputable def d2sProgramFirstRateRevised
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R))
    (capacity : Vector U SpongeSize.C) :
    D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U) :=
  let stateOut := d2sSynthesisState (U := U) firstRate capacity
  d2sReplaceRateCacheOnContinue (programResidualRateCache normal stateOut remainingRates)
    (d2sPermResolvedStep normal (.forward stateIn stateOut))

/-- A continuing Program materialization appends exactly its first programmed forward
occurrence.  The remaining rate blocks are cache-only data and have no hidden trace effect. -/
lemma d2sProgramFirstRateRevised_continue_trace
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R))
    (capacity : Vector U SpongeSize.C)
    {stateOut : CanonicalSpongeState U}
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hContinue : d2sProgramFirstRateRevised normal stateIn firstRate remainingRates capacity =
      .continue stateOut normal') :
    normal'.state.trace = normal.state.trace ++
      [⟨dsPermQuery stateIn, d2sSynthesisState (U := U) firstRate capacity⟩] := by
  unfold d2sProgramFirstRateRevised at hContinue
  obtain ⟨source, hSource, hTrace, _⟩ :=
    d2sReplaceRateCacheOnContinue_continue_source
      (programResidualRateCache normal
        (d2sSynthesisState (U := U) firstRate capacity) remainingRates)
      (d2sPermResolvedStep normal
        (.forward stateIn (d2sSynthesisState (U := U) firstRate capacity))) hContinue
  rw [hTrace]
  exact d2sPermResolvedStep_continue_trace normal
    (.forward stateIn (d2sSynthesisState (U := U) firstRate capacity)) hSource

/-- A stopped Program materialization is rooted at the input trace.  The residual `Cache_p`
update is continuation-only and therefore cannot alter a stop record's terminal history. -/
lemma d2sProgramFirstRateRevised_stopped_trace_extends
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R))
    (capacity : Vector U SpongeSize.C)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    {record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal'}
    (hStop : d2sProgramFirstRateRevised normal stateIn firstRate remainingRates capacity =
      .stopped normal' record) :
    ∃ tail, record.trace = normal.state.trace ++ tail := by
  unfold d2sProgramFirstRateRevised at hStop
  cases hStep : d2sPermResolvedStep normal
      (.forward stateIn (d2sSynthesisState (U := U) firstRate capacity))
  next answer normal'' =>
    simp [hStep] at hStop
  next normal'' record'' =>
    have hInput : normal'' = normal := d2sPermResolvedStep_stopped_normal_eq normal
      (.forward stateIn (d2sSynthesisState (U := U) firstRate capacity)) hStep
    subst normal''
    simp [hStep] at hStop
    cases hStop.1
    exact ⟨[⟨record.query, record.answer⟩], rfl⟩
  next =>
    exact False.elim (d2sPermResolvedStep_ne_underlyingAbort normal
      (.forward stateIn (d2sSynthesisState (U := U) firstRate capacity)) hStep)

/-- The sampling form of Program's fresh mapping.  It exposes the exact one capacity sample after
the first rate block has been determined; later tail capacities remain latent. -/
noncomputable def d2sHandleProgramFirstRateRevised
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R)) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) := do
  let capacity ← d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
  pure (d2sProgramFirstRateRevised normal stateIn firstRate remainingRates capacity)

@[simp] lemma d2sHandleProgramFirstRateRevised_eq
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R)) :
    d2sHandleProgramFirstRateRevised normal stateIn firstRate remainingRates =
      d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>= fun capacity =>
        pure (d2sProgramFirstRateRevised normal stateIn firstRate remainingRates capacity) := rfl

/-- None of the rate-only-tail machinery addresses the programmed `gᵢ` oracle.  These local
accounting lemmas isolate the auxiliary sampling performed by the three forward continuations,
so the only positive `gᵢ` cost in the complete dispatcher is the explicit query in Step 4.e.i. -/
lemma d2sHandlePoppedRateOnlyTailRevised_isQueryBoundP_g_zero
    [Fintype U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U))) :
    OracleComp.IsQueryBoundP
      (d2sHandlePoppedRateOnlyTailRevised normal entry cacheRest)
      (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) 0 := by
  rw [d2sHandlePoppedRateOnlyTailRevised_eq]
  simpa using d2sSampleCapacity_isQueryBoundP_g_zero
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)

lemma d2sHandleForwardNoResultRevised_isQueryBoundP_g_zero
    [Fintype U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U) :
    OracleComp.IsQueryBoundP
      (d2sHandleForwardNoResultRevised normal stateIn)
      (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) 0 := by
  unfold d2sHandleForwardNoResultRevised
  split
  · rename_i tail cacheRest _
    simpa using d2sHandlePoppedRateOnlyTailRevised_isQueryBoundP_g_zero
      (normal := normal) (entry := ⟨stateIn, tail⟩) (cacheRest := cacheRest)
  · split
    · simp
    · change (d2sSampleState (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>= fun stateOut =>
        pure (d2sPermResolvedStep normal (.forward stateIn stateOut))).IsQueryBoundP _ 0
      simpa using d2sSampleState_isQueryBoundP_g_zero
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)

lemma d2sHandleProgramFirstRateRevised_isQueryBoundP_g_zero
    [Fintype U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R)) :
    OracleComp.IsQueryBoundP
      (d2sHandleProgramFirstRateRevised normal stateIn firstRate remainingRates)
      (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) 0 := by
  rw [d2sHandleProgramFirstRateRevised_eq]
  simpa using d2sSampleCapacity_isQueryBoundP_g_zero
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)

/-! ## Revised inverse branch

The inverse branch is the first live sampler path to use the resolved-action core.  It has no
rate-only-cache interaction: an installed reverse lookup supplies the normalized preimage, and a
miss samples one full input state.  In both cases the selected pair is then passed unchanged to
the common conflict-aware transition.
-/

/-- Revised Algorithm 5.3 Step 3.  A reverse-table hit uses its installed preimage; a miss draws
one uniform full input state.  Both paths return the three-way result of the common resolved
inverse action, so a sampled input that conflicts with an existing forward input is retained as a
post-occurrence monitor stop rather than being silently converted to `Option.none`.

This is intentionally an `OracleComp` rather than the legacy mutable `StateT` handler: the only
reusable successor is carried by `.continue`, while `.stopped` carries no successor table/cache.
-/
noncomputable def d2sHandleInversePermQueryRevised
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut : CanonicalSpongeState U) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (CanonicalSpongeState U)) := do
  match TraceTableOps.outlu normal.state.trΔ.p stateOut with
  | some stateIn =>
      pure (d2sPermResolvedStep normal (.inverse stateOut stateIn))
  | none =>
      let stateIn ← d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      pure (d2sPermResolvedStep normal (.inverse stateOut stateIn))

/-- On an installed reverse lookup, the revised inverse branch makes no new random draw and
delegates definitionally to the common inverse action. -/
@[simp] lemma d2sHandleInversePermQueryRevised_hit
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = some stateIn) :
    d2sHandleInversePermQueryRevised normal stateOut =
      pure (d2sPermResolvedStep normal (.inverse stateOut stateIn)) := by
  unfold d2sHandleInversePermQueryRevised
  rw [hLookup]

/-- On a reverse-table miss, Step 3 makes exactly its one full-state sample and immediately sends
the selected pair to the common inverse action.  This equation is the local sampling interface for
the inverse part of the Lemma 5.8 first-bad calculation. -/
@[simp] lemma d2sHandleInversePermQueryRevised_miss
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut : CanonicalSpongeState U)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = none) :
    d2sHandleInversePermQueryRevised normal stateOut =
      d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>= fun stateIn =>
        pure (d2sPermResolvedStep normal (.inverse stateOut stateIn)) := by
  unfold d2sHandleInversePermQueryRevised
  rw [hLookup]

/-! ## Revised hash branch

Hash queries do not use permutation `Install`, but they obey the same append-then-monitor terminal
discipline.  Keeping this branch here makes the revised online transition total on all three oracle
directions before the forward sampling branches are migrated.
-/

/-- The deterministic continuation of a revised hash-table hit.  Sampling is deliberately absent:
the stored capacity is appended, then `Monitor` either retains the same hash table in a normal
successor or emits its post-occurrence stop record. -/
noncomputable def d2sHandleHashPresentRevised
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = some capacity) :
    D2SRevisedStepResult
  (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (Vector U SpongeSize.C) := by
  classical
  let trace' := normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩]
  by_cases hE : BadEventDS.E trace'
  · exact .stopped normal ⟨dsHashQuery stmt, capacity, hE⟩
  · let hMem : (stmt, capacity) ∈ TraceTableOps.entries normal.state.trΔ.h :=
      TraceTableOps.mem_entries_of_inlu_eq_some hLookup
    let hInv : normal.state.trΔ.IsSubsetOfQueryLog trace' :=
      TraceNabla.IsSubsetOfQueryLog_append_any normal.state.h_inv ⟨dsHashQuery stmt, capacity⟩
    let hMirror : normal.state.trΔ.MirrorsQueryLog trace' :=
      TraceNabla.MirrorsQueryLog_append_hash_existing normal.state.h_mirror stmt capacity hMem
    let state' : D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
      { normal.state with trace := trace', h_inv := hInv, h_mirror := hMirror }
    exact .continue capacity ⟨state', hE, normal.permutationNodup,
      normal.hashNodup, normal.hashInputFunctional⟩

/-- The deterministic continuation of a revised hash-table miss after its one capacity sample.
The caller establishes the `none` lookup guard before invoking this continuation; its role here is
only to install the selected mapping, append its sole occurrence, and run `Monitor`. -/
noncomputable def d2sHandleHashFreshRevised
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = none) :
    D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (Vector U SpongeSize.C) := by
  classical
  let trace' := normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩]
  by_cases hE : BadEventDS.E trace'
  · exact .stopped normal ⟨dsHashQuery stmt, capacity, hE⟩
  · let trDelta' : TraceNabla T_H T_P StmtIn U :=
      { normal.state.trΔ with h := TraceTableOps.add normal.state.trΔ.h stmt capacity }
    let hInv : trDelta'.IsSubsetOfQueryLog trace' :=
      TraceNabla.IsSubsetOfQueryLog_append_hash normal.state.h_inv stmt capacity
    let hMirror : trDelta'.MirrorsQueryLog trace' :=
      TraceNabla.MirrorsQueryLog_append_hash_add normal.state.h_mirror stmt capacity
    let state' : D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
      { normal.state with trace := trace', trΔ := trDelta', h_inv := hInv, h_mirror := hMirror }
    exact .continue capacity ⟨state', hE, normal.permutationNodup,
      normal.hash_add_nodup hLookup, normal.hash_add_inputFunctional hLookup⟩

omit [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
/-- A continuing stored-hash replay appends its one queried occurrence exactly. -/
lemma d2sHandleHashPresentRevised_continue_trace
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = some capacity)
    {answer : Vector U SpongeSize.C}
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hContinue : d2sHandleHashPresentRevised normal stmt capacity hLookup =
      .continue answer normal') :
    normal'.state.trace = normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩] := by
  classical
  unfold d2sHandleHashPresentRevised at hContinue
  dsimp at hContinue
  by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩])
  · simp [hE] at hContinue
  · simp [hE] at hContinue
    rcases hContinue with ⟨_, hNormal⟩
    rw [← hNormal]

/-- A stored-hash monitor stop keeps the input normal state as its pre-occurrence state, so its
terminal record extends precisely that input trace. -/
lemma d2sHandleHashPresentRevised_stopped_trace_extends
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = some capacity)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    {record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal'}
    (hStop : d2sHandleHashPresentRevised normal stmt capacity hLookup = .stopped normal' record) :
    ∃ tail, record.trace = normal.state.trace ++ tail := by
  classical
  unfold d2sHandleHashPresentRevised at hStop
  dsimp at hStop
  by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩])
  · simp [hE] at hStop
    cases hStop.1
    exact ⟨[⟨record.query, record.answer⟩], rfl⟩
  · simp [hE] at hStop

/-- A continuing freshly sampled hash mapping appends its one queried occurrence exactly. -/
lemma d2sHandleHashFreshRevised_continue_trace
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = none)
    {answer : Vector U SpongeSize.C}
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hContinue : d2sHandleHashFreshRevised normal stmt capacity hLookup =
      .continue answer normal') :
    normal'.state.trace = normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩] := by
  classical
  unfold d2sHandleHashFreshRevised at hContinue
  dsimp at hContinue
  by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩])
  · simp [hE] at hContinue
  · simp [hE] at hContinue
    rcases hContinue with ⟨_, hNormal⟩
    rw [← hNormal]

/-- A freshly sampled hash monitor stop has the same terminal-history discipline as a stored
hash replay: its stop record is rooted at the input normal trace. -/
lemma d2sHandleHashFreshRevised_stopped_trace_extends
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = none)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    {record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal'}
    (hStop : d2sHandleHashFreshRevised normal stmt capacity hLookup = .stopped normal' record) :
    ∃ tail, record.trace = normal.state.trace ++ tail := by
  classical
  unfold d2sHandleHashFreshRevised at hStop
  dsimp at hStop
  by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩])
  · simp [hE] at hStop
    cases hStop.1
    exact ⟨[⟨record.query, record.answer⟩], rfl⟩
  · simp [hE] at hStop

/-- Revised Algorithm 5.3 Step 2.  A stored hash answer is replayed; a missing answer is sampled
once and added to the normalized hash table.  In both cases the actual hash occurrence is appended
before `Monitor` decides whether a reusable normal state may be returned. -/
noncomputable def d2sHandleHashQueryRevised
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (Vector U SpongeSize.C)) := do
  match hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt with
  | some capacity =>
      pure (d2sHandleHashPresentRevised normal stmt capacity hLookup)
  | none =>
      let capacity ← d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      pure (d2sHandleHashFreshRevised normal stmt capacity hLookup)

/-- A revised hash hit makes no random query after the lookup. -/
@[simp] lemma d2sHandleHashQueryRevised_hit
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = some capacity) :
    d2sHandleHashQueryRevised normal stmt =
      pure (d2sHandleHashPresentRevised normal stmt capacity hLookup) := by
  unfold d2sHandleHashQueryRevised
  split
  · rename_i capacity' hCase
    have hEq : capacity' = capacity := Option.some.inj (hCase.symm.trans hLookup)
    subst capacity'
    rfl
  · rename_i hCase
    exact (nomatch (hCase.symm.trans hLookup))

/-- A revised hash miss consists of its one uniform capacity sample followed by the deterministic
fresh-hash continuation. -/
@[simp] lemma d2sHandleHashQueryRevised_miss
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = none) :
    d2sHandleHashQueryRevised normal stmt =
      d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>= fun capacity =>
        pure (d2sHandleHashFreshRevised normal stmt capacity hLookup) := by
  unfold d2sHandleHashQueryRevised
  split
  · rename_i capacity hCase
    exact (nomatch (hCase.symm.trans hLookup))
  · rfl

/-! ## Finite mixed-direction runner

The probability proof sees a sequence of actual oracle occurrences, while the three directions
return differently typed answers.  `D2SRevisedOracleAction` erases only that answer type: it keeps
the exact `h` occurrence or already-resolved `p`/`p⁻¹` pair, and every action returns the shared
three-way boundary.  Thus a finite first-bad-event induction has exactly one absorbing runner and
one terminal-record convention.

This is intentionally not a second implementation of the six semantic D2SQuery branches.  A
tail-hit, table-hit, fresh miss, or Program branch first selects a `D2SPermResolvedAction`; this
runner begins at that common `Install → append → Monitor` tail. -/

/-- An actual direction-tagged oracle action after the forward/inverse branch has selected its
input/output pair.  Hash actions still perform their one lookup-or-capacity-sample selection. -/
inductive D2SRevisedOracleAction (StmtIn U : Type) [SpongeUnit U] [SpongeSize] where
  | hash (stmt : StmtIn)
  | inverseQuery (stateOut : CanonicalSpongeState U)
  | forwardNoResult (stateIn : CanonicalSpongeState U)
  | programFirstRate (stateIn : CanonicalSpongeState U)
      (firstRate : Vector U SpongeSize.R)
      (remainingRates : List (Vector U SpongeSize.R))
  | perm (action : D2SPermResolvedAction U)
  | tail (entry : RateOnlyCacheEntry (U := U))
      (cacheRest : List (RateOnlyCacheEntry (U := U)))

/-- Execute one mixed-direction revised action, retaining only `Unit` as its public answer.  The
normal state or terminal stop record is unchanged by that answer erasure. -/
noncomputable def d2sRevisedOracleStep
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    D2SRevisedOracleAction StmtIn U →
      OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
        (D2SRevisedStepResult
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) Unit)
  | .hash stmt => do
      let result ← d2sHandleHashQueryRevised normal stmt
      pure (result.map fun _ => ())
  | .inverseQuery stateOut => do
      let result ← d2sHandleInversePermQueryRevised normal stateOut
      pure (result.map fun _ => ())
  | .forwardNoResult stateIn => do
      let result ← d2sHandleForwardNoResultRevised normal stateIn
      pure (result.map fun _ => ())
  | .programFirstRate stateIn firstRate remainingRates => do
      let result ← d2sHandleProgramFirstRateRevised normal stateIn firstRate remainingRates
      pure (result.map fun _ => ())
  | .perm action =>
      pure ((d2sPermResolvedStep normal action).map fun _ => ())
  | .tail entry cacheRest => do
      let result ← d2sHandlePoppedRateOnlyTailRevised normal entry cacheRest
      pure (result.map fun _ => ())

@[simp] lemma d2sRevisedOracleStep_hash
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) :
    d2sRevisedOracleStep normal (.hash stmt) = (do
      let result ← d2sHandleHashQueryRevised normal stmt
      pure (result.map fun _ => ())) := rfl

@[simp] lemma d2sRevisedOracleStep_inverseQuery
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut : CanonicalSpongeState U) :
    d2sRevisedOracleStep normal (.inverseQuery stateOut) = (do
      let result ← d2sHandleInversePermQueryRevised normal stateOut
      pure (result.map fun _ => ())) := rfl

@[simp] lemma d2sRevisedOracleStep_forwardNoResult
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U) :
    d2sRevisedOracleStep normal (.forwardNoResult stateIn) = (do
      let result ← d2sHandleForwardNoResultRevised normal stateIn
      pure (result.map fun _ => ())) := rfl

@[simp] lemma d2sRevisedOracleStep_programFirstRate
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R)) :
    d2sRevisedOracleStep normal (.programFirstRate stateIn firstRate remainingRates) = (do
      let result ← d2sHandleProgramFirstRateRevised normal stateIn firstRate remainingRates
      pure (result.map fun _ => ())) := rfl

@[simp] lemma d2sRevisedOracleStep_perm
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (action : D2SPermResolvedAction U) :
    d2sRevisedOracleStep normal (.perm action) =
      pure ((d2sPermResolvedStep normal action).map fun _ => ()) := rfl

@[simp] lemma d2sRevisedOracleStep_tail
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U))) :
    d2sRevisedOracleStep normal (.tail entry cacheRest) = (do
      let result ← d2sHandlePoppedRateOnlyTailRevised normal entry cacheRest
      pure (result.map fun _ => ())) := rfl

/-- Run a finite mixed-direction sequence and stop immediately on the first monitor failure or
underlying abort.  An unconsumed suffix is never queried.  This is the execution-level form of
the updated D2SQuery stop convention needed in the stopped first-event calculation. -/
noncomputable def d2sRevisedOracleRun
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    List (D2SRevisedOracleAction StmtIn U) →
      OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
        (D2SRevisedStepResult
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) Unit)
  | [] => pure (.continue () normal)
  | action :: actions => do
      let result ← d2sRevisedOracleStep normal action
      match result with
      | .continue _ normal' => d2sRevisedOracleRun normal' actions
      | .stopped normal' record => pure (.stopped normal' record)
      | .underlyingAbort => pure .underlyingAbort

@[simp] lemma d2sRevisedOracleRun_nil
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    d2sRevisedOracleRun normal [] = pure (.continue () normal) := rfl

/-- A mixed runner does not consume any suffix after the first stopped result: this unfolding
equation is intentionally the only induction entry point needed by a stopping-time proof. -/
@[simp] lemma d2sRevisedOracleRun_cons
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (action : D2SRevisedOracleAction StmtIn U)
    (actions : List (D2SRevisedOracleAction StmtIn U)) :
    d2sRevisedOracleRun normal (action :: actions) = (do
      let result ← d2sRevisedOracleStep normal action
      match result with
      | .continue _ normal' => d2sRevisedOracleRun normal' actions
      | .stopped normal' record => pure (.stopped normal' record)
      | .underlyingAbort => pure .underlyingAbort) := rfl

/-- Run finitely many resolved permutation actions, stopping at the first monitor failure or
underlying abort.  The `Unit` answer says only that the whole resolved-action list completed; the
last concrete sponge-state answer is intentionally not retained here because every action's exact
answer already remains in the insertion trace. -/
noncomputable def d2sPermResolvedRun
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    List (D2SPermResolvedAction U) →
      D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) Unit
  | [] => .continue () normal
  | action :: actions =>
      match d2sPermResolvedStep normal action with
      | .continue _ normal' => d2sPermResolvedRun normal' actions
      | .stopped normal' record => .stopped normal' record
      | .underlyingAbort => .underlyingAbort

@[simp] lemma d2sPermResolvedRun_nil
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    d2sPermResolvedRun normal [] = .continue () normal := rfl

end DuplexSpongeFS.ProverTransform
