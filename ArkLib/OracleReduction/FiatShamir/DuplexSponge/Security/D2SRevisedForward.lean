/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SRevisedOperations

/-!
# Revised forward branch for monitored D2SQuery

This module connects the live `Backtrack.backTrack` search result to the common revised
three-way transition boundary.  It deliberately contains no probability argument: its purpose is
to make Algorithm 5.3's complete Item 4 dispatch have one executable, proof-facing result type.

Every branch that has selected a forward permutation pair reaches

    Install → add one occurrence → Monitor.

Thus an installation conflict or any other first bad event is represented by a
`D2SPostOccurrenceStopRecord`, while `underlyingAbort` is reserved for a BackTrack/parser failure
*before* a permutation occurrence exists.  The call to the current executable `backTrack` remains
visible here.  Replacing it by the stateful replay implementation later is therefore a local
refinement of this boundary, not a change to the sampling/Monitor proof interface.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.ProverTransform

open DSTraceStorage

variable {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-! ## Program continuation and live BackTrack dispatch -/

/-- Algorithm 5.3 Step 4.e after the `g_i` response has been obtained.  A pre-existing forward
mapping wins before the response is parsed, as in the paper.  On a miss, parsing/padding produces
rate blocks; its first block is materialized by the one-capacity Program transition and all later
blocks remain a rate-only tail.  The empty-block case is the existing parser failure and produces
`underlyingAbort` before a permutation occurrence. -/
noncomputable def d2sHandleBacktrackAfterGRevised
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx)) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) := do
  match TraceTableOps.inlu normal.state.trΔ.p stateIn with
  | some stateOut =>
      pure (d2sPermResolvedStep normal (.forward stateIn stateOut))
  | none =>
      let rateBlocks ← d2sRateBlocksFromChallenge
        (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (i := backtrackOut.roundIdx) rhoHat
      match rateBlocks.toList with
      | [] => pure .underlyingAbort
      | firstRate :: remainingRates =>
          d2sHandleProgramFirstRateRevised normal stateIn firstRate remainingRates

/-- Algorithm 5.3 Step 4.e, including the `g_i` call.  A pending lazy tail has priority even
after BackTrack has returned a candidate: that input is a scheduled squeeze continuation, not a
new programming point, so it is materialized before any `g_i` query.  A zero-length challenge
then follows the paper's terminal/no-challenge convention and falls through to Step 4.c; a
genuine nonempty challenge with no pending tail reissues its encoded `g_i` query and enters the
Program continuation above. -/
noncomputable def d2sHandleBacktrackSomeRevised
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) :=
  match popRateOnlyTailByInput normal.state.rateCacheP stateIn with
  | some (tail, cacheRest) =>
      d2sHandlePoppedRateOnlyTailRevised normal ⟨stateIn, tail⟩ cacheRest
  | none =>
      if d2sInCodecImagePredicate
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut then
        if 0 < challengeSize (pSpec := pSpec) backtrackOut.roundIdx then do
          let rhoHat ← d2sQueryG (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
            backtrackOut.roundIdx backtrackOut.stmt backtrackOut.salt backtrackOut.encodedMessages
          d2sHandleBacktrackAfterGRevised normal stateIn backtrackOut rhoHat
        else
          d2sHandleForwardNoResultRevised normal stateIn
      else
        d2sHandleForwardNoResultRevised normal stateIn

/-- A successful BackTrack candidate cannot bypass a pending lazy continuation.  If the current
forward input is a cache key, the exact tail handler consumes that one pending rate block and no
`g_i` query is issued. -/
@[simp] lemma d2sHandleBacktrackSomeRevised_tail
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (tail : RateOnlyTail (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = some (tail, cacheRest)) :
    d2sHandleBacktrackSomeRevised normal stateIn backtrackOut =
      d2sHandlePoppedRateOnlyTailRevised normal ⟨stateIn, tail⟩ cacheRest := by
  simp [d2sHandleBacktrackSomeRevised, hPop]

/-- Step 4.d is selected exactly when the recovered BackTrack tuple is outside the codec image.
The corrected paper requires it to execute **all** of `Ordinary` Step 4.c.i--iii: in particular,
an existing rate-only tail is consumed before a table lookup or a full-state sample.  This equation
therefore shares the exact same lazy-sampling boundary as the `.noResult` case. -/
@[simp] lemma d2sHandleBacktrackSomeRevised_notInImage
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hImage : ¬ d2sInCodecImagePredicate
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut) :
    d2sHandleBacktrackSomeRevised normal stateIn backtrackOut =
      d2sHandleForwardNoResultRevised normal stateIn := by
  simp [d2sHandleBacktrackSomeRevised, hPop, hImage]

/-- A recovered codec-image tuple with an empty verifier challenge has no forward permutation
occurrence to program, so it follows the ordinary no-result continuation. -/
@[simp] lemma d2sHandleBacktrackSomeRevised_emptyChallenge
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hImage : d2sInCodecImagePredicate
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut)
    (hEmpty : ¬ 0 < challengeSize (pSpec := pSpec) backtrackOut.roundIdx) :
    d2sHandleBacktrackSomeRevised normal stateIn backtrackOut =
      d2sHandleForwardNoResultRevised normal stateIn := by
  simp [d2sHandleBacktrackSomeRevised, hPop, hImage, hEmpty]

/-- A nonempty in-image tuple first reissues the precise encoded `g_i` key.  The continuation is
the only place where its response can cause a parser abort or initiate Program materialization. -/
@[simp] lemma d2sHandleBacktrackSomeRevised_nonemptyChallenge
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hImage : d2sInCodecImagePredicate
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut)
    (hNonempty : 0 < challengeSize (pSpec := pSpec) backtrackOut.roundIdx) :
    d2sHandleBacktrackSomeRevised normal stateIn backtrackOut =
      d2sQueryG (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        backtrackOut.roundIdx backtrackOut.stmt backtrackOut.salt backtrackOut.encodedMessages
        >>= fun rhoHat => d2sHandleBacktrackAfterGRevised normal stateIn backtrackOut rhoHat := by
  simp [d2sHandleBacktrackSomeRevised, hPop, hImage, hNonempty]

/-- The Program continuation reuses an already-installed forward mapping before it parses or
samples from the codec answer. -/
@[simp] lemma d2sHandleBacktrackAfterGRevised_hit
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx))
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = some stateOut) :
    d2sHandleBacktrackAfterGRevised normal stateIn backtrackOut rhoHat =
      pure (d2sPermResolvedStep normal (.forward stateIn stateOut)) := by
  unfold d2sHandleBacktrackAfterGRevised
  rw [hLookup]

/-- On a codec-image forward-table miss, all parser/padding randomness occurs before the one
Program capacity sample.  This equation exposes that exact two-stage factorization. -/
@[simp] lemma d2sHandleBacktrackAfterGRevised_miss
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx))
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none) :
    d2sHandleBacktrackAfterGRevised normal stateIn backtrackOut rhoHat =
      d2sRateBlocksFromChallenge
        (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (i := backtrackOut.roundIdx) rhoHat >>= fun rateBlocks =>
          match rateBlocks.toList with
          | [] => pure .underlyingAbort
          | firstRate :: remainingRates =>
              d2sHandleProgramFirstRateRevised normal stateIn firstRate remainingRates := by
  unfold d2sHandleBacktrackAfterGRevised
  rw [hLookup]

/-- The result-facing half of Algorithm 5.3 Step 4.  It is factored away from the current
`Backtrack.backTrack` call so that the later stateful-replay refinement need only prove that it
produces the same `ExperimentOutput`: it reuses this exact branch dispatcher unchanged. -/
noncomputable def d2sHandleForwardSearchResultRevised
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (search : ExperimentOutput (Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) :=
  match search with
  | .err => pure .underlyingAbort
  | .noResult => d2sHandleForwardNoResultRevised normal stateIn
  | .some backtrackOut => d2sHandleBacktrackSomeRevised normal stateIn backtrackOut

@[simp] lemma d2sHandleForwardSearchResultRevised_err
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U) :
    d2sHandleForwardSearchResultRevised normal stateIn .err = pure .underlyingAbort := rfl

@[simp] lemma d2sHandleForwardSearchResultRevised_noResult
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U) :
    d2sHandleForwardSearchResultRevised normal stateIn .noResult =
      d2sHandleForwardNoResultRevised normal stateIn := rfl

@[simp] lemma d2sHandleForwardSearchResultRevised_some
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    d2sHandleForwardSearchResultRevised normal stateIn (.some backtrackOut) =
      d2sHandleBacktrackSomeRevised normal stateIn backtrackOut := rfl

/-- Complete revised Algorithm 5.3 Step 4 dispatcher.  A pending lazy tail has **priority** over
BackTrack: it is the scheduled continuation of an already-programmed squeeze, so it consumes one
tail block without performing a new search or `g_i` query.  Only a cache miss invokes BackTrack;
then `.err` is the sole source of `underlyingAbort`, and every selected forward pair uses the
shared revised Install/Monitor transition. -/
noncomputable def d2sHandleForwardPermQueryRevised
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U)) :=
  match popRateOnlyTailByInput normal.state.rateCacheP stateIn with
  | some (tail, cacheRest) =>
      d2sHandlePoppedRateOnlyTailRevised normal ⟨stateIn, tail⟩ cacheRest
  | none =>
      d2sHandleForwardSearchResultRevised normal stateIn (Backtrack.backTrack
        (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        normal.state.trace normal.state.trΔ normal.state.h_inv stateIn
        (normal.state.trace.length + 1))

/-- A cache hit at the outer forward dispatcher is consumed before BackTrack.  In particular,
neither a BackTrack error nor a `g_i` query can preempt a scheduled lazy squeeze continuation. -/
@[simp] lemma d2sHandleForwardPermQueryRevised_tail
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = some (tail, cacheRest)) :
    d2sHandleForwardPermQueryRevised normal stateIn =
      d2sHandlePoppedRateOnlyTailRevised normal ⟨stateIn, tail⟩ cacheRest := by
  simp [d2sHandleForwardPermQueryRevised, hPop]

/-- The revised forward handler preserves the existing BackTrack `.err` branch exactly, but its
abort is now explicitly distinguished from a monitored post-occurrence stop. -/
@[simp] lemma d2sHandleForwardPermQueryRevised_err
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hBacktrack : Backtrack.backTrack
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      normal.state.trace normal.state.trΔ normal.state.h_inv stateIn
      (normal.state.trace.length + 1) = .err) :
    d2sHandleForwardPermQueryRevised normal stateIn = pure .underlyingAbort := by
  unfold d2sHandleForwardPermQueryRevised
  rw [hPop, hBacktrack]
  rfl

/-- The revised forward handler exposes Step 4.c verbatim when BackTrack finds no candidate. -/
@[simp] lemma d2sHandleForwardPermQueryRevised_noResult
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hBacktrack : Backtrack.backTrack
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      normal.state.trace normal.state.trΔ normal.state.h_inv stateIn
      (normal.state.trace.length + 1) = .noResult) :
    d2sHandleForwardPermQueryRevised normal stateIn =
      d2sHandleForwardNoResultRevised normal stateIn := by
  unfold d2sHandleForwardPermQueryRevised
  rw [hPop, hBacktrack]
  rfl

/-- The successful BackTrack branch carries its concrete recovered tuple into the revised
in-image/non-image dispatcher. -/
@[simp] lemma d2sHandleForwardPermQueryRevised_some
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hBacktrack : Backtrack.backTrack
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      normal.state.trace normal.state.trΔ normal.state.h_inv stateIn
      (normal.state.trace.length + 1) = .some backtrackOut) :
    d2sHandleForwardPermQueryRevised normal stateIn =
      d2sHandleBacktrackSomeRevised normal stateIn backtrackOut := by
  unfold d2sHandleForwardPermQueryRevised
  rw [hPop, hBacktrack]
  rfl

/-- Complete revised D2SQuery one-step dispatcher.  It is the live counterpart of the paper's
three top-level cases: hash, inverse permutation, and forward permutation.  In all directions a
monitor stop is absorbing and preserves its actual final occurrence. -/
noncomputable def d2sQueryStepRevised
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        ((duplexSpongeChallengeOracle StmtIn U).Range q)) :=
  match q with
  | dsHashQuery stmt => d2sHandleHashQueryRevised normal stmt
  | dsPermInvQuery stateOut => d2sHandleInversePermQueryRevised normal stateOut
  | dsPermQuery stateIn => d2sHandleForwardPermQueryRevised normal stateIn

@[simp] lemma d2sQueryStepRevised_hash
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) :
    d2sQueryStepRevised normal (dsHashQuery stmt) = d2sHandleHashQueryRevised normal stmt := rfl

@[simp] lemma d2sQueryStepRevised_inverse
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut : CanonicalSpongeState U) :
    d2sQueryStepRevised normal (dsPermInvQuery stateOut) =
      d2sHandleInversePermQueryRevised normal stateOut := rfl

@[simp] lemma d2sQueryStepRevised_forward
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U) :
    d2sQueryStepRevised normal (dsPermQuery stateIn) =
      d2sHandleForwardPermQueryRevised normal stateIn := rfl

/-! ## One-sample gateway distribution equations

Each revised random gateway below is reduced to exactly one uniform sample followed by a
deterministic post-sample transition.  These equations are deliberately stated before any
bad-event predicate: the Lemma 5.8 proof can combine them with the common first-bad finite-target
normal forms, without unfolding a handler, a rate-only cache, or a `simulateQ` implementation.
-/

/-- A Step 2 hash miss is one uniform capacity draw followed by the deterministic fresh-hash
transition. -/
lemma d2sHandleHashQueryRevised_miss_simulateQ_probEvent_eq
    [Fintype U] [SampleableType U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = none)
    (P : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (Vector U SpongeSize.C) → Prop) :
    Pr[ P |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandleHashQueryRevised normal stmt)]
      =
    Pr[ fun capacity => P (d2sHandleHashFreshRevised normal stmt capacity hLookup) |
      ($ᵗ (Vector U SpongeSize.C)) ] := by
  rw [d2sHandleHashQueryRevised_miss normal stmt hLookup]
  simpa using d2sSampleCapacity_simulateQ_probEvent_eq
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) gImpl
    (fun capacity => P (d2sHandleHashFreshRevised normal stmt capacity hLookup))

/-- A Step 3 inverse-table miss is one uniform full-state draw followed by the resolved inverse
transition. -/
lemma d2sHandleInversePermQueryRevised_miss_simulateQ_probEvent_eq
    [Fintype U] [SampleableType U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut : CanonicalSpongeState U)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = none)
    (P : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (CanonicalSpongeState U) → Prop) :
    Pr[ P |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandleInversePermQueryRevised normal stateOut)]
      =
    Pr[ fun stateIn => P (d2sPermResolvedStep normal (.inverse stateOut stateIn)) |
      ($ᵗ (CanonicalSpongeState U)) ] := by
  rw [d2sHandleInversePermQueryRevised_miss normal stateOut hLookup]
  simpa using d2sSampleState_simulateQ_probEvent_eq
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) gImpl
    (fun stateIn => P (d2sPermResolvedStep normal (.inverse stateOut stateIn)))

/-- A Step 4.c true miss is one uniform full-state draw followed by the resolved forward
transition. -/
lemma d2sHandleForwardNoResultRevised_fresh_simulateQ_probEvent_eq
    [Fintype U] [SampleableType U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none)
    (P : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (CanonicalSpongeState U) → Prop) :
    Pr[ P |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandleForwardNoResultRevised normal stateIn)]
      =
    Pr[ fun stateOut => P (d2sPermResolvedStep normal (.forward stateIn stateOut)) |
      ($ᵗ (CanonicalSpongeState U)) ] := by
  rw [d2sHandleForwardNoResultRevised_fresh normal stateIn hPop hLookup]
  simpa using d2sSampleState_simulateQ_probEvent_eq
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) gImpl
    (fun stateOut => P (d2sPermResolvedStep normal (.forward stateIn stateOut)))

/-- A selected rate-only tail is materialized by exactly one uniform capacity draw. -/
lemma d2sHandlePoppedRateOnlyTailRevised_simulateQ_probEvent_eq
    [Fintype U] [SampleableType U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (P : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (CanonicalSpongeState U) → Prop) :
    Pr[ P |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandlePoppedRateOnlyTailRevised normal entry cacheRest)]
      =
    Pr[ fun capacity => P (d2sConsumePoppedRateOnlyTailRevised normal entry cacheRest capacity) |
      ($ᵗ (Vector U SpongeSize.C)) ] := by
  rw [d2sHandlePoppedRateOnlyTailRevised_eq normal entry cacheRest]
  simpa using d2sSampleCapacity_simulateQ_probEvent_eq
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) gImpl
    (fun capacity => P (d2sConsumePoppedRateOnlyTailRevised normal entry cacheRest capacity))

/-- A nonempty Program branch materializes its first rate block with exactly one uniform capacity
draw; later rate blocks remain latent in the rate-only tail. -/
lemma d2sHandleProgramFirstRateRevised_simulateQ_probEvent_eq
    [Fintype U] [SampleableType U]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R))
    (P : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (CanonicalSpongeState U) → Prop) :
    Pr[ P |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandleProgramFirstRateRevised normal stateIn firstRate remainingRates)]
      =
    Pr[ fun capacity =>
      P (d2sProgramFirstRateRevised normal stateIn firstRate remainingRates capacity) |
      ($ᵗ (Vector U SpongeSize.C)) ] := by
  rw [d2sHandleProgramFirstRateRevised_eq normal stateIn firstRate remainingRates]
  simpa using d2sSampleCapacity_simulateQ_probEvent_eq
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) gImpl
    (fun capacity =>
      P (d2sProgramFirstRateRevised normal stateIn firstRate remainingRates capacity))

/-! ## Revised `QueryImpl` bridge -/

/-- The proof-visible reason why an oracle-driven revised `D2SQuery` execution stopped.  This is
the lossless counterpart of the public `Alternative.failure` adapter below: a monitored stop
retains its *actual* pre-occurrence normal state and the final occurrence certified by `Monitor`,
whereas a parser/search failure retains the normal state at which no occurrence was produced.

The type is deliberately local to the revised executor.  It is the error payload needed by the
instrumented Hyb₁ coupling boundary; it neither invents a successor after a bad event nor turns an
ordinary oracle failure into a bad-event witness. -/
inductive D2SRevisedStoppingReason where
  | monitorStop
      (state : D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (record : D2SPostOccurrenceStopRecord
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) state) :
      D2SRevisedStoppingReason
  | underlyingAbort
      (state : D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
      D2SRevisedStoppingReason
  | oracleAbort
      (state : D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
      D2SRevisedStoppingReason

/-- The complete base trace visible at an instrumented stop.  A monitor stop includes its final
attempted occurrence; an underlying/parser or oracle abort has produced no additional occurrence
and therefore exposes the current normal trace.  This is the observable used to define the first
bad index in a whole-execution coupling. -/
def D2SRevisedStoppingReason.trace
    (reason : D2SRevisedStoppingReason
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  match reason with
  | .monitorStop _ record => record.trace
  | .underlyingAbort state => state.state.trace
  | .oracleAbort state => state.state.trace

/-- Whether an instrumented stop is the monitored, post-occurrence stop that contributes to the
Lemma 5.8 bad-event charge.  This is intentionally false for search/parser and ambient-oracle
failures: they are separately ruled out by the replay/no-abort lemmas. -/
def D2SRevisedStoppingReason.isMonitorStop
    (reason : D2SRevisedStoppingReason
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Prop :=
  match reason with
  | .monitorStop _ _ => True
  | .underlyingAbort _ => False
  | .oracleAbort _ => False

/-- Classify one revised D2S step for a lossless D2F execution while preserving the memo state.
The construction has one continuing result and exactly the two paper-visible absorbing reasons;
expressing it as a pure `Except` value makes the `StateT`/`ExceptT` simulation naturality used in
the Lemma 5.8 Hyb₁ coupling explicit. -/
def d2sRevisedStepPost
    {α M : Type}
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) α)
    (memo : M) :
    Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      ((α × D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × M) :=
  match result with
  | .continue answer normal' => .ok ((answer, normal'), memo)
  | .stopped state record => .error (.monitorStop state record)
  | .underlyingAbort => .error (.underlyingAbort normal)

/-- The lossless, `simulateQ`-ready one-query adapter for the revised dispatcher.  It executes
the real `d2sQueryStepRevised` with the same `gᵢ` and auxiliary implementations as the public
adapter, but sends an absorbing outcome to `ExceptT` instead of erasing it to `failure`.

Consequently the generated distribution is unchanged after forgetting the exception payload,
while a coupling or first-bad-event proof can inspect the precise post-occurrence stop record.
This is the required instrumentation boundary for Hyb₁; the existing
`d2sQueryImplRevised` remains the public, abort-erasing Algorithm 5.3 interface. -/
noncomputable def d2sQueryImplRevisedStopping
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp)) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT
        (D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (ExceptT
          (D2SRevisedStoppingReason
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          ProbComp)) := by
  classical
  exact fun q normal => do
    let combinedImpl :
        QueryImpl
          (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
          (OptionT ProbComp) :=
      gImpl + auxImpl
    let result? ← ExceptT.lift (simulateQ combinedImpl
      (d2sQueryStepRevised (T_H := T_H) (T_P := T_P) normal q)).run
    match result? with
    | none => throw (.oracleAbort normal)
    | some (.continue answer normal') => pure ⟨answer, normal'⟩
    | some (.stopped state record) => throw (.monitorStop state record)
    | some .underlyingAbort => throw (.underlyingAbort normal)

/-- The live `QueryImpl` adapter for revised Algorithm 5.3.

It preserves the existing outer interpreter architecture: internal `gᵢ` and sampling queries are
translated by `gImpl + auxImpl`, while the mutable state is now the proof-carrying
`D2SNormalState`.  A `continue` result exposes its answer and reusable state.  Both absorbing
outcomes become the caller's ordinary `Alternative` failure, exactly as the existing D2SQuery
interface does; the more informative stopped record remains available in
`d2sQueryStepRevised` for the first-bad-event coupling.

This is intentionally a new adapter, rather than a modification of legacy `d2sQueryImpl`: the
latter remains temporarily available for comparison while Hyb₁--Hyb₄ are migrated to the revised
stateful executor. -/
noncomputable def d2sQueryImplRevised
    {m : Type → Type} [Monad m] [Alternative m]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) m)
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) m) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT
        (D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        m) := by
  classical
  exact fun q normal => do
    let combinedImpl :
        QueryImpl
          (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) m :=
      gImpl + auxImpl
    let result ← simulateQ combinedImpl
      (d2sQueryStepRevised (T_H := T_H) (T_P := T_P) normal q)
    match result with
    | .continue answer normal' => pure ⟨answer, normal'⟩
    | .stopped _ _ => failure
    | .underlyingAbort => failure

/-! ## Revised D2F / D2SAlgo executable bridge -/

section RevisedD2F

variable {ι : Type} {oSpec : OracleSpec ι}
  [Fintype U]

/-- The lossless inner handler for one revised D2S query in the Eq. (16) executor.

It is factored out of `d2fOuterImplRevisedStopping` so that a proof may push an outer oracle
interpretation through exactly the same `gᵢ`-memo and auxiliary-query layer.  An absent `gᵢ`
answer is an input-state oracle abort; the two absorbing D2S step outcomes are classified only
by the outer handler after this computation returns. -/
noncomputable def d2fStoppingD2SInner
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type}
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    QueryImpl (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (StateT M
        (ExceptT
          (D2SRevisedStoppingReason
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          (OracleComp (oSpec +
            D2SChallengePlusUnitOracle (U := U) challengeSpec)))) := by
  classical
  exact fun
    | .inl gq => fun memo => do
      let answer? ← ExceptT.lift ((gImpl gq).run memo).run
      match answer? with
      | some (answer, memo') => pure (answer, memo')
      | none => throw (D2SRevisedStoppingReason.oracleAbort normal)
    | .inr aux => StateT.lift <| ExceptT.lift <|
      query (spec := oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
        (Sum.inr (Sum.inr aux))

/-- The Eq. (16) outer oracle implementation with the revised D2SQuery state boundary.
It has exactly the same ambient and target oracle interfaces as `d2fOuterImpl`; the only change is
that a duplex-sponge query is interpreted by `d2sQueryImplRevised` and therefore can continue only
from a monitor-passing, partial-bijection state. -/
noncomputable def d2fOuterImplRevised
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type}
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M) :
    QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StateT
        (D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (StateT M
          (OptionT
            (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))))) :=
  QueryImpl.addLift (QueryImpl.id oSpec)
    (d2sQueryImplRevised (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (gImpl := gImpl)
      (auxImpl := fun aux =>
        query
          (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
          (Sum.inr aux)))

/-- The lossless Eq. (16) outer implementation.  It is extensionally the same sequence of
oracle calls as `d2fOuterImplRevised`, but an absorbing revised-D2SQuery outcome is returned as a
`D2SRevisedStoppingReason` instead of disappearing through the inner `OptionT`.

The `gImpl` memo state is still threaded in exactly the paper's Item 3 order.  In particular, a
failure of the `gᵢ` implementation is classified at the *current D2S normal state* as
`oracleAbort`; it is not misclassified as a post-occurrence bad event. -/
noncomputable def d2fOuterImplRevisedStopping
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type}
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M) :
    QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StateT
        (D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (StateT M
          (ExceptT
            (D2SRevisedStoppingReason
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
            (OracleComp (oSpec +
              D2SChallengePlusUnitOracle (U := U) challengeSpec))))) := by
  classical
  exact fun
    | .inl q => StateT.lift <| StateT.lift <| ExceptT.lift <|
        query (spec := oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec) (Sum.inl q)
    | .inr q => fun normal => do
      let result ← simulateQ (d2fStoppingD2SInner (T_H := T_H) (T_P := T_P) gImpl normal)
        (d2sQueryStepRevised (T_H := T_H) (T_P := T_P) normal q)
      StateT.mk fun memo => ExceptT.mk (pure (d2sRevisedStepPost normal result memo))

/-- Generic Eq. (16) execution under the revised D2SQuery interpreter, beginning from an
explicit normal D2S state.  This is the state-threadable form used by the revised Figure-4 game:
a successful verifier phase must begin from the successful prover phase's exact trace, tables,
rate-only cache, and cursor state.  The result retains both that successor normal state and the
`gᵢ` memo state; wrappers may discard them only after the source computation has completed. -/
noncomputable def d2fRawRevisedFrom
    {α : Type}
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (comp : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (initialNormal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (initM : M) :
    AbortComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      ((α × D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × M) :=
  (((simulateQ (d2fOuterImplRevised (T_H := T_H) (T_P := T_P) gImpl) comp).run
    initialNormal).run initM)

/-- Generic Eq. (16) execution from the fresh initial D2S state.  This remains the correct
entrypoint for a standalone execution; multi-phase games should instead use
`d2fRawRevisedFrom` to preserve the global D2S simulator state across phases. -/
noncomputable def d2fRawRevised
    {α : Type}
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (comp : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (initM : M) :
    AbortComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      ((α × D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × M) :=
  d2fRawRevisedFrom (T_H := T_H) (T_P := T_P) gImpl comp
    (D2SNormalState.initial (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) initM

/-- The instrumented Eq. (16) execution used by the Hyb₁ lazy-sampling coupling.  It retains all
successful outputs exactly as `d2fRawRevised` does, but reports a structured first stop rather
than erasing it to an `AbortComp` failure.  Its result is therefore the smallest lossless object
from which one can recover the direct D2SQuery base trace, its first monitored-bad prefix, and the
shared `gᵢ` memo-state boundary.

The public hybrid must still project this result through the existing abort-erasing map; proving
that projection preserves its distribution is a separate, local refinement theorem. -/
noncomputable def d2fRawRevisedStoppingFrom
    {α : Type}
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (comp : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (initialNormal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (initM : M) :
    OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (Except
        (D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        ((α × D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × M)) :=
  (((simulateQ (d2fOuterImplRevisedStopping (T_H := T_H) (T_P := T_P) gImpl) comp).run
    initialNormal).run initM).run

/-- Lossless revised Eq. (16) execution from the fresh initial D2S state.  A multi-phase
execution must use `d2fRawRevisedStoppingFrom`: a monitored stop is absorbing, and a successful
second phase must inherit the first phase's exact normal state rather than a fresh one. -/
noncomputable def d2fRawRevisedStopping
    {α : Type}
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (comp : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (initM : M) :
    OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (Except
        (D2SRevisedStoppingReason
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        ((α × D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × M)) :=
  d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P) gImpl comp
    (D2SNormalState.initial (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) initM

/-- A lossless revised D2F execution preserves sequential composition exactly.  If its first
component stops, the second component is not run; otherwise the second component receives the
first component's returned normal state and memo.  This is the algebraic form of the revised
Figure-4 phase discipline and is the phase-fusion bridge used by the stateful Lemma 5.8 proof. -/
theorem d2fRawRevisedStoppingFrom_bind
    {α β : Type}
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (first : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (next : α → OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) β)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (memo : M) :
    d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P) gImpl
      (first >>= next) normal memo =
      d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P) gImpl first normal memo >>=
        fun result =>
          match result with
          | Except.error reason => pure (Except.error reason)
          | Except.ok ((value, normal'), memo') =>
              d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P) gImpl
                (next value) normal' memo' := by
  unfold d2fRawRevisedStoppingFrom
  simp only [simulateQ_bind, StateT.run_bind, ExceptT.run_bind]
  apply bind_congr
  rintro (reason | ⟨⟨value, normal'⟩, memo'⟩) <;> rfl

end RevisedD2F

section RevisedD2SAlgo

variable {ι : Type} {oSpec : OracleSpec ι}
  [Fintype U]
  [∀ i, Fintype (pSpec.Challenge i)]
  [∀ i, DecidableEq (pSpec.Challenge i)]
  {Salt : Type} [SaltCodec U δ Salt]

/-- Revised D2SAlgo Items 1--3: the malicious prover is run through the live stateful,
monitoring D2SQuery bridge.  The public result is identical in shape to `D2FQueryProver`; the
additional state is retained only inside the simulator and proves that every returned execution
ended in a reusable normal state. -/
noncomputable def D2FQueryProverRevised
    (𝒜 : MaliciousProver oSpec pSpec StmtIn U δ) :
    AbortComp (oSpec +
      D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ) :=
  Prod.fst <$> Prod.fst <$>
    (d2fRawRevised (T_H := T_H) (T_P := T_P)
      (gImpl := d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt))
      𝒜 default)

/-- Revised D2SAlgo Items 1--6.  This is the concrete replacement target for the legacy
`d2sAlgo` in the updated Section 5 hybrids: it uses the stateful `Install → append → Monitor`
interpreter while retaining the original memoized codec bridge and salt re-encoding. -/
noncomputable def d2sAlgoRevised
    (𝒜 : MaliciousProver oSpec pSpec StmtIn U δ) :
    AbortComp (oSpec +
      D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StmtIn × FSSaltedProof pSpec Salt) := do
  let ⟨stmt, ⟨salt, messages⟩⟩ ←
    D2FQueryProverRevised (Salt := Salt) (T_H := T_H) (T_P := T_P) 𝒜
  return ⟨stmt, ⟨SaltCodec.encode (Salt := Salt) salt, messages⟩⟩

end RevisedD2SAlgo

/-! ## Whole revised query execution -/

/-- Run a finite list of concrete duplex-sponge oracle requests through the complete revised
Algorithm 5.3 dispatcher.  A `stopped` record or underlying search/parser abort is absorbing:
the suffix is not queried.  This is the executable induction object for the new stopped-run
Lemma 5.8 accounting, while `d2sRevisedOracleRun` remains a smaller post-selection core. -/
noncomputable def d2sQueryRunRevised
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    List (duplexSpongeChallengeOracle StmtIn U).Domain →
      OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
        (D2SRevisedStepResult
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) Unit)
  | [] => pure (.continue () normal)
  | q :: qs => do
      let result ← d2sQueryStepRevised normal q
      match result with
      | .continue _ normal' => d2sQueryRunRevised normal' qs
      | .stopped normal' record => pure (.stopped normal' record)
      | .underlyingAbort => pure .underlyingAbort

@[simp] lemma d2sQueryRunRevised_nil
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    d2sQueryRunRevised normal [] = pure (.continue () normal) := rfl

/-- The single recursive equation used by the first-event proof.  It makes it definitionally
impossible to query a suffix after a stop record or an underlying abort. -/
@[simp] lemma d2sQueryRunRevised_cons
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (qs : List (duplexSpongeChallengeOracle StmtIn U).Domain) :
    d2sQueryRunRevised normal (q :: qs) = (do
      let result ← d2sQueryStepRevised normal q
      match result with
      | .continue _ normal' => d2sQueryRunRevised normal' qs
      | .stopped normal' record => pure (.stopped normal' record)
      | .underlyingAbort => pure .underlyingAbort) := rfl

end DuplexSpongeFS.ProverTransform
