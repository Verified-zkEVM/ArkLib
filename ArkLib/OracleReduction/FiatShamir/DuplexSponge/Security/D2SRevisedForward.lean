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
  [codec : CodecCore pSpec U] {δ : Nat}
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

/-- A revised hash query cannot invoke the programmed `gᵢ` interface.  Its only fresh branch
samples one capacity from the auxiliary unit oracle. -/
lemma d2sQueryStepRevised_hash_isQueryBoundP_g_zero
    [Fintype U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) :
    OracleComp.IsQueryBoundP
      (d2sQueryStepRevised normal (dsHashQuery stmt))
      (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) 0 := by
  rw [d2sQueryStepRevised_hash]
  unfold d2sHandleHashQueryRevised
  split
  · simp
  · change (d2sSampleCapacity (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>=
      fun capacity => pure (d2sHandleHashFreshRevised normal stmt capacity _)).IsQueryBoundP _ 0
    simpa using d2sSampleCapacity_isQueryBoundP_g_zero
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)

/-- A revised inverse-permutation query cannot invoke the programmed `gᵢ` interface.  Its
only fresh branch samples one full state from the auxiliary unit oracle. -/
lemma d2sQueryStepRevised_inverse_isQueryBoundP_g_zero
    [Fintype U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut : CanonicalSpongeState U) :
    OracleComp.IsQueryBoundP
      (d2sQueryStepRevised normal (dsPermInvQuery stateOut))
      (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) 0 := by
  rw [d2sQueryStepRevised_inverse]
  unfold d2sHandleInversePermQueryRevised
  split
  · simp
  · change (d2sSampleState (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) >>=
      fun stateIn => pure (d2sPermResolvedStep normal (.inverse stateOut stateIn))).IsQueryBoundP _ 0
    simpa using d2sSampleState_isQueryBoundP_g_zero
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)

/-- Once the explicit `gᵢ` answer is available, Program parsing/padding and its first
materialization use only auxiliary randomness. -/
lemma d2sHandleBacktrackAfterGRevised_isQueryBoundP_g_zero
    [Fintype U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx)) :
    OracleComp.IsQueryBoundP
      (d2sHandleBacktrackAfterGRevised normal stateIn backtrackOut rhoHat)
      (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) 0 := by
  unfold d2sHandleBacktrackAfterGRevised
  split
  · simp
  · refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
      (d2sRateBlocksFromChallenge_isQueryBoundP_g_zero
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) rhoHat)
      (fun rateBlocks _ => ?_)
    cases hBlocks : rateBlocks.toList with
    | nil => simp
    | cons firstRate remainingRates =>
      simpa [hBlocks] using d2sHandleProgramFirstRateRevised_isQueryBoundP_g_zero
        (normal := normal) (stateIn := stateIn) (firstRate := firstRate)
        (remainingRates := remainingRates)

lemma d2sHandleBacktrackSomeRevised_isQueryBoundP_g_le_one
    [Fintype U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    OracleComp.IsQueryBoundP
      (d2sHandleBacktrackSomeRevised normal stateIn backtrackOut)
      (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) 1 := by
  by_cases hPop : ∃ tail cacheRest,
      popRateOnlyTailByInput normal.state.rateCacheP stateIn = some (tail, cacheRest)
  · obtain ⟨tail, cacheRest, hPop⟩ := hPop
    rw [d2sHandleBacktrackSomeRevised_tail normal stateIn backtrackOut tail cacheRest hPop]
    exact (d2sHandlePoppedRateOnlyTailRevised_isQueryBoundP_g_zero
      (normal := normal) (entry := ⟨stateIn, tail⟩) (cacheRest := cacheRest)).mono (by omega)
  · have hPopNone : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none := by
      cases h : popRateOnlyTailByInput normal.state.rateCacheP stateIn with
      | none => rfl
      | some pair =>
        rcases pair with ⟨tail, cacheRest⟩
        exact False.elim (hPop ⟨tail, cacheRest, h⟩)
    by_cases hImage : d2sInCodecImagePredicate
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut
    · by_cases hNonempty : 0 < challengeSize (pSpec := pSpec) backtrackOut.roundIdx
      · rw [d2sHandleBacktrackSomeRevised_nonemptyChallenge
          normal stateIn backtrackOut hPopNone hImage hNonempty]
        have hG : OracleComp.IsQueryBoundP
            (d2sQueryG (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
              backtrackOut.roundIdx backtrackOut.stmt backtrackOut.salt
              backtrackOut.encodedMessages)
            (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) 1 := by
          unfold d2sQueryG
          apply (OracleComp.isQueryBoundP_query_iff _ _ 1).mpr
          exact fun _ => by omega
        refine OracleComp.isQueryBoundP_bind (n := 1) (m := 0) hG (fun rhoHat _ => ?_)
        · exact d2sHandleBacktrackAfterGRevised_isQueryBoundP_g_zero
            normal stateIn backtrackOut rhoHat
      · rw [d2sHandleBacktrackSomeRevised_emptyChallenge
          normal stateIn backtrackOut hPopNone hImage hNonempty]
        exact (d2sHandleForwardNoResultRevised_isQueryBoundP_g_zero normal stateIn).mono
          (by omega)
    · rw [d2sHandleBacktrackSomeRevised_notInImage
        normal stateIn backtrackOut hPopNone hImage]
      exact (d2sHandleForwardNoResultRevised_isQueryBoundP_g_zero normal stateIn).mono
        (by omega)

/-- The complete revised forward permutation branch can cross the `gᵢ` boundary at most once.
All tail, ordinary, and parser-error paths are `gᵢ`-free; a successful in-image candidate has
one direct `gᵢ` query followed by the zero-cost Program continuation above. -/
lemma d2sQueryStepRevised_forward_isQueryBoundP_g_le_one
    [Fintype U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U) :
    OracleComp.IsQueryBoundP
      (d2sQueryStepRevised normal (dsPermQuery stateIn))
      (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) 1 := by
  rw [d2sQueryStepRevised_forward]
  by_cases hPop : ∃ tail cacheRest,
      popRateOnlyTailByInput normal.state.rateCacheP stateIn = some (tail, cacheRest)
  · obtain ⟨tail, cacheRest, hPop⟩ := hPop
    rw [d2sHandleForwardPermQueryRevised_tail normal stateIn tail cacheRest hPop]
    exact (d2sHandlePoppedRateOnlyTailRevised_isQueryBoundP_g_zero
      (normal := normal) (entry := ⟨stateIn, tail⟩) (cacheRest := cacheRest)).mono (by omega)
  · have hPopNone : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none := by
      cases h : popRateOnlyTailByInput normal.state.rateCacheP stateIn with
      | none => rfl
      | some pair =>
        rcases pair with ⟨tail, cacheRest⟩
        exact False.elim (hPop ⟨tail, cacheRest, h⟩)
    cases hBacktrack : Backtrack.backTrack
        (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        normal.state.trace normal.state.trΔ normal.state.h_inv stateIn
        (normal.state.trace.length + 1) with
    | err =>
      rw [d2sHandleForwardPermQueryRevised_err normal stateIn hPopNone hBacktrack]
      simp
    | noResult =>
      rw [d2sHandleForwardPermQueryRevised_noResult normal stateIn hPopNone hBacktrack]
      exact (d2sHandleForwardNoResultRevised_isQueryBoundP_g_zero normal stateIn).mono
        (by omega)
    | some backtrackOut =>
      rw [d2sHandleForwardPermQueryRevised_some
        normal stateIn backtrackOut hPopNone hBacktrack]
      exact d2sHandleBacktrackSomeRevised_isQueryBoundP_g_le_one normal stateIn backtrackOut

/-- Per-request accounting for the revised dispatcher.  This is the executable version of the
paper fact that only a source forward-permutation request can reach D2SQuery Step 4.e.i, and it
can do so only once. -/
lemma d2sQueryStepRevised_isQueryBoundP_g
    [Fintype U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain) :
    OracleComp.IsQueryBoundP
      (d2sQueryStepRevised normal q)
      (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (if isD2SForwardPermPoint (StmtIn := StmtIn) (U := U) q then 1 else 0) := by
  rcases q with stmt | stateIn | stateOut
  · simpa [isD2SForwardPermPoint] using
      d2sQueryStepRevised_hash_isQueryBoundP_g_zero normal stmt
  · simpa [isD2SForwardPermPoint] using
      d2sQueryStepRevised_forward_isQueryBoundP_g_le_one normal stateIn
  · simpa [isD2SForwardPermPoint] using
      d2sQueryStepRevised_inverse_isQueryBoundP_g_zero normal stateOut

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

/-- The source requests that can reach an Item-4(e)i codec-bridge query in the revised
Eq. (16) executor.  Ambient requests are passed through and hashes/inverses never reach `gᵢ`. -/
def isD2SOuterForwardPermPoint :
    (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain → Prop
  | .inl _ => False
  | .inr q => isD2SForwardPermPoint (StmtIn := StmtIn) (U := U) q

instance : DecidablePred
    (isD2SOuterForwardPermPoint (oSpec := oSpec) (StmtIn := StmtIn) (U := U)) :=
  fun q =>
    match q with
    | .inl _ => isFalse (fun h => h)
    | .inr q => by
        exact (inferInstance : Decidable
          (isD2SForwardPermPoint (StmtIn := StmtIn) (U := U) q))

/-- The standard challenge-table requests among the enlarged target interface. -/
def isD2SOuterChallengePoint {κ : Type} {challengeSpec : OracleSpec κ} :
    (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec).Domain → Prop
  | .inl _ => False
  | .inr (.inl _) => True
  | .inr (.inr _) => False

instance {κ : Type} {challengeSpec : OracleSpec κ} : DecidablePred
    (isD2SOuterChallengePoint (oSpec := oSpec) (U := U) (challengeSpec := challengeSpec)) :=
  fun q =>
    match q with
    | .inl _ => isFalse (fun h => h)
    | .inr (.inl _) => isTrue trivial
    | .inr (.inr _) => isFalse (fun h => h)

/-- Query-bound transport along the right injection of an oracle-spec sum.  Unlike the generic
sub-spec theorem, this structural induction deliberately needs no `IsUniformSpec` instance for
the ambient left summand: no left-summand query is ever introduced by this lift. -/
private theorem isQueryBoundP_liftComp_inr
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {α : Type}
    {p : spec₁.Domain → Prop} [DecidablePred p]
    {q : (spec₂ + spec₁).Domain → Prop} [DecidablePred q]
    (hpq : ∀ t : spec₁.Domain, q (Sum.inr t) ↔ p t)
    {oa : OracleComp spec₁ α} {n : ℕ}
    (hb : OracleComp.IsQueryBoundP oa p n) :
    OracleComp.IsQueryBoundP (liftComp oa (spec₂ + spec₁)) q n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => simp [liftComp]
  | query_bind t mx ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hb
    rw [liftComp_def, simulateQ_query_bind]
    refine (OracleComp.isQueryBoundP_bind
      (n := if p t then 1 else 0)
      (m := if p t then n - 1 else n) ?_ (fun response _ => ?_)).mono ?_
    · show OracleComp.IsQueryBoundP
        (liftM (liftM (OracleSpec.query t) :
          OracleQuery (spec₂ + spec₁) _) : OracleComp (spec₂ + spec₁) _) q
        (if p t then 1 else 0)
      rw [liftM_query_reshape, OracleComp.isQueryBoundP_map_iff,
        OracleComp.isQueryBoundP_query_iff]
      intro hq
      have hpt : p t := (hpq t).mp (by simpa using hq)
      simp [hpt]
    · exact ih response (hb.2 response)
    · by_cases hpt : p t
      · simp only [if_pos hpt]
        rcases hb.1 with hnot | hpositive
        · exact False.elim (hnot hpt)
        · omega
      · simp only [if_neg hpt]
        omega

/-- One revised D2S query preserves the source forward-permutation charge when the internal
`gᵢ` implementation charges at most one standard challenge query per `gᵢ` request. -/
lemma d2sQueryImplRevised_isQueryBoundP_outerChallenge
    {κ : Type} {challengeSpec : OracleSpec κ} {M : Type}
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (hG : ∀ q memo, OracleComp.IsQueryBoundP (((gImpl q).run memo).run)
      (isD2SChallengePoint (U := U) (challengeSpec := challengeSpec)) 1)
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec)
      (StateT M (OptionT
        (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)))))
    (hAux : ∀ q memo, OracleComp.IsQueryBoundP (((auxImpl q).run memo).run)
      (isD2SChallengePoint (U := U) (challengeSpec := challengeSpec)) 0)
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (memo : M) :
    OracleComp.IsQueryBoundP
      ((((d2sQueryImplRevised (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (gImpl := gImpl)
        (auxImpl := auxImpl) q).run
          normal).run memo).run)
      (isD2SChallengePoint (U := U) (challengeSpec := challengeSpec))
      (if isD2SForwardPermPoint (StmtIn := StmtIn) (U := U) q then 1 else 0) := by
  let combinedImpl :
      QueryImpl (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
        (StateT M (OptionT
          (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)))) :=
    gImpl + auxImpl
  have hInner : OracleComp.IsQueryBoundP
      (((simulateQ combinedImpl
        (d2sQueryStepRevised (T_H := T_H) (T_P := T_P) normal q)).run memo).run)
      (isD2SChallengePoint (U := U) (challengeSpec := challengeSpec))
      (if isD2SForwardPermPoint (StmtIn := StmtIn) (U := U) q then 1 else 0) := by
    apply isQueryBoundP_simulateQ_run_StateT_OptionT_of_step
      (d2sQueryStepRevised_isQueryBoundP_g normal q)
    intro point memo
    rcases point with gq | aux
    · simpa [combinedImpl, isD2SQueryGPoint] using hG gq memo
    · simpa [combinedImpl, isD2SQueryGPoint] using hAux aux memo
  unfold d2sQueryImplRevised
  change OracleComp.IsQueryBoundP
    (((do
      let result ← simulateQ (gImpl + auxImpl)
        (d2sQueryStepRevised (T_H := T_H) (T_P := T_P) normal q)
      match result with
      | .continue answer normal' => pure (answer, normal')
      | .stopped _ _ => failure
      | .underlyingAbort => failure :
      StateT M (OptionT
        (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)))
        ((duplexSpongeChallengeOracle StmtIn U).Range q ×
          D2SNormalState (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))).run memo).run)
    (isD2SChallengePoint (U := U) (challengeSpec := challengeSpec))
    (if isD2SForwardPermPoint (StmtIn := StmtIn) (U := U) q then 1 else 0)
  simp only [StateT.run_bind, OptionT.run_bind, Option.elimM]

  change OracleComp.IsQueryBoundP
    (Option.elimM
      (((simulateQ (gImpl + auxImpl)
        (d2sQueryStepRevised (T_H := T_H) (T_P := T_P) normal q)).run memo).run)
      (pure none)
      (fun result =>
        ((match result.1 with
          | .continue answer normal' => pure (answer, normal')
          | .stopped _ _ => failure
          | .underlyingAbort => failure :
          StateT M (OptionT
            (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)))
            ((duplexSpongeChallengeOracle StmtIn U).Range q ×
              D2SNormalState (δ := δ) (T_H := T_H) (T_P := T_P)
                (StmtIn := StmtIn) (pSpec := pSpec) (U := U))).run result.2).run))
    (isD2SChallengePoint (U := U) (challengeSpec := challengeSpec))
    (if isD2SForwardPermPoint (StmtIn := StmtIn) (U := U) q then 1 else 0)
  unfold Option.elimM
  refine (OracleComp.isQueryBoundP_bind
    (n := if isD2SForwardPermPoint (StmtIn := StmtIn) (U := U) q then 1 else 0)
    (m := 0) hInner (fun result _ => ?_)).mono ?_
  · cases result with
    | none => simp
    | some result =>
      rcases result with ⟨step, memo'⟩
      cases step <;> simp
  · omega

/-- The concrete memoized codec bridge instantiates the one-query D2S bound.  A cache hit is
included: it reissues `fᵢ` and therefore still consumes exactly the permitted single charge. -/
lemma d2sQueryImplRevised_memo_isQueryBoundP_challenge
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    {Salt : Type} [SaltCodec U δ Salt]
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec) :
    OracleComp.IsQueryBoundP
      ((((d2sQueryImplRevised (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (gImpl := d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn)
          (pSpec := pSpec) (δ := δ) (Salt := Salt))
        (auxImpl := fun aux => StateT.lift <| query
          (spec := D2SChallengePlusUnitOracle (U := U)
            (fsChallengeOracle (StmtIn × Salt) pSpec))
          (Sum.inr aux)) q).run normal).run memo).run)
      (isD2SChallengePoint (U := U)
        (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec))
      (if isD2SForwardPermPoint (StmtIn := StmtIn) (U := U) q then 1 else 0) := by
  apply d2sQueryImplRevised_isQueryBoundP_outerChallenge
    (gImpl := d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn)
      (pSpec := pSpec) (δ := δ) (Salt := Salt))
  · intro gq memo
    exact d2sCodecBridgeImplMemo_run_isQueryBoundP_challenge_le_one
      (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) (Salt := Salt) gq memo
  · intro aux memo
    change OracleComp.IsQueryBoundP
      (liftM (OracleSpec.query
        (Sum.inr aux : (D2SChallengePlusUnitOracle (U := U)
          (fsChallengeOracle (StmtIn × Salt) pSpec)).Domain) :
        OracleQuery (D2SChallengePlusUnitOracle (U := U)
          (fsChallengeOracle (StmtIn × Salt) pSpec)) _) :
        OracleComp (D2SChallengePlusUnitOracle (U := U)
          (fsChallengeOracle (StmtIn × Salt) pSpec)) _) _ 0
    rw [OracleComp.isQueryBoundP_query_iff]
    simp [isD2SChallengePoint]

/-- A concrete request to the complete revised Eq. (16) outer handler makes at most one standard
challenge query, and only when the original request is a forward permutation request. -/
lemma d2fOuterImplRevised_memo_step_isQueryBoundP_challenge
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    {Salt : Type} [SaltCodec U δ Salt]
    (source : (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec) :
    OracleComp.IsQueryBoundP
      ((((d2fOuterImplRevised (oSpec := oSpec) (δ := δ) (T_H := T_H) (T_P := T_P)
        (gImpl := d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn)
          (pSpec := pSpec) (δ := δ) (Salt := Salt)) source).run normal).run memo).run)
      (isD2SOuterChallengePoint (oSpec := oSpec) (U := U)
        (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec))
      (if isD2SOuterForwardPermPoint (oSpec := oSpec) (StmtIn := StmtIn) (U := U) source
        then 1 else 0) := by
  rcases source with source | source
  · unfold d2fOuterImplRevised
    simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply]
    change OracleComp.IsQueryBoundP
      (liftM (OracleSpec.query (Sum.inl source) :
        OracleQuery (oSpec + D2SChallengePlusUnitOracle (U := U)
          (fsChallengeOracle (StmtIn × Salt) pSpec)) _) :
        OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
          (fsChallengeOracle (StmtIn × Salt) pSpec)) _) _ 0
    rw [OracleComp.isQueryBoundP_query_iff]
    simp [isD2SOuterChallengePoint]
  · have hInner := d2sQueryImplRevised_memo_isQueryBoundP_challenge
      (T_H := T_H) (T_P := T_P) (Salt := Salt) source normal memo
    unfold d2fOuterImplRevised
    simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply]
    simp [MonadLiftT.monadLift, MonadLift.monadLift, StateT.run_monadLift,
      OptionT.run_monadLift]
    change OracleComp.IsQueryBoundP
      (liftComp
        (((d2sQueryImplRevised (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (gImpl := d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn)
            (pSpec := pSpec) (δ := δ) (Salt := Salt))
          (auxImpl := fun aux => StateT.lift <| query
            (spec := D2SChallengePlusUnitOracle (U := U)
              (fsChallengeOracle (StmtIn × Salt) pSpec))
            (Sum.inr aux)) source).run normal).run memo)
        (oSpec + D2SChallengePlusUnitOracle (U := U)
          (fsChallengeOracle (StmtIn × Salt) pSpec)))
      (isD2SOuterChallengePoint (oSpec := oSpec) (U := U)
        (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec))
      (if isD2SForwardPermPoint (StmtIn := StmtIn) (U := U) source then 1 else 0)
    refine isQueryBoundP_liftComp_inr
      (p := isD2SChallengePoint (U := U)
        (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec))
      (q := isD2SOuterChallengePoint (oSpec := oSpec) (U := U)
        (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec))
      (fun point => ?_) hInner
    rcases point with point | point
    · simp [isD2SChallengePoint, isD2SOuterChallengePoint]
    · simp [isD2SChallengePoint, isD2SOuterChallengePoint]

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

/-- The revised D2SAlgo invokes the standard challenge oracle at most once for each source
forward-permutation request.  This is the exact query-budget half of revised Lemma 5.1; ambient
and auxiliary sampling requests are not counted. -/
lemma d2sAlgoRevised_isQueryBoundP_challenge_of_forward
    (𝒜 : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₚ : ℕ)
    (h𝒜 : OracleComp.IsQueryBoundP 𝒜
      (isD2SOuterForwardPermPoint (oSpec := oSpec) (StmtIn := StmtIn) (U := U)) tₚ) :
    OracleComp.IsQueryBoundP
      (d2sAlgoRevised (Salt := Salt) (T_H := T_H) (T_P := T_P) 𝒜)
      (isD2SOuterChallengePoint (oSpec := oSpec) (U := U)
        (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)) tₚ := by
  have hRaw : OracleComp.IsQueryBoundP
      (d2fRawRevised (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
        (gImpl := d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn)
          (pSpec := pSpec) (δ := δ) (Salt := Salt))
        𝒜 default)
      (isD2SOuterChallengePoint (oSpec := oSpec) (U := U)
        (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)) tₚ := by
    unfold d2fRawRevised d2fRawRevisedFrom
    apply isQueryBoundP_simulateQ_run_StateT_StateT_OptionT_of_step h𝒜
    intro source normal memo
    exact d2fOuterImplRevised_memo_step_isQueryBoundP_challenge
      (T_H := T_H) (T_P := T_P) (Salt := Salt) source normal memo
      |>.mono (by
        simp only [isD2SOuterForwardPermPoint]
        split <;> omega)
  change OracleComp.IsQueryBoundP
    (d2sAlgoRevised (Salt := Salt) (T_H := T_H) (T_P := T_P) 𝒜).run
    (isD2SOuterChallengePoint (oSpec := oSpec) (U := U)
      (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)) tₚ
  unfold d2sAlgoRevised D2FQueryProverRevised
  simp only [OptionT.run_bind, OptionT.run_map, OptionT.run_pure, Option.elimM]
  let raw := d2fRawRevised (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
    (gImpl := d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn)
      (pSpec := pSpec) (δ := δ) (Salt := Salt)) 𝒜 default
  have hRawRun : OracleComp.IsQueryBoundP raw.run
      (isD2SOuterChallengePoint (oSpec := oSpec) (U := U)
        (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)) tₚ := hRaw
  have hD2FRun : OracleComp.IsQueryBoundP
      (Option.map Prod.fst <$> Option.map Prod.fst <$> raw.run)
      (isD2SOuterChallengePoint (oSpec := oSpec) (U := U)
        (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)) tₚ := by
    rw [OracleComp.isQueryBoundP_map_iff, OracleComp.isQueryBoundP_map_iff]
    exact hRawRun
  change OracleComp.IsQueryBoundP
    (Option.elimM (Option.map Prod.fst <$> Option.map Prod.fst <$> raw.run)
      (pure none)
      (fun result => pure (some (result.1,
        (SaltCodec.encode (Salt := Salt) result.2.1, result.2.2)))))
    (isD2SOuterChallengePoint (oSpec := oSpec) (U := U)
      (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)) tₚ
  unfold Option.elimM
  refine (OracleComp.isQueryBoundP_bind (n := tₚ) (m := 0) hD2FRun
    (fun result _ => ?_)).mono (by omega)
  cases result <;> simp

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

/-- Number of source forward-permutation requests in a finite concrete D2SQuery request stream.
The runner can stop before reaching the end of the stream, so this is an upper bound rather than
an assertion that every listed request is executed. -/
def d2sForwardRequestCount :
    List (duplexSpongeChallengeOracle StmtIn U).Domain → ℕ
  | [] => 0
  | q :: qs => (if isD2SForwardPermPoint (StmtIn := StmtIn) (U := U) q then 1 else 0) +
      d2sForwardRequestCount qs

/-- The live absorbing runner crosses the programmed `gᵢ` interface at most once per source
forward-permutation request.  This is the finite-run form of the D2SAlgo query-complexity
argument; later transport through the malicious prover only has to account for the source
forward-query budget. -/
lemma d2sQueryRunRevised_isQueryBoundP_g
    [Fintype U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (qs : List (duplexSpongeChallengeOracle StmtIn U).Domain) :
    OracleComp.IsQueryBoundP
      (d2sQueryRunRevised normal qs)
      (isD2SQueryGPoint (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (d2sForwardRequestCount (StmtIn := StmtIn) (U := U) qs) := by
  induction qs generalizing normal with
  | nil => simp [d2sQueryRunRevised, d2sForwardRequestCount]
  | cons q qs ih =>
    rw [d2sQueryRunRevised_cons]
    refine OracleComp.isQueryBoundP_bind
      (d2sQueryStepRevised_isQueryBoundP_g normal q) (fun result _ => ?_)
    exact match result with
      | .continue _ normal' => by
          simpa [d2sForwardRequestCount] using ih normal'
      | .stopped _ _ => by simp
      | .underlyingAbort => by simp

end DuplexSpongeFS.ProverTransform
