/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Backtrack
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lookahead
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceDataStructures
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceTransform

/-!
# Prover transformation

This file contains the prover transformation (via query simulation) for the analysis of duplex
sponge Fiat-Shamir, following Section 5.4 in the paper.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [HasChallengeSize pSpec]

local instance : Inhabited U := ⟨0⟩

noncomputable section

section D2SQueryCore

variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [Section52.LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
  [Section52.LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]

/-- Paper-facing key for `gᵢ`-style memoized queries in D2SQuery Item 4(e)i. -/
private structure D2SStdQuery where
  roundIdx : pSpec.ChallengeIdx
  stmt : StmtIn
  absorbedRatePrefix : List (Vector U SpongeSize.R)

/-- Memo entry for one `gᵢ`-style query-answer pair. -/
private structure D2SStdEntry where
  query : D2SStdQuery (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  responseRateBlocks : List (Vector U SpongeSize.R)

/-- Internal mutable state of the Section 5.4 `D2SQuery` oracle wrapper.

`trΔ` is the paper's `tr_∇` (CO25 Definition 5.2): a deduplicated index over `trace` that supports
`inlu`/`outlu` lookups in `O(log N)` (or `O(1)`) once the default `ListTraceTable` is later swapped
for an `RBMap`/`HashMap`-backed instance. It mirrors the lazy "build alongside `tr`" pattern of
the paper's `D2SQuery` (Section 5.4): each branch checks `tr_∇` first and only `add`s on a miss. -/
structure D2SQueryState where
  trace : QueryLog (duplexSpongeChallengeOracle StmtIn U) := []
  cacheP : List (CanonicalSpongeState U × CanonicalSpongeState U) := []
  stdMemo : List (D2SStdEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := []
  trΔ : Section52.TraceNabla T_H T_P StmtIn U :=
    ⟨Section52.TraceTableOps.empty, Section52.TraceTableOps.empty⟩

instance : Inhabited (D2SQueryState
    (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) :=
  ⟨{}⟩

/-- Forward-permutation projection `tr.p` of a DS trace. -/
private def forwardPermTraceOfDS
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (forwardPermutationOracle (CanonicalSpongeState U)) :=
  trace.filterMap fun entry =>
    match entry with
    | ⟨.inr (.inl stateIn), stateOut⟩ => some ⟨stateIn, stateOut⟩
    | _ => none

/-- Recover the challenge-round index (if any) from a `BackTrack` output. -/
private def challengeIdxOfBacktrackOutput
    (out : BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U)) :
    Option pSpec.ChallengeIdx := by
  if hRound : out.round.1 < n then
    let roundFin : Fin n := ⟨out.round.1, hRound⟩
    if hDir : pSpec.dir roundFin = Direction.V_to_P then
      exact some ⟨roundFin, hDir⟩
    else
      exact none
  else
    exact none

/-- Lookup of a prior `gᵢ`-style answer for the same key (Item 4(e)i consistency). -/
private def lookupStdMemo
    (memo : List (D2SStdEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
    (q : D2SStdQuery (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Option (List (Vector U SpongeSize.R)) := by
  classical
  exact memo.findSome? fun entry =>
    if hEq : entry.query = q then
      some entry.responseRateBlocks
    else
      none

/-- Insert a fresh `gᵢ`-style answer in memo order. -/
private def insertStdMemo
    (memo : List (D2SStdEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
    (q : D2SStdQuery (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (responseRateBlocks : List (Vector U SpongeSize.R)) :
    List (D2SStdEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  memo ++ [{ query := q, responseRateBlocks := responseRateBlocks }]

/-- Paper-facing `ψ⁻¹ ∘ f ∘ φ⁻¹` bridge used by `D2SQuery` Item 4(e)i. -/
structure D2SCodecBridge where
  /-- Codec-image predicate for BackTrack outputs (Item 4(d)/(e) branch split). -/
  inCodecImage :
    BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U) → Bool := fun _ => true
  /-- Evaluation of `gᵢ = ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹` on encoded tuple keys. -/
  evalGI :
    (i : pSpec.ChallengeIdx) →
      StmtIn →
        List (Vector U SpongeSize.R) →
          OptionT (OracleComp (Unit →ₒ U))
            (Vector U (challengeSize (pSpec := pSpec) i))

/-- Core parameters for a simplified (but paper-shaped) `D2SQuery` implementation.

`codecBridge` provides the explicit `ψ⁻¹ ∘ f ∘ φ⁻¹` / codec-image interface for Item 4(d)/(e),
and `forwardExtensionLength` controls how many additional permutation links are memoized in
`cacheP` after a valid backtrack hit (Item 4(e)iiiD). -/
structure D2SQueryParams where
  codecBridge : D2SCodecBridge (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
  forwardExtensionLength :
    BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U) → Nat := fun _ => 0

private def popCacheByInput
    (cache : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (stateIn : CanonicalSpongeState U) :
    Option (CanonicalSpongeState U × List (CanonicalSpongeState U × CanonicalSpongeState U)) := by
  classical
  induction cache with
  | nil =>
      exact none
  | cons pair rest ih =>
      let (qIn, qOut) := pair
      by_cases hEq : qIn = stateIn
      · exact some (qOut, rest)
      · match ih with
        | none => exact none
        | some (qOut', rest') => exact some (qOut', pair :: rest')

private def sampleArrayExact :
    (m : Nat) → OracleComp (Unit →ₒ U) {xs : Array U // xs.size = m}
  | 0 => pure ⟨#[], rfl⟩
  | m + 1 => do
      let u ← query (spec := (Unit →ₒ U)) ()
      let ⟨xs, hxs⟩ ← sampleArrayExact m
      pure ⟨xs.push u, by simp [hxs]⟩

private def sampleVector (m : Nat) : OracleComp (Unit →ₒ U) (Vector U m) := do
  let ⟨xs, hxs⟩ ← sampleArrayExact (U := U) m
  pure ⟨xs, hxs⟩

private def sampleCapacity : OracleComp (Unit →ₒ U) (Vector U SpongeSize.C) :=
  sampleVector (U := U) SpongeSize.C

private def sampleCapacityList : Nat → OracleComp (Unit →ₒ U) (List (Vector U SpongeSize.C))
  | 0 => pure []
  | m + 1 => do
      let head ← sampleCapacity (U := U)
      let tail ← sampleCapacityList m
      pure (head :: tail)

private def sampleState : OracleComp (Unit →ₒ U) (CanonicalSpongeState U) :=
  sampleVector (U := U) SpongeSize.N

private def sampleStateList : Nat → OracleComp (Unit →ₒ U) (List (CanonicalSpongeState U))
  | 0 => pure []
  | m + 1 => do
      let head ← sampleState (U := U)
      let tail ← sampleStateList m
      pure (head :: tail)

private def chainPairsFrom
    (start : CanonicalSpongeState U)
    (rest : List (CanonicalSpongeState U)) :
    List (CanonicalSpongeState U × CanonicalSpongeState U) :=
  match rest with
  | [] => []
  | next :: tail => (start, next) :: chainPairsFrom next tail

private def mkStateFromSegments
    (rateSeg : Vector U SpongeSize.R)
    (capSeg : Vector U SpongeSize.C) :
    CanonicalSpongeState U :=
  (Vector.append rateSeg capSeg).cast (by
    simp [SpongeSize.R_plus_C_eq_N])

private def rateBlocksFromUnitsM :
    Nat → List U → OracleComp (Unit →ₒ U) (List (Vector U SpongeSize.R))
  | 0, _ => pure []
  | m + 1, units => do
      let headUnits := units.take SpongeSize.R
      let restUnits := units.drop SpongeSize.R
      let block ←
        if hFull : headUnits.length = SpongeSize.R then
          pure <|
            Vector.ofFn (fun j => headUnits.get ⟨j.1, by simpa [hFull] using j.2⟩)
        else do
          let padLen := SpongeSize.R - headUnits.length
          let pad ← sampleVector (U := U) padLen
          let blockList := headUnits ++ pad.toList
          have hTake : headUnits.length ≤ SpongeSize.R := by
            simpa [headUnits] using List.length_take_le SpongeSize.R units
          have hLen : blockList.length = SpongeSize.R := by
            simp [blockList, padLen, Nat.add_sub_of_le hTake]
          pure <|
            Vector.ofFn (fun j => blockList.get ⟨j.1, by simpa [hLen] using j.2⟩)
      let tail ← rateBlocksFromUnitsM m restUnits
      pure (block :: tail)

private def rateBlocksFromChallengeM
    {i : pSpec.ChallengeIdx}
    (challenge : Vector U (challengeSize i)) :
    OracleComp (Unit →ₒ U) (List (Vector U SpongeSize.R)) :=
  rateBlocksFromUnitsM (U := U) (pSpec.Lᵥᵢ i) challenge.toList

/-- Simplified but paper-shaped `D2SQuery` step function (Section 5.4).

The function preserves the key control flow:
- `backTrack = err` aborts,
- `backTrack = none` follows cache/trace/random fallback,
- `backTrack = some` branches by validity and can extend `cacheP`. -/
def d2sQueryStep
    (params : D2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain) :
    StateT (D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
      (OptionT (OracleComp (Unit →ₒ U)))
      ((duplexSpongeChallengeOracle StmtIn U).Range q) := do
  let st ← get
  match q with
  | .inl stmt =>
      -- Paper Item 2 (CO25 §5.4, line 1039): `tr_∇.h.inlu(𝕩)`; on `⟂`, sample and
      -- `tr_∇.h.add(𝕩, s_C,out)` (line 1041); always append to `tr` (line 1043).
      let (capOut, trΔ') ←
        match Section52.TraceTableOps.inlu st.trΔ.h stmt with
        | some capSeg => pure (capSeg, st.trΔ)
        | none =>
            let sampled ← StateT.lift <| OptionT.lift <| sampleCapacity (U := U)
            pure (sampled,
              { st.trΔ with h := Section52.TraceTableOps.add st.trΔ.h stmt sampled })
      let trace' := st.trace ++ [⟨.inl stmt, capOut⟩]
      set { st with trace := trace', trΔ := trΔ' }
      return capOut
  | .inr (.inr stateOut) =>
      -- Paper Item 3 (line 1044): `tr_∇.p.outlu(s_out)`; on `⟂`, sample and
      -- `tr_∇.p.add(s_in, s_out)` (line 1046); always append `(p⁻¹, s_out, s_in)` to `tr`.
      let (stateIn, trΔ') ←
        match Section52.TraceTableOps.outlu st.trΔ.p stateOut with
        | some recovered => pure (recovered, st.trΔ)
        | none =>
            let sampled ← StateT.lift <| OptionT.lift <| sampleState (U := U)
            pure (sampled,
              { st.trΔ with p := Section52.TraceTableOps.add st.trΔ.p sampled stateOut })
      let trace' := st.trace ++ [⟨.inr (.inr stateOut), stateIn⟩]
      set { st with trace := trace', trΔ := trΔ' }
      return stateIn
  | .inr (.inl stateIn) =>
      match
          (backTrack
            (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
            st.trΔ (st.trace.length + 1) stateIn).run with
      | none =>
          -- `err` branch: abort.
          StateT.lift failure
      | some none =>
          -- `none` branch: cache, then `tr_∇.p.inlu`, then fresh sampling.
          -- Paper Item 4(c) (line 1052). Cache hit / fresh sample both extend `tr_∇.p`.
          let (stateOut, cache', stdMemo', trΔ') ←
            match popCacheByInput (U := U) st.cacheP stateIn with
            | some (cachedOut, cacheTail) =>
                -- Cache extras from a prior `some` branch were not in `tr_∇.p`; record now.
                let trΔ' :=
                  { st.trΔ with p := Section52.TraceTableOps.add st.trΔ.p stateIn cachedOut }
                pure (cachedOut, cacheTail, st.stdMemo, trΔ')
            | none =>
                match Section52.TraceTableOps.inlu st.trΔ.p stateIn with
                | some recovered => pure (recovered, st.cacheP, st.stdMemo, st.trΔ)
                | none =>
                    let sampledOut ← StateT.lift <| OptionT.lift <| sampleState (U := U)
                    let trΔ' :=
                      { st.trΔ with p :=
                          Section52.TraceTableOps.add st.trΔ.p stateIn sampledOut }
                    pure (sampledOut, st.cacheP, st.stdMemo, trΔ')
          let trace' := st.trace ++ [⟨.inr (.inl stateIn), stateOut⟩]
          set { st with trace := trace', cacheP := cache', stdMemo := stdMemo', trΔ := trΔ' }
          return stateOut
      | some (some backtrackOut) =>
          -- `some` branch: valid tuple path evaluates `gᵢ` before `tr_∇.p.inlu` fallback.
          -- Paper Item 4(d)/(e) (lines 1056-1071). Only the head of the synthesized chain is
          -- `tr_∇.p.add`-ed; cache extras stay in `cacheP` until consumed (line 1070).
          let (stateOut, cache', stdMemo', trΔ') ←
            if params.codecBridge.inCodecImage backtrackOut then
              match challengeIdxOfBacktrackOutput
                  (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) backtrackOut with
              | some roundIdx =>
                  let stdQuery :
                      D2SStdQuery (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
                    { roundIdx := roundIdx
                      stmt := backtrackOut.stmt
                      absorbedRatePrefix := backtrackOut.absorbedRatePrefix }
                  let (rateBlocks, stdMemo') ←
                    match lookupStdMemo
                        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                        st.stdMemo stdQuery with
                    | some cachedRateBlocks =>
                        pure (cachedRateBlocks, st.stdMemo)
                    | none =>
                        let sampledRhoHat ←
                          StateT.lift <|
                            params.codecBridge.evalGI
                              roundIdx backtrackOut.stmt backtrackOut.absorbedRatePrefix
                        let sampledRateBlocks ←
                          StateT.lift <|
                            OptionT.lift <|
                              rateBlocksFromChallengeM
                                (pSpec := pSpec) (U := U) sampledRhoHat
                        let stdMemo' :=
                          insertStdMemo
                            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                            st.stdMemo stdQuery sampledRateBlocks
                        pure (sampledRateBlocks, stdMemo')
                  match Section52.TraceTableOps.inlu st.trΔ.p stateIn with
                  | some recovered =>
                      pure (recovered, st.cacheP, stdMemo', st.trΔ)
                  | none =>
                      let firstRate : Vector U SpongeSize.R :=
                        rateBlocks.headD (Vector.replicate SpongeSize.R default)
                      let sampledCap ←
                        StateT.lift <| OptionT.lift <| sampleCapacity (U := U)
                      let synthesizedOut :=
                        mkStateFromSegments (U := U) firstRate sampledCap
                      let tailRatesAll := rateBlocks.drop 1
                      let extensionLen :=
                        Nat.min (params.forwardExtensionLength backtrackOut)
                          tailRatesAll.length
                      let tailRates := tailRatesAll.take extensionLen
                      let caps ←
                        StateT.lift <|
                          OptionT.lift <| sampleCapacityList (U := U) tailRates.length
                      let extraStates :=
                        (tailRates.zip caps).map fun rc =>
                          mkStateFromSegments (U := U) rc.1 rc.2
                      let extraPairs :=
                        chainPairsFrom (U := U) synthesizedOut extraStates
                      let trΔ' :=
                        { st.trΔ with p :=
                            Section52.TraceTableOps.add st.trΔ.p stateIn synthesizedOut }
                      pure (synthesizedOut, st.cacheP ++ extraPairs, stdMemo', trΔ')
              | none =>
                  match Section52.TraceTableOps.inlu st.trΔ.p stateIn with
                  | some recovered => pure (recovered, st.cacheP, st.stdMemo, st.trΔ)
                  | none =>
                      let sampledOut ← StateT.lift <| OptionT.lift <| sampleState (U := U)
                      let trΔ' :=
                        { st.trΔ with p :=
                            Section52.TraceTableOps.add st.trΔ.p stateIn sampledOut }
                      pure (sampledOut, st.cacheP, st.stdMemo, trΔ')
            else
              match Section52.TraceTableOps.inlu st.trΔ.p stateIn with
              | some recovered => pure (recovered, st.cacheP, st.stdMemo, st.trΔ)
              | none =>
                  let sampledOut ← StateT.lift <| OptionT.lift <| sampleState (U := U)
                  let trΔ' :=
                    { st.trΔ with p :=
                        Section52.TraceTableOps.add st.trΔ.p stateIn sampledOut }
                  pure (sampledOut, st.cacheP, st.stdMemo, trΔ')
          let trace' := st.trace ++ [⟨.inr (.inl stateIn), stateOut⟩]
          set { st with trace := trace', cacheP := cache', stdMemo := stdMemo', trΔ := trΔ' }
          return stateOut

/-- Query implementation form of the `D2SQuery` core procedure. -/
def d2sQueryImplCore
    (params : D2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
        (OptionT (OracleComp (Unit →ₒ U)))) :=
  fun q => d2sQueryStep params q

/-- Execute the Section 5.4 query-wrapper semantics on a DS oracle computation.

`none` denotes abort (the `err` branch in the paper). -/
def runD2SQueryCore
    (params : D2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
    {α : Type}
    (comp : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) :
    OptionT (OracleComp (Unit →ₒ U))
      (α × D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) :=
  (simulateQ
    (d2sQueryImplCore params)
    comp).run default

/--
Uniform implementation of the auxiliary unit-sampling oracle used by `d2sQueryStep`.

This is the bridge point when interpreting Section 5.4 simulator steps in `ProbComp`.
-/
def d2sUnitSampleImpl [SampleableType U] :
    QueryImpl (Unit →ₒ U) ProbComp :=
  fun
  | () => by
      change ProbComp U
      exact $ᵗ U

/--
Run one `d2sQueryStep` in `ProbComp` by providing a concrete implementation of the
auxiliary unit-sampling oracle.
-/
def runD2SQueryStepWithUnitImpl
    (unitImpl : QueryImpl (Unit →ₒ U) ProbComp)
    (params : D2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) :
    ProbComp
      (Option
        ((duplexSpongeChallengeOracle StmtIn U).Range q ×
          D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))) :=
  simulateQ unitImpl
    (((d2sQueryStep
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) params q).run st).run)

/--
Default totalization fallback for `d2sQueryStep` aborts when interpreted in `ProbComp`.

It preserves the input state and returns a default response.
-/
def d2sQueryAbortFallback
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) :
    (duplexSpongeChallengeOracle StmtIn U).Range q ×
      D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) :=
  (default, st)

/--
`ProbComp` adapter for the Section 5.4 simulator core.

This turns `d2sQueryStep` (which runs in `StateT ... (OptionT (OracleComp (Unit →ₒ U)))`)
into a concrete `QueryImpl ... (StateT ... ProbComp)` by:
1. interpreting the unit-sampling oracle via `unitImpl`;
2. totalizing aborts with `onAbort`.
-/
def d2sQueryImplCoreProb
    (unitImpl : QueryImpl (Unit →ₒ U) ProbComp)
    (params : D2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
    (onAbort :
      (q : (duplexSpongeChallengeOracle StmtIn U).Domain) →
        D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) →
          (duplexSpongeChallengeOracle StmtIn U).Range q ×
            D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) :=
      d2sQueryAbortFallback
        (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
        ProbComp) :=
  fun q => do
    let st ← get
    let out? ←
      StateT.lift <|
        runD2SQueryStepWithUnitImpl
          (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
          unitImpl params q st
    match out? with
    | some (resp, st') =>
        set st'
        pure resp
    | none =>
        let (resp, st') := onAbort q st
        set st'
        pure resp

/--
Uniform-sampling instantiation of `d2sQueryImplCoreProb`.
-/
def d2sQueryImplCoreUniform
    [SampleableType U]
    (params : D2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
        ProbComp) :=
  d2sQueryImplCoreProb
    (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    (unitImpl := d2sUnitSampleImpl (U := U))
    params

end D2SQueryCore

section D2SAlgoBridge

variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [Section52.LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
  [Section52.LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
  [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

private abbrev fsPlusUnitOracle :=
  (fsChallengeOracle StmtIn pSpec) + (Unit →ₒ U)

/-- Executable approximation of Item 4(d)/(e) tuple-image branching, tightened with
`BackTrack`-shape checks and challenge-block length sanity. -/
private def messageInSerializeImage
    (msgIdx : pSpec.MessageIdx)
    (encoded : Vector U (messageSize msgIdx)) : Bool := by
  classical
  exact decide (∃ msg : pSpec.Message msgIdx, Serialize.serialize msg = encoded)

/-- Paper-facing witness that the `BackTrack` output has the tuple shape needed by Item 4(d)/(e),
including successful recovery of the Section 5.8 `φ⁻¹` message prefix. -/
private structure PaperCodecImageWitness where
  roundIdx : pSpec.ChallengeIdx
  messagesUpTo : pSpec.MessagesUpTo roundIdx.1.castSucc

/-- Exact paper-facing branch data used by the Section 5.8 Item 4(d)/(e) split.

This is the semantic side of the branch: `BackTrack` produced a challenge round, the recovered
prefix is long enough, and the paper's `φ⁻¹` parser succeeded on the absorbed-rate prefix. -/
private noncomputable def paperCodecImageWitness?
    (out : BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U)) :
    Option (PaperCodecImageWitness (pSpec := pSpec)) := do
  match challengeIdxOfBacktrackOutput
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) out with
  | none => none
  | some roundIdx =>
      if _hShape :
          BacktrackOutput.paperShapeValidb
            (StmtIn := StmtIn) (n := n) (U := U) out &&
          decide (pSpec.Lᵥᵢ roundIdx ≤ out.absorbedRatePrefix.length) then
        match section58AbsorbedPrefixMessagesUpTo?
            (pSpec := pSpec) (U := U) roundIdx out.absorbedRatePrefix with
        | some messagesUpTo =>
            some { roundIdx := roundIdx, messagesUpTo := messagesUpTo }
        | none => none
      else
        none

/-- Executable approximation of Item 4(d)/(e) tuple-image branching.

This sits strictly on top of `paperCodecImageWitness?`: after the paper-facing tuple recovery
succeeds, we additionally approximate the paper's `α̂ ∈ Im(φ)` side condition via explicit
`Serialize`-image checks on the recovered encoded messages. -/
private def defaultInCodecImageApprox
    (out : BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U)) : Bool :=
  let parseParams : BacktrackParseParams := {}
  match paperCodecImageWitness?
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) out with
  | none => false
  | some witness =>
      backtrackOutputMessagesInImage
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        parseParams witness.roundIdx
        (messageInSerializeImage (pSpec := pSpec) (U := U))
        out

/-- Executable default for Item 4(d)/(e) branching.

This is intentionally layered:
- `paperCodecImageWitness?` names the paper-facing semantic branch data, and
- `defaultInCodecImageApprox` adds the current executable `Serialize`-image approximation.

It still defers full paper parser recovery of all tuple components to the abstract
`D2SCodecBridge` surface.

TODO: state and prove the exact relationship between `paperCodecImageWitness?` and the paper's
Item 4(d)/(e) branch predicate. At the moment, `defaultInCodecImageApprox` should be read only as
the executable approximation used by the default simulator, not as a proved equivalent
formalization of the paper condition. -/
private def defaultD2SCodecBridge :
    D2SCodecBridge (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) :=
  { inCodecImage := defaultInCodecImageApprox
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    evalGI := fun i _stmt _absorbedRatePrefix =>
      OptionT.lift <| sampleVector (U := U) (challengeSize (pSpec := pSpec) i) }

private def defaultD2SQueryParams :
    D2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) :=
  { codecBridge :=
      defaultD2SCodecBridge (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    forwardExtensionLength := fun out =>
      match challengeIdxOfBacktrackOutput
          (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) out with
      | some roundIdx => (pSpec.Lᵥᵢ roundIdx).pred
      | none => 0 }

/-- Parametric query simulation bridge (Section 5.4) with explicit codec interface. -/
def duplexSpongeToBasicFSQueryImplWithParams
    (params : D2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
        (OptionT
          (OracleComp (fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) ) :=
  QueryImpl.liftTarget
    (StateT (D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
      (OptionT
        (OracleComp (fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))))
    (d2sQueryImplCore
      (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      params)

/-- The query simulation between duplex sponge oracles and basic Fiat-Shamir oracles. This is then
  composed with the duplex-sponge malicious prover to obtain a basic F-S malicious prover -/
def duplexSpongeToBasicFSQueryImpl :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
        (OptionT
          (OracleComp (fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) ) :=
  duplexSpongeToBasicFSQueryImplWithParams
    (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    (defaultD2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))

abbrev d2SQueryImpl :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
        (OptionT
          (OracleComp (fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) ) :=
  duplexSpongeToBasicFSQueryImpl

/-- The transformation of a duplex-sponge Fiat-Shamir malicious prover to a basic Fiat-Shamir one.

Note: this transformation needs to be an oracle computation itself -/
def duplexSpongeToBasicFSAlgoWithParams
    (params : D2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
    (StmtIn × pSpec.Messages)) :
    OracleComp (oSpec + fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (Option (StmtIn × pSpec.Messages)) :=
  let d2sOuterImpl :
      QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (StateT (D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
          (OptionT
            (OracleComp
              (oSpec + fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))))) :=
    QueryImpl.addLift
      (r := StateT (D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
        (OptionT
          (OracleComp
            (oSpec + fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))))
      (QueryImpl.id oSpec)
      (duplexSpongeToBasicFSQueryImplWithParams
        (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        params)
  let outWithState :
      OptionT
        (OracleComp
          (oSpec + fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
        ((StmtIn × pSpec.Messages) ×
          D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) :=
    (simulateQ d2sOuterImpl P).run default
  do
    let out? ← outWithState.run
    pure (out?.map Prod.fst)

/-- Default D2S malicious-prover transform used across Section 5, with the default codec bridge. -/
def duplexSpongeToBasicFSAlgo
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
    (StmtIn × pSpec.Messages)) :
    OracleComp (oSpec + fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (Option (StmtIn × pSpec.Messages)) :=
  duplexSpongeToBasicFSAlgoWithParams
    (T_H := T_H) (T_P := T_P)
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    (defaultD2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
    P

abbrev d2SAlgo
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    OracleComp (oSpec + fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (Option (StmtIn × pSpec.Messages)) :=
  duplexSpongeToBasicFSAlgo
    (T_H := T_H) (T_P := T_P)
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) P

end D2SAlgoBridge

section D2SQueryWithOracle

variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [Section52.LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
  [Section52.LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
  [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- External challenge-oracle family augmented with the auxiliary unit-sampling oracle used by the
Section 5.4 simulator. -/
abbrev D2SChallengePlusUnitOracle {κ : Type} (challengeSpec : OracleSpec κ) :=
  challengeSpec + ((Unit →ₒ U) + unifSpec)

/-- `D2SQuery` codec bridge with explicit access to an external challenge-oracle family. -/
structure D2SCodecBridgeWithOracle {κ : Type} (challengeSpec : OracleSpec κ) where
  /-- Codec-image predicate for BackTrack outputs (Item 4(d)/(e) branch split). -/
  inCodecImage :
    BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U) → Bool := fun _ => true
  /-- Evaluation of `gᵢ = ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹` on encoded tuple keys. -/
  evalGI :
    (i : pSpec.ChallengeIdx) →
      StmtIn →
        List (Vector U SpongeSize.R) →
          OptionT
            (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec))
            (Vector U (challengeSize (pSpec := pSpec) i))

/-- Section 5.4 simulator parameters with explicit access to an external challenge-oracle family. -/
structure D2SQueryParamsWithOracle {κ : Type} (challengeSpec : OracleSpec κ) where
  codecBridge :
    D2SCodecBridgeWithOracle
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) challengeSpec
  forwardExtensionLength :
    BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U) → Nat := fun _ => 0

private def sampleArrayExactWithOracle
    {κ : Type} (challengeSpec : OracleSpec κ) :
    (m : Nat) →
      OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)
        {xs : Array U // xs.size = m}
  | 0 => pure ⟨#[], rfl⟩
  | m + 1 => do
      let u ← query
        (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
        (Sum.inr (.inl ()))
      let ⟨xs, hxs⟩ ← sampleArrayExactWithOracle challengeSpec m
      pure ⟨xs.push u, by simp [hxs]⟩

private def sampleVectorWithOracle
    {κ : Type} (challengeSpec : OracleSpec κ)
    (m : Nat) :
    OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec) (Vector U m) := do
  let ⟨xs, hxs⟩ ← sampleArrayExactWithOracle (U := U) challengeSpec m
  pure ⟨xs, hxs⟩

private def sampleCapacityWithOracle
    {κ : Type} (challengeSpec : OracleSpec κ) :
    OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (Vector U SpongeSize.C) :=
  sampleVectorWithOracle (U := U) challengeSpec SpongeSize.C

private def sampleCapacityListWithOracle
    {κ : Type} (challengeSpec : OracleSpec κ) :
    Nat →
      OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)
        (List (Vector U SpongeSize.C))
  | 0 => pure []
  | m + 1 => do
      let head ← sampleCapacityWithOracle (U := U) challengeSpec
      let tail ← sampleCapacityListWithOracle challengeSpec m
      pure (head :: tail)

private def sampleStateWithOracle
    {κ : Type} (challengeSpec : OracleSpec κ) :
    OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (CanonicalSpongeState U) :=
  sampleVectorWithOracle (U := U) challengeSpec SpongeSize.N

private def rateBlocksFromUnitsMWithOracle
    {κ : Type} (challengeSpec : OracleSpec κ) :
    Nat → List U →
      OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)
        (List (Vector U SpongeSize.R))
  | 0, _ => pure []
  | m + 1, units => do
      let headUnits := units.take SpongeSize.R
      let restUnits := units.drop SpongeSize.R
      let block ←
        if hFull : headUnits.length = SpongeSize.R then
          pure <|
            Vector.ofFn (fun j => headUnits.get ⟨j.1, by
              rw [hFull]
              exact j.2⟩)
        else do
          let padLen := SpongeSize.R - headUnits.length
          let pad ← sampleVectorWithOracle (U := U) challengeSpec padLen
          let blockList := headUnits ++ pad.toList
          have hTake : headUnits.length ≤ SpongeSize.R := by
            dsimp [headUnits]
            exact List.length_take_le SpongeSize.R units
          have hLen : blockList.length = SpongeSize.R := by
            simp [blockList, padLen, Nat.add_sub_of_le hTake]
          pure <|
            Vector.ofFn (fun j => blockList.get ⟨j.1, by
              rw [hLen]
              exact j.2⟩)
      let tail ← rateBlocksFromUnitsMWithOracle challengeSpec m restUnits
      pure (block :: tail)

private def rateBlocksFromChallengeMWithOracle
    {κ : Type} (challengeSpec : OracleSpec κ)
    {i : pSpec.ChallengeIdx}
    (challenge : Vector U (challengeSize i)) :
    OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (List (Vector U SpongeSize.R)) :=
  rateBlocksFromUnitsMWithOracle
    (U := U) challengeSpec (pSpec.Lᵥᵢ i) challenge.toList

/-- Section 5.4 `D2SQuery` step with an explicit external challenge-oracle family. -/
def d2sQueryStepWithOracle
    {κ : Type} {challengeSpec : OracleSpec κ}
    (params :
      D2SQueryParamsWithOracle
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) challengeSpec)
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain) :
    StateT (D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
      (OptionT
        (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)))
      ((duplexSpongeChallengeOracle StmtIn U).Range q) := do
  let st ← get
  match q with
  | .inl stmt =>
      -- Paper Item 2 (CO25 §5.4, line 1039): `tr_∇.h.inlu(𝕩)`; on `⟂`, sample and
      -- `tr_∇.h.add(𝕩, s_C,out)` (line 1041); always append to `tr` (line 1043).
      let (capOut, trΔ') ←
        match Section52.TraceTableOps.inlu st.trΔ.h stmt with
        | some capSeg => pure (capSeg, st.trΔ)
        | none =>
            let sampled ←
              StateT.lift <|
                OptionT.lift <| sampleCapacityWithOracle (U := U) challengeSpec
            pure (sampled,
              { st.trΔ with h := Section52.TraceTableOps.add st.trΔ.h stmt sampled })
      let trace' := st.trace ++ [⟨.inl stmt, capOut⟩]
      set { st with trace := trace', trΔ := trΔ' }
      return capOut
  | .inr (.inr stateOut) =>
      -- Paper Item 3 (line 1044): `tr_∇.p.outlu(s_out)`; on `⟂`, sample and
      -- `tr_∇.p.add(s_in, s_out)` (line 1046); always append `(p⁻¹, s_out, s_in)` to `tr`.
      let (stateIn, trΔ') ←
        match Section52.TraceTableOps.outlu st.trΔ.p stateOut with
        | some recovered => pure (recovered, st.trΔ)
        | none =>
            let sampled ←
              StateT.lift <|
                OptionT.lift <| sampleStateWithOracle (U := U) challengeSpec
            pure (sampled,
              { st.trΔ with p := Section52.TraceTableOps.add st.trΔ.p sampled stateOut })
      let trace' := st.trace ++ [⟨.inr (.inr stateOut), stateIn⟩]
      set { st with trace := trace', trΔ := trΔ' }
      return stateIn
  | .inr (.inl stateIn) =>
      match
          (backTrack
            (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
            st.trΔ (st.trace.length + 1) stateIn).run with
      | none =>
          StateT.lift failure
      | some none =>
          -- Paper Item 4(c) (line 1052). Cache hit / fresh sample both extend `tr_∇.p`.
          let (stateOut, cache', stdMemo', trΔ') ←
            match popCacheByInput (U := U) st.cacheP stateIn with
            | some (cachedOut, cacheTail) =>
                let trΔ' :=
                  { st.trΔ with p := Section52.TraceTableOps.add st.trΔ.p stateIn cachedOut }
                pure (cachedOut, cacheTail, st.stdMemo, trΔ')
            | none =>
                match Section52.TraceTableOps.inlu st.trΔ.p stateIn with
                | some recovered => pure (recovered, st.cacheP, st.stdMemo, st.trΔ)
                | none =>
                    let sampledOut ←
                      StateT.lift <|
                        OptionT.lift <| sampleStateWithOracle (U := U) challengeSpec
                    let trΔ' :=
                      { st.trΔ with p :=
                          Section52.TraceTableOps.add st.trΔ.p stateIn sampledOut }
                    pure (sampledOut, st.cacheP, st.stdMemo, trΔ')
          let trace' := st.trace ++ [⟨.inr (.inl stateIn), stateOut⟩]
          set { st with trace := trace', cacheP := cache', stdMemo := stdMemo', trΔ := trΔ' }
          return stateOut
      | some (some backtrackOut) =>
          -- Paper Item 4(d)/(e) (lines 1056-1071). Only the head of the synthesized chain is
          -- `tr_∇.p.add`-ed; cache extras stay in `cacheP` until consumed (line 1070).
          let (stateOut, cache', stdMemo', trΔ') ←
            if params.codecBridge.inCodecImage backtrackOut then
              match challengeIdxOfBacktrackOutput
                  (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) backtrackOut with
              | some roundIdx =>
                  let stdQuery :
                      D2SStdQuery (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
                    { roundIdx := roundIdx
                      stmt := backtrackOut.stmt
                      absorbedRatePrefix := backtrackOut.absorbedRatePrefix }
                  let (rateBlocks, stdMemo') ←
                    match lookupStdMemo
                        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                        st.stdMemo stdQuery with
                    | some cachedRateBlocks =>
                        pure (cachedRateBlocks, st.stdMemo)
                    | none =>
                        let sampledRhoHat ←
                          StateT.lift <|
                            params.codecBridge.evalGI
                              roundIdx backtrackOut.stmt backtrackOut.absorbedRatePrefix
                        let sampledRateBlocks ←
                          StateT.lift <|
                            OptionT.lift <|
                              rateBlocksFromChallengeMWithOracle
                                (pSpec := pSpec) (U := U) challengeSpec sampledRhoHat
                        let stdMemo' :=
                          insertStdMemo
                            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                            st.stdMemo stdQuery sampledRateBlocks
                        pure (sampledRateBlocks, stdMemo')
                  match Section52.TraceTableOps.inlu st.trΔ.p stateIn with
                  | some recovered =>
                      pure (recovered, st.cacheP, stdMemo', st.trΔ)
                  | none =>
                      let firstRate : Vector U SpongeSize.R :=
                        rateBlocks.headD (Vector.replicate SpongeSize.R default)
                      let sampledCap ←
                        StateT.lift <|
                          OptionT.lift <|
                            sampleCapacityWithOracle (U := U) challengeSpec
                      let synthesizedOut :=
                        mkStateFromSegments (U := U) firstRate sampledCap
                      let tailRatesAll := rateBlocks.drop 1
                      let extensionLen :=
                        Nat.min (params.forwardExtensionLength backtrackOut)
                          tailRatesAll.length
                      let tailRates := tailRatesAll.take extensionLen
                      let caps ←
                        StateT.lift <|
                          OptionT.lift <|
                            sampleCapacityListWithOracle (U := U) challengeSpec tailRates.length
                      let extraStates :=
                        (tailRates.zip caps).map fun rc =>
                          mkStateFromSegments (U := U) rc.1 rc.2
                      let extraPairs :=
                        chainPairsFrom (U := U) synthesizedOut extraStates
                      let trΔ' :=
                        { st.trΔ with p :=
                            Section52.TraceTableOps.add st.trΔ.p stateIn synthesizedOut }
                      pure (synthesizedOut, st.cacheP ++ extraPairs, stdMemo', trΔ')
              | none =>
                  match Section52.TraceTableOps.inlu st.trΔ.p stateIn with
                  | some recovered => pure (recovered, st.cacheP, st.stdMemo, st.trΔ)
                  | none =>
                      let sampledOut ←
                        StateT.lift <|
                          OptionT.lift <| sampleStateWithOracle (U := U) challengeSpec
                      let trΔ' :=
                        { st.trΔ with p :=
                            Section52.TraceTableOps.add st.trΔ.p stateIn sampledOut }
                      pure (sampledOut, st.cacheP, st.stdMemo, trΔ')
            else
              match Section52.TraceTableOps.inlu st.trΔ.p stateIn with
              | some recovered => pure (recovered, st.cacheP, st.stdMemo, st.trΔ)
              | none =>
                  let sampledOut ←
                    StateT.lift <|
                      OptionT.lift <| sampleStateWithOracle (U := U) challengeSpec
                  let trΔ' :=
                    { st.trΔ with p :=
                        Section52.TraceTableOps.add st.trΔ.p stateIn sampledOut }
                  pure (sampledOut, st.cacheP, st.stdMemo, trΔ')
          let trace' := st.trace ++ [⟨.inr (.inl stateIn), stateOut⟩]
          set { st with trace := trace', cacheP := cache', stdMemo := stdMemo', trΔ := trΔ' }
          return stateOut

/-- Query implementation form of the Section 5.4 simulator with an explicit external
challenge-oracle family. -/
def d2sQueryImplCoreWithOracle
    {κ : Type} {challengeSpec : OracleSpec κ}
    (params :
      D2SQueryParamsWithOracle
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) challengeSpec) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
        (OptionT
          (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)))) :=
  fun q => d2sQueryStepWithOracle params q

/-- Default `BackTrack`-shape checks and cache-extension length, paired with a caller-supplied
external `evalGI` oracle bridge. -/
def defaultD2SQueryParamsWithOracle
    {κ : Type} {challengeSpec : OracleSpec κ}
    (evalGI :
      (i : pSpec.ChallengeIdx) →
        StmtIn →
          List (Vector U SpongeSize.R) →
            OptionT
              (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec))
              (Vector U (challengeSize (pSpec := pSpec) i))) :
    D2SQueryParamsWithOracle
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) challengeSpec :=
  { codecBridge :=
      { inCodecImage := defaultInCodecImageApprox
          (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        evalGI := evalGI }
    forwardExtensionLength := fun out =>
      match challengeIdxOfBacktrackOutput
          (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) out with
      | some roundIdx => (pSpec.Lᵥᵢ roundIdx).pred
      | none => 0 }

end D2SQueryWithOracle

end

end DuplexSpongeFS
