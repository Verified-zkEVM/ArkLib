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
  {codec : Codec pSpec U}

local instance : Inhabited U := ⟨0⟩

noncomputable section

section D2SQueryCore

variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [Section52.LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
  [Section52.LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]

/-- CO25 §5.4 — Key for a memoized `gᵢ`-style query used by D2SQuery Item 4(e).

`gᵢ : {0,1}^{≤n} × Σ^δ × Σ^{ℓ_P(1)} × … × Σ^{ℓ_P(i)} → Σ^{ℓ_V(i)}` is the
`i`-th oracle drawn from `𝒟_Σ(λ, n)` (CO25 Equation 15). This key uniquely identifies
one query to `gᵢ` given the challenge-round index `i`, the statement `𝕩`, and the
absorbed rate-block prefix `(ŝ_R^{(0)}, …, ŝ_R^{(L_P(i)-1)})` (§5.4 Item 4(e)i). -/
private structure D2SStdQuery where
  roundIdx : pSpec.ChallengeIdx  -- `i ∈ [k]`: challenge round index (§5.4 Item 4(e))
  stmt : StmtIn                  -- `𝕩 ∈ {0,1}^{≤n}`: statement input (§5.4 Item 3)
  absorbedRatePrefix : List (Vector U SpongeSize.R)  -- `Σ^{ℓ_P(ι)}` prefix blocks for `gᵢ` input

/-- CO25 §5.4 — Memo entry for one memoized `gᵢ`-query-answer pair (§5.4 Item 4(e)i).

Stores the pair `((i, 𝕩, τ̂, α̂_1, …, α̂_i), ρ̂_i)` where `ρ̂_i ∈ Σ^{ℓ_V(i)}` is the
cached response of the `gᵢ` oracle for consistency across repeated D2SQuery calls. -/
private structure D2SStdEntry where
  query : D2SStdQuery (StmtIn := StmtIn) (pSpec := pSpec) (U := U)  -- `gᵢ` query key
  responseRateBlocks : List (Vector U SpongeSize.R)  -- `ρ̂_i` encoded as rate blocks `∈ Σ^r`

/-- CO25 §5.4 Item 1 — Internal mutable state of the `D2SQuery` oracle wrapper.

`D2SQuery` is initialized with the following state (§5.4 Item 1):
- `trace` (`tr`): ordered list of query-answer pairs for `h` and `p`, stored as tuples
  `('h', 𝕩, s_{C,out})` for hash queries and `('p', s_in, s_out)` / `('p⁻¹', s_out, s_in)`
  for permutation queries, ordered by query time of the adversary (§5.4 Item 1, bullet 1).
- `cacheP` (`Cache_p`): list of `(s_in, s_out) ∈ Σ^{r+c} × Σ^{r+c}` pairs sorted
  lexicographically by input (§5.4 Item 1, bullet 2); consumed by Item 4(c)i.
- `trΔ` (`tr_∇`): deduplicated index over `trace` supporting `inlu`/`outlu` lookups
  in `O(log N)` — CO25 Definition 5.2 / §5.1. Built lazily alongside `trace` (§5.4 Item 1,
  bullet 3): each D2SQuery branch checks `tr_∇` first and only calls `.add` on a miss.
- `stdMemo`: memoization table for `gᵢ`-style query-answer pairs (§5.4 Item 4(e)i);
  not explicitly named in the paper but required for consistency of repeated `gᵢ` queries. -/
structure D2SQueryState where
  -- `tr`: ordered `('h', 𝕩, s_C)` / `('p', s_in, s_out)` / `('p⁻¹', …)` pairs (§5.4 Item 1)
  trace : QueryLog (duplexSpongeChallengeOracle StmtIn U) := []
  -- `Cache_p`: `(s_in, s_out) ∈ Σ^{r+c} × Σ^{r+c}` sorted by input (§5.4 Item 1, bullet 2)
  cacheP : List (CanonicalSpongeState U × CanonicalSpongeState U) := []
  -- memoized `gᵢ` query-answer pairs for consistency (§5.4 Item 4(e)i)
  stdMemo : List (D2SStdEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := []
  -- `tr_∇`: deduplicated index for `O(log N)` `inlu`/`outlu` lookups (CO25 Def. 5.2, §5.1)
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

/-- CO25 §5.4 — Paper-facing `gᵢ = ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹` codec bridge for `D2SQuery`.

Bundles the two functions needed by D2SQuery Items 4(d)/(e):
- `inCodecImage`: implements the `∀ ι ∈ [i], α̂_ι ∈ Im(φ_ι)` branch predicate
  (CO25 §5.4 Items 4(d) vs 4(e) split — abort vs call `gᵢ`).
- `evalGI`: computes `ρ̂_i := gᵢ(𝕩, τ̂, α̂_1, …, α̂_i)` for the valid branch (§5.4 Item 4(e)i),
  where `gᵢ = ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹` with `φᵢ` the prover-message encoder and `ψᵢ` the
  verifier-message encoder from the Codec (CO25 §5.2). -/
structure D2SCodecBridge where
  /-- `∀ ι ∈ [i], α̂_ι ∈ Im(φ_ι)` branch predicate (§5.4 Item 4(d) vs 4(e) split). -/
  inCodecImage :
    BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U) → Bool := fun _ => true
  /-- `gᵢ(𝕩, τ̂, α̂_1, …, α̂_i) = ψᵢ⁻¹(fᵢ(𝕩, τ̌, φᵢ⁻¹(α̂_1), …, φᵢ⁻¹(α̂_i)))` (§5.4 Item 4(e)i). -/
  evalGI :
    (i : pSpec.ChallengeIdx) →
      StmtIn →
        List (Vector U SpongeSize.R) →
          OptionT (OracleComp (Unit →ₒ U))
            (Vector U (challengeSize (pSpec := pSpec) i))

/-- CO25 §5.4 — Core parameters for the (paper-shaped) `D2SQuery` implementation.

`codecBridge` provides the `ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹` / codec-image interface for Items 4(d)/(e).
`forwardExtensionLength` controls how many additional `(s_in, s_out)` permutation links from
the `ρ̂_i`-derived chain are appended to `Cache_p` after a valid backtrack hit (§5.4 Item 4(e)iiiD:
pairs `(s_R^{(0)}, s_C^{(0)}), …, (s_R^{(L_V(i)-2)}, s_C^{(L_V(i)-2)})` added to `Cache_p`). -/
structure D2SQueryParams where
  -- `D2SCodecBridge` supplying the `φ⁻¹`/`ψ⁻¹` codec interface (§5.4 Items 4(d)/(e))
  codecBridge :
    D2SCodecBridge (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)
  -- number of extra `Cache_p` pairs to synthesize per valid backtrack hit (§5.4 Item 4(e)iiiD)
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

/-- CO25 §5.4 — One-step dispatch for the `D2SQuery` oracle wrapper.

Handles a single query `q` to `(h, p, p⁻¹)` by dispatching on its variant:
- `.inl stmt` (query to `h`): §5.4 Item 2 — lookup `tr_∇.h.inlu(𝕩)`, sample `s_{C,out} ← 𝒰(Σ^c)`
  on miss, call `tr_∇.h.add`, always append `('h', 𝕩, s_{C,out})` to `tr`.
- `.inr (.inr stateOut)` (query to `p⁻¹`): §5.4 Item 3 — lookup `tr_∇.p.outlu(s_out)`, sample
  `s_in ← 𝒰(Σ^{r+c})` on miss, call `tr_∇.p.add`, append `('p⁻¹', s_out, s_in)` to `tr`.
- `.inr (.inl stateIn)` (query to `p`): §5.4 Item 4 — call `BackTrack(tr, tr_∇, s_in)` and branch:
  - `err` → abort (§5.4 Item 4(b));
  - `none` → consult `Cache_p`, then `tr_∇.p.inlu`, then fresh sample (§5.4 Item 4(c));
  - `some (i, 𝕩, τ̂, α̂_1, …, α̂_i)` with `∃ ι, α̂_ι ∉ Im(φ_ι)` → fallback path (§5.4 Item 4(d));
  - `some (i, 𝕩, τ̂, α̂_1, …, α̂_i)` with `∀ ι, α̂_ι ∈ Im(φ_ι)` → call `gᵢ`, build
    `Cache_p` chain from `ρ̂_i ‖ z` rate-segments, set `s_out` (§5.4 Item 4(e)).
Returns `none` (abort) or `some resp` with updated `D2SQueryState`. -/
def d2sQueryStep
    (params : D2SQueryParams
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec))
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

/-- CO25 §5.4 — `QueryImpl` form of the `D2SQuery` oracle wrapper core.

Lifts `d2sQueryStep` into a `QueryImpl` so it can be passed to `simulateQ`. Each call
dispatches one query `q` to `(h, p, p⁻¹)` following the §5.4 Items 2–4 control flow
and threads the mutable `D2SQueryState` via `StateT`. -/
def d2sQueryImplCore
    (params : D2SQueryParams
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
        (OptionT (OracleComp (Unit →ₒ U)))) :=
  fun q => d2sQueryStep params q

/-- CO25 §5.4 — Execute the `D2SQuery` oracle-wrapper semantics on a DS oracle computation.

Runs `comp` under the `D2SQuery` simulation starting from an empty `D2SQueryState`.
Returns `none` when `D2SQuery` aborts (the `err` branch, §5.4 Item 4(b)), or
`some (result, finalState)` on success. -/
def runD2SQueryCore
    (params : D2SQueryParams
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec))
    {α : Type}
    (comp : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) :
    OptionT (OracleComp (Unit →ₒ U))
      (α × D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) :=
  (simulateQ
    (d2sQueryImplCore params)
    comp).run default

/-- CO25 §5.4 — Uniform `ProbComp` implementation of the auxiliary `U`-sampling oracle.

Provides the concrete `𝒰(Σ)` random-sampling semantics used by `d2sQueryStep` for the
fresh-sample branches (§5.4 Items 2(b), 3(b), 4(c)iii, 4(e)iiiC). Bridge point when
interpreting §5.4 simulator steps in `ProbComp`. -/
def d2sUnitSampleImpl [SampleableType U] :
    QueryImpl (Unit →ₒ U) ProbComp :=
  fun
  | () => by
      change ProbComp U
      exact $ᵗ U

/-- CO25 §5.4 — Run one `d2sQueryStep` in `ProbComp` with a concrete unit-sampling oracle.

Takes `unitImpl : QueryImpl (Unit →ₒ U) ProbComp` (e.g. `d2sUnitSampleImpl`) and resolves
the `OracleComp (Unit →ₒ U)` monad stack inside `d2sQueryStep` into `ProbComp`.
Returns `none` on abort (§5.4 `err` branch) or `some (resp, newState)` on success. -/
def runD2SQueryStepWithUnitImpl
    (unitImpl : QueryImpl (Unit →ₒ U) ProbComp)
    (params : D2SQueryParams
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) :
    ProbComp
      (Option
        ((duplexSpongeChallengeOracle StmtIn U).Range q ×
          D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))) :=
  simulateQ unitImpl
    (((d2sQueryStep
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) params q).run st).run)

/-- CO25 §5.4 — Default abort fallback for `d2sQueryStep` in `ProbComp`.

When `d2sQueryStep` returns `none` (the §5.4 `err` branch, Item 4(b)), this fallback
totalizes the computation by returning `(default, st)` — preserving the current state
and answering with a type-default response. Used as `onAbort` in `d2sQueryImplCoreProb`. -/
def d2sQueryAbortFallback
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) :
    (duplexSpongeChallengeOracle StmtIn U).Range q ×
      D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) :=
  (default, st)

/-- CO25 §5.4 — `ProbComp` adapter for the `D2SQuery` simulator core.

Converts `d2sQueryStep` (monad stack: `StateT D2SQueryState (OptionT (OracleComp (Unit →ₒ U)))`)
into a `QueryImpl … (StateT D2SQueryState ProbComp)` by:
1. resolving the `Unit →ₒ U` sampling oracle via `unitImpl` (uniform `𝒰(Σ)` sampling);
2. totalizing `err`-aborts via `onAbort` (defaults to `d2sQueryAbortFallback`).
This is the main entry point for constructing the §5.4 D2SAlgo prover-transform in `ProbComp`. -/
def d2sQueryImplCoreProb
    (unitImpl : QueryImpl (Unit →ₒ U) ProbComp)
    (params : D2SQueryParams
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec))
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

/-- CO25 §5.4 — Uniform-sampling `ProbComp` instantiation of the `D2SQuery` core.

Specializes `d2sQueryImplCoreProb` with `d2sUnitSampleImpl` as the uniform `𝒰(Σ)` oracle,
giving the canonical §5.4 D2SQuery semantics where all fresh samples are drawn uniformly. -/
def d2sQueryImplCoreUniform
    [SampleableType U]
    (params : D2SQueryParams
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)) :
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
            (codec := codec)
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
      (codec := codec)
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
    D2SCodecBridge
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec) :=
  { inCodecImage := defaultInCodecImageApprox
      (codec := codec)
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    evalGI := fun i _stmt _absorbedRatePrefix =>
      OptionT.lift <| sampleVector (U := U) (challengeSize (pSpec := pSpec) i) }

private def defaultD2SQueryParams :
    D2SQueryParams
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec) :=
  { codecBridge :=
      defaultD2SCodecBridge
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)
    forwardExtensionLength := fun out =>
      match challengeIdxOfBacktrackOutput
          (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) out with
      | some roundIdx => (pSpec.Lᵥᵢ roundIdx).pred
      | none => 0 }

/-- CO25 §5.4 — Parametric `D2SQuery` simulation bridge with explicit codec interface.

Lifts `d2sQueryImplCore` into the larger oracle `fsPlusUnitOracle` target monad,
enabling the D2SQuery simulation to run within computations that also make queries to
`fsChallengeOracle StmtIn pSpec` (the standard Fiat-Shamir challenge oracle) alongside
the auxiliary `Unit →ₒ U` sampling oracle. Parametrized by `D2SQueryParams` to allow
different `φ⁻¹`/`ψ⁻¹` codec bridges (§5.4, CO25 Equation 16). -/
def duplexSpongeToBasicFSQueryImplWithParams
    (params : D2SQueryParams
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)) :
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
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)
      params)

/-- CO25 §5.4 — Default `D2SQuery` simulation: duplex-sponge oracles → basic Fiat-Shamir oracles.

Uses `defaultD2SQueryParams` (uniform `evalGI`, `defaultInCodecImageApprox` branch predicate,
forward extension length `L_V(i) - 1`). Composed with a duplex-sponge malicious prover `𝒜`
to obtain the basic Fiat-Shamir malicious prover `D2SAlgo(𝒜)` from CO25 §5.4 (Equation 16). -/
def duplexSpongeToBasicFSQueryImpl :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
        (OptionT
          (OracleComp (fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) ) :=
  duplexSpongeToBasicFSQueryImplWithParams
    (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)
    (defaultD2SQueryParams
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec))

/-- CO25 §5.4 — Canonical alias for `duplexSpongeToBasicFSQueryImpl`. -/
abbrev d2SQueryImpl :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
        (OptionT
          (OracleComp (fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) ) :=
  duplexSpongeToBasicFSQueryImpl
    (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)

/-- CO25 §5.4 — `D2SAlgo^f`: parametric duplex-sponge → basic Fiat-Shamir prover transform.

Implements the D2SAlgo construction (CO25 §5.4, Equation 16):
`D2SAlgo^f(𝒜) := 𝒜^{D2SQuery^{ψ⁻¹ ∘ f ∘ φ⁻¹}}`

Given a malicious prover `P` against the duplex-sponge Fiat-Shamir oracle `𝒟_{DS}(λ, n)`, runs
`P` under the `D2SQuery` simulation (controlled by `params`) to obtain a malicious prover against
the standard Fiat-Shamir oracle `𝒟_{IP}(λ, n)`. Returns `none` when D2SQuery aborts. The output
oracle family is `oSpec + fsChallengeOracle + Unit →ₒ U` (CO25 §5.4, Equation 17 time bound). -/
def duplexSpongeToBasicFSAlgoWithParams
    (params : D2SQueryParams
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec))
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
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)
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

/-- CO25 §5.4 — Default `D2SAlgo`: duplex-sponge → basic Fiat-Shamir prover transform.

Specializes `duplexSpongeToBasicFSAlgoWithParams` with `defaultD2SQueryParams`:
- `inCodecImage` via `defaultInCodecImageApprox` (Serialize-image approximation of `Im(φ)`),
- `evalGI` via uniform sampling `𝒰(Σ^{ℓ_V(i)})` (i.e. `gᵢ ← 𝒟_Σ(λ, n)`),
- `forwardExtensionLength = L_V(i) - 1` (fills `Cache_p` chain, §5.4 Item 4(e)iiiD).
This is the canonical D2SAlgo instance used throughout the CO25 §5 security analysis. -/
def duplexSpongeToBasicFSAlgo
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
    (StmtIn × pSpec.Messages)) :
    OracleComp (oSpec + fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (Option (StmtIn × pSpec.Messages)) :=
  duplexSpongeToBasicFSAlgoWithParams
    (T_H := T_H) (T_P := T_P)
    (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)
    (defaultD2SQueryParams
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec))
    P

/-- CO25 §5.4 — Canonical alias for `duplexSpongeToBasicFSAlgo`. -/
abbrev d2SAlgo
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    OracleComp (oSpec + fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (Option (StmtIn × pSpec.Messages)) :=
  duplexSpongeToBasicFSAlgo
    (T_H := T_H) (T_P := T_P)
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec) P

end D2SAlgoBridge

section D2SQueryWithOracle

variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [Section52.LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
  [Section52.LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- CO25 §5.4 — External challenge-oracle family augmented with the auxiliary sampling oracles.

`D2SChallengePlusUnitOracle challengeSpec` is `challengeSpec + (Unit →ₒ U) + unifSpec`:
the sum of the caller-supplied challenge oracle `gᵢ`-family, the auxiliary unit-sampling
oracle `𝒰(Σ)` used by D2SQuery fresh-sample branches (§5.4 Items 2(b), 3(b), 4(c)iii, 4(e)iiiC),
and `unifSpec` for any additional uniform randomness. -/
abbrev D2SChallengePlusUnitOracle {κ : Type} (challengeSpec : OracleSpec κ) :=
  challengeSpec + ((Unit →ₒ U) + unifSpec)

/-- CO25 §5.4 — `D2SCodecBridge` variant with access to an external challenge-oracle family.

Same structure as `D2SCodecBridge` but `evalGI` is allowed to query `challengeSpec` (the
caller-supplied `gᵢ`-family oracle) in addition to the auxiliary `Unit →ₒ U` sampling oracle.
This is the oracle-aware version used when D2SQuery is embedded inside a larger computation
that already has access to challenge oracles `f_i : {0,1}^{≤n} × … → ℳ_{V,i}`. -/
structure D2SCodecBridgeWithOracle {κ : Type} (challengeSpec : OracleSpec κ) where
  /-- `∀ ι ∈ [i], α̂_ι ∈ Im(φ_ι)` branch predicate (§5.4 Item 4(d) vs 4(e) split). -/
  inCodecImage :
    BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U) → Bool := fun _ => true
  /-- `gᵢ = ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹` via oracle query to `challengeSpec` (§5.4 Item 4(e)i). -/
  evalGI :
    (i : pSpec.ChallengeIdx) →
      StmtIn →
        List (Vector U SpongeSize.R) →
          OptionT
            (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec))
            (Vector U (challengeSize (pSpec := pSpec) i))

/-- CO25 §5.4 — `D2SQueryParams` variant with access to an external challenge-oracle family.

Oracle-aware counterpart to `D2SQueryParams`: uses `D2SCodecBridgeWithOracle` so that
the `evalGI` branch can make oracle queries to `challengeSpec` (e.g. `fᵢ`) when computing
the `gᵢ = ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹` response in §5.4 Item 4(e)i. -/
structure D2SQueryParamsWithOracle {κ : Type} (challengeSpec : OracleSpec κ) where
  -- `D2SCodecBridgeWithOracle` with oracle-access `evalGI` (§5.4 Item 4(e)i)
  codecBridge :
    D2SCodecBridgeWithOracle
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec) challengeSpec
  -- number of extra `Cache_p` pairs synthesized per valid backtrack hit (§5.4 Item 4(e)iiiD)
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

/-- CO25 §5.4 — One-step dispatch for `D2SQuery` with an explicit external challenge-oracle family.

Oracle-aware variant of `d2sQueryStep`: same §5.4 Items 2–4 control flow but `evalGI` can
query `challengeSpec` (the `gᵢ`-family oracle) via `D2SChallengePlusUnitOracle`. Used when
D2SQuery is embedded in a larger computation that already holds the `fᵢ` oracles. -/
def d2sQueryStepWithOracle
    {κ : Type} {challengeSpec : OracleSpec κ}
    (params :
      D2SQueryParamsWithOracle
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec) challengeSpec)
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

/-- CO25 §5.4 — `QueryImpl` form of `d2sQueryStepWithOracle`.

Lifts `d2sQueryStepWithOracle` into a `QueryImpl` that can be passed to `simulateQ`,
enabling the §5.4 D2SQuery simulation under an explicit external challenge-oracle family
`challengeSpec` (carrying the `gᵢ`-family oracle `f_i`). -/
def d2sQueryImplCoreWithOracle
    {κ : Type} {challengeSpec : OracleSpec κ}
    (params :
      D2SQueryParamsWithOracle
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec) challengeSpec) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
        (OptionT
          (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)))) :=
  fun q => d2sQueryStepWithOracle params q

/-- CO25 §5.4 — Default `D2SQueryParamsWithOracle` with caller-supplied `evalGI` oracle bridge.

Constructs `D2SQueryParamsWithOracle` using:
- `inCodecImage := defaultInCodecImageApprox` (Serialize-image approximation of `Im(φ_ι)`),
- `evalGI` := caller-supplied oracle bridge to `challengeSpec` (e.g. querying `fᵢ` directly),
- `forwardExtensionLength = L_V(i) - 1` (fills `Cache_p` chain, §5.4 Item 4(e)iiiD). -/
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
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec) challengeSpec :=
  { codecBridge :=
      { inCodecImage := defaultInCodecImageApprox
          (codec := codec)
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
