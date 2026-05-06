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

namespace DuplexSpongeFS.ProverTransform

open Backtrack Lookahead DSTraceStorage TraceTransform

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  {codec : Codec pSpec U}
  {δ : Nat}

local instance : Inhabited U := ⟨0⟩

noncomputable section

section D2SQueryCore

-- `D2SQueryState` takes many named type parameters; long lines are unavoidable in signatures.
set_option linter.style.longLine false

variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
  [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- CO25 §5.4 — Key for a memoized `gᵢ`-style query used by D2SQuery Item 4(e).

`gᵢ : {0,1}^{≤n} × Σ^δ × Σ^{ℓ_P(1)} × … × Σ^{ℓ_P(i)} → Σ^{ℓ_V(i)}` is the
`i`-th oracle drawn from `𝒟_Σ(λ, n)` (CO25 Equation 15). This key uniquely identifies
one query to `gᵢ` given the challenge-round index `i`, the statement `𝕩`, the salt `τ`, and the
encoded prover-message tuple `(α̂_1, …, α̂_i)` (§5.4 Item 4(e)i).

Field types match `BacktrackOutput` (paper-strict shape) — `salt : Vector U δ` and
`encodedMessages : pSpec.EncodedMessagesUpTo U roundIdx.1.castSucc`; conversion to lossy lists
happens only at codec/oracle boundaries when needed. -/
-- TODO(section5-cleanup): this key shape duplicates TraceTransform.StdTraceQuery. The response
-- payloads differ, so do not merge now; reassess after BadEvents.lean and Section 5 proof surfaces
-- stabilize.
private abbrev D2SStdQuery :=
  BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)

/-- CO25 §5.4 — Memo entry for one memoized `gᵢ`-query-answer pair (§5.4 Item 4(e)i).

Stores the pair `((i, 𝕩, τ̂, α̂_1, …, α̂_i), ρ̂_i)` where `ρ̂_i ∈ Σ^{ℓ_V(i)}` is the
cached response of the `gᵢ` oracle for consistency across repeated D2SQuery calls. -/
-- TODO(section5-cleanup): parallel to TraceTransform.StdTraceEntry but stores rate blocks instead
-- of a deserialized challenge vector. Consider a shared key plus two response wrappers later.
private structure D2SStdEntry where
  query : D2SStdQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)
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
  stdMemo :
    List (D2SStdEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) := []
  -- `tr_∇`: deduplicated index for `O(log N)` `inlu`/`outlu` lookups (CO25 Def. 5.2, §5.1)
  trΔ : TraceNabla T_H T_P StmtIn U :=
    ⟨TraceTableOps.empty, TraceTableOps.empty⟩

instance : Inhabited (D2SQueryState
    (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) :=
  ⟨{}⟩

/-- Lookup of a prior `gᵢ`-style answer for the same key (Item 4(e)i consistency). -/
private def lookupStdMemo
    (memo :
      List (D2SStdEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)))
    (q : D2SStdQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) :
    Option (List (Vector U SpongeSize.R)) := by
  classical
  exact memo.findSome? fun entry =>
    if hEq : entry.query = q then
      some entry.responseRateBlocks
    else
      none

/-- Insert a fresh `gᵢ`-style answer in memo order. -/
private def insertStdMemo
    (memo :
      List (D2SStdEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)))
    (q : D2SStdQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
    (responseRateBlocks : List (Vector U SpongeSize.R)) :
    List (D2SStdEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) :=
  memo ++ [{ query := q, responseRateBlocks := responseRateBlocks }]

/-- Executable approximation of Item 4(d)/(e) tuple-image branching, tightened with
`BackTrack`-shape checks and challenge-block length sanity. -/
private def messageInSerializeImage
    (msgIdx : pSpec.MessageIdx)
    (encoded : Vector U (messageSize msgIdx)) : Bool := by
  classical
  exact decide (∃ msg : pSpec.Message msgIdx, Serialize.serialize msg = encoded)

/-- CO25 §5.4 Items 4(d)/(e) — paper predicate `∀ ι ∈ [i], α̂_ι ∈ Im(φ_ι)`.

Implements the executable approximation of the paper branch predicate (CO25 §5.4 Item 4(d) vs
4(e) split, lines 1056/1059): given a `BackTrack` output, returns `true` iff the recovered tuple
satisfies the codec-image side condition. Since `BackTrack` now returns the paper tuple directly,
this is just the `Serialize`-image check on the recovered encoded messages.

This is the **paper-derived** predicate used directly inside `d2sQueryStep`; it is no longer a
free field of `D2SCodecBridge`, removing the prior under-constrained shape (D5 in
`audit-report.md`). -/
private noncomputable def paperInCodecImagePredicate
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Bool :=
  backtrackOutputMessagesInImage
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
    (messageInSerializeImage (pSpec := pSpec) (U := U))
    out

/-- CO25 §5.4 Item 4(e)iiiD — paper-derived `Cache_p` extension length.

The paper requires appending exactly `L_V(i) - 1` pairs to `Cache_p` after a valid backtrack
hit (CO25 §5.4 lines 1064–1068). Returns that count given a `BackTrack` output; returns `0`
when the round index is unrecoverable (the simulator falls through to the non-tuple branch).

Replaces the prior free `forwardExtensionLength` field of `D2SQueryParams` (D5 in
`audit-report.md`). -/
private def paperForwardExtensionLength
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Nat :=
  (pSpec.Lᵥᵢ out.roundIdx).pred

/-- CO25 §5.4 — Paper-facing `gᵢ = ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹` codec bridge for `D2SQuery`.

Bundles the function needed by D2SQuery Item 4(e)i:
- `evalGI`: computes `ρ̂_i := gᵢ(𝕩, τ̂, α̂_1, …, α̂_i)` for the valid branch (§5.4 Item 4(e)i),
  where `gᵢ = ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹` with `φᵢ` the prover-message encoder and `ψᵢ` the
  verifier-message encoder from the Codec (CO25 §5.2).

The Item 4(d) vs 4(e) branch predicate `∀ ι ∈ [i], α̂_ι ∈ Im(φ_ι)` is **not** a free field —
the simulator uses the paper-derived `paperInCodecImagePredicate` directly (CO25 §5.4 lines
1056/1059). See D5 in `audit-report.md`. -/
structure D2SCodecBridge where
  /-- `gᵢ(𝕩, τ̂, α̂_1, …, α̂_i) = ψᵢ⁻¹(fᵢ(𝕩, τ̌, φᵢ⁻¹(α̂_1), …, φᵢ⁻¹(α̂_i)))` (§5.4 Item 4(e)i).

  Paper-strict argument shape: `salt : Vector U δ` and
  `encodedMessages : pSpec.EncodedMessagesUpTo U i.1.castSucc` matching `BacktrackOutput`. -/
  evalGI :
    (i : pSpec.ChallengeIdx) →
      StmtIn →
        Vector U δ →
          pSpec.EncodedMessagesUpTo U i.1.castSucc →
            OptionT (OracleComp (Unit →ₒ U))
              (Vector U (challengeSize (pSpec := pSpec) i))

/-- CO25 §5.4 — Core parameters for the (paper-shaped) `D2SQuery` implementation.

`codecBridge` provides the `ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹` evaluation interface for Item 4(e)i.

The `Cache_p` forward-extension length is **not** a free field — `d2sQueryStep` uses the
paper-derived `paperForwardExtensionLength = L_V(i) - 1` directly (CO25 §5.4 Item 4(e)iiiD,
lines 1064–1068). See D5 in `audit-report.md`. -/
structure D2SQueryParams where
  -- `D2SCodecBridge` supplying the `φ⁻¹`/`ψ⁻¹` codec interface (§5.4 Item 4(e)i)
  codecBridge :
    D2SCodecBridge (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)

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
            Vector.ofFn (fun j => headUnits.get ⟨j.1, by simp only [hFull]; exact j.2⟩)
        else do
          let padLen := SpongeSize.R - headUnits.length
          let pad ← sampleVector (U := U) padLen
          let blockList := headUnits ++ pad.toList
          have hTake : headUnits.length ≤ SpongeSize.R := by
            simp only [headUnits]; exact List.length_take_le SpongeSize.R units
          have hLen : blockList.length = SpongeSize.R := by
            simp [blockList, padLen, Nat.add_sub_of_le hTake]
          pure <|
            Vector.ofFn (fun j => blockList.get ⟨j.1, by simp only [hLen]; exact j.2⟩)
      let tail ← rateBlocksFromUnitsM m restUnits
      pure (block :: tail)

private def rateBlocksFromChallengeM
    {i : pSpec.ChallengeIdx}
    (challenge : Vector U (challengeSize i)) :
    OracleComp (Unit →ₒ U) (List (Vector U SpongeSize.R)) :=
  rateBlocksFromUnitsM (U := U) (pSpec.Lᵥᵢ i) challenge.toList

/-- Runtime operations that differ between the uniform Hyb1-style `D2SQuery` wrapper and the
paper-facing external-`f` wrapper. The shared `d2sQueryStepCore` below owns the §5.4 branch tree. -/
private structure D2SQueryRuntime
    (pSpec : ProtocolSpec n) (U : Type) [SpongeUnit U] [SpongeSize]
    [HasMessageSize pSpec] [HasChallengeSize pSpec]
    (δ : Nat) (StmtIn : Type) (m : Type _ → Type _) [Monad m] where
  sampleCapacity : m (Vector U SpongeSize.C)
  sampleState : m (CanonicalSpongeState U)
  sampleCapacityList : Nat → m (List (Vector U SpongeSize.C))
  rateBlocksFromChallenge :
    {i : pSpec.ChallengeIdx} → Vector U (challengeSize (pSpec := pSpec) i) →
      m (List (Vector U SpongeSize.R))
  evalGI :
    (i : pSpec.ChallengeIdx) →
      StmtIn →
        Vector U δ →
          pSpec.EncodedMessagesUpTo U i.1.castSucc →
            m (Vector U (challengeSize (pSpec := pSpec) i))

/-- CO25 §5.4 — shared branch tree for `D2SQuery`.

The runtime supplies only sampling and `g_i`/`f_i` evaluation. All control flow remains here, in
paper order: Item 2 (`h`), Item 3 (`p⁻¹`), and Item 4 (`p`) with BackTrack branches 4(b)-4(g). -/
private def d2sQueryStepCore
    {m : Type _ → Type _} [Monad m] [Alternative m]
    (runtime : D2SQueryRuntime pSpec U δ StmtIn m)
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain) :
    StateT
      (D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
      m
      ((duplexSpongeChallengeOracle StmtIn U).Range q) := do
  let st ← get
  match q with
  | .inl stmt =>
      -- Paper Item 2 (CO25 §5.4, line 1039): `tr_∇.h.inlu(𝕩)`; on `⟂`, sample and
      -- `tr_∇.h.add(𝕩, s_C,out)` (line 1041); always append to `tr` (line 1043).
      let (capOut, trΔ') ←
        match TraceTableOps.inlu st.trΔ.h stmt with
        | some capSeg => pure (capSeg, st.trΔ)
        | none =>
            let sampled ← StateT.lift runtime.sampleCapacity
            pure (sampled,
              { st.trΔ with h := TraceTableOps.add st.trΔ.h stmt sampled })
      let trace' := st.trace ++ [⟨.inl stmt, capOut⟩]
      set { st with trace := trace', trΔ := trΔ' }
      return capOut
  | .inr (.inr stateOut) =>
      -- Paper Item 3 (line 1044): `tr_∇.p.outlu(s_out)`; on `⟂`, sample and
      -- `tr_∇.p.add(s_in, s_out)` (line 1046); always append `(p⁻¹, s_out, s_in)` to `tr`.
      let (stateIn, trΔ') ←
        match TraceTableOps.outlu st.trΔ.p stateOut with
        | some recovered => pure (recovered, st.trΔ)
        | none =>
            let sampled ← StateT.lift runtime.sampleState
            pure (sampled,
              { st.trΔ with p := TraceTableOps.add st.trΔ.p sampled stateOut })
      let trace' := st.trace ++ [⟨.inr (.inr stateOut), stateIn⟩]
      set { st with trace := trace', trΔ := trΔ' }
      return stateIn
  | .inr (.inl stateIn) =>
      match
          (backTrack
            (δ := δ)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            st.trΔ (st.trace.length + 1) stateIn).run with
      | none =>
          -- Paper Item 4(b): `err` branch aborts.
          StateT.lift failure
      | some none =>
          -- Paper Item 4(c): cache, then `tr_∇.p.inlu`, then fresh sampling.
          let (stateOut, cache', stdMemo', trΔ') ←
            match popCacheByInput (U := U) st.cacheP stateIn with
            | some (cachedOut, cacheTail) =>
                let trΔ' :=
                  { st.trΔ with p := TraceTableOps.add st.trΔ.p stateIn cachedOut }
                pure (cachedOut, cacheTail, st.stdMemo, trΔ')
            | none =>
                match TraceTableOps.inlu st.trΔ.p stateIn with
                | some recovered => pure (recovered, st.cacheP, st.stdMemo, st.trΔ)
                | none =>
                    let sampledOut ← StateT.lift runtime.sampleState
                    let trΔ' :=
                      { st.trΔ with p :=
                          TraceTableOps.add st.trΔ.p stateIn sampledOut }
                    pure (sampledOut, st.cacheP, st.stdMemo, trΔ')
          let trace' := st.trace ++ [⟨.inr (.inl stateIn), stateOut⟩]
          set { st with trace := trace', cacheP := cache', stdMemo := stdMemo', trΔ := trΔ' }
          return stateOut
      | some (some backtrackOut) =>
          -- Paper Items 4(d)-4(g). Only Item 4(e)'s `g_i` evaluation comes from the runtime.
          let (stateOut, cache', stdMemo', trΔ') ←
            if paperInCodecImagePredicate
                (codec := codec)
                (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut then
              let roundIdx := backtrackOut.roundIdx
              let stdQuery :
                  D2SStdQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                    (codec := codec) :=
                { roundIdx := roundIdx
                  stmt := backtrackOut.stmt
                  salt := backtrackOut.salt
                  encodedMessages := backtrackOut.encodedMessages }
              let (rateBlocks, stdMemo') ←
                match lookupStdMemo
                    (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                    st.stdMemo stdQuery with
                | some cachedRateBlocks =>
                    pure (cachedRateBlocks, st.stdMemo)
                | none =>
                    let sampledRhoHat ←
                      StateT.lift <|
                        runtime.evalGI
                          roundIdx backtrackOut.stmt backtrackOut.salt
                          backtrackOut.encodedMessages
                    let sampledRateBlocks ←
                      StateT.lift <| runtime.rateBlocksFromChallenge (i := roundIdx) sampledRhoHat
                    let stdMemo' :=
                      insertStdMemo
                        (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
                        st.stdMemo stdQuery sampledRateBlocks
                    pure (sampledRateBlocks, stdMemo')
              match TraceTableOps.inlu st.trΔ.p stateIn with
              | some recovered =>
                  pure (recovered, st.cacheP, stdMemo', st.trΔ)
              | none =>
                  -- Paper Item 4(e)iii.B: parse `ρ̂_i ‖ z` as exactly `L_V(i)` rate segments.
                  match rateBlocks with
                  | [] => StateT.lift failure
                  | firstRate :: tailRates =>
                      let sampledCap ← StateT.lift runtime.sampleCapacity
                      let synthesizedOut :=
                        mkStateFromSegments (U := U) firstRate sampledCap
                      let caps ← StateT.lift <| runtime.sampleCapacityList tailRates.length
                      let extraStates :=
                        (tailRates.zip caps).map fun
                          (rc : Vector U SpongeSize.R × Vector U SpongeSize.C) =>
                          mkStateFromSegments (U := U) rc.1 rc.2
                      let extraPairs :=
                        chainPairsFrom (U := U) synthesizedOut extraStates
                      let trΔ' :=
                        { st.trΔ with p :=
                            TraceTableOps.add st.trΔ.p stateIn synthesizedOut }
                      pure (synthesizedOut, st.cacheP ++ extraPairs, stdMemo', trΔ')
            else
              -- Paper Item 4(d): tuple not in image; fallback to normal `p` handling.
              match TraceTableOps.inlu st.trΔ.p stateIn with
              | some recovered => pure (recovered, st.cacheP, st.stdMemo, st.trΔ)
              | none =>
                  let sampledOut ← StateT.lift runtime.sampleState
                  let trΔ' :=
                    { st.trΔ with p :=
                        TraceTableOps.add st.trΔ.p stateIn sampledOut }
                  pure (sampledOut, st.cacheP, st.stdMemo, trΔ')
          let trace' := st.trace ++ [⟨.inr (.inl stateIn), stateOut⟩]
          set { st with trace := trace', cacheP := cache', stdMemo := stdMemo', trΔ := trΔ' }
          return stateOut

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
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain) :
    StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
      (OptionT (OracleComp (Unit →ₒ U)))
      ((duplexSpongeChallengeOracle StmtIn U).Range q) :=
  let runtime :
      D2SQueryRuntime pSpec U δ StmtIn (OptionT (OracleComp (Unit →ₒ U))) :=
    { sampleCapacity := OptionT.lift <| sampleCapacity (U := U)
      sampleState := OptionT.lift <| sampleState (U := U)
      sampleCapacityList := fun k => OptionT.lift <| sampleCapacityList (U := U) k
      rateBlocksFromChallenge := fun challenge =>
        OptionT.lift <| rateBlocksFromChallengeM (pSpec := pSpec) (U := U) challenge
      evalGI := params.codecBridge.evalGI }
  d2sQueryStepCore (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec) runtime q

/-- CO25 §5.4 — `QueryImpl` form of the `D2SQuery` oracle wrapper core.

Lifts `d2sQueryStep` into a `QueryImpl` so it can be passed to `simulateQ`. Each call
dispatches one query `q` to `(h, p, p⁻¹)` following the §5.4 Items 2–4 control flow
and threads the mutable `D2SQueryState` via `StateT`. -/
def d2sQueryImplCore
    (params : D2SQueryParams
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
        (OptionT (OracleComp (Unit →ₒ U)))) :=
  fun q => d2sQueryStep (δ := δ) params q

/-- CO25 §5.4 — Execute the `D2SQuery` oracle-wrapper semantics on a DS oracle computation.

Runs `comp` under the `D2SQuery` simulation starting from an empty `D2SQueryState`.
Returns `none` when `D2SQuery` aborts (the `err` branch, §5.4 Item 4(b)), or
`some (result, finalState)` on success. -/
def runD2SQueryCore
    (params : D2SQueryParams
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
    {α : Type}
    (comp : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) :
    OptionT (OracleComp (Unit →ₒ U))
      (α × D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) :=
  (simulateQ
    (d2sQueryImplCore (δ := δ) params)
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
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) :
    ProbComp
      (Option
        ((duplexSpongeChallengeOracle StmtIn U).Range q ×
          D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))) :=
  simulateQ unitImpl
    (((d2sQueryStep
      (δ := δ)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) params q).run st).run)

/-- CO25 §5.4 — Default abort fallback for `d2sQueryStep` in `ProbComp`.

When `d2sQueryStep` returns `none` (the §5.4 `err` branch, Item 4(b)), this fallback
totalizes the computation by returning `(default, st)` — preserving the current state
and answering with a type-default response. Used as `onAbort` in `d2sQueryImplCoreProb`. -/
def d2sQueryAbortFallback
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) :
    (duplexSpongeChallengeOracle StmtIn U).Range q ×
      D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec) :=
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
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
    (onAbort :
      (q : (duplexSpongeChallengeOracle StmtIn U).Domain) →
        D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec) →
          (duplexSpongeChallengeOracle StmtIn U).Range q ×
            D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec) :=
      d2sQueryAbortFallback
        (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
        ProbComp) :=
  fun q => do
    let st ← get
    let out? ←
      StateT.lift <|
        runD2SQueryStepWithUnitImpl
          (δ := δ)
          (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
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
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
        ProbComp) :=
  d2sQueryImplCoreProb
    (δ := δ)
    (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
    (unitImpl := d2sUnitSampleImpl (U := U))
    params

end D2SQueryCore

section D2SAlgoBridge

-- `D2SQueryState` takes many named type parameters; long lines are unavoidable in signatures.
set_option linter.style.longLine false

variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
  [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

private abbrev fsPlusUnitOracle :=
  (fsChallengeOracle StmtIn pSpec) + (Unit →ₒ U)

/-- CO25 §5.4 — Default `D2SCodecBridge` with uniform `evalGI` sampler.

The Item 4(d)/(e) branch predicate `∀ ι ∈ [i], α̂_ι ∈ Im(φ_ι)` is no longer a field; the
simulator now uses the paper-derived `paperInCodecImagePredicate` directly (see D5 in
`audit-report.md`). Only `evalGI` (the `gᵢ = ψ⁻¹ ∘ f ∘ φ⁻¹` evaluator) remains, here
specialized to a uniform `𝒰(Σ^{ℓ_V(i)})` sampler. -/
private def defaultD2SCodecBridge :
    D2SCodecBridge
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec) :=
  { evalGI := fun i _stmt _salt _encodedMessages =>
      OptionT.lift <| sampleVector (U := U) (challengeSize (pSpec := pSpec) i) }

private def defaultD2SQueryParams :
    D2SQueryParams
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec) :=
  { codecBridge :=
      defaultD2SCodecBridge
        (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec) }

/-- CO25 §5.4 — Parametric `D2SQuery` simulation bridge with explicit codec interface.

Lifts `d2sQueryImplCore` into the larger oracle `fsPlusUnitOracle` target monad,
enabling the D2SQuery simulation to run within computations that also make queries to
`fsChallengeOracle StmtIn pSpec` (the standard Fiat-Shamir challenge oracle) alongside
the auxiliary `Unit →ₒ U` sampling oracle. Parametrized by `D2SQueryParams` to allow
different `φ⁻¹`/`ψ⁻¹` codec bridges (§5.4, CO25 Equation 16). -/
def duplexSpongeToBasicFSQueryImplWithParams
    (params : D2SQueryParams
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
        (OptionT
          (OracleComp (fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) ) :=
  QueryImpl.liftTarget
    (StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
      (OptionT
        (OracleComp (fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))))
    (d2sQueryImplCore
      (δ := δ)
      (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)
      params)

/-- CO25 §5.4 — Default `D2SQuery` simulation: duplex-sponge oracles → basic Fiat-Shamir oracles.

Uses `defaultD2SQueryParams` (uniform `evalGI` via `sampleVector`; `inCodecImage` is baked in
as `paperInCodecImagePredicate` and `forwardExtensionLength` inlined as `(pSpec.Lᵥᵢ i).pred`
after D5.1 cleanup, so they are no longer free fields). Composed with a duplex-sponge malicious
prover `𝒜`
to obtain the basic Fiat-Shamir malicious prover `D2SAlgo(𝒜)` from CO25 §5.4 (Equation 16). -/
def duplexSpongeToBasicFSQueryImpl :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
        (OptionT
          (OracleComp (fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) ) :=
  duplexSpongeToBasicFSQueryImplWithParams
    (δ := δ)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)
    (defaultD2SQueryParams
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))

/-- CO25 §5.4 — Main paper-facing `D2SQuery` oracle wrapper.

This is the clean entry point for the default §5.4 query simulator. The longer
`duplexSpongeToBasicFSQueryImpl*` names are implementation/bridge names exposing the same
construction with explicit parameterization. -/
abbrev d2sQuery :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
        (OptionT
          (OracleComp (fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) ) :=
  duplexSpongeToBasicFSQueryImpl
    (δ := δ)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)

/-- Compatibility alias for the older §5.4 `D2SQuery` implementation name. Prefer `d2sQuery`. -/
abbrev d2SQueryImpl :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
        (OptionT
          (OracleComp (fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) ) :=
  d2sQuery
    (δ := δ)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)

/-- CO25 §5.4 — `D2SAlgo^f`: parametric duplex-sponge → basic Fiat-Shamir prover transform.

Implements the D2SAlgo construction (CO25 §5.4, Equation 16):
`D2SAlgo^f(𝒜) := 𝒜^{D2SQuery^{ψ⁻¹ ∘ f ∘ φ⁻¹}}`

Given a malicious prover `P` against the duplex-sponge Fiat-Shamir oracle `𝒟_{DS}(λ, n)`, runs
`P` under the `D2SQuery` simulation (controlled by `params`) to obtain a malicious prover against
the standard Fiat-Shamir oracle `𝒟_{IP}(λ, n)`. Returns `none` when D2SQuery aborts. The output
oracle family is `oSpec + fsChallengeOracle + Unit →ₒ U` (CO25 §5.4, Equation 17 time bound). -/
def duplexSpongeToBasicFSAlgoWithParams
    (params : D2SQueryParams
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
    (StmtIn × pSpec.Messages)) :
    OracleComp (oSpec + fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (Option (StmtIn × pSpec.Messages)) :=
  let d2sOuterImpl :
      QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
          (OptionT
            (OracleComp
              (oSpec + fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))))) :=
    QueryImpl.addLift
      (r := StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
        (OptionT
          (OracleComp
            (oSpec + fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))))
      (QueryImpl.id oSpec)
      (duplexSpongeToBasicFSQueryImplWithParams
        (δ := δ)
        (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)
        params)
  let outWithState :
      OptionT
        (OracleComp
          (oSpec + fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
        ((StmtIn × pSpec.Messages) ×
          D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) :=
    (simulateQ d2sOuterImpl P).run default
  do
    let out? ← outWithState.run
    pure (out?.map Prod.fst)

/-- CO25 §5.4 — Default `D2SAlgo`: duplex-sponge → basic Fiat-Shamir prover transform.

Specializes `duplexSpongeToBasicFSAlgoWithParams` with `defaultD2SQueryParams`:
- `inCodecImage` is baked into `d2sQueryStep` as `paperInCodecImagePredicate` (built from
  `paperCodecImageWitness?` + `messageInSerializeImage`) — D5.1 cleanup removed it as a
  free field of `D2SCodecBridge`/`D2SQueryParams`,
- `evalGI` via uniform sampling `𝒰(Σ^{ℓ_V(i)})` (i.e. `gᵢ ← 𝒟_Σ(λ, n)`),
- `forwardExtensionLength` is inlined as `(pSpec.Lᵥᵢ i).pred` (also exposed as
  `paperForwardExtensionLength`); fills `Cache_p` chain, §5.4 Item 4(e)iiiD.
This is the canonical D2SAlgo instance used throughout the CO25 §5 security analysis. -/
def duplexSpongeToBasicFSAlgo
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
    (StmtIn × pSpec.Messages)) :
    OracleComp (oSpec + fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (Option (StmtIn × pSpec.Messages)) :=
  duplexSpongeToBasicFSAlgoWithParams
    (δ := δ)
    (T_H := T_H) (T_P := T_P)
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)
    (defaultD2SQueryParams
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
    P

/-- CO25 §5.4 — Main paper-facing `D2SAlgo` prover transform.

This is the clean entry point for the default §5.4 prover transform
`D2SAlgo(𝒜) := 𝒜^{D2SQuery}`. The longer `duplexSpongeToBasicFSAlgo*` names are
implementation/bridge names exposing explicit parameters. -/
abbrev d2sAlgo
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    OracleComp (oSpec + fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (Option (StmtIn × pSpec.Messages)) :=
  duplexSpongeToBasicFSAlgo
    (δ := δ)
    (T_H := T_H) (T_P := T_P)
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec) P

/-- Compatibility alias for the older §5.4 `D2SAlgo` name. Prefer `d2sAlgo`. -/
abbrev d2SAlgo
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    OracleComp (oSpec + fsPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (Option (StmtIn × pSpec.Messages)) :=
  d2sAlgo
    (δ := δ)
    (T_H := T_H) (T_P := T_P)
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec) P

/-- CO25 §5.4 — Salted basic-FS challenge oracle augmented with auxiliary unit-sampling.

Encoding A (salt threaded through the augmented statement, matching
`Prover.singleSaltFiatShamir` in `SingleSalt.lean`): the basic-FS oracle queries
`(salt, stmt) ∈ Vector U δ × StmtIn`. Salted analogue of `fsPlusUnitOracle`. -/
private abbrev fsSaltedPlusUnitOracle :=
  (fsChallengeOracle (Vector U δ × StmtIn) pSpec) + (Unit →ₒ U)

/-- CO25 §5.4 — Salted variant of `duplexSpongeToBasicFSQueryImplWithParams`.

Same simulator core as the unsalted version, but lifts the inner
`OptionT (OracleComp (Unit →ₒ U))` target to `oSpec + fsSaltedPlusUnitOracle` so the
output prover can be embedded in a context with a salted basic-FS challenge oracle. The
simulator core itself does not query `f` (default `evalGI` samples uniformly); the salt is
passed through at the wrapper level via the salted output proof type. -/
def duplexSpongeToBasicFSQueryImplWithParamsSalted
    (params : D2SQueryParams
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
        (OptionT
          (OracleComp
            (fsSaltedPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))))) :=
  QueryImpl.liftTarget
    (StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
      (OptionT
        (OracleComp
          (fsSaltedPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)))))
    (d2sQueryImplCore
      (δ := δ)
      (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)
      params)

/-- CO25 §5.4 — Salted parametric `D2SAlgo`: duplex-sponge → salted basic Fiat-Shamir prover.

Paper-faithful per Eq. 16 Step 4-6: input prover `P̃` outputs `(x, π)` with
`π = (τ, α_1, …, α_k) ∈ Σ^δ × messages` (`DSSaltedProof pSpec U δ`); output prover targets
the salted basic-FS oracle with the same salted proof type. The salt is threaded through
unchanged (the simulator core is salt-agnostic; the salted oracle records salt-aware
challenges only when the bridge `evalGI` issues `f_i` queries on `(stmt, salt, ·)`). -/
def duplexSpongeToBasicFSAlgoSaltedWithParams
    (params : D2SQueryParams
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :
    OracleComp
      (oSpec + fsSaltedPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (Option (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :=
  let d2sOuterImpl :
      QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
          (OptionT
            (OracleComp
              (oSpec + fsSaltedPlusUnitOracle
                (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))))) :=
    QueryImpl.addLift
      (r := StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
        (OptionT
          (OracleComp
            (oSpec + fsSaltedPlusUnitOracle
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)))))
      (QueryImpl.id oSpec)
      (duplexSpongeToBasicFSQueryImplWithParamsSalted
        (δ := δ)
        (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)
        params)
  let outWithState :
      OptionT
        (OracleComp
          (oSpec + fsSaltedPlusUnitOracle
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)))
        ((StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ) ×
          D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)) :=
    (simulateQ d2sOuterImpl P).run default
  do
    let out? ← outWithState.run
    pure (out?.map Prod.fst)

/-- CO25 §5.4 — Default salted `D2SAlgo`: specializes `duplexSpongeToBasicFSAlgoSaltedWithParams`
with `defaultD2SQueryParams` (uniform `evalGI` and paper-derived `paperForwardExtensionLength`). -/
def duplexSpongeToBasicFSAlgoSalted
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :
    OracleComp
      (oSpec + fsSaltedPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (Option (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :=
  duplexSpongeToBasicFSAlgoSaltedWithParams
    (δ := δ)
    (T_H := T_H) (T_P := T_P)
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)
    (defaultD2SQueryParams
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
    P

/-- Salted Hyb₁-style uniform `D2SAlgo` helper.

This helper specializes with `defaultD2SQueryParams`, so its `g_i` responses are sampled uniformly
from encoded challenges. The paper-facing Theorem 5.1 witness instead uses
`KeyLemma.paperD2SAlgoSaltedExternal`, which bridges through an external salted `f_i` oracle. -/
abbrev d2sAlgoSaltedUniform
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :
    OracleComp
      (oSpec + fsSaltedPlusUnitOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (Option (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ)) :=
  duplexSpongeToBasicFSAlgoSalted
    (δ := δ)
    (T_H := T_H) (T_P := T_P)
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec) P

end D2SAlgoBridge

section D2SQueryWithOracle

variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
  [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- CO25 §5.4 — External challenge-oracle family augmented with the auxiliary sampling oracles.

`D2SChallengePlusUnitOracle challengeSpec` is `challengeSpec + (Unit →ₒ U) + unifSpec`:
the sum of the caller-supplied challenge oracle `gᵢ`-family, the auxiliary unit-sampling
oracle `𝒰(Σ)` used by D2SQuery fresh-sample branches (§5.4 Items 2(b), 3(b), 4(c)iii, 4(e)iiiC),
and `unifSpec` for any additional uniform randomness. -/
abbrev D2SChallengePlusUnitOracle {κ : Type} (challengeSpec : OracleSpec κ) :=
  challengeSpec + ((Unit →ₒ U) + unifSpec)

/-- CO25 §5.8 — Finite preimage set of a verifier-message decoder `ψᵢ`.

`{α̂ ∈ Σ^{ℓ_V(i)} | ψᵢ(α̂) = α}` for a target challenge `α : ℳ_{V,i}`. Backs the uniform
preimage sampler `uniformDeserializePreimage`; surjectivity of `ψᵢ` (`Codec.decode_surjective`)
guarantees nonemptiness. -/
noncomputable def deserializePreimageFinset
    {i : pSpec.ChallengeIdx}
    [Fintype U] [DecidableEq U]
    [Fintype (pSpec.Challenge i)] [DecidableEq (pSpec.Challenge i)]
    (challenge : pSpec.Challenge i) :
    Finset (Vector U (challengeSize (pSpec := pSpec) i)) := by
  classical
  let _ : Fintype (Vector U (challengeSize (pSpec := pSpec) i)) :=
    Fintype.ofEquiv (Fin (challengeSize (pSpec := pSpec) i) → U) Equiv.rootVectorEquivFin.symm
  exact (Finset.univ : Finset (Vector U (challengeSize (pSpec := pSpec) i))).filter fun encoded =>
    Deserialize.deserialize encoded = challenge

/-- CO25 §5.4 / §5.8 — Uniform `ψᵢ⁻¹` preimage sampler.

Given a challenge `α : ℳ_{V,i}`, samples a uniform encoded preimage `α̂ ∈ Σ^{ℓ_V(i)}` with
`ψᵢ(α̂) = α` by toListing `deserializePreimageFinset α` and indexing with a `unifSpec`-sampled
`Fin`. Used to lift `f_i : … → ℳ_{V,i}` to `g_i = ψᵢ⁻¹ ∘ f_i ∘ φᵢ⁻¹ : … → Σ^{ℓ_V(i)}` inside
`d2sQueryStepWithOracle` (CO25 §5.4 Item 4(e)i). -/
noncomputable def uniformDeserializePreimage
    {κ : Type} {challengeSpec : OracleSpec κ}
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    {i : pSpec.ChallengeIdx}
    (challenge : pSpec.Challenge i) :
    OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (Vector U (challengeSize (pSpec := pSpec) i)) := do
  have hpreimages_nonempty :
      (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).Nonempty := by
    rcases codec.decode_surjective i challenge with ⟨encoded, hencoded⟩
    have hencoded' : Deserialize.deserialize encoded = challenge := hencoded
    exact ⟨encoded, by simp [deserializePreimageFinset, hencoded']⟩
  let preimages := (deserializePreimageFinset (pSpec := pSpec) (U := U) challenge).toList
  have hpreimages_ne : preimages ≠ [] := by
    simpa [preimages] using hpreimages_nonempty.toList_ne_nil
  have hlen_pos : 0 < preimages.length := List.length_pos_iff_ne_nil.mpr hpreimages_ne
  let idxRaw ←
    (show OracleComp
        (D2SChallengePlusUnitOracle (U := U) challengeSpec)
        (Fin ((preimages.length - 1) + 1)) from
      query
        (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
        (.inr (.inr (preimages.length - 1))))
  have hlen_eq : (preimages.length - 1) + 1 = preimages.length := Nat.sub_add_cancel
    (Nat.succ_le_of_lt hlen_pos)
  let idx : Fin preimages.length := ⟨idxRaw.1, by simpa [hlen_eq] using idxRaw.2⟩
  pure (preimages.get idx)

/-- CO25 §5.4 — `D2SCodecBridge` variant with access to an external challenge-oracle family.

Same structure as `D2SCodecBridge` but `evalGI` is allowed to query `challengeSpec` (the
caller-supplied `fᵢ`-family oracle) in addition to the auxiliary `Unit →ₒ U` sampling oracle.
This is the oracle-aware version used when D2SQuery is embedded inside a larger computation
that already has access to challenge oracles `f_i : {0,1}^{≤n} × … → ℳ_{V,i}`.

`evalGI` returns the **paper-facing `f_i` value** in `pSpec.Challenge i = ℳ_{V,i}`; the
simulator (`d2sQueryStepWithOracle`) auto-applies `ψᵢ⁻¹` via `uniformDeserializePreimage`
to recover the encoded `ρ̂_i ∈ Σ^{ℓ_V(i)}`. The φᵢ⁻¹ side stays implicit in the
paper tuple `(τ, α̂_1, …, α̂_i)` argument shape (CO25 §5.4 Item 4(e)i). See D5.1 #2 in
`audit-report.md`.

The Item 4(d) vs 4(e) branch predicate `∀ ι ∈ [i], α̂_ι ∈ Im(φ_ι)` is **not** a free field —
the simulator uses the paper-derived `paperInCodecImagePredicate` directly (CO25 §5.4 lines
1056/1059). See D5 in `audit-report.md`. -/
structure D2SCodecBridgeWithOracle {κ : Type} (challengeSpec : OracleSpec κ) where
  /-- `gᵢ = ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹ : {0,1}^{≤n} × Σ^{ℓ_P(<i)} → Σ^{ℓ_V(i)}` via oracle query
    to `challengeSpec` (§5.4 Item 4(e)i). Already encoded in `Σ^{ℓ_V(i)}` — the user-facing
    helper `defaultD2SQueryParamsWithOracle` performs the `ψᵢ⁻¹` composition via
    `uniformDeserializePreimage` when constructing this bridge. -/
  evalGI :
    (i : pSpec.ChallengeIdx) →
      StmtIn →
        Vector U δ →
          pSpec.EncodedMessagesUpTo U i.1.castSucc →
            OptionT
              (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec))
              (Vector U (challengeSize (pSpec := pSpec) i))

/-- CO25 §5.4 — `D2SQueryParams` variant with access to an external challenge-oracle family.

Oracle-aware counterpart to `D2SQueryParams`: uses `D2SCodecBridgeWithOracle` so that
the `evalGI` branch can make oracle queries to `challengeSpec` (e.g. `fᵢ`) when computing
the `gᵢ = ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹` response in §5.4 Item 4(e)i.

The `Cache_p` forward-extension length is **not** a free field — `d2sQueryStepWithOracle`
uses the paper-derived `paperForwardExtensionLength = L_V(i) - 1` directly (CO25 §5.4
Item 4(e)iiiD, lines 1064–1068). See D5 in `audit-report.md`. -/
structure D2SQueryParamsWithOracle {κ : Type} (challengeSpec : OracleSpec κ) where
  -- `D2SCodecBridgeWithOracle` with oracle-access `evalGI` (§5.4 Item 4(e)i)
  codecBridge :
    D2SCodecBridgeWithOracle
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec) challengeSpec

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
query `challengeSpec` (the `fᵢ`-family oracle) via `D2SChallengePlusUnitOracle`. Used when
D2SQuery is embedded in a larger computation that already holds the `fᵢ` oracles.

Item 4(e)i `ρ̂_i := ψᵢ⁻¹(f_i(𝕩, τ̂, α̂_1, …, α̂_i))` is materialized inside
`params.codecBridge.evalGI`; the user-facing constructor `defaultD2SQueryParamsWithOracle`
auto-composes `ψᵢ⁻¹` from a caller-supplied `f_i` via `uniformDeserializePreimage`. -/
def d2sQueryStepWithOracle
    {κ : Type} {challengeSpec : OracleSpec κ}
    (params :
      D2SQueryParamsWithOracle
        (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec) challengeSpec)
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain) :
    StateT
        (D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
      (OptionT
        (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)))
      ((duplexSpongeChallengeOracle StmtIn U).Range q) :=
  let runtime :
      D2SQueryRuntime pSpec U δ StmtIn
        (OptionT (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec))) :=
    { sampleCapacity := OptionT.lift <| sampleCapacityWithOracle (U := U) challengeSpec
      sampleState := OptionT.lift <| sampleStateWithOracle (U := U) challengeSpec
      sampleCapacityList := fun k =>
        OptionT.lift <| sampleCapacityListWithOracle (U := U) challengeSpec k
      rateBlocksFromChallenge := fun challenge =>
        OptionT.lift <|
          rateBlocksFromChallengeMWithOracle
            (pSpec := pSpec) (U := U) challengeSpec challenge
      evalGI := params.codecBridge.evalGI }
  d2sQueryStepCore (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec) runtime q

/-- CO25 §5.4 — `QueryImpl` form of `d2sQueryStepWithOracle`.

Lifts `d2sQueryStepWithOracle` into a `QueryImpl` that can be passed to `simulateQ`,
enabling the §5.4 D2SQuery simulation under an explicit external challenge-oracle family
`challengeSpec` (carrying the `fᵢ`-family oracle). -/
def d2sQueryImplCoreWithOracle
    {κ : Type} {challengeSpec : OracleSpec κ}
    (params :
      D2SQueryParamsWithOracle
        (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)
        challengeSpec) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT
        (D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec))
        (OptionT
          (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec)))) :=
  fun q => d2sQueryStepWithOracle (δ := δ) (codec := codec) params q

/-- CO25 §5.4 — Default `D2SQueryParamsWithOracle` with caller-supplied `fᵢ` oracle bridge.

Constructs `D2SQueryParamsWithOracle` using `evalGI := f_i` — the paper-facing external
challenge oracle returning `pSpec.Challenge i = ℳ_{V,i}`. The simulator
(`d2sQueryStepWithOracle`) auto-applies `ψᵢ⁻¹` via `uniformDeserializePreimage` to recover
the encoded `ρ̂_i ∈ Σ^{ℓ_V(i)}` (CO25 §5.4 Item 4(e)i, D5.1 #2 in `audit-report.md`).

The Item 4(d) vs 4(e) branch predicate `∀ ι, α̂_ι ∈ Im(φ_ι)` and the `Cache_p` forward-extension
length are **not** parameters — `d2sQueryStepWithOracle` uses the paper-derived
`paperInCodecImagePredicate` and `paperForwardExtensionLength = L_V(i) - 1` directly
(CO25 §5.4 lines 1056/1059, 1064–1068). See D5 in `audit-report.md`. -/
def defaultD2SQueryParamsWithOracle
    [Fintype U] [DecidableEq U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    {κ : Type} {challengeSpec : OracleSpec κ}
    (evalGI :
      (i : pSpec.ChallengeIdx) →
        StmtIn →
          Vector U δ →
            pSpec.EncodedMessagesUpTo U i.1.castSucc →
              OptionT
                (OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec))
                (pSpec.Challenge i)) :
    D2SQueryParamsWithOracle
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (codec := codec)
      challengeSpec :=
  { codecBridge :=
      { evalGI := fun i stmt salt encodedMessages => do
          let challenge ← evalGI i stmt salt encodedMessages
          OptionT.lift <|
            uniformDeserializePreimage
              (pSpec := pSpec) (U := U) (codec := codec)
              (challengeSpec := challengeSpec) challenge } }

end D2SQueryWithOracle

end

end DuplexSpongeFS.ProverTransform
