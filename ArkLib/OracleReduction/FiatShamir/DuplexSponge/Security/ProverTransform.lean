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

Note: The paper's §5.5.2 D2STrace Step 3 `bin(τ) ∈ {0,1}^{δ_*}` salt binarization is modeled
using the `SaltCodec` class from `Defs.lean`, decoupling the FS-standard `Salt` type from
the on-sponge `Vector U δ` type.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.ProverTransform

open Backtrack Lookahead DSTraceStorage TraceTransform

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U]
  {δ : Nat}

local instance : Inhabited U := ⟨0⟩

noncomputable section

section D2SQueryState

set_option linter.style.longLine false

variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- CO25 §5.4 Item 1 — Internal mutable state of the `D2SQuery` oracle wrapper.

- `trace` (`tr`): ordered `h`/`p`/`p⁻¹` query-answer pairs (bullet 1).
- `cacheP` (`Cache_p`): `(s_in, s_out)` pairs sorted by input, consumed by Item 4(c)i (bullet 2).
- `trΔ` (`tr_∇`): dedup index over `trace` for `O(log N)` `inlu`/`outlu` (CO25 Def. 5.2; bullet 3).

`gᵢ`-response consistency (paper Item 4(e)i) is **not** carried in this struct — it is
provided by `D2SAlgo`'s `tr_i` memo at the bridge layer (`D2SAlgoMemo`, threaded through
`d2sCodecBridgeImplMemo`). Keeping `tr_i` out of `D2SQuery` matches the paper's placement of
the memo inside `D2SAlgo` (Item 3, lines 1066-1075), and keeps the §5.8 hybrid `D2SQuery`
analysis (`d2sQueryImpl`) independent of the bridge memo. -/
structure D2SQueryState where
  -- `tr`: ordered `('h', 𝕩, s_C)` / `('p', s_in, s_out)` / `('p⁻¹', …)` pairs (§5.4 Item 1)
  trace : QueryLog (duplexSpongeChallengeOracle StmtIn U) := []
  -- `Cache_p`: `(s_in, s_out) ∈ Σ^{r+c} × Σ^{r+c}` sorted by input (§5.4 Item 1, bullet 2)
  cacheP : List (CanonicalSpongeState U × CanonicalSpongeState U) := []
  -- `tr_∇`: deduplicated index for `O(log N)` `inlu`/`outlu` lookups (CO25 Def. 5.2, §5.1)
  trΔ : TraceNabla T_H T_P StmtIn U :=
    ⟨TraceTableOps.empty, TraceTableOps.empty⟩
  -- Invariant: every entry in `trΔ` appears in `trace`. Maintained by construction:
  -- each step that appends to `trace` either leaves `trΔ` unchanged or adds an entry
  -- that matches the new trace element. Required by `backTrack` (CO25 §5.2).
  h_inv : trΔ.IsSubsetOfQueryLog trace
  -- Phantom: auto-binds `δ` and `pSpec` as implicit struct params (matches the original
  -- shape pre-`gMemo`-deletion, so `set { st with … }` resolves `MonadStateOf` cleanly).
  _phantom : Option (BacktrackOutput
    (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := none

instance : Inhabited (D2SQueryState
    (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  ⟨{ h_inv := TraceNabla.IsSubsetOfQueryLog_empty_nil }⟩

/-- Executable approximation of Item 4(d)/(e) tuple-image branching, tightened with
`BackTrack`-shape checks and challenge-block length sanity. -/
private def messageInSerializeImage
    (msgIdx : pSpec.MessageIdx)
    (encoded : Vector U (messageSize msgIdx)) : Bool := by
  exact decide (∃ msg : pSpec.Message msgIdx, Serialize.serialize msg = encoded)

/-- Executable check for the paper branch condition
`∀ ι ≤ i, α̂_ι ∈ Im(φ_ι)` on one parsed `BackTrack` output. -/
def backtrackOutputMessagesInImage
    (inImage : (msgIdx : pSpec.MessageIdx) → Vector U (messageSize msgIdx) → Bool)
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Bool :=
  let before : List pSpec.MessageIdx := messageIdxListBefore (pSpec := pSpec) out.roundIdx
  before.attach.all fun ⟨j, hj⟩ =>
    let hlt := (Finset.mem_filter.mp (Finset.mem_toList.mp hj)).2
    inImage j (out.encodedMessages ⟨j, hlt⟩)

/-- CO25 §5.4 Items 4(d)/(e) — paper predicate `∀ ι ∈ [i], α̂_ι ∈ Im(φ_ι)`, decided as a
`Serialize`-image check on the recovered encoded messages. -/
private noncomputable def d2sInCodecImagePredicate
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Bool :=
  backtrackOutputMessagesInImage
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
    (inImage := messageInSerializeImage (pSpec := pSpec) (U := U))
    (out := out)

private def popCacheByInput
    (cache : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (stateIn : CanonicalSpongeState U) :
    Option (CanonicalSpongeState U × List (CanonicalSpongeState U × CanonicalSpongeState U)) := by
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

/-- CO25 §5.4 — `𝒰(Σ)` realization of `Unit →ₒ U` in `ProbComp`; used by §5.4 fresh-sample
branches (Items 2(b), 3(b), 4(c)iii, 4(e)iiiC). -/
def d2sUnitSampleImpl [SampleableType U] :
    QueryImpl (Unit →ₒ U) ProbComp :=
  fun
  | () => $ᵗ U

end D2SQueryState

section D2SChallengePlusUnit

variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]


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
  let _ : Fintype (Vector U (challengeSize (pSpec := pSpec) i)) :=
    Fintype.ofEquiv (Fin (challengeSize (pSpec := pSpec) i) → U) Equiv.rootVectorEquivFin.symm
  exact (Finset.univ : Finset (Vector U (challengeSize (pSpec := pSpec) i))).filter fun encoded =>
    Deserialize.deserialize encoded = challenge

/-- Sample a uniformly random element from a non-empty list using the `unifSpec` branch. -/
def sampleFromList {α κ : Type} {challengeSpec : OracleSpec κ} [SpongeUnit U]
    (l : List α) (hl : l ≠ []) :
    OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec) α := do
  let idxRaw ← query
    (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
    (.inr (.inr (l.length - 1))) -- from unifSpec
  let idx : Fin l.length := ⟨idxRaw.1, by
    have hlen_pos : 0 < l.length := List.length_pos_iff_ne_nil.mpr hl
    have hlen_eq : (l.length - 1) + 1 = l.length := Nat.sub_add_cancel (Nat.succ_le_of_lt hlen_pos)
    simpa [hlen_eq] using idxRaw.2⟩
  pure (l.get idx)

/-- CO25 §5.4 / §5.8 — Uniform `ψᵢ⁻¹` preimage sampler: samples `α̂ ←$ ψᵢ⁻¹(α)` by toListing
`deserializePreimageFinset α` and indexing via `unifSpec` -/
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
  sampleFromList preimages hpreimages_ne

end D2SChallengePlusUnit

/-! ## Oracle-first `D2SQuery` API

CO25 §5.4 — `D2SQuery` oracle spec and direct-query helpers.

`d2sQueryOracles = gSpec + ((Unit →ₒ U) + unifSpec)` where
`gSpec = gSpec StmtIn pSpec δ` is the `gᵢ`-family oracle.
All sampling (`𝒰(Σ^c)`, `𝒰(Σ^{r+c})`, etc.) goes through `Unit →ₒ U`;
the `gᵢ` query is a single `.inl` injection into the sum spec. -/
section D2SQuery

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]

/-- CO25 §5.4 — `D2SQuery` oracle spec: `gSpec + ((Unit →ₒ U) + unifSpec)`.

- `gSpec` = `gSpec` — the `gᵢ`-family (Item 4(e)i)
- `Unit →ₒ U` — `𝒰(Σ)` for sampling `s_{C,out}`, `s_in`, `s_out`, etc.
- `unifSpec` — `Fin`-sampling for `ψᵢ⁻¹` preimage selection -/
abbrev d2sQueryOracles :=
  D2SChallengePlusUnitOracle
    (U := U) (challengeSpec := gSpec (U := U) StmtIn pSpec δ)

/-- CO25 §5.4 Item 4(e)i — Query `gᵢ(𝕩, τ̂, α̂₁, …, α̂ᵢ) → ρ̂ᵢ ∈ Σ^{ℓ_V(i)}`.

Direct `.inl` injection into `d2sQueryOracles`. -/
def d2sQueryG
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (salt : Vector U δ)
    (encodedMessages : pSpec.EncodedMessagesBefore U i.1.castSucc) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (Vector U (challengeSize (pSpec := pSpec) i)) :=
  query (spec := d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
    (Sum.inl ⟨i, (stmt, salt, encodedMessages)⟩)

/-- CO25 §5.4 — Sample `u ← 𝒰(Σ)` via `Unit →ₒ U`. -/
private def d2sSampleUnit :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) U :=
  query (spec := d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
    (Sum.inr (.inl ()))

/-- Sample `m` consecutive units; helper for `d2sSampleVector`. -/
private def d2sSampleArrayExact :
    (m : Nat) →
      OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
        {xs : Array U // xs.size = m}
  | 0 => pure ⟨#[], rfl⟩
  | m + 1 => do
      let u ← d2sSampleUnit (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      let ⟨xs, hxs⟩ ← d2sSampleArrayExact m
      pure ⟨xs.push u, by simp [hxs]⟩

private def d2sSampleVector (m : Nat) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (Vector U m) := do
  let ⟨xs, hxs⟩ ← d2sSampleArrayExact (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m
  pure ⟨xs, hxs⟩

/-- CO25 §5.4 Item 2(b) — Sample `s_{C,out} ← 𝒰(Σ^c)`. -/
def d2sSampleCapacity :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (Vector U SpongeSize.C) :=
  d2sSampleVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) SpongeSize.C

/-- CO25 §5.4 Items 3(b)/4(d)ii — Sample `s ← 𝒰(Σ^{r+c})`. -/
def d2sSampleState :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (CanonicalSpongeState U) :=
  d2sSampleVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) SpongeSize.N

/-- CO25 §5.4 Item 4(e)iiiC — Sample `s_C^{(0)}, …, s_C^{(k-1)} ← 𝒰(Σ^c)`. -/
def d2sSampleCapacityList :
    Nat →
      OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
        (List (Vector U SpongeSize.C))
  | 0 => pure []
  | m + 1 => do
      let head ← d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      let tail ← d2sSampleCapacityList m
      pure (head :: tail)

/-- CO25 §5.4 Item 4(e)iiiB — Split units into `m` rate blocks of size `r`,
padding the final partial block with fresh `𝒰(Σ)` samples. -/
private def d2sRateBlocksFromUnitsM :
    (m : Nat) → List U →
      OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
        { blocks : List (Vector U SpongeSize.R) // blocks.length = m }
  | 0, _ => pure ⟨[], rfl⟩
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
          -- MUST sample z units for the remainder where `|z| = r - (ℓᵥ(i) % r)`
          let padLen := SpongeSize.R - headUnits.length
          let pad ←
            d2sSampleVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) padLen
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
      let ⟨tail, hTail⟩ ← d2sRateBlocksFromUnitsM m restUnits
      pure ⟨block :: tail, by simp [hTail]⟩

/-- CO25 §5.4 Item 4(e)iiiB — Reshape `ρ̂ᵢ ∈ Σ^{ℓ_V(i)}` into `L_V(i)` rate blocks,
padding the final partial block with fresh `𝒰(Σ)` samples. -/
def d2sRateBlocksFromChallenge
    {i : pSpec.ChallengeIdx}
    (challenge : Vector U (challengeSize (pSpec := pSpec) i)) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (Vector (Vector U SpongeSize.R) (pSpec.Lᵥᵢ i)) := do
  let ⟨blocks, hBlocks⟩ ← d2sRateBlocksFromUnitsM (U := U) (StmtIn := StmtIn)
    (pSpec := pSpec) (δ := δ) (pSpec.Lᵥᵢ i) challenge.toList
  pure ⟨blocks.toArray, by simp [hBlocks]⟩

/-! ### `d2sQueryStep` / `d2sQueryImpl`

CO25 §5.4 — Wires the Items 2-4 branch tree to the `d2sQueryOracles` direct-query helpers.
Sampling goes through `Unit →ₒ U`; `gᵢ` evaluation goes through `d2sQueryG`. -/

section StepImpl

variable {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- CO25 §5.4 Item 2 — hash-oracle (`h`) branch of `D2SQuery`.

Paper steps (lines 1039-1043): lookup `tr_∇.h.inlu(𝕩)`; on `⟂`, sample `s_{C,out} ← 𝒰(Σ^c)` and
call `tr_∇.h.add(𝕩, s_{C,out})`; always append `('h', 𝕩, s_{C,out})` to `tr`. -/
private def d2sHandleHashQuery
    (stmt : StmtIn) :
    StateT
      (D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      (Vector U SpongeSize.C) := do
  let st ← get
  match TraceTableOps.inlu st.trΔ.h stmt with
  -- Item 2(a) — cache hit: `s_{C,out} := tr_∇.h.inlu(𝕩)`.
  | some capSeg =>
      let trace' := st.trace ++ [⟨dsHashQuery stmt, capSeg⟩]
      let h_inv' : st.trΔ.IsSubsetOfQueryLog trace' := TraceNabla.IsSubsetOfQueryLog_append_any
        st.h_inv ⟨dsHashQuery stmt, capSeg⟩
      set { st with trace := trace', h_inv := h_inv' }
      return capSeg
  | none =>
      -- Item 2(b) — cache miss: `s_{C,out} ←$ 𝒰(Σ^c)`; then `tr_∇.h.add(𝕩, s_{C,out})`.
      let sampled ← StateT.lift <| OptionT.lift <| d2sSampleCapacity (U := U) (StmtIn := StmtIn)
        (pSpec := pSpec) (δ := δ)
      -- Item 2(c) — append `('h', 𝕩, s_{C,out})` to `tr`; return `s_{C,out}`.
      let trace' := st.trace ++ [⟨dsHashQuery stmt, sampled⟩]
      let trΔ' : TraceNabla T_H T_P StmtIn U :=
        { st.trΔ with h := TraceTableOps.add st.trΔ.h stmt sampled }
      let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
        TraceNabla.IsSubsetOfQueryLog_append_hash st.h_inv stmt sampled
      set { st with trace := trace', trΔ := trΔ', h_inv := h_inv' }
      return sampled

/-- CO25 §5.4 Item 3 — inverse-permutation (`p⁻¹`) branch of `D2SQuery`.

Paper steps (lines 1044-1046): lookup `tr_∇.p.outlu(s_out)`; on `⟂`, sample `s_in ← 𝒰(Σ^{r+c})`
and call `tr_∇.p.add(s_in, s_out)`; always append `('p⁻¹', s_out, s_in)` to `tr`. -/
private def d2sHandleInversePermQuery
    (stateOut : CanonicalSpongeState U) :
    StateT
      (D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      (CanonicalSpongeState U) := do
  let st ← get
  match TraceTableOps.outlu st.trΔ.p stateOut with
  -- Item 3(a) — reverse cache hit: `s_in := tr_∇.p.outlu(s_out)`.
  | some recovered =>
      let trace' := st.trace ++ [⟨dsPermInvQuery stateOut, recovered⟩]
      let h_inv' : st.trΔ.IsSubsetOfQueryLog trace' :=
        TraceNabla.IsSubsetOfQueryLog_append_any st.h_inv ⟨dsPermInvQuery stateOut, recovered⟩
      set { st with trace := trace', h_inv := h_inv' }
      return recovered
  | none =>
      -- Item 3(b) — miss: `s_in ←$ 𝒰(Σ^{r+c})`; then `tr_∇.p.add(s_in, s_out)`.
      let sampled ← StateT.lift <| OptionT.lift <|
        d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      -- Item 3(c) — append `('p⁻¹', s_out, s_in)` to `tr`; return `s_in`.
      let trace' := st.trace ++ [⟨dsPermInvQuery stateOut, sampled⟩]
      let trΔ' : TraceNabla T_H T_P StmtIn U :=
        { st.trΔ with p := TraceTableOps.add st.trΔ.p sampled stateOut }
      let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
        TraceNabla.IsSubsetOfQueryLog_append_perm_inv st.h_inv sampled stateOut
      set { st with trace := trace', trΔ := trΔ', h_inv := h_inv' }
      return sampled

/-- CO25 §5.4 Item 4(c) — `BackTrack` returned `.noResult`.

Cache lookup (Item 4(c)i) → `tr_∇.p.inlu` (Item 4(c)ii) → fresh sampling fallback. -/
private def d2sHandleBacktrackNoResult
    (stateIn : CanonicalSpongeState U) :
    StateT
      (D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      (CanonicalSpongeState U) := do
  -- find `s_out` for `s_in` from `Cache_p -> inlu -> sample`
  let st ← get
  match popCacheByInput (U := U) st.cacheP stateIn with
  -- Item 4(c)i — cache pop: `(s_out, Cache_p') := pop(Cache_p, s_in)`, `tr_∇.p.add(s_in, s_out)`.
  | some (cachedOut, cacheTail) =>
      -- Item 4(c)iv — append `('p', s_in, s_out)` to `tr`.
      let trace' := st.trace ++ [⟨dsPermQuery stateIn, cachedOut⟩]
      let trΔ' : TraceNabla T_H T_P StmtIn U :=
        { st.trΔ with p := TraceTableOps.add st.trΔ.p stateIn cachedOut }
      let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
        TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv stateIn cachedOut
      set { st with trace := trace', cacheP := cacheTail, trΔ := trΔ', h_inv := h_inv' }
      return cachedOut
  | none =>
      match TraceTableOps.inlu st.trΔ.p stateIn with
      -- Item 4(c)ii — forward cache hit: `s_out := tr_∇.p.inlu(s_in)`.
      | some recovered =>
          -- Item 4(c)iv — append `('p', s_in, s_out)` to `tr`.
          let trace' := st.trace ++ [⟨dsPermQuery stateIn, recovered⟩]
          let h_inv' : st.trΔ.IsSubsetOfQueryLog trace' :=
            TraceNabla.IsSubsetOfQueryLog_append_any st.h_inv ⟨dsPermQuery stateIn, recovered⟩
          set { st with trace := trace', h_inv := h_inv' }
          return recovered
      | none =>
          -- Item 4(c)iii — fresh sample: `s_out ←$ 𝒰(Σ^{r+c})`; `tr_∇.p.add(s_in, s_out)`.
          let sampledOut ← StateT.lift <| OptionT.lift <|
            d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          -- Item 4(c)iv — append `('p', s_in, s_out)` to `tr`.
          let trace' := st.trace ++ [⟨dsPermQuery stateIn, sampledOut⟩]
          let trΔ' : TraceNabla T_H T_P StmtIn U :=
            { st.trΔ with p := TraceTableOps.add st.trΔ.p stateIn sampledOut }
          let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
            TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv stateIn sampledOut
          set { st with trace := trace', trΔ := trΔ', h_inv := h_inv' }
          return sampledOut

/-- CO25 §5.4 Item 4(e)iii.B — synthesize `s_out` from the first rate block and chain the
remaining rate blocks into `Cache_p` extensions.

Parses `ρ̂_i ‖ z` as exactly `L_V(i)` rate segments: the first becomes the rate half of the
sampled `s_out`; the rest seed paired states that extend `Cache_p`. -/
private def d2sSynthesizeStateFromRateBlocks
    (rateBlocks : List (Vector U SpongeSize.R)) :
    StateT
      (D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      (CanonicalSpongeState U × List (CanonicalSpongeState U × CanonicalSpongeState U)) := do
  let st ← get
  match rateBlocks with
  | [] => StateT.lift failure
  | _ =>
      -- Sample `s_C^{(k)} ←$ 𝒰(Σ^c)` for all `k = 0, …, L_V(i)-1` at once.
      let caps : List (Vector U SpongeSize.C) ← StateT.lift <| OptionT.lift <|
        d2sSampleCapacityList (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          rateBlocks.length
      let allStates :=
        (rateBlocks.zip caps).map fun
          (rc : Vector U SpongeSize.R × Vector U SpongeSize.C) =>
          mkStateFromSegments (U := U) rc.1 rc.2
      -- Since `rateBlocks` is not empty, `allStates` is not empty.
      match allStates with
      | [] => StateT.lift failure -- Unreachable if length > 0
      | synthesized_s_out :: extraStates =>
          -- Item 4(e)iii.E — extend `Cache_p` by chaining
          --   `(s_out, s^{(1)}), …, (s^{(L_V(i)-2)}, s^{(L_V(i)-1)})`.
          let extraPairs :=
            chainPairsFrom (U := U) synthesized_s_out extraStates
          pure (synthesized_s_out, st.cacheP ++ extraPairs)

/-- CO25 §5.4 Items 4(d)/4(e) — `BackTrack` returned `some (i, 𝕩, τ̂, α̂_1, …, α̂_i)`.

Splits on the codec-image predicate `∀ ι ∈ [i], α̂_ι ∈ Im(φ_ι)` (Item 4(d) vs 4(e), lines
1056/1059) and dispatches in paper order.

Paper Item 4(e) (in-image branch):
- (e)i  : `ρ̂_i := g_i(𝕩, τ̂, α̂_1, …, α̂_i)`  — issued **unconditionally**.
- (e)ii : `s_out := tr_∇.p.inlu(s_in)`, if any.
- (e)iii: else, sample `z`, reshape `ρ̂_i ‖ z` into `L_V(i)` rate blocks, synthesize `s_out`
  from the first block, chain the remainder into `Cache_p`, and `tr_∇.p.add(s_in, s_out)`.

The unconditional `g_i` query in (e)i is essential: `tr_i` (paper Item 3 of `D2SAlgo`, lived
externally to D2SQuery) makes the bridge `ψ⁻¹ ∘ f ∘ φ⁻¹` deterministic w.r.t. the encoded
query, so the cost of a repeat `gᵢ` call is a cache hit, not fresh randomness. -/
private def d2sHandleBacktrackSome
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    StateT
      (D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      (CanonicalSpongeState U) := do
  let st ← get
  if d2sInCodecImagePredicate -- all encoded-messages `α̂ᵢ` are in `Im(φᵢ)`
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut then
    -- Paper Item 4(e)i — **unconditional** `g_i` query: `ρ̂_i := g_i(𝕩, τ̂, α̂_1, …, α̂_i)`.
    -- Determinism w.r.t. the encoded key is enforced by `D2SAlgo`'s `tr_i` memo at the
    -- bridge layer (`d2sCodecBridgeImplMemo` in §5.4 D2SAlgo); same key ⇒ same response.
    let sampledRhoHat ← StateT.lift <| OptionT.lift <|
      d2sQueryG (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        backtrackOut.roundIdx backtrackOut.stmt backtrackOut.salt
        backtrackOut.encodedMessages
    -- Paper Item 4(e)ii — `s_out := tr_∇.p.inlu(s_in)`, if any.
    match TraceTableOps.inlu st.trΔ.p stateIn with
    | some recovered =>
        -- Paper Item 4(f) — append `('p', s_in, s_out)` to `tr`; Item 4(g) returns `s_out`.
        let trace' := st.trace ++ [⟨dsPermQuery stateIn, recovered⟩]
        let h_inv' : st.trΔ.IsSubsetOfQueryLog trace' :=
          TraceNabla.IsSubsetOfQueryLog_append_any st.h_inv ⟨dsPermQuery stateIn, recovered⟩
        set { st with trace := trace', h_inv := h_inv' }
        return recovered
    | none =>
        -- Paper Item 4(e)iii.A/B — sample `z`, concat `ρ̂_i ‖ z`, reshape into `L_V(i)`
        -- rate blocks.
        let rateBlocks ← StateT.lift <| OptionT.lift <|
          d2sRateBlocksFromChallenge
            (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
            (i := backtrackOut.roundIdx) sampledRhoHat
        -- Paper Item 4(e)iii.C/D/E — **sample capacities** for tail rate blocks, extend `Cache_p`,
        -- emit `s_out := (s_R^(0), s_C^(0))`.
        let (s_out, cache') ←
          d2sSynthesizeStateFromRateBlocks (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) rateBlocks.toList
        -- Paper Item 4(e)iii.F — `tr_∇.p.add(s_in, s_out)`
        let trace' := st.trace ++ [⟨dsPermQuery stateIn, s_out⟩]
        let trΔ' : TraceNabla T_H T_P StmtIn U :=
          { st.trΔ with p := TraceTableOps.add st.trΔ.p stateIn s_out }
        let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
          TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv stateIn s_out
        set { st with trace := trace', cacheP := cache', trΔ := trΔ', h_inv := h_inv' }
        return s_out
  else
    -- Paper Item 4(d) — tuple not in image; `tr_∇.p.inlu(s_in)` else fresh sample
    match TraceTableOps.inlu st.trΔ.p stateIn with
    | some recovered =>
        -- Item 4(d)i — cache hit
        let trace' := st.trace ++ [⟨dsPermQuery stateIn, recovered⟩]
        let h_inv' : st.trΔ.IsSubsetOfQueryLog trace' :=
          TraceNabla.IsSubsetOfQueryLog_append_any st.h_inv ⟨dsPermQuery stateIn, recovered⟩
        set { st with trace := trace', h_inv := h_inv' }
        return recovered
    | none =>
        -- Item 4(d)ii — fresh sample
        let sampledOut ← StateT.lift <| OptionT.lift <|
          d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        let trace' := st.trace ++ [⟨dsPermQuery stateIn, sampledOut⟩]
        let trΔ' : TraceNabla T_H T_P StmtIn U :=
          { st.trΔ with p := TraceTableOps.add st.trΔ.p stateIn sampledOut }
        let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
          TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv stateIn sampledOut
        set { st with trace := trace', trΔ := trΔ', h_inv := h_inv' }
        return sampledOut

/-- CO25 §5.4 Item 4 — forward-permutation (`p`) branch of `D2SQuery`.

Calls `BackTrack(tr, tr_∇, s_in)` (Item 4(a)) and dispatches:
- `.err` → abort (Item 4(b));
- `.noResult` → cache / `inlu` / sample fallback (Item 4(c));
- `.some backtrackOut` → codec-image dispatch (Items 4(d)/4(e)). -/
private def d2sHandleForwardPermQuery
    (stateIn : CanonicalSpongeState U) :
    StateT
      (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      (CanonicalSpongeState U) := do
  let st ← get
  match
      backTrack
        (δ := δ)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        st.trace st.trΔ st.h_inv stateIn (st.trace.length + 1) with
  | .err =>
      -- Paper Item 4(b): `err` branch aborts.
      StateT.lift failure
  | .noResult =>
      d2sHandleBacktrackNoResult (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn
  | .some backtrackOut =>
      d2sHandleBacktrackSome (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn backtrackOut

/-- CO25 §5.4 — `D2SQuery` one-step dispatcher over `d2sQueryOracles`: dispatches `h` (Item 2),
`p⁻¹` (Item 3), `p` (Item 4 with BackTrack branches 4(b)-4(g)). -/
def d2sQueryStep
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain) :
    StateT
        (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      ((duplexSpongeChallengeOracle StmtIn U).Range q) :=
  match q with
  | dsHashQuery stmt =>
      d2sHandleHashQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt
  | dsPermInvQuery stateOut =>
      d2sHandleInversePermQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateOut
  | dsPermQuery stateIn =>
      d2sHandleForwardPermQuery (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn

end StepImpl

/-! ### `d2sQueryImpl` — generalization with a caller-supplied `gᵢ` realization

`d2sQueryImpl` parameterizes the D2SQuery simulator over an arbitrary
`challengeSpec`-targeted `gᵢ`-implementation `gImpl`.  The result lives in
`StateT _ (AbortComp (D2SChallengePlusUnitOracle challengeSpec))`, which is the
shape `KeyLemma.hybridGame` consumes.

The pipeline reuses `d2sQueryStep` for the §5.4 Items 2–4 branch tree and translates the
resulting `d2sQueryOracles = gSpec + ((Unit →ₒ U) + unifSpec)` queries through
`gImpl + auxImpl`, where `auxImpl` injects the `(Unit →ₒ U) + unifSpec` side into the
`D2SChallengePlusUnitOracle challengeSpec` target unchanged. -/

section WithOracle

variable {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- CO25 §5.4 — `D2SQuery` simulator parameterized over a `gᵢ` realization `gImpl` and an
auxiliary `(Unit →ₒ U) + unifSpec` realization `auxImpl`, both landing in an arbitrary monad
`m` with `Alternative` (for the §5.4 Item 4(b) `err` abort branch); reuses `d2sQueryStep`
for Items 2-4.

Single interface used by:
- `d2sAlgo` (Phase 14): `m = StateT (D2SAlgoMemo …) (AbortComp …)`,
  `gImpl = d2sCodecBridgeImplMemo` — threads the paper Item 3 `tr_i` memo;
  `auxImpl` lifts `(Unit →ₒ U) + unifSpec` queries through to the outer
  `D2SChallengePlusUnitOracle`.
- §5.8 hybrid games (`hybridGame`): `m = OptionT (OracleComp _)`,
  `gImpl` varies per hybrid (`g`, `e`, `f`, …); `auxImpl` lifts to the same outer spec.
- `lemma5_8SigmaTraceDist` (BadEvents): `m = OptionT ProbComp`, `auxImpl` resolves
  `(Unit →ₒ U) + unifSpec` directly via `d2sUnitSampleImpl + QueryImpl.id' unifSpec`. The
  `OptionT`-abort halts the §5.8 experiment (paper line 1417); the partial trace at the moment
  of abort is preserved by `BadEvents.lemma5_8ProjectedTraceDistAbortable`. -/
def d2sQueryImpl
    {m : Type → Type} [Monad m] [Alternative m]
    (gImpl :
      QueryImpl (gSpec (U := U) StmtIn pSpec δ) m)
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) m) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT
        (D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        m) :=
  fun (q : (duplexSpongeChallengeOracle StmtIn U).Domain) st => do
    let combinedImpl :
        QueryImpl
          (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) m :=
      gImpl + auxImpl
    let pairOpt ←
      simulateQ combinedImpl
        (((d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run st).run)
    match pairOpt with
    | none => failure
    | some ⟨query_answer, newState⟩ => pure ⟨query_answer, newState⟩

end WithOracle

end D2SQuery

/-! ## Codec bridge `gᵢ = ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹`

CO25 §5.4 Eq. 16 — Translates `d2sQueryOracles` into `fsChallengeOracle`-based queries:
- `.inl` (`gSpec`): `φ⁻¹` (decode prefix) → `f` (query FS oracle) → `ψ⁻¹` (uniform preimage)
- `.inr` (`(Unit →ₒ U) + unifSpec`): identity passthrough

The `OptionT` layer models `φ⁻¹` parse failure (⊥ on malformed encoded-message prefixes). -/

section CodecBridge

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
variable [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  {Salt : Type} [SaltCodec U δ Salt]

/-- CO25 §5.4 Eq. 16 — `gᵢ`-summand of the codec bridge: `ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹`.

Given a `gSpec` query `(i, 𝕩, τ̂, α̂₁, …, α̂ᵢ)`:
1. `φ⁻¹`: parse `α̂_{<i}` → `α_{<i}` via `hybEncodedMessagesBefore?` (⊥ on failure)
2. `f`: query `fᵢ(𝕩, bin(τ̂), α₁, …, αᵢ)` → `ρᵢ ∈ ℳ_{V,i}` via `fsChallengeOracle`
   keyed at the pre-encoded salt `Salt` (paper's `{0,1}^{δ⋆}`; bridge =
   `SaltCodec.encode = bin`)
3. `ψ⁻¹`: sample `ρ̂ᵢ ← 𝒰(ψᵢ⁻¹(ρᵢ))` via `uniformDeserializePreimage` -/
noncomputable def d2sCodecBridgeImpl :
    QueryImpl (gSpec (U := U) StmtIn pSpec δ)
      (OptionT (OracleComp
        (D2SChallengePlusUnitOracle (U := U)
          (fsChallengeOracle (StmtIn × Salt) pSpec)))) :=
  fun q =>
    let roundIdx : pSpec.ChallengeIdx := q.1
    let stmt : StmtIn := q.2.1
    let salt : Vector U δ := q.2.2.1
    let encodedMessages : pSpec.EncodedMessagesBefore U roundIdx.1.castSucc := q.2.2.2
    do
      -- Step 1 (`φ⁻¹`) — decode prover prefix: `(α_1, …, α_{i-1}) := φ⁻¹(α̂_1, …, α̂_{i-1})`;
      -- abort if any block lies outside `Im(φ_ι)`.
      let messagesBefore ←
        match hybEncodedMessagesBefore?
            (pSpec := pSpec) (U := U) roundIdx encodedMessages with
        | some messagesBefore => pure messagesBefore
        | none => failure
      -- Step 2 (`f`) — query the FS oracle at the binarized salt:
      --   `ρ_i := f_i(𝕩, bin(τ̂), α_1, …, α_{i-1}) ∈ ℳ_{V,i}`, with `bin = SaltCodec.encode`.
      let challenge ←
        OptionT.lift <|
          (show OracleComp
              (D2SChallengePlusUnitOracle (U := U)
                (fsChallengeOracle (StmtIn × Salt) pSpec))
              (pSpec.Challenge roundIdx) from
            query
              (spec := D2SChallengePlusUnitOracle (U := U)
                (fsChallengeOracle (StmtIn × Salt) pSpec))
              (.inl ⟨roundIdx,
                ((stmt, SaltCodec.encode (Salt := Salt) salt), messagesBefore)⟩))
      -- Step 3 (`ψ⁻¹`) — uniform preimage: `ρ̂_i ←$ ψ_i⁻¹(ρ_i) ⊆ Σ^{ℓ_V(i)}`.
      OptionT.lift <|
        uniformDeserializePreimage
          (pSpec := pSpec) (U := U)
          (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)
          challenge

end CodecBridge

/-! ## `D2SAlgoMemo` — `tr_i` memo for the codec bridge (CO25 §5.4 D2SAlgo Item 3)

The unconditional `gᵢ` query in `D2SQuery` Item 4(e)i (see `d2sHandleBacktrackSome`) means
that two adversary queries with the same `BacktrackOutput` produce two `gᵢ` queries with the
same encoded key in the resulting `OracleComp` tree. Without a memo at the bridge layer, the
randomness in `uniformDeserializePreimage` (the `ψ⁻¹` step) would give them different
responses, violating CO25 §5.4 D2SAlgo Item 3's determinism on repeat keys.

`D2SAlgoMemo` is the `tr_i : (i, 𝕩, τ̂, α̂_1, …, α̂_i) ↦ ρ̂_i` table the paper threads through
the bridge as a `StateT` layer over `d2sCodecBridge`. On a cache hit, the stored `ρ̂_i` is
returned; on a miss, `d2sCodecBridgeImpl` is invoked and the resulting `ρ̂_i` is appended. -/

section D2SAlgoMemo

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
variable [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  {Salt : Type} [SaltCodec U δ Salt]

/-- CO25 §5.4 D2SAlgo Item 3 — entry of the bridge-layer memo `tr_i`, keyed on the
encoded `gᵢ` query `(i, 𝕩, τ̂, α̂_1, …, α̂_i)` with **binarized** salt `τ̂ := bin(τ) ∈ Salt`
(paper `{0,1}^{δ⋆}`; see Item 3c/3f), carrying the sampled encoded response
`ρ̂_i ∈ Σ^{ℓ_V(i)}` (the `ψ⁻¹` preimage of the basic-FS challenge). -/
structure D2SAlgoMemoEntry
    (StmtIn : Type) (U : Type) (δ : ℕ) (Salt : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    [HasMessageSize pSpec] [HasChallengeSize pSpec] where
  roundIdx : pSpec.ChallengeIdx
  stmt : StmtIn
  salt : Salt
  encodedMessages : pSpec.EncodedMessagesBefore U roundIdx.1.castSucc
  response : Vector U (challengeSize (pSpec := pSpec) roundIdx)

/-- CO25 §5.4 D2SAlgo Item 3 — `tr_i` table, indexed by `gᵢ`-query keys with binarized salt. -/
abbrev D2SAlgoMemo (StmtIn : Type) (U : Type) (δ : ℕ) (Salt : Type)
    {n : ℕ} (pSpec : ProtocolSpec n)
    [HasMessageSize pSpec] [HasChallengeSize pSpec] :=
  List (D2SAlgoMemoEntry StmtIn U δ Salt pSpec)

instance [HasMessageSize pSpec] [HasChallengeSize pSpec] :
    Inhabited (D2SAlgoMemo StmtIn U δ Salt pSpec) := ⟨[]⟩

open Classical in
/-- CO25 §5.4 D2SAlgo Item 3 — `tr_i[(i, 𝕩, τ̂, α̂_1, …, α̂_i)]`, returning `some ρ̂_i` if the
encoded key was previously stored. Salt key is the **binarized** `τ̂ : Salt` (paper Item 3c). -/
noncomputable def lookupD2SAlgoMemo
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (salt : Salt)
    (encodedMessages : pSpec.EncodedMessagesBefore U i.1.castSucc) :
    Option (Vector U (challengeSize (pSpec := pSpec) i)) :=
  memo.foldl (init := none) fun acc entry =>
    acc.orElse fun _ =>
      if hRound : entry.roundIdx = i then by
        subst hRound
        exact
          if entry.stmt = stmt ∧ entry.salt = salt ∧ entry.encodedMessages = encodedMessages
            then some entry.response
            else none
      else none

/-- CO25 §5.4 D2SAlgo Item 3 — append a fresh `(key, ρ̂_i)` entry to `tr_i`. -/
def insertD2SAlgoMemo
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (entry : D2SAlgoMemoEntry StmtIn U δ Salt pSpec) :
    D2SAlgoMemo StmtIn U δ Salt pSpec :=
  memo ++ [entry]

/-- CO25 §5.4 D2SAlgo Item 3 — memoized `gᵢ`-summand of the codec bridge.

Wraps `d2sCodecBridgeImpl` in a `StateT (D2SAlgoMemo …)` layer. On `lookupD2SAlgoMemo` hit,
returns the stored response without resampling `ψ⁻¹`; on miss, invokes the unmemoized bridge
and appends the result via `insertD2SAlgoMemo`. -/
noncomputable def d2sCodecBridgeImplMemo :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (fsChallengeOracle (StmtIn × Salt) pSpec)
      (D2SAlgoMemo StmtIn U δ Salt pSpec) :=
  fun q =>
    let roundIdx : pSpec.ChallengeIdx := q.1
    let stmt : StmtIn := q.2.1
    let salt : Vector U δ := q.2.2.1
    let encodedMessages : pSpec.EncodedMessagesBefore U roundIdx.1.castSucc := q.2.2.2
    -- Paper Item 3c — binarize `τ̂ := bin(τ) ∈ Salt` once before memo lookup/insert.
    let encodedSalt : Salt := SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) salt
    do
      let memo ← get
      match lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
          memo roundIdx stmt encodedSalt encodedMessages with
      -- Item 3 cache hit: `tr_i[(i, 𝕩, τ̂, α̂_1, …, α̂_i)] = some ρ̂_i` ⇒ return stored `ρ̂_i`.
      | some response => pure response
      | none =>
          -- Item 3 cache miss: invoke `ψ⁻¹∘f∘φ⁻¹` to sample `ρ̂_i`,
          --   then `tr_i := tr_i ∪ {(i, 𝕩, τ̂, α̂_1, …, α̂_i) ↦ ρ̂_i}`.
          let response ←
            (d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
              (Salt := Salt) q :
              OptionT (OracleComp _) _)
          modify (fun m =>
            insertD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec) m
              { roundIdx := roundIdx, stmt := stmt, salt := encodedSalt,
                encodedMessages := encodedMessages, response := response })
          pure response

end D2SAlgoMemo

/-! ## `d2fProverRaw` — shared `𝒜^{D2SQuery^{gImpl}}` inner pipeline

Raw post-`simulateQ` shape of the paper Eq. 16 RHS prover loop, keeping the two state layers
(`D2SQueryState`, inner `M`) so different call sites can project differently:
- `D2FQueryProver` projects via `Prod.fst ∘ Prod.fst` — drops both states, used by Hyb_4.
- `KeyLemma.hybridGame` keeps the triple — uses `D2SQueryState` for the verifier-half
  independent run and threads `M` (paper Item 3 `tr_i`) from prover to verifier, matching
  CO25 §5.4 D2SAlgo Item 3 ("`tr_i` is global to a single run").

Polymorphic over `M` (`PUnit` for Hyb_1 / Hyb_2's inline `g` / `e` realizations;
`D2SAlgoMemo …` for Hyb_3 / Hyb_4's memoized `gᵢ` bridge) and `challengeSpec` (`gSpec` /
`eSpec` / `fsChallengeOracle (StmtIn × Salt) pSpec` per-hybrid). Single source of truth for
the `outerImpl := QueryImpl.addLift (QueryImpl.id oSpec) (d2sQueryImpl gImpl auxImpl)`
construction. -/

section D2FProverRaw

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
variable {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- CO25 §5.4 — Outer-spec `QueryImpl` for the paper Eq. 16 RHS simulator:
`id_oSpec ⊕ D2SQuery^{gImpl}`. Reused by `d2fProverRaw` and by `KeyLemma.hybridGame`'s
verifier-half (which re-runs the same `QueryImpl` against the honest verifier with the
shared `M` state threaded in — paper §5.4 D2SAlgo Item 3, `tr_i` global to a single run). -/
noncomputable def d2fOuterImpl
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type}
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M) :
    QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StateT (D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (StateT M
          (OptionT
            (OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec))))) :=
  QueryImpl.addLift (QueryImpl.id oSpec)
    (d2sQueryImpl (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (gImpl := gImpl)
      (auxImpl := fun aux =>
        query
          (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
          (Sum.inr aux)))

/-- CO25 §5.4 Eq. 16 RHS — generic raw pipeline for `comp^{D2SQuery^{gImpl}}`, keeping the
post-run `D2SQueryState` and inner `M`.

Generalizes `d2fProverRaw` from prover-only to any wide-DSFS computation. Two call sites:
- **Prover**: `d2fProverRaw gImpl 𝒜 = d2fRaw gImpl 𝒜 default` (fresh inner state).
- **Verifier** (in `KeyLemma.hybridGame`): `d2fRaw gImpl verifyCompWide memo₁`
  (threads the prover's post-run `M` as the verifier's initial state, matching CO25 §5.4
  D2SAlgo Item 3 that `tr_i` is global to a single run). -/
noncomputable def d2fRaw
    {α : Type}
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (comp : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (initM : M) :
    AbortComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
        ((α × D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ×
          M) :=
  (((simulateQ (d2fOuterImpl (T_H := T_H) (T_P := T_P) gImpl) comp).run default).run initM)

end D2FProverRaw

/-! ## `D2FQueryProver` + `d2sAlgo` — paper Eq. 16 split

Paper §5.4 D2SAlgo (lines 1121-1138) decomposes into two structurally distinct pieces:

- **Items 1-3** = the inner prover loop running `𝒜^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}` (paper Eq. 16
  RHS). Output salt stays on the DS side (`Vector U δ`, paper `Σ^δ`). Mirrored in Lean by
  `D2FQueryProver` returning `DSSaltedProof`.
- **Items 4-6** = parse `(τ, αᵢ)`, set `τ̌ := bin(τ) ∈ {0,1}^{δ⋆}`, repackage as
  `π̌ := (τ̌, αᵢ)`. This is a pure post-processing wrapper that re-encodes the salt to the
  FS-standard side. Mirrored in Lean by `d2sAlgo`, which applies `SaltCodec.encode = bin`
  to the salt-component of `D2FQueryProver`'s output, returning `FSSaltedProof`.

The split makes paper Figure 4 lines 2-3 explicit at the type level:
- Hyb_3 prover surface `𝒫̃^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}` outputs DS-form salt → `D2FQueryProver`.
- Hyb_4 prover surface `D2SAlgo^f(𝒫̃)` outputs FS-std-form salt → `d2sAlgo`.

Both share the same oracle-first pipeline:
1. `d2sQueryImpl` simulates the duplex-sponge challenge oracle into the encoded spec
   `d2sQueryOracles = gSpec + (Unit + unifSpec)`.
2. `d2sCodecBridgeImplMemo` translates `gSpec` queries into basic-FS `fsChallengeOracle` queries
   with `uniformDeserializePreimage`, threading the `tr_i` memo (CO25 §5.4 D2SAlgo Item 3) so
   that repeat encoded keys reuse the cached `ρ̂_i`; the `(Unit + unifSpec)` summand passes
   through unchanged.
3. The result lives in the basic-FS target spec
   `oSpec + D2SChallengePlusUnitOracle fsChallengeOracle`, matching `D2SAlgo`'s return monad.
   Both intermediate states (`D2SQueryState`, `D2SAlgoMemo`) are discarded. -/

section D2SAlgo

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
variable {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)]
  [∀ i, DecidableEq (pSpec.Challenge i)]
  {Salt : Type} [SaltCodec U δ Salt]

/-- CO25 §5.4 Eq. 16 RHS — the inner prover surface `𝒜^{D2SQuery^{ψ⁻¹∘f∘φ⁻¹}}` (paper
D2SAlgo Items 1-3, lines 1121-1135). Runs `𝒜` with its duplex-sponge `(h, p, p⁻¹)` queries
answered by `D2SQuery` under the codec-bridged oracle `ψ⁻¹∘f∘φ⁻¹`, where `f` is the salted
FS challenge oracle keyed at `(StmtIn × Salt)`. Salt is bridged via `SaltCodec.encode = bin`
inside `d2sCodecBridgeImpl` at every `gᵢ`-query; the `tr_i` memo (Item 3) is threaded via
`d2sCodecBridgeImplMemo`.
**Output salt stays on the DS side (`Vector U δ`, paper `Σ^δ`)** — this is the paper-Hyb_3
prover surface, before the bin-repackaging of D2SAlgo Items 4-6. -/
noncomputable def D2FQueryProver
    (𝒜 : MaliciousProver oSpec pSpec StmtIn U δ) :
    AbortComp (oSpec +
      D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ) :=
  -- Shared raw pipeline: id_oSpec ⊕ D2SQuery^{tr_i-memoized ψ⁻¹∘f∘φ⁻¹}, single `simulateQ`,
  -- both states `default`-initialized. Strip `D2SQueryState` and `D2SAlgoMemo` at the
  -- boundary; `none` propagates as `OptionT` abort.
  Prod.fst <$> Prod.fst <$> -- DTOP the states (from the two nested StateT)
    (d2fRaw (T_H := T_H) (T_P := T_P)
      (gImpl := d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt))
      𝒜 default)

/-- CO25 §5.4 Eq. 16 LHS — full `D2SAlgo^f(𝒜)` (paper Items 1-6, lines 1121-1138). Thin
wrapper over `D2FQueryProver` (Items 1-3) that applies the paper's Items 4-6 post-processing:
parse the inner output `(τ, αᵢ)` with `τ ∈ Σ^δ`, set `τ̌ := bin(τ) = SaltCodec.encode τ`,
and repackage as `(τ̌, αᵢ) : FSSaltedProof`.
**Output salt is the pre-encoded FS-std type `Salt` (paper `{0,1}^{δ⋆}`)** — this is the
paper-Hyb_4 prover surface, ready to be consumed by `𝒱_std^f` (`Verifier.singleSaltFiatShamir`)
without any further bin step. -/
noncomputable def d2sAlgo
    (𝒜 : MaliciousProver oSpec pSpec StmtIn U δ) :
    AbortComp (oSpec +
      D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec))
      (StmtIn × FSSaltedProof pSpec Salt) := do
  -- Items 1-3 — run inner prover to obtain `(𝕩, (τ, (α̂_1, …, α̂_n))) ∈ StmtIn × DSSaltedProof`.
  let ⟨stmt, ⟨τ, msgs⟩⟩ ← D2FQueryProver (Salt := Salt) (T_H := T_H) (T_P := T_P) 𝒜
  -- Items 4-6 — re-encode salt: `τ̌ := bin(τ) ∈ {0,1}^{δ⋆}`; emit `(𝕩, (τ̌, α̂))`.
  return ⟨stmt, ⟨SaltCodec.encode (Salt := Salt) τ, msgs⟩⟩

end D2SAlgo

end

end DuplexSpongeFS.ProverTransform
