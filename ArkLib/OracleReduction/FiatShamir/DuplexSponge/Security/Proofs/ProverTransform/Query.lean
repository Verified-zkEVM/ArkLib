/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.Backtrack
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.D2SRateOnlyCache
public import ArkLib.VCVioStaging.OracleComp.QueryTracking.AbortZeroBound
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.Lookahead
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.TraceDataStructures
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.TraceTransform
public import ArkLib.VCVioStaging.OracleComp.QueryTracking.QueryBound

/-!
# Prover transformation: the `D2SQuery` oracle wrapper

[CO25, §5.4 Item 4]: the `D2SQuery` state, samplers, branch handlers, `d2sQueryStep` and
`d2sQueryImpl`, shared masked-query accounting, and the §5.8 step guard.
-/

@[expose] public section

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

variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-!
The wrapper stores only a keyed, rate-only continuation. Its capacity is sampled when a
permutation query consumes the tail; no latent full-state permutation pair is stored in `Cache_p`.
-/

variable (StmtIn U pSpec δ T_H T_P) in
/-- **[CO25, §5.4]** Internal mutable state of the rate-only `D2SQuery` wrapper.

`rateCacheP` maps a full input state to a pending suffix of rate blocks.  It contains no output
capacity.  `trΔ` is the deduplicated lookup index used by `BackTrack`.  The stronger exact-mirror
lemmas remain available in `TraceDataStructures` and are introduced with the monitored Lemma 5.8
state, rather than multiplying every raw Claim 5.22/5.23 state update. -/
structure D2SQueryState where
  trace : QueryLog (duplexSpongeOracle StmtIn U) := []
  rateCacheP : List (RateOnlyCacheEntry (U := U)) := []
  trΔ : TraceNabla T_H T_P StmtIn U :=
    ⟨TraceTableOps.empty, TraceTableOps.empty⟩
  h_inv : trΔ.IsSubsetOfQueryLog trace
  _phantom : Option (BacktrackOutput
    (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := none

instance : Inhabited (D2SQueryState StmtIn pSpec U δ T_H T_P) :=
  ⟨{ h_inv := TraceNabla.IsSubsetOfQueryLog_empty_nil }⟩

/-- Executable approximation of Item 4(d)/(e) tuple-image branching, tightened with
`BackTrack`-shape checks and verifier message-block length sanity. -/
def proverMessageInSerializeImage
    (msgIdx : pSpec.MessageIdx)
    (encoded : Vector U (proverMessageSize msgIdx)) : Bool := by
  exact decide (∃ msg : pSpec.Message msgIdx, Serialize.serialize msg = encoded)

/-- Executable check for the paper branch condition
`∀ ι ≤ i, α̂_ι ∈ Im(φ_ι)` on one parsed `BackTrack` output. -/
def backtrackOutputProverMessagesInImage
    (inImage : (msgIdx : pSpec.MessageIdx) → Vector U (proverMessageSize msgIdx) → Bool)
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Bool :=
  let before : List pSpec.MessageIdx := proverMessageIdxListBefore (pSpec := pSpec) out.roundIdx
  before.attach.all fun ⟨j, hj⟩ =>
    let hlt : j.1 < out.roundIdx.1 := of_decide_eq_true (List.mem_filter.mp hj).2
    inImage j (out.encodedProverMessages ⟨j, hlt⟩)

/-- **[CO25, §5.4]** Items 4(d)/(e) — paper predicate `∀ ι ∈ [i], α̂_ι ∈ Im(φ_ι)`, decided as a
`Serialize`-image check on the recovered encoded messages. -/
noncomputable def d2sInCodecImagePredicate
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Bool :=
  backtrackOutputProverMessagesInImage
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
    (inImage := proverMessageInSerializeImage (pSpec := pSpec) (U := U))
    (out := out)

omit [SpongeUnit U] [SpongeSize] [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] in
/-- **Obligation B (§5.8).**  The §5.4 Item 4(d)/(e) codec-image gate implies the codec
bridge's `φ⁻¹` parse (`hybEncodedProverMessagesBefore?`) succeeds on the gated `gᵢ`-query's message
prefix — so the `OptionT`-abort branch of `d2sCodecBridgeImpl` (and of
`d2sCodecBridgeParseAndQueryF`) is unreachable from `D2SQuery`-issued `gᵢ`-queries. -/
lemma hybEncodedProverMessagesBefore?_isSome_of_d2sInCodecImagePredicate
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (h : d2sInCodecImagePredicate (StmtIn := StmtIn) (pSpec := pSpec) (U := U) out = true) :
    (hybEncodedProverMessagesBefore? (pSpec := pSpec) (U := U)
      out.roundIdx out.encodedProverMessages).isSome := by
  apply TraceTransform.hybEncodedProverMessagesBefore?_isSome
  intro j hj
  unfold d2sInCodecImagePredicate backtrackOutputProverMessagesInImage at h
  rw [List.all_eq_true] at h
  have hmem : j ∈ Backtrack.proverMessageIdxListBefore (pSpec := pSpec) out.roundIdx :=
    Backtrack.mem_proverMessageIdxListBefore_of_lt (pSpec := pSpec) j hj
  have hblock := h ⟨j, hmem⟩ (List.mem_attach _ _)
  simp only [proverMessageInSerializeImage] at hblock
  exact of_decide_eq_true hblock

/-- **[CO25, §5.4]** `𝒰(Σ)` realization of `Unit →ₒ U` in `ProbComp`; used by §5.4 fresh-sample
branches (Items 2(b), 3(b), 4(c)iii, 4(e)iiiC). -/
def d2sUnitSampleImpl [instSampleable : SampleableType U] :
    QueryImpl (Unit →ₒ U) ProbComp :=
  fun
  | () => uniformSample _ (h := instSampleable)

end D2SQueryState

section D2SVerifierMessagePlusUnit

variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- **[CO25, §5.8]** Finite preimage set of a verifier-message decoder `ψᵢ`.

`{α̂ ∈ Σ^{ℓ_V(i)} | ψᵢ(α̂) = α}` for a target verifier message `α : ℳ_{V,i}`. Backs the uniform
preimage sampler `uniformDeserializePreimage`; surjectivity of `ψᵢ` (`Codec.decode_surjective`)
guarantees nonemptiness. -/
noncomputable def deserializePreimageFinset
    {i : pSpec.ChallengeIdx}
    [Fintype U]
    [Fintype (pSpec.Challenge i)] [DecidableEq (pSpec.Challenge i)]
    (verifierMessage : pSpec.Challenge i) :
    Finset (Vector U (verifierMessageSize (pSpec := pSpec) i)) := by
  let _ : Fintype (Vector U (verifierMessageSize (pSpec := pSpec) i)) :=
    Fintype.ofEquiv (Fin (verifierMessageSize (pSpec := pSpec) i) → U) Equiv.rootVectorEquivFin.symm
  exact (Finset.univ : Finset (Vector U (verifierMessageSize (pSpec := pSpec) i))).filter
    fun encoded => Deserialize.deserialize encoded = verifierMessage

omit [SpongeUnit U] [SpongeSize] [DecidableEq U] [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- Membership in the `ψᵢ⁻¹` preimage finset is exactly the deserialization fiber.

The single source for this fact (unified at polish from a `Reachability.lean` copy and a
`CodecBias.lean` copy): the `codec.decode`-spelled corollary
`mem_deserializePreimageFinset_decode` (`CodecBias.lean`) follows via the
`Codec.instDeserializeChallenge` bridge `Deserialize.deserialize = codec.decode i`, which
holds definitionally. -/
lemma mem_deserializePreimageFinset
    {i : pSpec.ChallengeIdx}
    [Fintype U]
    [Fintype (pSpec.Challenge i)] [DecidableEq (pSpec.Challenge i)]
    (verifierMessage : pSpec.Challenge i)
    (x : Vector U (verifierMessageSize (pSpec := pSpec) i)) :
    x ∈ deserializePreimageFinset (pSpec := pSpec) (U := U) verifierMessage
      ↔ Deserialize.deserialize x = verifierMessage := by
  simp [deserializePreimageFinset]

/-- Sample a uniformly random element from a non-empty list using the `unifSpec` branch. -/
def sampleFromList {α κ : Type} {verifierMessageSpec : OracleSpec κ}
    (l : List α) (hl : l ≠ []) :
    OracleComp (D2SVerifierMessagePlusUnitOracle (U := U) verifierMessageSpec) α := do
  let idxRaw ← query
    (spec := D2SVerifierMessagePlusUnitOracle (U := U) verifierMessageSpec)
    (.inr (.inr (l.length - 1))) -- from unifSpec
  let idx : Fin l.length := ⟨idxRaw.1, by
    have hlen_pos : 0 < l.length := List.length_pos_iff_ne_nil.mpr hl
    have hlen_eq : (l.length - 1) + 1 = l.length := Nat.sub_add_cancel (Nat.succ_le_of_lt hlen_pos)
    simpa [hlen_eq] using idxRaw.2⟩
  pure (l.get idx)

/-- **[CO25, §5.4]** (also used in §5.8) Uniform `ψᵢ⁻¹` preimage sampler: samples `α̂ ←$ ψᵢ⁻¹(α)` by
toListing `deserializePreimageFinset α` and indexing via `unifSpec` -/
noncomputable def uniformDeserializePreimage
    {κ : Type} {verifierMessageSpec : OracleSpec κ}
    [Fintype U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    {i : pSpec.ChallengeIdx}
    (verifierMessage : pSpec.Challenge i) :
    OracleComp (D2SVerifierMessagePlusUnitOracle (U := U) verifierMessageSpec)
      (Vector U (verifierMessageSize (pSpec := pSpec) i)) := do
  have hpreimages_nonempty :
      (deserializePreimageFinset (pSpec := pSpec) (U := U) verifierMessage).Nonempty := by
    rcases codec.decode_surjective i verifierMessage with ⟨encoded, hencoded⟩
    have hencoded' : Deserialize.deserialize encoded = verifierMessage := hencoded
    exact ⟨encoded, by simp [deserializePreimageFinset, hencoded']⟩
  let preimages := (deserializePreimageFinset (pSpec := pSpec) (U := U) verifierMessage).toList
  have hpreimages_ne : preimages ≠ [] := by
    simpa [preimages] using hpreimages_nonempty.toList_ne_nil
  sampleFromList preimages hpreimages_ne

omit [SpongeUnit U] [SpongeSize] [DecidableEq U] [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- Every reachable output of the preimage sampler decodes to its prescribed verifier message. -/
lemma deserialize_of_mem_support_uniformDeserializePreimage
    {κ : Type} {verifierMessageSpec : OracleSpec κ} [Fintype U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    {i : pSpec.ChallengeIdx} (verifierMessage : pSpec.Challenge i)
    (x : Vector U (verifierMessageSize (pSpec := pSpec) i))
    (hx : x ∈ support (uniformDeserializePreimage (U := U)
      (verifierMessageSpec := verifierMessageSpec) verifierMessage)) :
    Deserialize.deserialize x = verifierMessage := by
  unfold uniformDeserializePreimage sampleFromList at hx
  obtain ⟨idx, _, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
  obtain rfl := (mem_support_pure_iff _ _).mp hx
  exact (mem_deserializePreimageFinset _ _).mp (Finset.mem_toList.mp (List.get_mem _ _))

end D2SVerifierMessagePlusUnit

/-! ## Oracle-first `D2SQuery` API

[CO25, §5.4] — `D2SQuery` oracle spec and direct-query helpers.

`d2sQueryOracles = gSpec + ((Unit →ₒ U) + unifSpec)` where
`gSpec = gSpec StmtIn pSpec δ` is the `gᵢ`-family oracle.
All sampling (`𝒰(Σ^c)`, `𝒰(Σ^{r+c})`, etc.) goes through `Unit →ₒ U`;
the `gᵢ` query is a single `.inl` injection into the sum spec. -/
section D2SQuery

variable [DecidableEq StmtIn] [DecidableEq U] [Fintype U]

/-- **[CO25, §5.4]** `D2SQuery` oracle spec: `gSpec + ((Unit →ₒ U) + unifSpec)`.

- `gSpec` = `gSpec` — the `gᵢ`-family (Item 4(e)i)
- `Unit →ₒ U` — `𝒰(Σ)` for sampling `s_{C,out}`, `s_in`, `s_out`, etc.
- `unifSpec` — `Fin`-sampling for `ψᵢ⁻¹` preimage selection -/
abbrev d2sQueryOracles :=
  D2SVerifierMessagePlusUnitOracle
    (U := U) (verifierMessageSpec := gSpec (U := U) StmtIn pSpec δ)

/-- **[CO25, §5.4]** Item 4(e)i — Query `gᵢ(𝕩, τ̂, α̂₁, …, α̂ᵢ) → ρ̂ᵢ ∈ Σ^{ℓ_V(i)}`.

Direct `.inl` injection into `d2sQueryOracles`. -/
def d2sQueryG
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (salt : Vector U δ)
    (encodedProverMessages : pSpec.EncodedProverMessagesBefore U i.1.castSucc) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (Vector U (verifierMessageSize (pSpec := pSpec) i)) :=
  query (spec := d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
    (Sum.inl ⟨i, (stmt, salt, encodedProverMessages)⟩)

/-- **[CO25, §5.4]** Sample `u ← 𝒰(Σ)` via `Unit →ₒ U`. -/
def d2sSampleUnit :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) U :=
  query (spec := d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
    (Sum.inr (.inl ()))

/-- Sample `m` consecutive units; helper for `d2sSampleVector`. -/
def d2sSampleArrayExact :
    (m : Nat) →
      OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
        {xs : Array U // xs.size = m}
  | 0 => pure ⟨#[], rfl⟩
  | m + 1 => do
      let u ← d2sSampleUnit (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      let ⟨xs, hxs⟩ ← d2sSampleArrayExact m
      pure ⟨xs.push u, by simp [hxs]⟩

/-- Sample a length-`m` vector of units (`m` consecutive `𝒰(Σ)` draws).

De-privatized (visibility only) so that native source-effect proofs in `Hyb3Hyb4.NativeEffects`
can transport
the §5.4 samplers through the memoized codec bridge. -/
def d2sSampleVector (m : Nat) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (Vector U m) := do
  let ⟨xs, hxs⟩ ← d2sSampleArrayExact
    (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m
  pure ⟨xs, hxs⟩

/-- **[CO25, §5.4]** Item 2(b) — Sample `s_{C,out} ← 𝒰(Σ^c)`. -/
def d2sSampleCapacity :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (Vector U SpongeSize.C) :=
  d2sSampleVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) SpongeSize.C

/-- **[CO25, §5.4]** Items 3(b)/4(d)ii — Sample `s ← 𝒰(Σ^{r+c})`. -/
def d2sSampleState :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (CanonicalSpongeState U) :=
  d2sSampleVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) SpongeSize.N

/-- **[CO25, §5.4]** Item 4(e)iiiB — Split units into `m` rate blocks of size `r`,
padding the final partial block with fresh `𝒰(Σ)` samples. -/
def d2sRateBlocksFromUnitsM :
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

/-- **[CO25, §5.4]** Item 4(e)iiiB — Reshape `ρ̂ᵢ ∈ Σ^{ℓ_V(i)}` into `L_V(i)` rate blocks,
padding the final partial block with fresh `𝒰(Σ)` samples. -/
def d2sRateBlocksFromVerifierMessage
    {i : pSpec.ChallengeIdx}
    (verifierMessage : Vector U (verifierMessageSize (pSpec := pSpec) i)) :
    OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (Vector (Vector U SpongeSize.R) (pSpec.Lᵥᵢ i)) := do
  let ⟨blocks, hBlocks⟩ ← d2sRateBlocksFromUnitsM (U := U) (StmtIn := StmtIn)
    (pSpec := pSpec) (δ := δ) (pSpec.Lᵥᵢ i) verifierMessage.toList
  pure ⟨blocks.toArray, by simp [hBlocks]⟩

/-! ### `d2sQueryStep` / `d2sQueryImpl`

[CO25, §5.4] — Wires the Items 2-4 branch tree to the `d2sQueryOracles` direct-query helpers.
Sampling goes through `Unit →ₒ U`; `gᵢ` evaluation goes through `d2sQueryG`. -/

section StepImpl

variable {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- **[CO25, §5.4]** Item 2 — hash-oracle (`h`) branch of `D2SQuery`.

Paper steps: lookup `tr_∇.h.inlu(𝕩)`; on `⟂`, sample `s_{C,out} ← 𝒰(Σ^c)` and
call `tr_∇.h.add(𝕩, s_{C,out})`; always append `('h', 𝕩, s_{C,out})` to `tr`. -/
def d2sHandleHashQuery
    (stmt : StmtIn) :
    StateT
      (D2SQueryState StmtIn pSpec U δ T_H T_P)
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
        { st.trΔ with h := TraceTableOps.insert st.trΔ.h stmt sampled }
      let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
        TraceNabla.IsSubsetOfQueryLog_append_hash st.h_inv stmt sampled
      set { st with trace := trace', trΔ := trΔ', h_inv := h_inv' }
      return sampled

/-- **[CO25, §5.4]** Item 3 — inverse-permutation (`p⁻¹`) branch of `D2SQuery`.

Paper steps: lookup `tr_∇.p.outlu(s_out)`; on `⟂`, sample `s_in ← 𝒰(Σ^{r+c})`
and call `tr_∇.p.add(s_in, s_out)`; always append `('p⁻¹', s_out, s_in)` to `tr`. -/
def d2sHandleInversePermQuery
    (stateOut : CanonicalSpongeState U) :
    StateT
      (D2SQueryState StmtIn pSpec U δ T_H T_P)
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
        { st.trΔ with p := TraceTableOps.insert st.trΔ.p sampled stateOut }
      let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
        TraceNabla.IsSubsetOfQueryLog_append_perm_inv st.h_inv sampled stateOut
      set { st with trace := trace', trΔ := trΔ', h_inv := h_inv' }
      return sampled

/-- **[CO25, §5.4]** Item 4(c) — `BackTrack` returned `.noResult`.

Cache lookup (Item 4(c)i) → `tr_∇.p.inlu` (Item 4(c)ii) → fresh sampling fallback. -/
def d2sHandleBacktrackNoResult
    (stateIn : CanonicalSpongeState U) :
    StateT
      (D2SQueryState StmtIn pSpec U δ T_H T_P)
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      (CanonicalSpongeState U) := do
  let st ← get
  match popRateOnlyTailByInput (U := U) st.rateCacheP stateIn with
  | some (tail, cacheTail) =>
      let capacity ← StateT.lift <| OptionT.lift <|
        d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      let realized := materializePoppedRateOnlyTail (U := U) stateIn tail cacheTail capacity
      let cachedOut := realized.1
      let rateCache' := realized.2
      let trace' := st.trace ++ [⟨dsPermQuery stateIn, cachedOut⟩]
      let trΔ' : TraceNabla T_H T_P StmtIn U :=
        { st.trΔ with p := TraceTableOps.insert st.trΔ.p stateIn cachedOut }
      let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
        TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv stateIn cachedOut
      set { st with trace := trace', rateCacheP := rateCache', trΔ := trΔ', h_inv := h_inv' }
      return cachedOut
  | none =>
      match TraceTableOps.inlu st.trΔ.p stateIn with
      | some recovered =>
          let trace' := st.trace ++ [⟨dsPermQuery stateIn, recovered⟩]
          let h_inv' : st.trΔ.IsSubsetOfQueryLog trace' :=
            TraceNabla.IsSubsetOfQueryLog_append_any st.h_inv ⟨dsPermQuery stateIn, recovered⟩
          set { st with trace := trace', h_inv := h_inv' }
          return recovered
      | none =>
          let sampledOut ← StateT.lift <| OptionT.lift <|
            d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          let trace' := st.trace ++ [⟨dsPermQuery stateIn, sampledOut⟩]
          let trΔ' : TraceNabla T_H T_P StmtIn U :=
            { st.trΔ with p := TraceTableOps.insert st.trΔ.p stateIn sampledOut }
          let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
            TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv stateIn sampledOut
          set { st with trace := trace', trΔ := trΔ', h_inv := h_inv' }
          return sampledOut

/-- Continuation of Item 4(e) after its `g_i` answer.  It samples one capacity for the first
rate block only and stores the remaining blocks without capacities. -/
def d2sHandleBacktrackAfterG
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (sampledRhoHat : Vector U (verifierMessageSize (pSpec := pSpec) backtrackOut.roundIdx)) :
    StateT
      (D2SQueryState StmtIn pSpec U δ T_H T_P)
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      (CanonicalSpongeState U) := do
  let st ← get
  match TraceTableOps.inlu st.trΔ.p stateIn with
  | some recovered =>
      let trace' := st.trace ++ [⟨dsPermQuery stateIn, recovered⟩]
      let h_inv' : st.trΔ.IsSubsetOfQueryLog trace' :=
        TraceNabla.IsSubsetOfQueryLog_append_any st.h_inv ⟨dsPermQuery stateIn, recovered⟩
      set { st with trace := trace', h_inv := h_inv' }
      return recovered
  | none =>
      let rateBlocks ← StateT.lift <| OptionT.lift <|
        d2sRateBlocksFromVerifierMessage
          (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (i := backtrackOut.roundIdx) sampledRhoHat
      match rateBlocks.toList with
      | [] => StateT.lift failure
      | firstRate :: remainingRates =>
          let capacity ← StateT.lift <| OptionT.lift <|
            d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          let s_out := d2sSynthesisState (U := U) firstRate capacity
          let rateCache' : List (RateOnlyCacheEntry (U := U)) :=
            match RateOnlyTail.ofBlocks? (U := U) remainingRates with
            | none => st.rateCacheP
            | some tail => st.rateCacheP ++ [⟨s_out, tail⟩]
          let trace' := st.trace ++ [⟨dsPermQuery stateIn, s_out⟩]
          let trΔ' : TraceNabla T_H T_P StmtIn U :=
            { st.trΔ with p := TraceTableOps.insert st.trΔ.p stateIn s_out }
          let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
            TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv stateIn s_out
          set { st with trace := trace', rateCacheP := rateCache', trΔ := trΔ', h_inv := h_inv' }
          return s_out

/-- **[CO25, §5.4]** Items 4(d)/4(e) — `BackTrack` returned `some (i, 𝕩, τ̂, α̂_1, …, α̂_i)`.

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
def d2sHandleBacktrackSome
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    StateT
      (D2SQueryState StmtIn pSpec U δ T_H T_P)
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      (CanonicalSpongeState U) := do
  let st ← get
  if d2sInCodecImagePredicate -- all encoded-messages `α̂ᵢ` are in `Im(φᵢ)`
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut then
    -- Paper Item 4(e)i — **unconditional** `g_i` query: `ρ̂_i := g_i(𝕩, τ̂, α̂_1, …, α̂_i)`.
    -- Determinism w.r.t. the encoded key is enforced by `D2SAlgo`'s `tr_i` memo at the
    -- bridge layer (`d2sCodecBridgeImplMemo` in §5.4 D2SAlgo); same key ⇒ same answer.
    let sampledRhoHat ← StateT.lift <| OptionT.lift <|
      d2sQueryG (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        backtrackOut.roundIdx backtrackOut.stmt backtrackOut.salt
        backtrackOut.encodedProverMessages
    d2sHandleBacktrackAfterG (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn backtrackOut sampledRhoHat
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
          { st.trΔ with p := TraceTableOps.insert st.trΔ.p stateIn sampledOut }
        let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
          TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv stateIn sampledOut
        set { st with trace := trace', trΔ := trΔ', h_inv := h_inv' }
        return sampledOut

/-- **[CO25, §5.4]** Item 4 — permutation (`p`) branch of `D2SQuery`.

Check a pending rate-only `Cache_p[s_in]` first.  Such a tail is the already-scheduled
continuation of `s_in`, so a `BackTrack` candidate must not bypass it.  On a cache miss, call
`BackTrack(tr, tr_∇, s_in)` and dispatch `.err`, `.noResult`, and `.some` as usual. -/
def d2sHandleForwardPermQuery
    (stateIn : CanonicalSpongeState U) :
    StateT
      (D2SQueryState StmtIn pSpec U δ T_H T_P)
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      (CanonicalSpongeState U) := do
  let st ← get
  match popRateOnlyTailByInput (U := U) st.rateCacheP stateIn with
  | some _ =>
      -- Re-evaluate the pure lookup in the shared consumption handler.  The state has not changed,
      -- so this performs the unique capacity draw and rekeying step.
      d2sHandleBacktrackNoResult (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn
  | none =>
      match
          backTrackFwd
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

/-- **[CO25, §5.4]** `D2SQuery` one-step dispatcher over `d2sQueryOracles`: dispatches `h` (Item 2),
`p⁻¹` (Item 3), `p` (Item 4 with BackTrack branches 4(b)-4(g)). -/
def d2sQueryStep
    (q : (duplexSpongeOracle StmtIn U).Domain) :
    StateT
        (D2SQueryState StmtIn pSpec U δ T_H T_P)
      (AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
      ((duplexSpongeOracle StmtIn U).Range q) :=
  match q with
  | dsHashQuery stmt =>
      d2sHandleHashQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt
  | dsPermInvQuery stateOut =>
      d2sHandleInversePermQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateOut
  | dsPermQuery stateIn =>
      d2sHandleForwardPermQuery (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn

/-! ### Rate-only cache-consumption normal form

An eager cache-pop treatment would regard a programmed verifier squeeze as a deterministic
chain of already sampled full states.  In the rate-only oracle wrapper, consuming a cached rate
block draws its capacity *at that consumption*.  The normal form below is the sole
transition-level fact needed by the verifier-shadow argument: it exposes precisely one auxiliary
capacity sample, one realized forward occurrence, and a residual tail rekeyed at that output.
-/

section RateOnlyCacheNormalForm

omit [Fintype U] [∀ i, DecidableEq (pSpec.Message i)] in
/-- A pending rate-only tail is consumed before `BackTrack` is inspected.  Consequently its raw
normal form does not require a `BackTrack = noResult` premise: the handler deliberately routes a
cache hit straight to the shared materialization code.  This premise-free form is the one used by
the stopped Lemma-5.8 observer. -/
lemma d2sQueryStep_rateOnlyCache
    (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U))
    (cacheTail : List (RateOnlyCacheEntry (U := U)))
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P)
    (hpop : popRateOnlyTailByInput (U := U) st.rateCacheP stateIn = some (tail, cacheTail)) :
    (d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (dsPermQuery stateIn)).run st
      = ((do
          let capacity ← StateT.lift <| OptionT.lift <|
            d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          let realized := materializePoppedRateOnlyTail (U := U) stateIn tail cacheTail capacity
          set { st with
            trace := st.trace ++ [(⟨dsPermQuery stateIn, realized.1⟩ :
              Sigma (duplexSpongeOracle StmtIn U))]
            rateCacheP := realized.2
            trΔ := { st.trΔ with p := TraceTableOps.insert st.trΔ.p stateIn realized.1 }
            h_inv := TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv stateIn realized.1 }
          return realized.1 :
        StateT (D2SQueryState StmtIn pSpec U δ T_H T_P)
          (AbortComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))
          (CanonicalSpongeState U)).run st) := by
  simp only [d2sQueryStep, d2sHandleForwardPermQuery, StateT.run, bind, StateT.bind, get,
    getThe, MonadStateOf.get, StateT.get, pure]
  simp only [OptionT.pure, OptionT.bind, OptionT.mk, pure_bind]
  rw [hpop]
  simp only [d2sHandleBacktrackNoResult, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, set, pure]
  simp only [OptionT.pure, OptionT.bind, OptionT.mk, pure_bind]
  rw [hpop]
  rfl

end RateOnlyCacheNormalForm

/-! ### §5.8 step guard — `d2sQueryStep` only issues parseable `gᵢ`-queries

`d2sHandleBacktrackSome` gates its (single) `gSpec` query site behind the codec-image
predicate, which implies `φ⁻¹` parse success (obligation B); every other query the step makes
is auxiliary.  `isQueryBoundP_d2sQueryStep_not_goodQuery` packages this as the zero-budget
predicate bound consumed by the guard-restricted relational `simulateQ` lemma
(`relTriple_simulateQ_run_of_isQueryBoundP`). -/

section StepGuard

/-- §5.8 guard for `D2SQuery`-issued queries: auxiliary queries are always good; a `gᵢ`-query
is good iff its encoded prover prefix parses under `φ⁻¹` (`hybEncodedProverMessagesBefore?`). -/
def d2sGoodQuery :
    (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)).Domain → Prop
  | .inl gkey =>
      (hybEncodedProverMessagesBefore? (pSpec := pSpec) (U := U) gkey.1 gkey.2.2.2).isSome = true
  | .inr _ => True

instance : DecidablePred
    (d2sGoodQuery (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) := fun t =>
  match t with
  | .inl _ => inferInstanceAs (Decidable (_ = true))
  | .inr _ => inferInstanceAs (Decidable True)

/-! The shared counted-query argument ignores auxiliary sampling and charges only the
codec-image `gᵢ` leaf. Its zero-budget specialization gives the §5.8 parse guard; its
one-query specialization supplies the §5.4 query accounting in `D2SAlgo`. -/
section QueryMask

variable (Q :
    (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)).Domain → Prop)
  [DecidablePred Q] (haux : ∀ t, ¬ Q (.inr t))

include haux

omit [SpongeSize] [DecidableEq StmtIn] [Fintype U] [∀ i, DecidableEq (pSpec.Message i)]
  [DecidableEq U] [∀ i, Fintype (pSpec.Message i)] in
private lemma queryMask_bound_query_inr
    (t' : ((Unit →ₒ U) + unifSpec).Domain) :
    IsQueryBoundP
      ((query
          (spec := d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
          (Sum.inr t')) :
        OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
          ((d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)).Range
            (Sum.inr t')))
      Q 0 := by
  change OracleComp.IsQueryBoundP
    (liftM (OracleSpec.query (spec := d2sQueryOracles (U := U) (StmtIn := StmtIn)
      (pSpec := pSpec) (δ := δ)) (Sum.inr t')) : OracleComp _ _)
    Q 0
  rw [OracleComp.isQueryBoundP_query_iff]
  intro h
  exact (haux _ h).elim

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] [Fintype U] [SpongeSize]
  [DecidableEq U] [∀ i, Fintype (pSpec.Message i)] in
private lemma queryMask_bound_d2sSampleUnit :
    IsQueryBoundP (d2sSampleUnit (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      Q 0 :=
  (queryMask_bound_query_inr Q haux) (Sum.inl ())

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] [Fintype U] [SpongeSize]
  [DecidableEq U] [∀ i, Fintype (pSpec.Message i)] in
private lemma queryMask_bound_d2sSampleArrayExact (m : ℕ) :
    IsQueryBoundP
      (d2sSampleArrayExact (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m)
      Q 0 := by
  induction m with
  | zero => exact OracleComp.isQueryBoundP_pure _ _ 0
  | succ m ih =>
      refine OracleComp.isQueryBoundP_bind_zero _ _
        (queryMask_bound_d2sSampleUnit Q haux) (fun u => ?_)
      refine OracleComp.isQueryBoundP_bind_zero _ _ ih (fun xs => ?_)
      rcases xs with ⟨xs, hxs⟩
      exact OracleComp.isQueryBoundP_pure _ _ 0

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] [Fintype U] [SpongeSize]
  [DecidableEq U] [∀ i, Fintype (pSpec.Message i)] in
/-- Sampling counts no queries when `haux` excludes every auxiliary query. -/
lemma isQueryBoundP_d2sSampleVector_of_aux (m : ℕ) :
    IsQueryBoundP
      (d2sSampleVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m)
      Q 0 := by
  refine OracleComp.isQueryBoundP_bind_zero _ _ ((queryMask_bound_d2sSampleArrayExact Q haux) m)
    (fun xs => ?_)
  rcases xs with ⟨xs, hxs⟩
  exact OracleComp.isQueryBoundP_pure _ _ 0

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] [Fintype U]
  [DecidableEq U] [∀ i, Fintype (pSpec.Message i)] in
private lemma queryMask_bound_d2sRateBlocksFromUnitsM (m : ℕ) (units : List U) :
    IsQueryBoundP
      (d2sRateBlocksFromUnitsM (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m units)
      Q 0 := by
  induction m generalizing units with
  | zero => exact OracleComp.isQueryBoundP_pure _ _ 0
  | succ m ih =>
      simp only [d2sRateBlocksFromUnitsM]
      split
      · refine OracleComp.isQueryBoundP_bind_zero _ _
          (OracleComp.isQueryBoundP_pure _ _ 0) (fun y => ?_)
        refine OracleComp.isQueryBoundP_bind_zero _ _ (ih _) (fun d => ?_)
        exact OracleComp.isQueryBoundP_pure _ _ 0
      · refine OracleComp.isQueryBoundP_bind_zero _ _
          (isQueryBoundP_d2sSampleVector_of_aux Q haux _)
          (fun pad => ?_)
        refine OracleComp.isQueryBoundP_bind_zero _ _
          (OracleComp.isQueryBoundP_pure _ _ 0) (fun y => ?_)
        refine OracleComp.isQueryBoundP_bind_zero _ _ (ih _) (fun d => ?_)
        exact OracleComp.isQueryBoundP_pure _ _ 0

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] [Fintype U]
  [DecidableEq U] [∀ i, Fintype (pSpec.Message i)] in
/-- Rate-block padding counts no queries when `haux` excludes every auxiliary query. -/
lemma isQueryBoundP_d2sRateBlocksFromVerifierMessage_of_aux
    {i : pSpec.ChallengeIdx} (verifierMessage : Vector U (verifierMessageSize (pSpec := pSpec) i)) :
    IsQueryBoundP
      (d2sRateBlocksFromVerifierMessage (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (i := i) verifierMessage)
      Q 0 := by
  refine OracleComp.isQueryBoundP_bind_zero _ _
    ((queryMask_bound_d2sRateBlocksFromUnitsM Q haux) _ _)
    (fun bl => ?_)
  rcases bl with ⟨blocks, hBlocks⟩
  exact OracleComp.isQueryBoundP_pure _ _ 0

-- Compose zero-cost state operations locally; sampling uses the explicit bounds below.
attribute [local aesop safe apply] StateTAbortZeroBoundP.bind StateTAbortZeroBoundP.get
  StateTAbortZeroBoundP.set StateTAbortZeroBoundP.pure StateTAbortZeroBoundP.liftComp
  StateTAbortZeroBoundP.liftAbort AbortZeroBoundP.failure AbortZeroBoundP.lift
  StateTAbortZeroBoundP.map

omit [∀ i, DecidableEq (pSpec.Message i)] [Fintype U]
  [∀ i, Fintype (pSpec.Message i)] in
/-- **[CO25, §5.4]** Item 2 — the hash branch makes only auxiliary queries. -/
private lemma queryMask_d2sHandleHashQuery (stmt : StmtIn) :
    StateTAbortZeroBoundP
      Q
      (d2sHandleHashQuery (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt) := by
  unfold d2sHandleHashQuery
  refine StateTAbortZeroBoundP.bind StateTAbortZeroBoundP.get (fun st => ?_)
  have hsample := isQueryBoundP_d2sSampleVector_of_aux Q haux
  split <;> aesop (add simp [d2sSampleCapacity])

omit [∀ i, DecidableEq (pSpec.Message i)] [Fintype U]
  [∀ i, Fintype (pSpec.Message i)] in
/-- **[CO25, §5.4]** Item 3 — the inverse branch makes only auxiliary queries. -/
private lemma queryMask_d2sHandleInversePermQuery (stateOut : CanonicalSpongeState U) :
    StateTAbortZeroBoundP
      Q
      (d2sHandleInversePermQuery (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateOut) := by
  unfold d2sHandleInversePermQuery
  refine StateTAbortZeroBoundP.bind StateTAbortZeroBoundP.get (fun st => ?_)
  have hsample := isQueryBoundP_d2sSampleVector_of_aux Q haux
  split <;> aesop (add simp [d2sSampleState])

omit [∀ i, DecidableEq (pSpec.Message i)] [Fintype U]
  [∀ i, Fintype (pSpec.Message i)] in
/-- **[CO25, §5.4]** Item 4(c) — no-result replies make only auxiliary queries. -/
private lemma queryMask_d2sHandleBacktrackNoResult (stateIn : CanonicalSpongeState U) :
    StateTAbortZeroBoundP
      Q
      (d2sHandleBacktrackNoResult (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn) := by
  unfold d2sHandleBacktrackNoResult
  refine StateTAbortZeroBoundP.bind StateTAbortZeroBoundP.get (fun st => ?_)
  have hsample := isQueryBoundP_d2sSampleVector_of_aux Q haux
  split <;> aesop (add simp [d2sSampleCapacity, d2sSampleState])

omit [∀ i, DecidableEq (pSpec.Message i)] [Fintype U]
  [∀ i, Fintype (pSpec.Message i)] in
/-- The post-`g_i` continuation makes only auxiliary queries. -/
private lemma queryMask_d2sHandleBacktrackAfterG
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (sampledRhoHat : Vector U (verifierMessageSize (pSpec := pSpec) backtrackOut.roundIdx)) :
    StateTAbortZeroBoundP
      Q
      (d2sHandleBacktrackAfterG (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn backtrackOut sampledRhoHat) := by
  unfold d2sHandleBacktrackAfterG
  refine StateTAbortZeroBoundP.bind StateTAbortZeroBoundP.get (fun st => ?_)
  have hsample := isQueryBoundP_d2sSampleVector_of_aux Q haux
  have hblocks := isQueryBoundP_d2sRateBlocksFromVerifierMessage_of_aux Q haux
    (i := backtrackOut.roundIdx)
  split <;> aesop (add simp [d2sSampleCapacity, d2sSampleState])

variable (m : ℕ)
  (hleaf : ∀ out : BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U),
    d2sInCodecImagePredicate (StmtIn := StmtIn) (pSpec := pSpec) (U := U) out = true →
      IsQueryBoundP (d2sQueryG out.roundIdx out.stmt out.salt out.encodedProverMessages) Q m)

include hleaf

omit [∀ i, DecidableEq (pSpec.Message i)] [Fintype U] in
/-- **[CO25, §5.4]** Items 4(d)/(e) — the `BackTrack = .some` branch uses only the
codec-image leaf budget; out-of-image replies make only auxiliary queries. -/
private lemma queryMask_d2sHandleBacktrackSome (stateIn : CanonicalSpongeState U)
    (backtrackOut : BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P) :
    IsQueryBoundP (((d2sHandleBacktrackSome (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn backtrackOut).run st).run) Q m := by
  unfold d2sHandleBacktrackSome
  rcases hImg : d2sInCodecImagePredicate
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut with _ | _
  · -- Not in image: `inlu` else fresh sample — no counted query.
    rcases hInlu : TraceTableOps.inlu st.trΔ.p stateIn with _ | recovered <;>
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_lift,
        StateT.run_pure, OptionT.run_bind, OptionT.run_lift,
        OptionT.run_pure, Option.elimM, pure_bind, bind_assoc, hInlu,
        Bool.false_eq_true, ite_false]
    · exact (isQueryBoundP_bind (n := 0) (m := 0) (isQueryBoundP_d2sSampleVector_of_aux Q haux _)
        fun a _ => by simp).mono (Nat.zero_le m)
    · simp
  · -- In image: the leaf budget followed by an auxiliary-only rate continuation.
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift,
      OptionT.run_bind, OptionT.run_lift,
      Option.elimM, pure_bind, bind_assoc, ite_true]
    refine isQueryBoundP_bind (n := m) (m := 0) (hleaf backtrackOut hImg)
      fun rhoHat _ => ?_
    exact queryMask_d2sHandleBacktrackAfterG Q haux stateIn backtrackOut rhoHat st

omit [∀ i, DecidableEq (pSpec.Message i)] [Fintype U] in
/-- **[CO25, §5.4]** Per-step masked query bound: only a permutation query
can reach the codec-image leaf, whose budget is `m`; hash and inverse queries cost zero. -/
theorem isQueryBoundP_d2sQueryStep_mask
    (q : (duplexSpongeOracle StmtIn U).Domain)
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P) :
    IsQueryBoundP
      (((d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run st).run)
      Q
      (match q with | .inr (.inl _) => m | _ => 0) := by
  rcases q with stmt | stateIn | stateOut
  · -- hash query
    simpa [d2sQueryStep, AbortZeroBoundP] using
      queryMask_d2sHandleHashQuery Q haux (T_H := T_H) (T_P := T_P) stmt st
  · -- permutation: a cache hit is a zero-cost transition; only a miss reaches BackTrack.
    have hstep :
        IsQueryBoundP
          (((d2sHandleForwardPermQuery (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st).run)
          Q m := by
      unfold d2sHandleForwardPermQuery
      rcases hPop : popRateOnlyTailByInput (U := U) st.rateCacheP stateIn with _ | ⟨tail, cacheTail⟩
      · rcases hBT : backTrackFwd (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            st.trace st.trΔ st.h_inv stateIn (st.trace.length + 1) with _ | _ | out <;>
          simp only [StateT.run_bind, StateT.run_get, StateT.run_lift,
            OptionT.run_bind, OptionT.run_pure,
            Option.elimM, pure_bind, OptionT.run_failure, hPop, hBT]
        · simp
        · exact (queryMask_d2sHandleBacktrackNoResult Q haux stateIn st).mono (Nat.zero_le m)
        · exact queryMask_d2sHandleBacktrackSome Q haux m hleaf stateIn out st
      · simp only [StateT.run_bind, StateT.run_get,
          pure_bind, hPop]
        exact (queryMask_d2sHandleBacktrackNoResult Q haux stateIn st).mono (Nat.zero_le m)
    simpa [d2sQueryStep, AbortZeroBoundP] using hstep
  · -- inverse-permutation query
    simpa [d2sQueryStep, AbortZeroBoundP] using
      queryMask_d2sHandleInversePermQuery Q haux (T_H := T_H) (T_P := T_P) stateOut st

end QueryMask

omit [∀ i, DecidableEq (pSpec.Message i)] [Fintype U] in
/-- **§5.8 step guard (obligation D).**  One `d2sQueryStep` makes no queries outside
`d2sGoodQuery`: every `gᵢ`-query it issues has a `φ⁻¹`-parseable encoded prover prefix
(via the §5.4 Item 4(d)/(e) codec-image gate and obligation B), and all other queries are
auxiliary.  Shape consumed by `relTriple_simulateQ_run_of_isQueryBoundP`. -/
theorem isQueryBoundP_d2sQueryStep_not_goodQuery
    (q : (duplexSpongeOracle StmtIn U).Domain)
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P) :
    IsQueryBoundP
      (((d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run st).run)
      (fun t => ¬ d2sGoodQuery (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) t) 0 := by
  have h := isQueryBoundP_d2sQueryStep_mask
    (fun t => ¬ d2sGoodQuery (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) t)
    (fun _ h => h trivial) 0 (fun out hGate => by
      -- Codec-image gate: the `gᵢ` key parses, so no bad query is charged (obligation B).
      unfold d2sQueryG
      change OracleComp.IsQueryBoundP
        (liftM (OracleSpec.query (spec := d2sQueryOracles (U := U) (StmtIn := StmtIn)
          (pSpec := pSpec) (δ := δ))
          (Sum.inl ⟨out.roundIdx, (out.stmt, out.salt, out.encodedProverMessages)⟩)) :
          OracleComp _ _) _ 0
      rw [OracleComp.isQueryBoundP_query_iff]
      intro hbad
      exact absurd
        (hybEncodedProverMessagesBefore?_isSome_of_d2sInCodecImagePredicate
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) out hGate) hbad) q st
  rcases q with _ | _ | _ <;> exact h

end StepGuard

end StepImpl

/-! ### `d2sQueryImpl` — generalization with a caller-supplied `gᵢ` realization

`d2sQueryImpl` parameterizes the D2SQuery oracle wrapper over an arbitrary
`verifierMessageSpec`-targeted `gᵢ`-implementation `gImpl`.  The result lives in
`StateT _ (AbortComp (D2SVerifierMessagePlusUnitOracle verifierMessageSpec))`, which is the
shape `KeyLemma.hybridGame` consumes.

The pipeline reuses `d2sQueryStep` for the §5.4 Items 2–4 branch tree and translates the
resulting `d2sQueryOracles = gSpec + ((Unit →ₒ U) + unifSpec)` queries through
`gImpl + auxImpl`, where `auxImpl` injects the `(Unit →ₒ U) + unifSpec` side into the
`D2SVerifierMessagePlusUnitOracle verifierMessageSpec` target unchanged. -/

section WithOracle

variable {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- **[CO25, §5.4]** `D2SQuery` oracle wrapper parameterized over a `gᵢ` realization `gImpl` and
an auxiliary `(Unit →ₒ U) + unifSpec` realization `auxImpl`, both landing in an arbitrary monad
`m` with `Alternative` (for the §5.4 Item 4(b) `err` abort branch); reuses `d2sQueryStep`
for Items 2-4.

Single interface used by:
- `d2sAlgo` (Phase 14): `m = StateT (D2SAlgoMemo …) (AbortComp …)`,
  `gImpl = d2sCodecBridgeImplMemo` — threads the paper Item 3 `tr_i` memo;
  `auxImpl` lifts `(Unit →ₒ U) + unifSpec` queries through to the outer
  `D2SVerifierMessagePlusUnitOracle`.
- §5.8 hybrid games (`hybridGame`): `m = OptionT (OracleComp _)`,
  `gImpl` varies per hybrid (`g`, `e`, `f`, …); `auxImpl` lifts to the same outer spec.
- `sigmaTraceDist` (BadEvents): `m = OptionT ProbComp`, `auxImpl` resolves
  `(Unit →ₒ U) + unifSpec` directly via `d2sUnitSampleImpl + QueryImpl.id' unifSpec`. The
  `OptionT`-abort halts the §5.8 experiment (proof of [CO25, Lemma 5.8]); the partial trace at
  the moment of abort is preserved by `BadEventDS.abortableTraceDist`. -/
def d2sQueryImpl
    {m : Type → Type} [AlternativeMonad m]
    (gImpl :
      QueryImpl (gSpec (U := U) StmtIn pSpec δ) m)
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) m) :
    QueryImpl (duplexSpongeOracle StmtIn U)
      (StateT
        (D2SQueryState StmtIn pSpec U δ T_H T_P)
        m) :=
  fun (q : (duplexSpongeOracle StmtIn U).Domain) st => do
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

/-- The literal step-tree interpreter used by `d2sQueryImpl`, with the final ordinary-abort
converted to the target monad's `Alternative.failure`. -/
def d2sQueryImplRunRhs
    {m : Type → Type} [AlternativeMonad m]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) m)
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) m)
    (q : (duplexSpongeOracle StmtIn U).Domain)
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P) :
    m (((duplexSpongeOracle StmtIn U).Range q) ×
      D2SQueryState StmtIn pSpec U δ T_H T_P) := do
  let pairOpt ← simulateQ (gImpl + auxImpl)
    (((d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run st).run)
  match pairOpt with
  | none => failure
  | some ⟨query_answer, newState⟩ => pure ⟨query_answer, newState⟩

omit [Fintype U] [∀ i, DecidableEq (pSpec.Message i)] in
/-- Exact one-step normal form of the parameterized `D2SQuery` implementation. -/
lemma d2sQueryImpl_run
    {m : Type → Type} [AlternativeMonad m]
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) m)
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) m)
    (q : (duplexSpongeOracle StmtIn U).Domain)
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P) :
    (d2sQueryImpl (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q).run st =
      d2sQueryImplRunRhs (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st := by
  unfold d2sQueryImpl d2sQueryImplRunRhs
  rfl

omit [Fintype U] [∀ i, DecidableEq (pSpec.Message i)] in
/-- Running the compiled step collapses its raw abort and the interpreter's semantic failure
by a deterministic map. All preceding effects of the underlying monad are retained. -/
lemma d2sQueryImpl_run_map
    {m : Type → Type} [Monad m] [LawfulMonad m] {M : Type}
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (StateT M (OptionT m)))
    (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (StateT M (OptionT m)))
    (q : (duplexSpongeOracle StmtIn U).Domain)
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P) (memo : M) :
    (((d2sQueryImpl (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q).run st).run memo).run =
      (fun o => o.bind fun p => p.1.map fun a => (a, p.2)) <$>
        (((simulateQ (gImpl + auxImpl) (((d2sQueryStep q).run st).run)).run memo).run) := by
  simp only [d2sQueryImpl, StateT.run]
  have hbind {A B : Type} (X : StateT M (OptionT m) A)
      (K : A → StateT M (OptionT m) B) :
      OptionT.run ((X >>= K) memo) = OptionT.run (X memo) >>= fun o =>
        match o with
        | none => pure none
        | some p => OptionT.run (K p.1 p.2) := by
    change OptionT.run (X memo >>= fun p => K p.1 p.2) = _
    rw [OptionT.run_bind, Option.elimM]
    exact bind_congr fun o => by cases o <;> rfl
  rw [hbind]
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun o => ?_
  rcases o with _ | ⟨_ | a, memo'⟩
  · rfl
  · exact congrArg OptionT.run (congrFun StateT.run_failure' memo')
  · rfl

end WithOracle

end D2SQuery

end

end DuplexSpongeFS.ProverTransform
