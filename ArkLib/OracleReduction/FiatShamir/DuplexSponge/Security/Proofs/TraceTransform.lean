/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.Backtrack
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.Lookahead

/-!
# Trace Transformations

This file contains the trace transformations for duplex sponge Fiat-Shamir, following CO25
Section 5.5.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.TraceTransform

open Backtrack Lookahead DSTraceStorage

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type} [DecidableEq StmtIn]
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)]
  {δ : Nat}


noncomputable section

/-- Key for `StdTrace` memoized `gᵢ`-style entries ([CO25, §5.2 Step 4(a)iii.D] output; strict shape
`BacktrackOutput`). -/
abbrev StdTraceQuery :=
  Backtrack.BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)

/-- **[CO25, §5.5.1]** One query-answer pair in `tr_std` / `tr_std^LA`. -/
structure StdTraceEntry where
  query : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  response : Vector U (verifierMessageSize query.roundIdx)

/-- **[CO25, §5.5.1]** Internal accumulator for `StdTrace`.
Stores synthesized entries plus memoized LookAhead results. -/
structure StdTraceState where
  trStd : List (StdTraceEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

  trStdLA : List (StdTraceEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

/-- Project DS-oracle entries from a mixed `oSpec + DS` log. -/
def dsTraceOfLog
    (log : QueryLog (oSpec + duplexSpongeOracle StmtIn U)) :
    QueryLog (duplexSpongeOracle StmtIn U) :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.inl _, _⟩ => none
    | ⟨.inr q, r⟩ => some ⟨q, r⟩

/-- Lookup of a prior `tr_std^LA` entry with the same query key. -/
def lookupStdTraceMemo
    (memo : List (StdTraceEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec)
                                (U := U)))
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Option (Vector U (verifierMessageSize q.roundIdx)) := by
  classical
  exact memo.findSome? fun entry =>
    if hEq : entry.query = q then
      some (hEq ▸ entry.response)
    else
      none

/-- Insert a fresh query-answer pair into `tr_std^LA` order. -/
def insertStdTraceMemo
    (memo : List (StdTraceEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec)
                                (U := U)))
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (response : Vector U (verifierMessageSize q.roundIdx)) :
    List (StdTraceEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec)
                        (U := U)) :=
  memo ++ [{ query := q, response := response }]

/-! ## StdTrace helpers ([CO25, §5.5.1])

These helpers implement CO25's exact `∀ι, α̂_ι ∈ Im(φ_ι)` codec-image predicate and the
deterministic `e_i := ψ_i(ρ̂_i)` entry remap. They are forward-declared here so that the
single `StdTrace` pipeline (and its abort analysis) can use them without exposing a free
predicate/function field. -/

/-- Implements the deterministic inverse codec map `φ_i⁻¹ : Im(φ_i) → ℳ_{P,i}`.
Because `φ_i` (via `instSerializeMessageInjective`) is strictly injective and the message domain
is finite, we can invert the serialization computationally via brute-force search.
-/
def decodeProverMessagePhiInv?
    (msgIdx : pSpec.MessageIdx)
    (encoded : Vector U (proverMessageSize msgIdx)) :
    Option (pSpec.Message msgIdx) := by
  exact ((Finset.univ : Finset (pSpec.Message msgIdx)).toList.find? fun msg =>
    Serialize.serialize msg = encoded)

/-- Looks up the encoded message block `α̂_j` from the flat list of extracted sponge queries. -/
def lookupEncodedProverMessageAlphaHat?
    (encodedProverMessages :
      List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (proverMessageSize msgIdx)))
    (msgIdx : pSpec.MessageIdx) :
    Option (Vector U (proverMessageSize msgIdx)) := by
  exact encodedProverMessages.findSome? fun entry =>
    match entry with
    | ⟨idx, encoded⟩ =>
        if hEq : idx = msgIdx then
          some (hEq ▸ encoded)
        else
          none

/-- One step of the `decodeProverMessagesPrefixPhiInv?` walk: extend the partial `MessagesUpTo`
prefix by one round. On a `P_to_V` round, extract the encoded message `α̂_j` and apply `φ_j⁻¹`
(`decodeProverMessagePhiInv?`); on a `V_to_P` round, extend the prefix with no payload. -/
noncomputable def decodeProverMessagesPrefixStepPhiInv
    (encodedList :
      List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (proverMessageSize msgIdx)))
    (j : Fin n) (messages : pSpec.MessagesUpTo j.castSucc) :
    Option (pSpec.MessagesUpTo j.succ) := by
  exact
    match hDir : pSpec.dir j with
    | .P_to_V =>
        let msgIdx : pSpec.MessageIdx := ⟨j, hDir⟩
        match lookupEncodedProverMessageAlphaHat? (pSpec := pSpec) encodedList msgIdx with
        | none => none
        | some encodedMsg =>
            match decodeProverMessagePhiInv?
                (pSpec := pSpec) (U := U) msgIdx encodedMsg with
            | none => none
            | some msg =>
                some
                  (ProtocolSpec.MessagesUpTo.concat
                    (pSpec := pSpec) messages hDir msg)
    | .V_to_P =>
        some (ProtocolSpec.MessagesUpTo.extend (pSpec := pSpec) messages hDir)

/-- Implements the full `φ⁻¹` map over a structured prefix of encoded messages up to round `i`.
Walks the rounds `0..i-1` and iteratively applies `decodeProverMessagesPrefixStepPhiInv` to return
the unencoded message sequence `α_{<i}`. -/
noncomputable def decodeProverMessagesPrefixPhiInv?
    (roundIdx : pSpec.ChallengeIdx)
    (encodedProverMessages : pSpec.EncodedProverMessagesBefore U roundIdx.1.castSucc) :
    Option (pSpec.MessagesUpTo roundIdx.1.castSucc) := by
  -- Internal algorithm reuses the list-based lookup; we flatten via `toList` here so the
  -- structured [CO25, Eq. (18)] prefix surface is honored at the boundary, while the existing
  -- per-round walk stays unchanged.
  let encodedList :=
    EncodedProverMessagesBefore.toList (pSpec := pSpec) (U := U) encodedProverMessages
  let build : (k : Fin (n + 1)) → Option (pSpec.MessagesUpTo k) :=
    Fin.induction
      (some default)
      (fun j ih =>
        match ih with
        | none => none
        | some messages =>
            decodeProverMessagesPrefixStepPhiInv (pSpec := pSpec) (U := U) encodedList j messages)
  exact build roundIdx.1.castSucc

noncomputable def stdTraceProverMessagesBefore?
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Option (pSpec.MessagesUpTo q.roundIdx.1.castSucc) :=
  decodeProverMessagesPrefixPhiInv? (pSpec := pSpec) (U := U)
    q.roundIdx q.encodedProverMessages

/-- **[CO25, §5.5.1]** Item 4(a)iii — `∀ι, α̂_ι ∈ Im(φ_ι)` codec-image predicate over
StdTrace backtrack outputs. This is the canonical inCodecImage check baked into `stdTraceEntries`
in place of the previous free `BacktrackOutput → Bool` parameter. -/
noncomputable def stdTraceInCodecImage
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Bool :=
  let stdQuery : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) := out
  match stdTraceProverMessagesBefore?
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stdQuery with
  | some _ => true
  | none => false

/-- **[CO25, §5.5.1]** StdTrace Step 3: build `tr_∇` from the DS trace, keeping `h` and forward `p`
entries.

Kept polymorphic in the trace-table implementations `T_H`/`T_P` (with a `LawfulTraceNablaImpl`
instance) so callers stay blackbox over the concrete data structure. -/
def stdTraceDelta
    {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (dsTrace : QueryLog (duplexSpongeOracle StmtIn U)) :
    TraceNabla T_H T_P StmtIn U :=
  TraceNabla.ofQueryLogForwardOnly dsTrace

def StdTraceState.appendEntry
    (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat_i : Vector U (verifierMessageSize q.roundIdx)) :
    StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
  { st with trStd := st.trStd ++ [{ query := q, response := rhoHat_i }] }

def StdTraceState.appendMemoAndEntry
    (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat_i : Vector U (verifierMessageSize q.roundIdx)) :
    StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
  { trStd := st.trStd ++ [{ query := q, response := rhoHat_i }]
    -- cache `((i, 𝕩, τ, α̂_{<i}), ρ̂_i)` into `tr_std^LA`
    trStdLA := insertStdTraceMemo
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      st.trStdLA q rhoHat_i }

/-- **[CO25, §5.5.1]** StdTrace Item 4(a)iv-v — reuse memoized LookAhead output or call LookAhead
and append `tr_std`.

Blackbox over the permutation trace-table implementation: only `[LawfulTraceTable T_P
(CanonicalSpongeState U) (CanonicalSpongeState U)]` is assumed, matching `lookAhead`. -/
def stdTraceLookupOrLookAhead
    {T_P : Type}
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔp : T_P)
    (stateIn : CanonicalSpongeState U)
    (q : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    UnitSampleM U
      (StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := do
  match lookupStdTraceMemo
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) st.trStdLA q with
  | some rhoHat_i =>
      -- Item 4(a)ivA — `tr_std^LA` hit on key `(i, 𝕩, τ, α̂_{<i})`: reuse cached `ρ̂_i`.
      pure (st.appendEntry (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q rhoHat_i)
  | none =>
      -- Item 4(a)ivB — `tr_std^LA` miss on `(i, 𝕩, τ, α̂_{<i})`: call `LookAhead(tr_∇.p, s_in, i)`.
      let rhoHat_i? ← lookAhead (pSpec := pSpec) (U := U) trΔp stateIn q.roundIdx
      match rhoHat_i? with
      | .err =>
          -- CO25 `err`: multiple lookahead chains found (unexpected after backtrack).
          failure
      | .noResult =>
          -- [CO25, §5.5.1, Item 4(a)ivB-D]: once BackTrack returns a valid tuple for the
          -- current `p` entry, LookAhead should find the matching successor in `tr`.
          failure
      | .some rhoHat_i =>
          -- Item 4(a)ivD — append `((i, 𝕩, τ, α̂_{<i}), ρ̂_i)` to `tr_std^LA` and `tr_std`.
          pure (st.appendMemoAndEntry
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q rhoHat_i)

/-- **[CO25, §5.5.1]** StdTrace Item 4(a)iii-v — check codec image, then memo/lookahead and append
an entry.

Blackbox over `T_P` (the permutation trace table). -/
noncomputable def stdTraceHandleBacktrackTuple
    {T_P : Type}
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔp : T_P)
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    UnitSampleM U
      (StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  -- Item 4(a)iii — codec-image check: accept iff `(α̂_1, …, α̂_{i-1}) ∈ Image(φ)`; else skip.
  if stdTraceInCodecImage
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) backtrackOut then
    let stdQuery : StdTraceQuery (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
      backtrackOut
    -- Items 4(a)iv-v — dispatch into LookAhead memo / fresh call + append to `tr_std`.
    stdTraceLookupOrLookAhead
      (δ := δ)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) trΔp stateIn stdQuery st
  else
    pure st

/-- **[CO25, §5.5.1]** StdTrace Item 4(a) — process one forward `p` entry using BackTrack and
LookAhead.

Blackbox over `T_H T_P` via `[LawfulTraceNablaImpl …]`; the `tr_∇` value flows into `backTrackFwd`
(which is itself polymorphic in `T_H T_P`) and `dsTrΔ.p` flows into `lookAhead`. -/
noncomputable def stdTraceHandlePQuery
    {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (dsTrace : QueryLog (duplexSpongeOracle StmtIn U))
    (dsTrΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : dsTrΔ.IsSubsetOfQueryLog dsTrace)
    (depthBound : Nat)
    (stateIn : CanonicalSpongeState U)
    (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    UnitSampleM U
      (StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  -- Item 4(a)i-ii — call `BackTrack(tr, tr_∇, s_in)` to recover `(i, 𝕩, α̂_{<i}, τ̂)` ∈ Σ★.
  match
      backTrackFwd (δ := δ)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        dsTrace dsTrΔ h_trΔ stateIn depthBound with
  | .err =>
      failure
  | .noResult =>
      -- `BackTrack = ⊥` (no valid ancestor): skip this forward `p` entry per Item 4(a)ii.
      pure st
  | .some backtrackOut =>
      -- Items 4(a)iii-v — image check then memo/lookahead + append to `tr_std`.
      stdTraceHandleBacktrackTuple (δ := δ)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        dsTrΔ.p stateIn backtrackOut st

/-- **[CO25, §5.8]** Public wrapper for the Section 5.8 `φ⁻¹` parser from the encoded-message tuple
returned by `BackTrack` to basic-FS prover-message prefixes.

The input `(α̂₁, …, α̂ₘᵢ)` contains all prover messages before verifier position `i`;
`mᵢ` need not equal `i`, and the prefix is empty for an initial verifier message. -/
noncomputable def hybEncodedProverMessagesBefore?
    (roundIdx : pSpec.ChallengeIdx)
    (encodedProverMessages : pSpec.EncodedProverMessagesBefore U roundIdx.1.castSucc) :
    Option (pSpec.MessagesUpTo roundIdx.1.castSucc) :=
  decodeProverMessagesPrefixPhiInv?
    (pSpec := pSpec) (U := U)
    roundIdx encodedProverMessages

/-! ## [CO25, Claim 5.24] — `φ⁻¹` inverts `φ` on the honest prefix

The round trip needed by the `Hyb₃` / `Hyb₄` key comparison: when the encoded-message prefix
reconstructed by `BackTrack` consists of the literal serializations `φ_j(α_j)` of the honest
prover's messages, the parser `hybEncodedProverMessagesBefore?` returns exactly `α_{<i}`. -/

section PhiInvRoundTrip

omit [SpongeSize] in
/-- `List.find?` returns `a` as soon as `a` occurs in the list and is the *only* element of the
list satisfying the predicate. -/
private theorem find?_eq_some_of_unique {α : Type*} {p : α → Bool} :
    ∀ {l : List α} {a : α}, a ∈ l → p a = true → (∀ b ∈ l, p b = true → b = a) →
      l.find? p = some a := by
  intro l a ha hpa huniq
  cases h : l.find? p with
  | none => exact False.elim ((List.find?_eq_none.mp h) a ha hpa)
  | some b => exact congrArg some (huniq b (List.mem_of_find?_eq_some h) (List.find?_some h))

omit [SpongeUnit U] [SpongeSize] in
/-- **`φ_j⁻¹` inverts `φ_j`.** The brute-force search of `decodeProverMessagePhiInv?` over the
finite message type returns the unique preimage, because `φ_j` is injective
(`Codec.encode_injective`). -/
private theorem decodeProverMessagePhiInv?_serialize
    (msgIdx : pSpec.MessageIdx) (msg : pSpec.Message msgIdx) :
    decodeProverMessagePhiInv? (pSpec := pSpec) (U := U) msgIdx (Serialize.serialize msg)
      = some msg := by
  rw [decodeProverMessagePhiInv?]
  refine find?_eq_some_of_unique (Finset.mem_toList.mpr (Finset.mem_univ _)) (by simp) ?_
  intro b _ hb
  simp only [decide_eq_true_eq] at hb
  exact codec.encode_injective msgIdx hb

omit [SpongeSize] in
/-- `List.findSome?` returns `v` as soon as some element of the list maps to `some v` and every
element mapping to a `some` maps to `some v`. -/
private theorem findSome?_eq_some_of_unique {α β : Type*} {g : α → Option β} {v : β} :
    ∀ {l : List α}, (∃ a ∈ l, g a = some v) →
      (∀ b ∈ l, ∀ w, g b = some w → w = v) → l.findSome? g = some v := by
  intro l hex huniq
  cases h : l.findSome? g with
  | none =>
      obtain ⟨a, ha, hga⟩ := hex
      have hn := List.findSome?_eq_none_iff.mp h a ha
      simp [hga] at hn
  | some w =>
      obtain ⟨a, ha, hga⟩ := List.exists_of_findSome?_eq_some h
      exact congrArg some (huniq a ha w hga)

omit [SpongeSize] in
/-- `findSome?` after a `filterMap` is a single `findSome?` over the composed partial map. -/
private theorem findSome?_filterMap {α β γ : Type*} (gg : α → Option β) (g : β → Option γ) :
    ∀ (L : List α), (L.filterMap gg).findSome? g = L.findSome? fun a => (gg a).bind g := by
  intro L
  rw [← List.head?_filterMap, List.filterMap_filterMap, List.head?_filterMap]

omit [SpongeUnit U] [SpongeSize] [DecidableEq U] [∀ i, Fintype (pSpec.Message i)] in
/-- The `α̂` lookup used by `φ⁻¹` reads back exactly the entry stored in the structured
`EncodedProverMessagesBefore` prefix. -/
private theorem lookupEncodedProverMessageAlphaHat?_toList
    {k : Fin (n + 1)} (f : pSpec.EncodedProverMessagesBefore U k)
    (msgIdx : pSpec.MessageIdx) (hlt : msgIdx.1.1 < k.1) :
    lookupEncodedProverMessageAlphaHat? (pSpec := pSpec) (U := U)
        (EncodedProverMessagesBefore.toList (pSpec := pSpec) (U := U) f) msgIdx
      = some (f ⟨msgIdx, hlt⟩) := by
  rw [lookupEncodedProverMessageAlphaHat?, EncodedProverMessagesBefore.toList, findSome?_filterMap]
  refine findSome?_eq_some_of_unique
    ⟨msgIdx, Finset.mem_toList.mpr (Finset.mem_univ _), by simp [hlt]⟩ ?_
  intro b _ w hw
  split at hw
  · rename_i hbk
    simp only [Option.bind_some] at hw
    split at hw
    · rename_i hbm
      subst hbm
      exact (Option.some.inj hw).symm
    · exact absurd hw (by simp)
  · exact absurd hw (by simp)

omit [SpongeUnit U] [SpongeSize] in
/-- The prefix parser inverts serialization of a partial message tuple. No messages beyond
its cutoff are required, so future prover-message types may be empty. -/
private theorem decodeProverMessagesPrefix_build_eq
    {K : Fin (n + 1)} (encodedProverMessages : pSpec.EncodedProverMessagesBefore U K)
    (k : Fin (n + 1)) (hk : k.1 ≤ K.1) (messages : pSpec.MessagesUpTo k)
    (hEnc : ∀ (j : Fin n) (hDir : pSpec.dir j = .P_to_V) (hj : j.val < k.val),
      encodedProverMessages ⟨⟨j, hDir⟩, lt_of_lt_of_le hj hk⟩ =
        (Codec.instSerializeMessage (pSpec := pSpec) (U := U) ⟨j, hDir⟩).serialize
          (messages ⟨⟨j.val, hj⟩, hDir⟩)) :
    Fin.induction (motive := fun k => Option (pSpec.MessagesUpTo k)) (some default)
        (fun j ih =>
          match ih with
          | none => none
          | some ms =>
              decodeProverMessagesPrefixStepPhiInv (pSpec := pSpec) (U := U)
                (EncodedProverMessagesBefore.toList (pSpec := pSpec) (U := U)
                  encodedProverMessages) j ms)
        k = some messages := by
  induction k using Fin.induction with
  | zero => exact congrArg some (Subsingleton.elim _ _)
  | succ j ih =>
    let previous : pSpec.MessagesUpTo j.castSucc :=
      fun i => messages ⟨i.1.castSucc, i.2⟩
    have hjK : j.val < K.val := hk
    rw [Fin.induction_succ, ih (by simpa using hjK.le) previous
      (fun l hDir hl => hEnc l hDir (Nat.lt_succ_of_lt hl))]
    change decodeProverMessagesPrefixStepPhiInv _ j previous = _
    rw [decodeProverMessagesPrefixStepPhiInv]
    split
    · rename_i hDir
      simp only [lookupEncodedProverMessageAlphaHat?_toList (f := encodedProverMessages)
          (msgIdx := ⟨j, hDir⟩) (hlt := hjK),
        hEnc j hDir (Nat.lt_succ_self _)]
      erw [decodeProverMessagePhiInv?_serialize ⟨j, hDir⟩ (messages ⟨Fin.last j.val, hDir⟩)]
      apply congrArg some
      funext l
      obtain ⟨i, hi⟩ := l
      induction i using Fin.lastCases with
      | last => exact (MessagesUpTo.concat_apply_last _ _ _ _).trans rfl
      | cast i => exact (MessagesUpTo.concat_apply_castSucc _ _ _ _ _).trans rfl
    · rename_i hDir
      apply congrArg some
      funext l
      obtain ⟨i, hi⟩ := l
      induction i using Fin.lastCases with
      | last => exact absurd (hDir.symm.trans hi) (by simp)
      | cast i => exact (MessagesUpTo.extend_apply_castSucc _ _ _ _).trans rfl

omit [SpongeUnit U] [SpongeSize] in
/-- **`φ⁻¹` inverts `φ` on the honest prefix.** If every entry of `encodedProverMessages` is the
serialization of the corresponding honest message, the parser returns exactly that message
prefix. This is the round trip used by [CO25, Claim 5.24] to match the `Hyb₃` verifier's `gᵢ`-query
key with the key read by `Hyb₄`. -/
theorem hybEncodedProverMessagesBefore?_of_serialize
    (roundIdx : pSpec.ChallengeIdx) (messages : pSpec.Messages)
    (encodedProverMessages : pSpec.EncodedProverMessagesBefore U roundIdx.1.castSucc)
    (h : ∀ j, encodedProverMessages j
      = (Codec.instSerializeMessage (pSpec := pSpec) (U := U) j.1).serialize (messages j.1)) :
    hybEncodedProverMessagesBefore? (pSpec := pSpec) (U := U) roundIdx encodedProverMessages
      = some (Messages.take roundIdx.1.castSucc messages) := by
  rw [hybEncodedProverMessagesBefore?, decodeProverMessagesPrefixPhiInv?]
  exact decodeProverMessagesPrefix_build_eq encodedProverMessages _ le_rfl _
    (fun j hDir hj => h ⟨⟨j, hDir⟩, hj⟩)

omit [SpongeUnit U] [SpongeSize] in
/-- `MessagesUpTo`-flavoured restatement of `hybEncodedProverMessagesBefore?_of_serialize`, in the
spelling used by `VerifierStacks.fsDerivedAux` (`messages.take i.castSucc` for
`messages : pSpec.MessagesUpTo (Fin.last n)`). -/
theorem hybEncodedProverMessagesBefore?_of_serialize'
    (roundIdx : pSpec.ChallengeIdx) (messages : pSpec.MessagesUpTo (Fin.last n))
    (encodedProverMessages : pSpec.EncodedProverMessagesBefore U roundIdx.1.castSucc)
    (h : ∀ j, encodedProverMessages j
      = (Codec.instSerializeMessage (pSpec := pSpec) (U := U) j.1).serialize (messages j.1)) :
    hybEncodedProverMessagesBefore? (pSpec := pSpec) (U := U) roundIdx encodedProverMessages
      = some (messages.take roundIdx.1.castSucc) :=
  hybEncodedProverMessagesBefore?_of_serialize roundIdx messages encodedProverMessages h

end PhiInvRoundTrip

/-! ## Salted FS variants ([CO25, §5.5.2 (D2STrace), Step 3])

CO25's standard FS reduction `R_FS` keeps the public *pre-encoded* salt `τ̌ ∈ {0,1}^{δ★}` threaded
through the augmented statement of the FS-standard oracle ([CO25, Eqs. (55) and (57)]).
We model this as the abstract type `Salt`, bridged from the on-sponge `Vector U δ` salt via
`SaltCodec.encode = bin`. The salted variants below feed into `KeyLemma`'s `Hyb₃`/`Hyb₄`. -/

/-- **[CO25, §5.5.1]** Salted variant of `stdTraceEntryToFSQuery?` — projects the BackTrack salt
`out.salt : Vector U δ` to the FS-standard side via `bin = SaltCodec.encode` before placing it
in the augmented statement of the salted FS oracle query ([CO25, §5.4]). -/
noncomputable def stdTraceEntryToFSQuerySalted?
    {Salt : Type} [SaltCodec U δ Salt]
    (entry : StdTraceEntry (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Option (Sigma (fsChallengeOracle (StmtIn × Salt) pSpec)) := do
  let messagesBefore ←
    stdTraceProverMessagesBefore?
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      entry.query
  let verifierMessage : pSpec.Challenge entry.query.roundIdx :=
    Deserialize.deserialize entry.response
  pure ⟨⟨entry.query.roundIdx,
    ((entry.query.stmt, SaltCodec.encode entry.query.salt), messagesBefore)⟩, verifierMessage⟩

/-- **[CO25, §5.5.2]** Translate a tagged DSFS log into a single-salt FS log.
Ambient entries pass through unchanged; forward entries produce decoded round queries
with their original source tags. Order is preserved, but log positions can change.
Failed message decodings are omitted; procedure aborts propagate. Missing LookAhead
blocks are sampled through `Unit →ₒ U`. -/
noncomputable def d2sTraceSalted
    {T_H T_P : Type} {Salt : Type} [SaltCodec U δ Salt]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (log : TaggedQueryLog (oSpec + duplexSpongeOracle StmtIn U)) :
    UnitSampleM U
      (TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) := do
  let combinedRaw := TaggedQueryLog.untagged log
  let dsTrace := dsTraceOfLog (oSpec := oSpec) (StmtIn := StmtIn) (U := U) combinedRaw
  let dsTrΔ : TraceNabla T_H T_P StmtIn U :=
    stdTraceDelta (StmtIn := StmtIn) (U := U) dsTrace
  have h_trΔ : dsTrΔ.IsSubsetOfQueryLog dsTrace := TraceNabla.ofQueryLogForwardOnly_isSubset dsTrace
  let depthBound := dsTrace.length + 1
  let rec go
      (remaining : TaggedQueryLog (oSpec + duplexSpongeOracle StmtIn U))
      (st : StdTraceState (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (out : TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :
      UnitSampleM U (TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) := do
    match remaining with
    | [] => pure out
    | (tag, entry) :: rest =>
        match entry with
        | ⟨.inl query, response⟩ =>
            -- Forward oSpec entries verbatim, preserving their tag (C1)
            let outEntry : Sigma (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) :=
              ⟨.inl query, response⟩
            go rest st (out ++ [(tag, outEntry)])
        | ⟨.inr (.inr (.inl stateIn)), _stateOut⟩ =>
            let st' ← stdTraceHandlePQuery (δ := δ) (StmtIn := StmtIn) (n := n)
              (pSpec := pSpec) (U := U) dsTrace dsTrΔ h_trΔ depthBound stateIn st
            -- Extract newly synthesized basic-FS verifier message queries
            let newEntries := st'.trStd.drop st.trStd.length
            -- Apply line-4 transform to them
            let mappedNewEntries := newEntries.filterMap fun e =>
              match stdTraceEntryToFSQuerySalted? (δ := δ) (StmtIn := StmtIn)
              (pSpec := pSpec) (U := U) (Salt := Salt) e with
              | none => none
              | some mapped => some (tag, ⟨.inr mapped.1, mapped.2⟩)
            go rest st' (out ++ mappedNewEntries)
        | _ => go rest st out
  go log { trStd := [], trStdLA := [] } []

section TraceTranslation

/-- Section 5.8 `Hyb₁` line-4 per-entry remap. Encoded prover-prefix + encoded verifier message
↦ decoded prover-prefix + decoded verifier message. Salt is projected `Σ^δ → Salt` via
`SaltCodec.encode = bin` ([CO25, §5.4]). `oSpec` entries are forwarded verbatim. -/
noncomputable def hyb1RemapEntry?
    {Salt : Type} [SaltCodec U δ Salt]
    (entry : Sigma (oSpec + gSpec (U := U) StmtIn pSpec δ)) :
    Option (Sigma (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :=
  match entry with
  | ⟨.inl query, response⟩ => some ⟨.inl query, response⟩
  | ⟨.inr ⟨roundIdx, (stmt, salt, encodedProverMessages)⟩, response⟩ =>
      -- `Hyb₁` line 4 — `φ⁻¹`: decode `(α_1, …, α_{i-1}) := φ⁻¹(α̂_1, …, α̂_{i-1})`; abort on `⊥`.
      match hybEncodedProverMessagesBefore?
          (pSpec := pSpec) (U := U) roundIdx encodedProverMessages with
      | none => none
      | some messagesBefore =>
          let responseVec :
              Vector U (verifierMessageSize (pSpec := pSpec) roundIdx) := response
          -- `Hyb₁` line 4 — `ψ`: `ρ_i := ψ_i(ρ̂_i)`; salt projected `τ̌ := bin(τ̂)`.
          let verifierMessage : pSpec.Challenge roundIdx :=
            Deserialize.deserialize responseVec
          some ⟨.inr ⟨roundIdx, ((stmt, SaltCodec.encode salt), messagesBefore)⟩, verifierMessage⟩

/-- Section 5.8 `Hyb₁` line-4 trace translation.

This is the explicit `(φ⁻¹, ψ)(tr)` post-processing map applied directly to the single concatenated
query-answer trace `tr = tr_P̃ || tr_V`. -/
noncomputable def hyb1TraceTranslation
    {Salt : Type} [SaltCodec U δ Salt]
    (log : TaggedQueryLog (oSpec + gSpec (U := U) StmtIn pSpec δ)) :
    UnitSampleM U
      (TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :=
  pure (log.filterMap fun ⟨tag, entry⟩ =>
    match hyb1RemapEntry? (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) (Salt := Salt) entry with
    | some mapped => some (tag, mapped)
    | none => none)

/-- Section 5.8 `Hyb₂` line-4 per-entry remap. Encoded prover-prefix + decoded verifier message
↦ decoded prover-prefix + decoded verifier message. Salt is projected `Σ^δ → Salt` via
`SaltCodec.encode = bin` ([CO25, §5.4]). `oSpec` entries are forwarded verbatim. -/
noncomputable def hyb2RemapEntry?
    {Salt : Type} [SaltCodec U δ Salt]
    (entry : Sigma (oSpec + eSpec (U := U) StmtIn pSpec δ)) :
    Option (Sigma (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :=
  match entry with
  | ⟨.inl query, response⟩ => some ⟨.inl query, response⟩
  | ⟨.inr ⟨roundIdx, (stmt, salt, encodedProverMessages)⟩, verifierMessage⟩ =>
      -- `Hyb₂` line 4 — `φ⁻¹` only: decode `(α_1, …, α_{i-1}) := φ⁻¹(α̂_1, …, α̂_{i-1})`;
      --   verifier message `ρ_i` already on FS-side; salt projected `τ̌ := bin(τ̂)`.
      match hybEncodedProverMessagesBefore?
          (pSpec := pSpec) (U := U) roundIdx encodedProverMessages with
      | none => none
      | some messagesBefore =>
          some ⟨.inr ⟨roundIdx, ((stmt, SaltCodec.encode salt), messagesBefore)⟩, verifierMessage⟩

/-- Section 5.8 `Hyb₂` line-4 trace translation.

This is the explicit `φ⁻¹(tr)` post-processing map applied directly to the single concatenated
query-answer trace `tr = tr_P̃ || tr_V`. -/
noncomputable def hyb2TraceTranslation
    {Salt : Type} [SaltCodec U δ Salt]
    (log : TaggedQueryLog (oSpec + eSpec (U := U) StmtIn pSpec δ)) :
    UnitSampleM U
      (TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :=
  pure (log.filterMap fun ⟨tag, entry⟩ =>
    match hyb2RemapEntry? (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) (Salt := Salt) entry with
    | some mapped => some (tag, mapped)
    | none => none)

/-- Section 5.8 `Hyb₃` line-4 trace translation.

This is the identity-on-line-4 trace surface, viewed through the common single-log Section 5
interface used by `KeyLemma`. -/
noncomputable def hyb3TraceTranslation
    {Salt : Type}
    (log : TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :
    UnitSampleM U
      (TaggedQueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :=
  -- `Hyb₃` line 4 — identity: trace already lives on the salted-FS oracle; no remap needed.
  pure log

omit [DecidableEq StmtIn] [SpongeSize] in
/-- Public characterization of `hyb2TraceTranslation` (whose per-entry remap is private): it is the
pure `filterMap` that forwards `oSpec` entries, drops verifier message entries whose encoded prefix
fails the `φ⁻¹` parse, and remaps parsing verifier message entries to the decoded key (statement,
`bin`-encoded salt, parsed prover-message prefix) with the answer kept verbatim. -/
lemma hyb2TraceTranslation_eq_filterMap
    {Salt : Type} [SaltCodec U δ Salt]
    (log : TaggedQueryLog (oSpec + eSpec (U := U) StmtIn pSpec δ)) :
    hyb2TraceTranslation (δ := δ) (Salt := Salt)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) log
      = pure (log.filterMap fun e =>
          match e with
          | ⟨tg, ⟨.inl q, r⟩⟩ => some (tg, ⟨.inl q, r⟩)
          | ⟨tg, ⟨.inr ⟨roundIdx, (stmt, salt, encodedProverMessages)⟩, verifierMessage⟩⟩ =>
              match hybEncodedProverMessagesBefore?
                  (pSpec := pSpec) (U := U) roundIdx encodedProverMessages with
              | some messagesBefore =>
                  some (tg, ⟨.inr ⟨roundIdx,
                    ((stmt, SaltCodec.encode salt), messagesBefore)⟩, verifierMessage⟩)
              | none => none) := by
  unfold hyb2TraceTranslation
  congr 1
  apply List.filterMap_congr
  intro e _
  rcases e with ⟨tg, ⟨q, r⟩⟩
  rcases q with q | ⟨roundIdx, stmt, salt, encodedProverMessages⟩
  · rfl
  · change (match hyb2RemapEntry? (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) (Salt := Salt)
          ⟨.inr ⟨roundIdx, (stmt, salt, encodedProverMessages)⟩, r⟩ with
      | some mapped => some (tg, mapped)
      | none => none) = _
    unfold hyb2RemapEntry?
    rcases hparse : hybEncodedProverMessagesBefore?
        (pSpec := pSpec) (U := U) roundIdx encodedProverMessages with _ | messagesBefore
    · simp [hparse]
    · simp [hparse]

/-! ### `Hyb₁`/`Hyb₂` line-4 comparison

The two line-4 maps differ only in that `Hyb₁` decodes the logged encoded answer
(`ψ = Deserialize.deserialize`) while `Hyb₂`'s log already carries the decoded verifier message.
`gToELogEntry` performs exactly that per-entry decoding, and `hyb1TraceTranslation` factors as
`hyb2TraceTranslation ∘ (map gToELogEntry)`.  This is the log half of the [CO25, Claim 5.22]
`Hyb₁`-vs-`Hyb₂` coupling: it says the two line-4 maps identify a `gSpec` log with its
entry-wise decoded `eSpec` image. -/

/-- Per-entry decoding of a `Hyb₁` (`gSpec`) query-log entry into the corresponding `Hyb₂`
(`eSpec`) entry: verifier message answers `ρ̂ᵢ ∈ Σ^{ℓ_V(i)}` are mapped to `ρᵢ = ψᵢ(ρ̂ᵢ)`, all other
entries are forwarded verbatim.  Keys are untouched (`gSpec` and `eSpec` share their
domain). -/
def gToELogEntry
    (entry : Sigma (oSpec + gSpec (U := U) StmtIn pSpec δ)) :
    Sigma (oSpec + eSpec (U := U) StmtIn pSpec δ) :=
  match entry with
  | ⟨.inl query, response⟩ => ⟨.inl query, response⟩
  | ⟨.inr ⟨roundIdx, key⟩, response⟩ =>
      let responseVec : Vector U (verifierMessageSize (pSpec := pSpec) roundIdx) := response
      let verifierMessage : pSpec.Challenge roundIdx := Deserialize.deserialize responseVec
      ⟨.inr ⟨roundIdx, key⟩, verifierMessage⟩

omit [DecidableEq StmtIn] [SpongeSize] in
/-- The two line-4 per-entry remaps agree after `gToELogEntry`. -/
private lemma hyb1RemapEntry?_eq_hyb2RemapEntry?_gToELogEntry
    {Salt : Type} [SaltCodec U δ Salt]
    (entry : Sigma (oSpec + gSpec (U := U) StmtIn pSpec δ)) :
    hyb1RemapEntry? (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        (Salt := Salt) entry
      = hyb2RemapEntry? (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (δ := δ) (Salt := Salt)
          (gToELogEntry (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            (δ := δ) entry) := by
  obtain ⟨q, response⟩ := entry
  rcases q with query | ⟨roundIdx, stmt, salt, encodedProverMessages⟩
  · rfl
  · rcases h : hybEncodedProverMessagesBefore? (pSpec := pSpec) (U := U)
        roundIdx encodedProverMessages
      with _ | messagesBefore
    · simp only [hyb1RemapEntry?, hyb2RemapEntry?, gToELogEntry, h]
    · simp only [hyb1RemapEntry?, hyb2RemapEntry?, gToELogEntry, h]

omit [DecidableEq StmtIn] [SpongeSize] in
/-- **`Hyb₁`/`Hyb₂` line-4 maps identify a `gSpec` log with its decoded `eSpec` image.**

The log half of the Claim 5.22 `Hyb₁`-vs-`Hyb₂` coupling: whenever a `Hyb₂` run's raw
verifier message log is the entry-wise decoding of a `Hyb₁` run's, the two runs' line-4 traces are
literally equal. -/
theorem hyb1TraceTranslation_eq_hyb2TraceTranslation_map
    {Salt : Type} [SaltCodec U δ Salt]
    (log : TaggedQueryLog (oSpec + gSpec (U := U) StmtIn pSpec δ)) :
    hyb1TraceTranslation (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        (Salt := Salt) log
      = hyb2TraceTranslation (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (δ := δ) (Salt := Salt)
          (log.map fun e => (e.1,
            gToELogEntry (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
              (δ := δ) e.2)) := by
  simp only [hyb1TraceTranslation, hyb2TraceTranslation, List.filterMap_map, Function.comp_def]
  refine congrArg pure (List.filterMap_congr fun e _ => ?_)
  obtain ⟨tag, entry⟩ := e
  rw [hyb1RemapEntry?_eq_hyb2RemapEntry?_gToELogEntry (Salt := Salt) entry]

end TraceTranslation

/-! ## Parse-success lemmas for `φ⁻¹` (§5.8 obligation B)

`d2sHandleBacktrackSome` gates every `gᵢ`-query behind the codec-image predicate
`∀ ι ≤ i, α̂_ι ∈ Im(φ_ι)`.  The lemmas below show that this predicate implies that the codec
bridge's `φ⁻¹` parse (`hybEncodedProverMessagesBefore?`) succeeds, so the `OptionT`-abort branch of
`d2sCodecBridgeImpl` is unreachable from `D2SQuery`-issued `gᵢ`-queries. -/

section ParseSuccess

omit [SpongeUnit U] [SpongeSize] in
/-- **Obligation B (parse success).**  If every encoded block below the round index has a
`serialize` preimage (the §5.4 Item 4(d)/(e) codec-image predicate), the codec bridge's `φ⁻¹`
parse succeeds. -/
theorem hybEncodedProverMessagesBefore?_isSome
    (roundIdx : pSpec.ChallengeIdx)
    (ems : pSpec.EncodedProverMessagesBefore U roundIdx.1.castSucc)
    (h : ∀ (j : pSpec.MessageIdx) (hj : j.1.1 < roundIdx.1.1),
      ∃ msg : pSpec.Message j, Serialize.serialize msg = ems ⟨j, hj⟩) :
    (hybEncodedProverMessagesBefore? (pSpec := pSpec) (U := U) roundIdx ems).isSome := by
  classical
  let messages : pSpec.MessagesUpTo roundIdx.1.castSucc := fun j =>
    (h ⟨j.1.castLE roundIdx.1.isLt.le, j.2⟩ j.1.isLt).choose
  unfold hybEncodedProverMessagesBefore? decodeProverMessagesPrefixPhiInv?
  exact Option.isSome_iff_exists.mpr ⟨messages,
    decodeProverMessagesPrefix_build_eq ems _ le_rfl messages (fun j hDir hj =>
      (h ⟨j, hDir⟩ hj).choose_spec.symm)⟩

/-! ## Parse-injectivity lemmas for `φ⁻¹` (§5.8 obligation A)

`hybEncodedProverMessagesBefore?` determines its input: every successfully parsed message block
re-serializes to the encoded block it was parsed from (`hybEncodedProverMessagesBefore?_serialize`),
hence two encoded prefixes parsing to the same message prefix are equal
(`hybEncodedProverMessagesBefore?_inj`).  This is the dec-injectivity fact behind the §5.8
`Hyb₂`/`Hyb₃` carrier re-indexing (`decodeEKey` in `Hyb2Hyb3Indistinguishability` is injective). -/

section ParseInjective

omit [SpongeUnit U] [SpongeSize] in
/-- `φ_j⁻¹` roundtrip on a successful inversion: the recovered message re-serializes to the
encoded block.  (Renamed from claim-5-23's `decodeProverMessagePhiInv?_serialize` at integration:
the claim-5-24 lemma of that name in `section PhiInvRoundTrip` states the other direction.) -/
private lemma serialize_of_decodeProverMessagePhiInv?
    (msgIdx : pSpec.MessageIdx) (encoded : Vector U (proverMessageSize msgIdx))
    {msg : pSpec.Message msgIdx}
    (h : decodeProverMessagePhiInv? (pSpec := pSpec) (U := U) msgIdx encoded = some msg) :
    Serialize.serialize msg = encoded := by
  unfold decodeProverMessagePhiInv? at h
  simpa using List.find?_some h

omit [SpongeUnit U] [SpongeSize] in
/-- The `φ⁻¹` prefix walk determines its input blocks: any successful prefix parse up to a
cutoff `k` re-serializes, position by position, to the encoded blocks it consumed. -/
private lemma decodeProverMessagesPrefixPhiInv?_build_serialize
    (roundIdx : pSpec.ChallengeIdx)
    (ems : pSpec.EncodedProverMessagesBefore U roundIdx.1.castSucc)
    (k : Fin (n + 1)) :
    ∀ (m : pSpec.MessagesUpTo k),
      (Fin.induction (motive := fun k => Option (pSpec.MessagesUpTo k))
        (some default)
        (fun j ih =>
          match ih with
          | none => none
          | some messages =>
              decodeProverMessagesPrefixStepPhiInv (pSpec := pSpec) (U := U)
                (EncodedProverMessagesBefore.toList (pSpec := pSpec) (U := U) ems) j messages)
        k) = some m →
    ∀ (jf : Fin n) (hdir : pSpec.dir jf = .P_to_V) (hjk : jf.1 < k.1)
      (hjr : jf.1 < roundIdx.1.1),
      codec.encode ⟨jf, hdir⟩ (m ⟨⟨jf.1, hjk⟩, hdir⟩)
        = ems ⟨⟨jf, hdir⟩, hjr⟩ := by
  classical
  induction k using Fin.induction with
  | zero =>
    intro m _ jf hdir hjk hjr
    exact absurd hjk (Nat.not_lt_zero _)
  | succ j' ihj =>
    intro m hm jf hdir hjk hjr
    have hjk' : jf.1 < j'.1 + 1 := by simpa [Fin.val_succ] using hjk
    simp only [Fin.induction_succ] at hm
    split at hm
    · contradiction
    rename_i prev hprev
    unfold decodeProverMessagesPrefixStepPhiInv at hm
    split at hm
    · -- `P_to_V` round: the walk appended a decoded message.
      rename_i hDir
      dsimp only at hm
      split at hm
      · contradiction
      rename_i encodedMsg hlookup
      split at hm
      · contradiction
      rename_i msg hdec
      simp only [Option.some.injEq] at hm
      subst hm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjk' with hlt | heq
      · erw [MessagesUpTo.concat_apply_castSucc (pSpec := pSpec) prev hDir msg
          ⟨jf.1, hlt⟩ hdir]
        exact ihj prev hprev jf hdir hlt hjr
      · have hjf : jf = j' := Fin.ext heq
        subst hjf
        erw [MessagesUpTo.concat_apply_last (pSpec := pSpec) prev hDir msg hdir]
        have hser := serialize_of_decodeProverMessagePhiInv? (pSpec := pSpec) (U := U)
          ⟨jf, hDir⟩ encodedMsg hdec
        have hstored := lookupEncodedProverMessageAlphaHat?_toList (pSpec := pSpec) (U := U)
          (k := roundIdx.1.castSucc) ems ⟨jf, hDir⟩ hjr
        rw [hlookup] at hstored
        simp only [Option.some.injEq] at hstored
        exact hser.trans hstored
    · -- `V_to_P` round: the walk extended with no payload.
      rename_i hDir
      simp only [Option.some.injEq] at hm
      subst hm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjk' with hlt | heq
      · erw [MessagesUpTo.extend_apply_castSucc (pSpec := pSpec) prev hDir
          ⟨jf.1, hlt⟩ hdir]
        exact ihj prev hprev jf hdir hlt hjr
      · have hjf : jf = j' := Fin.ext heq
        subst hjf
        rw [hDir] at hdir
        exact absurd hdir (by simp)

omit [SpongeUnit U] [SpongeSize] in
/-- **Obligation A (serialize-determination).**  A successful `φ⁻¹` parse re-serializes to the
encoded prefix it consumed: the parsed value determines the encoded blocks. -/
theorem hybEncodedProverMessagesBefore?_serialize
    (roundIdx : pSpec.ChallengeIdx)
    (ems : pSpec.EncodedProverMessagesBefore U roundIdx.1.castSucc)
    {msgs : pSpec.MessagesUpTo roundIdx.1.castSucc}
    (h : hybEncodedProverMessagesBefore? (pSpec := pSpec) (U := U) roundIdx ems = some msgs)
    (jf : Fin n) (hdir : pSpec.dir jf = .P_to_V) (hjr : jf.1 < roundIdx.1.1) :
    codec.encode ⟨jf, hdir⟩ (msgs ⟨⟨jf.1, hjr⟩, hdir⟩)
      = ems ⟨⟨jf, hdir⟩, hjr⟩ := by
  unfold hybEncodedProverMessagesBefore? decodeProverMessagesPrefixPhiInv? at h
  exact decodeProverMessagesPrefixPhiInv?_build_serialize (pSpec := pSpec) (U := U)
    roundIdx ems roundIdx.1.castSucc msgs h jf hdir hjr hjr

omit [SpongeUnit U] [SpongeSize] in
/-- **Obligation A (parse-injectivity).**  Two encoded prefixes parsing (via `φ⁻¹`) to the same
message prefix are equal.  Injectivity of the §5.8 `Hyb₂`→`Hyb₃` key decoding. -/
theorem hybEncodedProverMessagesBefore?_inj
    (roundIdx : pSpec.ChallengeIdx)
    {ems ems' : pSpec.EncodedProverMessagesBefore U roundIdx.1.castSucc}
    {msgs : pSpec.MessagesUpTo roundIdx.1.castSucc}
    (h : hybEncodedProverMessagesBefore? (pSpec := pSpec) (U := U) roundIdx ems = some msgs)
    (h' : hybEncodedProverMessagesBefore? (pSpec := pSpec) (U := U) roundIdx ems' = some msgs) :
    ems = ems' := by
  funext jp
  obtain ⟨⟨jf, hdir⟩, hjr⟩ := jp
  rw [← hybEncodedProverMessagesBefore?_serialize (pSpec := pSpec) (U := U)
      roundIdx ems h jf hdir hjr,
    ← hybEncodedProverMessagesBefore?_serialize (pSpec := pSpec) (U := U)
      roundIdx ems' h' jf hdir hjr]

end ParseInjective

end ParseSuccess

end

end DuplexSpongeFS.TraceTransform
