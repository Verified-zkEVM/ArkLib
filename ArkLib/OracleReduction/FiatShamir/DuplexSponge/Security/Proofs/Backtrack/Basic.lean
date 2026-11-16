/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.TraceDataStructures

/-!
# Backtracking sequence family and procedure: core definitions

This file contains the backtracking sequence family and procedure for the analysis of duplex sponge
Fiat-Shamir, following Section 5.2 in the paper.

- `BacktrackSequence`: a single backtrack sequence
- `S_BT/BacktrackSequenceFamily`: a set of lawful backtrack sequences of a `(h,p,p⁻¹)`-trace,
  consumed as an explicit structure hypothesis by the bad-event lemmas (`BadEvents`,
  `AbortAnalysis`); no family-enumeration algorithm is provided — the executable surface is
  the linear scan (see the design note in `section S_BT_BacktrackComputation`).
- `J_BT`: the set of occurence index sequences of `S_BT`
  - `BacktrackSequence.Index`: compute the index sequence of a single backtrack sequence.
- `backTrack`: the core backtrack algorithm
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.Backtrack

open DSTraceStorage

variable {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasProverMessageSize pSpec] [HasVerifierMessageSize pSpec]
  {δ : Nat}

section CoreDefinitions
/-- **[CO25, Definition 5.3]** A backtracking sequence (Definition 5.3) for a given
  hash-duplex-sponge oracle trace `tr` and final permutation state `s` consists of the following
  data:
- An input statement `𝕩`
- A list `inputState = [sᵢₙ, ...]` of input states
- A list `outputState = [sₒᵤₜ, ...]` of output states

subject to the following conditions:
- The last of the input states is the given final state
- There is one more input state than output state
- The statement is queried with the hash, and returns the capacity of the first input state
  `(hash, 𝕩, inputState[0].capacitySegment) ∈ tr` -/
structure BacktrackSequence (trace : QueryLog (duplexSpongeOracle StmtIn U))
    (state : CanonicalSpongeState U) where
  /-- `𝕩^(k) ∈ {0,1}^≤n` — input statement for this backtracking sequence. -/
  stmt : StmtIn
  /-- `[s_{in,0}^(k), …, s_{in,m_k}^(k)]` — input permutation states of the chain; length
  `m_k + 1`. -/
  inputState : List (CanonicalSpongeState U)
  /-- `[s_{out,0}^(k), …, s_{out,m_k-1}^(k)]` — output permutation states; one shorter than
  inputs. -/
  outputState : List (CanonicalSpongeState U)

  /-- `|inputState| = |outputState| + 1` -/
  inputState_length_eq_outputState_length_succ : inputState.length = outputState.length + 1

  /-- `inputState[m_k] = s` — last input equals the given final state.
    [CO25, Def 5.3, condition (a)]. -/
  last_inputState_eq_state : inputState[inputState.length - 1] = state

  /-- `(h, 𝕩, inputState[0].capacitySegment) ∈ tr` — hash query anchors capacity.
    [CO25, Def 5.3, condition (b)]. -/
  hash_in_trace : ⟨.inl stmt, (Vector.drop inputState[0] SpongeSize.R)⟩ ∈ trace

  /-- **input-output states agree with p**: For all `ι < m_k`, either
    `(p, s_{in,ι}, s_{out,ι}) ∈ tr` or `(p⁻¹, s_{out,ι}, s_{in,ι}) ∈ tr`.
    [CO25, Def 5.3, condition (c)]. -/
  permute_or_inv_in_trace : ∀ i : Fin outputState.length,
    ⟨.inr (.inl inputState[i]), outputState[i]⟩ ∈ trace
    ∨ ⟨.inr (.inr outputState[i]), inputState[i]⟩ ∈ trace

  /-- **the capacity segment is shared across queries**: `s_{C,out,ι} = s_{C,in,ι+1}`
    for all `ι < m_k`. [CO25, Def 5.3, condition (d)]. -/
  capacitySegment_output_eq_input : ∀ i : Fin outputState.length,
    outputState[i].capacitySegment = inputState[i.val + 1].capacitySegment

  /-- **no “loops” across query and answer capacity segments**: `s_{C,in,ι} ≠ s_{C,out,ι}`
    for all `ι < m_k`. [CO25, Def 5.3, condition (e)]. -/
  capacitySegment_input_ne_output : ∀ i : Fin outputState.length,
    inputState[i].capacitySegment ≠ outputState[i].capacitySegment

noncomputable section

/-- The flattened sequence of states: `[s_{in,0}, s_{out,0}, s_{in,1}, s_{out,1}, ..., s]`. -/
def BacktrackSequence.flattenStateSequence
    {trace : QueryLog (duplexSpongeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) : List (CanonicalSpongeState U) :=
  (seq.inputState.zip seq.outputState).foldr (fun p acc => p.1 :: p.2 :: acc) [state]

noncomputable def matchesEntry
    (entry x : (t : (duplexSpongeOracle StmtIn U).Domain) ×
      (duplexSpongeOracle StmtIn U).Range t) : Bool := by
  classical
  exact decide (x = entry)

noncomputable def matchesEitherEntry
    (entryA entryB x : (t : (duplexSpongeOracle StmtIn U).Domain) ×
      (duplexSpongeOracle StmtIn U).Range t) : Bool := by
  classical
  exact decide (x = entryA ∨ x = entryB)

/-- First-occurrence index of an entry in a trace. -/
def firstOccurrenceIndex
    (trace : QueryLog (duplexSpongeOracle StmtIn U))
    (entry : (t : (duplexSpongeOracle StmtIn U).Domain) ×
      (duplexSpongeOracle StmtIn U).Range t)
    (hEntry : entry ∈ trace) : Fin trace.length := by
  classical
  exact ⟨trace.findIdx (matchesEntry entry), List.findIdx_lt_length_of_exists
    ⟨entry, hEntry, by simp [matchesEntry]⟩⟩

/-- First-occurrence index of EITHER entryA or entryB in a trace. -/
def firstOccurrenceOfEither
    (trace : QueryLog (duplexSpongeOracle StmtIn U))
    (entryA entryB : (t : (duplexSpongeOracle StmtIn U).Domain) ×
      (duplexSpongeOracle StmtIn U).Range t)
    (hEntry : entryA ∈ trace ∨ entryB ∈ trace) : Fin trace.length := by
  classical
  exact ⟨trace.findIdx (matchesEitherEntry entryA entryB),
    List.findIdx_lt_length_of_exists (by
      rcases hEntry with hA | hB
      · exact ⟨entryA, hA, by simp [matchesEitherEntry]⟩
      · exact ⟨entryB, hB, by simp [matchesEitherEntry]⟩)⟩

/-- **[CO25, Definition 5.4]** First-occurrence indices `(j_h; j₀, …, jₘ)` for one
backtracking sequence. Indices are zero-based; `jₘ = trace.length` denotes the upcoming query. -/
def BacktrackSequence.Index (trace : QueryLog (duplexSpongeOracle StmtIn U))
    (state : CanonicalSpongeState U) (seq : BacktrackSequence trace state) :
    Fin trace.length × (Fin seq.inputState.length → Fin (trace.length + 1)) := by
    classical
    have hInputStateNonempty : 0 < seq.inputState.length := by
      rw [seq.inputState_length_eq_outputState_length_succ]
      exact Nat.succ_pos _
    let inputState0 : CanonicalSpongeState U := -- first permutation state after the hash query
      seq.inputState[0]' hInputStateNonempty
    -- Get first occurrence indices of queries
    let firstHashQueryIdx : Fin trace.length :=
      firstOccurrenceIndex (StmtIn := StmtIn) (U := U)
        trace
        ⟨.inl seq.stmt, (Vector.drop inputState0 SpongeSize.R)⟩
        seq.hash_in_trace
    -- tight occurence index function for inner permutation query pairs `(s_{in,i},s_{out,i})`
    let permQueryIdxFunc : Fin seq.outputState.length → Fin trace.length := fun i =>
      let inputIdx : Fin seq.inputState.length := ⟨i.1, by
        have hi : i.1 < seq.outputState.length + 1 := Nat.lt_succ_of_lt i.2
        rw [seq.inputState_length_eq_outputState_length_succ]; exact hi⟩
      firstOccurrenceOfEither (trace := trace)
        (entryA := ⟨.inr (.inl seq.inputState[inputIdx]), seq.outputState[i]⟩)
        (entryB := ⟨.inr (.inr seq.outputState[i]), seq.inputState[inputIdx]⟩)
        (hEntry := seq.permute_or_inv_in_trace (i := i))
    -- simple utility for mapping indices from smaller Fin to larger Fin
    let embedTraceFinIdx : Fin trace.length → Fin (trace.length + 1) :=
      fun j => ⟨j.1, Nat.lt_succ_of_lt j.2⟩
    exact (firstHashQueryIdx, fun (pairIdx: Fin (seq.inputState.length)) =>
      if h : pairIdx.1 < seq.outputState.length then
        embedTraceFinIdx (permQueryIdxFunc ⟨pairIdx.1, h⟩) -- inner pairs
      else
        ⟨trace.length, Nat.lt_succ_self trace.length⟩) -- last pair

/-! ### First-occurrence / `Index` specification lemmas

These expose what `BacktrackSequence.Index` computes: the hash-query index points at the hash
anchor entry (and is the first such occurrence), and each permutation-step index points at one of
the two query forms `(p, s_in, s_out)` / `(p⁻¹, s_out, s_in)` (and is the first occurrence of
either form).  Downstream (Lemmas 5.12/5.14/5.16) these "first occurrence" facts are what place
the representative into the base trace `tr̄`. -/

section IndexSpec

variable {trace : QueryLog (duplexSpongeOracle StmtIn U)}
  {state : CanonicalSpongeState U}

/-- `firstOccurrenceIndex` indexes the given entry. -/
lemma firstOccurrenceIndex_get
    (entry : (t : (duplexSpongeOracle StmtIn U).Domain) ×
      (duplexSpongeOracle StmtIn U).Range t) (hEntry : entry ∈ trace) :
    trace.get (firstOccurrenceIndex trace entry hEntry) = entry := by
  classical
  rw [List.get_eq_getElem]
  have h := of_decide_eq_true (List.findIdx_getElem (xs := trace)
    (p := matchesEntry entry)
    (w := (firstOccurrenceIndex trace entry hEntry).isLt))
  with_unfolding_all exact h

/-- No earlier position than `firstOccurrenceIndex` carries the entry. -/
lemma firstOccurrenceIndex_not_mem_take
    (entry : (t : (duplexSpongeOracle StmtIn U).Domain) ×
      (duplexSpongeOracle StmtIn U).Range t) (hEntry : entry ∈ trace) :
    entry ∉ trace.take (firstOccurrenceIndex trace entry hEntry).val := by
  classical
  intro hmem
  simpa [matchesEntry] using
    (List.false_of_mem_take_findIdx (p := matchesEntry entry) hmem)

/-- `firstOccurrenceOfEither` indexes one of the two entries. -/
lemma firstOccurrenceOfEither_get
    (entryA entryB : (t : (duplexSpongeOracle StmtIn U).Domain) ×
      (duplexSpongeOracle StmtIn U).Range t)
    (hEntry : entryA ∈ trace ∨ entryB ∈ trace) :
    trace.get (firstOccurrenceOfEither trace entryA entryB hEntry) = entryA ∨
    trace.get (firstOccurrenceOfEither trace entryA entryB hEntry) = entryB := by
  classical
  rw [List.get_eq_getElem]
  have h := of_decide_eq_true (List.findIdx_getElem (xs := trace)
    (p := matchesEitherEntry entryA entryB)
    (w := (firstOccurrenceOfEither trace entryA entryB hEntry).isLt))
  with_unfolding_all exact h

/-- No earlier position than `firstOccurrenceOfEither` carries either entry. -/
lemma firstOccurrenceOfEither_not_mem_take
    (entryA entryB : (t : (duplexSpongeOracle StmtIn U).Domain) ×
      (duplexSpongeOracle StmtIn U).Range t)
    (hEntry : entryA ∈ trace ∨ entryB ∈ trace) :
    entryA ∉ trace.take (firstOccurrenceOfEither trace entryA entryB hEntry).val ∧
    entryB ∉ trace.take (firstOccurrenceOfEither trace entryA entryB hEntry).val := by
  classical
  constructor <;> intro hmem <;>
    simpa [matchesEitherEntry] using
      (List.false_of_mem_take_findIdx (p := matchesEitherEntry entryA entryB) hmem)

/-- The hash-query index `j_h` of a sequence indexes the hash anchor entry. -/
lemma BacktrackSequence.Index_fst_get (seq : BacktrackSequence trace state)
    (hpos : 0 < seq.inputState.length) :
    trace.get (BacktrackSequence.Index trace state seq).1
      = ⟨.inl seq.stmt, Vector.drop (seq.inputState[0]'hpos) SpongeSize.R⟩ :=
  firstOccurrenceIndex_get _ seq.hash_in_trace

/-- The hash anchor entry of a sequence does not occur before its `j_h` index. -/
lemma BacktrackSequence.Index_fst_not_mem_take (seq : BacktrackSequence trace state)
    (hpos : 0 < seq.inputState.length) :
    (⟨.inl seq.stmt, Vector.drop (seq.inputState[0]'hpos) SpongeSize.R⟩ : duplexSpongeTraceEntry)
        ∉ trace.take ((BacktrackSequence.Index trace state seq).1).val :=
  firstOccurrenceIndex_not_mem_take _ seq.hash_in_trace

/-- The value of the permutation-step index reduces to the first occurrence of either query form. -/
lemma BacktrackSequence.Index_snd_val (seq : BacktrackSequence trace state)
    (i : Fin seq.outputState.length) (hi : (i : ℕ) < seq.inputState.length) :
    ((BacktrackSequence.Index trace state seq).2 ⟨i.val, hi⟩).val
      = (firstOccurrenceOfEither trace
          ⟨.inr (.inl seq.inputState[i.val]), seq.outputState[i.val]⟩
          ⟨.inr (.inr seq.outputState[i.val]), seq.inputState[i.val]⟩
          (seq.permute_or_inv_in_trace i)).val := by
  classical
  simp only [BacktrackSequence.Index]
  rw [dite_eq_left i.isLt]
  rfl

/-- Each permutation-step index `j_ι` indexes one of the two query forms of the step. -/
lemma BacktrackSequence.Index_snd_getElem? (seq : BacktrackSequence trace state)
    (i : Fin seq.outputState.length) (hi : (i : ℕ) < seq.inputState.length) :
    (trace)[((BacktrackSequence.Index trace state seq).2 ⟨i.val, hi⟩).val]?
        = some ⟨.inr (.inl seq.inputState[i.val]), seq.outputState[i.val]⟩ ∨
    (trace)[((BacktrackSequence.Index trace state seq).2 ⟨i.val, hi⟩).val]?
        = some ⟨.inr (.inr seq.outputState[i.val]), seq.inputState[i.val]⟩ := by
  classical
  have hval := BacktrackSequence.Index_snd_val (trace := trace) (state := state) seq i hi
  have hb : (firstOccurrenceOfEither trace
      ⟨.inr (.inl seq.inputState[i.val]), seq.outputState[i.val]⟩
      ⟨.inr (.inr seq.outputState[i.val]), seq.inputState[i.val]⟩
      (seq.permute_or_inv_in_trace i)).val < trace.length :=
    (firstOccurrenceOfEither trace _ _ (seq.permute_or_inv_in_trace i)).isLt
  rcases firstOccurrenceOfEither_get (trace := trace)
      ⟨.inr (.inl seq.inputState[i.val]), seq.outputState[i.val]⟩
      ⟨.inr (.inr seq.outputState[i.val]), seq.inputState[i.val]⟩
      (seq.permute_or_inv_in_trace i) with h | h <;>
    rw [List.get_eq_getElem] at h
  · exact Or.inl (by rw [hval, List.getElem?_eq_getElem hb, h])
  · exact Or.inr (by rw [hval, List.getElem?_eq_getElem hb, h])

/-- Past the last permutation step, the index function returns `|trace|` (the "current state"
sentinel). -/
lemma BacktrackSequence.Index_snd_eq_length (seq : BacktrackSequence trace state)
    {k : ℕ} (hk : seq.outputState.length ≤ k) (hki : k < seq.inputState.length) :
    ((BacktrackSequence.Index trace state seq).2 ⟨k, hki⟩).val = trace.length := by
  classical
  simp only [BacktrackSequence.Index]
  rw [dite_eq_right (by omega)]

/-- Neither query form of step `ι` occurs before its `j_ι` index. -/
lemma BacktrackSequence.Index_snd_not_mem_take (seq : BacktrackSequence trace state)
    (i : Fin seq.outputState.length) (hi : (i : ℕ) < seq.inputState.length) :
    (⟨.inr (.inl seq.inputState[i.val]), seq.outputState[i.val]⟩ : duplexSpongeTraceEntry)
        ∉ trace.take ((BacktrackSequence.Index trace state seq).2 ⟨i.val, hi⟩).val ∧
    (⟨.inr (.inr seq.outputState[i.val]), seq.inputState[i.val]⟩ : duplexSpongeTraceEntry)
        ∉ trace.take ((BacktrackSequence.Index trace state seq).2 ⟨i.val, hi⟩).val := by
  rw [BacktrackSequence.Index_snd_val]
  exact firstOccurrenceOfEither_not_mem_take _ _ (seq.permute_or_inv_in_trace i)

end IndexSpec

/-- **[CO25, Definition 5.3]** Supplied finite family `S_BT(tr, s)` of hash-anchored
backtracking sequences ending at `s`. Distinct members with the same statement form an
antichain under sublist inclusion of their flattened states. This internal condition does
not assert global maximality or enumerate all valid sequences; the family may be empty. -/
structure BacktrackSequenceFamily (trace : QueryLog (duplexSpongeOracle StmtIn U))
    (state : CanonicalSpongeState U) where
  /-- `S_BT(tr, s)` — finite set of backtrack sequences [CO25, Def 5.3]. -/
  seqFamily : Finset (BacktrackSequence trace state)
  /-- Internal antichain condition: distinct members with the same statement cannot have
  one flattened state list included as a sublist of the other. -/
  maximality : ∀ s ∈ seqFamily, ∀ s' ∈ seqFamily, s ≠ s' →
    ¬ (s.stmt = s'.stmt ∧ s.flattenStateSequence.Sublist s'.flattenStateSequence)

/-- **[CO25, Definition 5.3]** `S_BT(tr,s)` family of backtracking sequences. -/
abbrev S_BT
    (trace : QueryLog (duplexSpongeOracle StmtIn U))
    (state : CanonicalSpongeState U) :=
  BacktrackSequenceFamily trace state

/-- Extensionality for `BacktrackSequence`: two sequences are equal once their three data fields
(`stmt`, `inputState`, `outputState`) agree.  The remaining fields are `Prop`-valued, so they are
equal by proof irrelevance. -/
@[ext]
lemma BacktrackSequence.ext
    {trace : QueryLog (duplexSpongeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    {s₁ s₂ : BacktrackSequence trace state}
    (hstmt : s₁.stmt = s₂.stmt)
    (hin : s₁.inputState = s₂.inputState)
    (hout : s₁.outputState = s₂.outputState) : s₁ = s₂ := by
  cases s₁; cases s₂
  simp only at hstmt hin hout
  subst hstmt; subst hin; subst hout
  rfl

/-- **[CO25, Definition 5.4]** Index list payload attached to one sequence. -/
abbrev BacktrackIndexList
    (trace : QueryLog (duplexSpongeOracle StmtIn U))
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) :=
  Fin trace.length × (Fin seq.inputState.length → Fin (trace.length + 1))

open Classical in
/-- **[CO25, Definition 5.4]** `J_BT(tr,s)` — the image of `S_BT(tr,s)` under
`BacktrackSequence.Index`. Every sequence in `S_BT` is paired with its unique index list; no
sequence is omitted. -/
def J_BT
    {trace : QueryLog (duplexSpongeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (family : BacktrackSequenceFamily trace state) :
    Finset (Sigma fun seq : BacktrackSequence trace state => BacktrackIndexList trace seq) :=
  family.seqFamily.image (fun seq => ⟨seq, BacktrackSequence.Index trace state seq⟩)

end
end CoreDefinitions

section BacktrackProcedure

variable [DecidableEq StmtIn] [DecidableEq U] {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- **[CO25, §5.2 Step 4(a)iii.D]** Output tuple `(i, 𝕩, τ, (α̂_1,…,α̂_i))` of BackTrack's
pre-squeeze marker, stored in `Outs`. -/
    -- if it fails the filter (e.g. bad salt/messages), return `none`
structure BacktrackOutput where
  roundIdx : pSpec.ChallengeIdx
  stmt : StmtIn
  salt : Vector U δ
  /-- `(α̂_1, …, α̂_i)` — encoded prover messages up to verifier message `i`, indexed by
  prover-message index. -/
  encodedProverMessages : pSpec.EncodedProverMessagesBefore U roundIdx.1.castSucc

section S_BT_BacktrackComputation

/- Design note [CO25, §5.2]: we deliberately provide **no executable enumeration** of the full
backtrack-sequence family `S_BT(tr, s)` (Definition 5.3). The executable `backTrack` below uses
the single-chain linear scan with scan-time fork detection — CO25's own "look for at most one
element" optimization. Downstream proofs (`BadEvents`, `AbortAnalysis`) quantify
over `S_BT` as an explicit structure hypothesis and never need to compute the family.

Forward-first restriction (see the section note at `backTrackFwd`): a scan-time fork is **not**
in general subsumed by `E_fork,p ∪ E_fork,h,p`. The
bidirectional `tr_∇.p` records the pair created by an inverse query `p⁻¹(t) = s'`, and a prover
that picks `t` with `t.capacitySegment = cur.capacitySegment` (but `t ≠ cur`) branches the scan
at `cur` for free. CO25's family cannot contain that decoy chain: Def. 5.3(b) requires a hash
anchor for the chain's first input capacity, which the `p⁻¹`-rooted chain does not have. The
event `E` of Def. 5.7 does not fire either, since it charges only *answer* capacities while `t`
is the adversary-chosen *input* of the `p⁻¹` query. The oracle wrapper and StdTrace therefore
call `backTrackFwd`, which runs this scan over the forward-first sub-index of `tr_∇.p`; the
raw `backTrack` is kept for the audit counterexample and for `p⁻¹`-free callers. -/

/-- Paper §5.2 partial-cap-segment matching for `BackTrack`: enumerate all distinct
`(stateIn, stateOut)` pairs in `tr_∇.p` whose output capacity matches the next input capacity.
The linear scan separately rejects self-loops (`stateIn.cap = stateOut.cap`) and repeated input
capacities as invalid candidates.

Black-box over `[LawfulTraceTable T_P ...]` via `TraceTableOps.entries`; both forward and inverse
permutation directions already collapse into the same bidirectional `tr_∇.p`
(cf. `TraceNabla.ofQueryLog` dispatch). -/
-- TODO: Replace this linear `entries` scan with a conflict-aware, logarithmic lookup by output
-- capacity, as required by [CO25, Eq. (15)].
def predecessorCandidates
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (nextInputCap : Vector U SpongeSize.C) :
    List (CanonicalSpongeState U × CanonicalSpongeState U) := by
  exact ((TraceTableOps.entries (V := CanonicalSpongeState U) trΔ.p).filterMap fun pair =>
    let stateOut := pair.2
    if stateOut.capacitySegment = nextInputCap then some pair else none).dedup

/-! ### Linear-scan helpers ([CO25, §5.2] BackTrack "look for at most one element" optimization)

The paper's Algorithm 1 enumerates all maximal sequences then post-filters. [CO25, §5.2] notes
the procedure can equivalently `look for at most one element` — i.e. abort on scan-time forks.
This is faithful only once the candidate source is restricted to mappings from which a
hash-anchored chain can be built; use `backTrackFwd` when modeling the oracle wrapper. -/

/-- Three-way classification of lookup results, used to detect scan-time forks. -/
inductive LookupResult (α : Type _) where
  | noMatch
  | unique (a : α)
  | conflict

def classifyLookup {α : Type _} (xs : List α) : LookupResult α :=
  match xs with
  | [] => .noMatch
  | [a] => .unique a
  | _ :: _ :: _ => .conflict

/-- Hash-anchor lookup of the `BackTrack` scan ([CO25, Definition 5.3, second item; §5.2
time-complexity paragraph]): collect distinct statements whose stored capacity
matches the chain's initial capacity. Multiple distinct matches indicate `E_fork,h,p`. -/
def hashAnchorCandidates
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (cap : Vector U SpongeSize.C) : List StmtIn := by
  classical
  exact ((TraceTableOps.entries (V := Vector U SpongeSize.C) trΔ.h).filterMap fun pair =>
    if pair.2 = cap then some pair.1 else none).dedup

/-! ### Helper lemmas connecting `trΔ.h`/`trΔ.p` entries to the original `trace`

The key insight: `toMultiSet_ofEntries` equates public-entry and abstract membership, while
`mem_toMultiSet_insert_iff` says each fold step preserves old pairs and represents the current
pair. Induction therefore connects table membership back to an original trace entry. -/

/-- An intermediate data structure representing a partially constructed backtrack sequence.
It carries all incremental properties of a valid chain from `head` to
`targetState`, without the hash anchor. This allows us to construct the sequence
iteratively via prepending (`::`), making structural induction proofs trivial. -/
structure PartialBacktrackSequence (trace : QueryLog (duplexSpongeOracle StmtIn U))
    (head targetState : CanonicalSpongeState U) where
  inputState : List (CanonicalSpongeState U)
  outputState : List (CanonicalSpongeState U)

  inputState_length_eq_outputState_length_succ : inputState.length = outputState.length + 1

  first_inputState_eq_head : inputState.head? = some head
  last_inputState_eq_state : inputState[inputState.length - 1]'(by omega) = targetState

  permute_or_inv_in_trace : ∀ i : Fin outputState.length,
    ⟨.inr (.inl inputState[i]), outputState[i]⟩ ∈ trace
    ∨ ⟨.inr (.inr outputState[i]), inputState[i]⟩ ∈ trace

  capacitySegment_output_eq_input : ∀ i : Fin outputState.length,
    outputState[i].capacitySegment = inputState[i.val + 1].capacitySegment

  capacitySegment_input_ne_output : ∀ i : Fin outputState.length,
    inputState[i].capacitySegment ≠ outputState[i].capacitySegment

def emptyPartialSequence (trace : QueryLog (duplexSpongeOracle StmtIn U))
    (targetState : CanonicalSpongeState U) :
    PartialBacktrackSequence trace targetState targetState :=
  { inputState := [targetState]
    outputState := []
    inputState_length_eq_outputState_length_succ := rfl
    first_inputState_eq_head := rfl
    last_inputState_eq_state := rfl
    permute_or_inv_in_trace := by intro i; exact i.elim0
    capacitySegment_output_eq_input := by intro i; exact i.elim0
    capacitySegment_input_ne_output := by intro i; exact i.elim0 }

def prependPartialSequence
    (trace : QueryLog (duplexSpongeOracle StmtIn U))
    (targetState seq_head : CanonicalSpongeState U)
    (s_in s_out : CanonicalSpongeState U)
    (seq : PartialBacktrackSequence trace seq_head targetState)
    (hMatch : s_out.capacitySegment = seq_head.capacitySegment)
    (hEntry : ⟨.inr (.inl s_in), s_out⟩ ∈ trace ∨ ⟨.inr (.inr s_out), s_in⟩ ∈ trace)
    (hNoLoop : s_in.capacitySegment ≠ s_out.capacitySegment) :
    PartialBacktrackSequence trace s_in targetState :=
  { inputState := s_in :: seq.inputState
    outputState := s_out :: seq.outputState
    inputState_length_eq_outputState_length_succ := by
      have h := seq.inputState_length_eq_outputState_length_succ
      simp [h]
    first_inputState_eq_head := rfl
    last_inputState_eq_state := by
      cases seq with
      | mk inputState outputState hLen hFirst hLast hTrace hCapOut hCapIn =>
          cases inputState with
          | nil =>
              simp at hLen
          | cons a tail =>
              exact hLast
    permute_or_inv_in_trace := by
      intro i
      match i with
      | ⟨0, h⟩ => exact hEntry
      | ⟨i' + 1, h⟩ =>
          have hi' : i' < seq.outputState.length := by
            have hl : (s_out :: seq.outputState).length = seq.outputState.length + 1 := rfl
            omega
          exact seq.permute_or_inv_in_trace ⟨i', hi'⟩
    capacitySegment_output_eq_input := by
      intro i
      match i with
      | ⟨0, h⟩ =>
          cases seq with
          | mk inputState outputState hLen hFirst hLast hTrace hCapOut hCapIn =>
              cases inputState with
              | nil =>
                  simp at hLen
              | cons a tail =>
                  have ha : a = seq_head := Option.some.inj hFirst
                  have hc : (s_in :: a :: tail)[1] = seq_head := ha
                  rw [hc]
                  exact hMatch
      | ⟨i' + 1, h⟩ =>
          have hi' : i' < seq.outputState.length := by
            have hl : (s_out :: seq.outputState).length = seq.outputState.length + 1 := rfl
            omega
          exact seq.capacitySegment_output_eq_input ⟨i', hi'⟩
    capacitySegment_input_ne_output := by
      intro i
      match i with
      | ⟨0, h⟩ => exact hNoLoop
      | ⟨i' + 1, h⟩ =>
          have hi' : i' < seq.outputState.length := by
            have hl : (s_out :: seq.outputState).length = seq.outputState.length + 1 := rfl
            omega
          exact seq.capacitySegment_input_ne_output ⟨i', hi'⟩ }

def completeBacktrackSequence
    (trace : QueryLog (duplexSpongeOracle StmtIn U))
    (targetState head : CanonicalSpongeState U)
    (stmt : StmtIn)
    (seq : PartialBacktrackSequence trace head targetState)
    (hHash : ⟨.inl stmt, (Vector.drop head SpongeSize.R)⟩ ∈ trace) :
    BacktrackSequence trace targetState :=
  { stmt := stmt
    inputState := seq.inputState
    outputState := seq.outputState
    inputState_length_eq_outputState_length_succ := seq.inputState_length_eq_outputState_length_succ
    last_inputState_eq_state := by
      have h := seq.last_inputState_eq_state
      exact h
    hash_in_trace := by
      cases seq with
      | mk inputState outputState hLen hFirst hLast hTrace hCapOut hCapIn =>
          cases inputState with
          | nil =>
              simp at hLen
          | cons a tail =>
              have ha : a = head := Option.some.inj hFirst
              have ht : (a :: tail)[0]'(by omega) = head := ha
              have ht2 : (a :: tail)[0] = head := ht
              rw [ht2]
              exact hHash
    permute_or_inv_in_trace := seq.permute_or_inv_in_trace
    capacitySegment_output_eq_input := seq.capacitySegment_output_eq_input
    capacitySegment_input_ne_output := seq.capacitySegment_input_ne_output }

/-! ### Bridge lemmas: `classifyLookup` + `filterMap` → entry membership -/

omit [SpongeSize] in
lemma classifyLookup_filterMap_singleton_mem {α β : Type _} [DecidableEq β]
    (l : List α) (f : α → Option β) (b : β)
    (h : classifyLookup (l.filterMap f).dedup = .unique b) :
    ∃ a ∈ l, f a = some b := by
  have hs : (l.filterMap f).dedup = [b] := by
    match he : (l.filterMap f).dedup with
    | [] | _ :: _ :: _ => simp [he, classifyLookup] at h
    | [a] => simpa [he, classifyLookup] using h
  exact List.mem_filterMap.mp (List.mem_dedup.mp (hs ▸ List.mem_singleton_self b))

lemma hash_unique_mem_entries
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (cap : Vector U SpongeSize.C)
    (stmt : StmtIn)
    (h : classifyLookup (hashAnchorCandidates trΔ cap) = .unique stmt) :
    (stmt, cap) ∈ TraceTableOps.entries (V := Vector U SpongeSize.C) trΔ.h := by
  unfold hashAnchorCandidates at h
  classical
  have ⟨pair, hMem, hEq⟩ := classifyLookup_filterMap_singleton_mem
      (TraceTableOps.entries (V := Vector U SpongeSize.C) trΔ.h)
      (fun pair => if pair.2 = cap then some pair.1 else none) stmt h
  rcases pair with ⟨x, c⟩
  split at hEq <;> simp_all

lemma pred_unique_mem_and_cap
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (cap : Vector U SpongeSize.C)
    (s_in s_out : CanonicalSpongeState U)
    (h : classifyLookup (predecessorCandidates trΔ cap) = .unique (s_in, s_out)) :
    (s_in, s_out) ∈ TraceTableOps.entries (V := CanonicalSpongeState U) trΔ.p ∧
      s_out.capacitySegment = cap := by
  unfold predecessorCandidates at h
  classical
  have ⟨pair, hMem, hEq⟩ := classifyLookup_filterMap_singleton_mem
      (TraceTableOps.entries (V := CanonicalSpongeState U) trΔ.p)
      (fun pair => if pair.2.capacitySegment = cap then some pair else none) (s_in, s_out) h
  split at hEq
  · next hCap =>
      injection hEq with hInj; subst hInj
      exact ⟨hMem, hCap.symm ▸ rfl⟩
  · contradiction

/-- Output of a linear backwards scan: either a fork was detected, or the scan terminated
with an optional BacktrackSequence. -/
inductive LinearScanResult (trace : QueryLog (duplexSpongeOracle StmtIn U))
  (targetState : CanonicalSpongeState U) where
  | forkErr
  | noResult
  | done (seq : BacktrackSequence trace targetState)

/-- **[CO25, §5.2]** BackTrack linear backwards scan: from `currentState`, classify the predecessor
candidates in `tr_∇.p`. `[]` ends the scan; `[pred]` continues; `_::_::_` is a fork → `.forkErr`.
Loops in capacity segment are detected using `vCap` and result in `.forkErr`.
Structurally recursive on `fuel`; the caller supplies `fuel = depthBound`.
Uses a tail-recursive accumulator `acc` to build the sequence by prepending. -/
def linearScanBackwards
    (trace : QueryLog (duplexSpongeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (fuel : Nat) (currentState targetState : CanonicalSpongeState U)
    (vCap : List (Vector U SpongeSize.C))
    (acc : PartialBacktrackSequence trace currentState targetState) :
    LinearScanResult trace targetState :=
  match fuel with
  | 0 => .noResult
  | fuel' + 1 =>
    -- Look up predecessor in `tr_∇.p` [CO25, §5.2 Step 2; time-complexity paragraph]
    match hClsPred : classifyLookup (predecessorCandidates (T_P := T_P) (U := U) trΔ
      currentState.capacitySegment) with
    | .noMatch =>
        -- Not in `tr_∇.p`, check `tr_∇.h` [CO25, §5.2 Step 2; time-complexity paragraph]
        match hClsHash : classifyLookup (hashAnchorCandidates (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (U := U) trΔ currentState.capacitySegment) with
        | .noMatch => .noResult
        | .unique stmt =>
            -- Found unique anchor `h`: sequence is complete
            have hHash : ⟨.inl stmt, (Vector.drop currentState SpongeSize.R)⟩ ∈ trace := by
              have hMem : (stmt, currentState.capacitySegment) ∈
                TraceTableOps.entries (V := Vector U SpongeSize.C) trΔ.h :=
                hash_unique_mem_entries trΔ currentState.capacitySegment stmt hClsHash
              exact h_trΔ.1 _ _ hMem
            .done (completeBacktrackSequence trace targetState currentState stmt acc hHash)
        | .conflict => .forkErr -- `L_h` collision → `E_fork`
    | .unique pred =>
        -- Found unique predecessor `p / p⁻¹` [CO25, Definition 5.3, third and fourth items]
        let s_in := pred.1
        let s_out := pred.2
        if hNoLoop : s_in.capacitySegment = s_out.capacitySegment then
          .forkErr -- Self-loop → `E_inv`
        else
          have hNoLoop' : s_in.capacitySegment ≠ s_out.capacitySegment := hNoLoop
          if s_in.capacitySegment ∈ vCap then
            .forkErr -- Cycle detected
          else
            have hMatch : s_out.capacitySegment = currentState.capacitySegment :=
              (pred_unique_mem_and_cap trΔ currentState.capacitySegment s_in s_out hClsPred).2
            have hEntry : ⟨.inr (.inl s_in), s_out⟩ ∈ trace ∨
              ⟨.inr (.inr s_out), s_in⟩ ∈ trace := by
              have hMem : (s_in, s_out) ∈
                TraceTableOps.entries (V := CanonicalSpongeState U) trΔ.p :=
                (pred_unique_mem_and_cap trΔ currentState.capacitySegment s_in s_out hClsPred).1
              exact h_trΔ.2 _ _ hMem
            -- Prepend to sequence and continue scanning [CO25, §5.2 Step 2, Eq. (11)]
            let acc' := prependPartialSequence trace targetState currentState
              s_in s_out acc hMatch hEntry hNoLoop'
            linearScanBackwards trace trΔ h_trΔ fuel' s_in targetState
              (s_in.capacitySegment :: vCap) acc'
    | .conflict => .forkErr -- `L_p` collision → `E_fork`

end S_BT_BacktrackComputation

def verifierMessageIdxList : List pSpec.ChallengeIdx :=
  (List.finRange n).filterMap fun i =>
    if h : pSpec.dir i = .V_to_P then some (⟨i, h⟩ : pSpec.ChallengeIdx) else none

def proverMessageIdxList : List pSpec.MessageIdx :=
  (List.finRange n).filterMap fun i =>
    if h : pSpec.dir i = .P_to_V then some (⟨i, h⟩ : pSpec.MessageIdx) else none

def proverMessageIdxListBefore (i : pSpec.ChallengeIdx) : List pSpec.MessageIdx :=
  proverMessageIdxList.filter fun j => decide (j.1 < i.1)

omit [SpongeSize] [pSpec.HasProverMessageSize] [pSpec.HasVerifierMessageSize] in
/-- Completeness of `proverMessageIdxListBefore`: every prover-message index with flat position
below the verifier message round appears in the list.  (The iff form is
`mem_proverMessageIdxListBefore` in `BacktrackRound.lean`.) -/
lemma mem_proverMessageIdxListBefore_of_lt {i : pSpec.ChallengeIdx} (j : pSpec.MessageIdx)
    (hj : j.1.1 < i.1.1) : j ∈ proverMessageIdxListBefore (pSpec := pSpec) i := by
  unfold proverMessageIdxListBefore proverMessageIdxList
  rw [List.mem_filter]
  refine ⟨?_, decide_eq_true hj⟩
  rw [List.mem_filterMap]
  exact ⟨j.1, List.mem_finRange _, by rw [dite_eq_left j.2]⟩

def lastProverMessageBefore? (i : pSpec.ChallengeIdx) : Option pSpec.MessageIdx :=
  (proverMessageIdxListBefore (pSpec := pSpec) i).getLast?

/-! ### The unit-level sponge position walk

The paper's cursor replay [CO25, §5.2 Steps 3–4] locates round `i` at unit granularity. The
duplex sponge of `ArkLib/Data/Hash/DuplexSponge.lean` is *lazy* and runs in *overwrite* mode, so a
block pointer `L_δ + Σ_{ι<i}(L_P(ι) + L_V(ι))`, which charges every sponge operation a whole
number of rate blocks, is off at two boundaries.

* Salt → first prover message.  `DuplexSponge.absorb` writes in place while `absorbPos < R` and
  permutes only when `absorbPos = R`, so when `R ∤ δ` the first prover message's units continue
  inside the salt's own partially filled block: that message does *not* start at block `L_δ`.
* verifier message → next prover message.  `DuplexSponge.squeeze` sets `absorbPos := 0`, so the
  next prover message overwrites the last squeeze-output block with no intervening permutation:
  the verifier message's last block and the next prover message's first block are **the same**
  chain slot.  The block-level formula counts that slot twice, over-counting by one per completed
  round — so on an honest chain the Step 4(a).iii.D exact-fit test could never fire from the
  second round on.

The generating fact of the unit-level accounting is: *unit `t` of an operation entered at cursor `c`
from block `b` lives at chain block `b + (c + t) / R`, rate position `(c + t) % R`.*  (For a
squeeze, "chain block `x`" means the input state `s_{in,x}`, whose rate part equals `s_{out,x-1}`
because squeezing does not write — the paper's "the rate part is preserved across invocations"
property.)  `absorbStepPos` / `squeezeStepPos` / `walkPos` package that fact as a state machine on
the triple `(chain block index, absorb cursor, squeeze cursor)`; they carry no `R ∣ δ` side
condition and handle both boundaries with one formula. -/

section SpongeWalkVocabulary

-- The walk vocabulary is pure `ℕ` bookkeeping plus one list slice; the ambient `DecidableEq`
-- instances of this file are carried by the signatures but not used in these statements.

/-- **[CO25, §5.2 Step 3]** BackTrack salt source: the concatenated rate
segments of the chain's input states. -/
def chainRateUnits (inputs : List (CanonicalSpongeState U)) : List U :=
  inputs.flatMap fun s => s.rateSegment.toList

omit [DecidableEq U] in
@[simp] lemma chainRateUnits_length (xs : List (CanonicalSpongeState U)) :
    (chainRateUnits (U := U) xs).length = xs.length * SpongeSize.R := by
  simp [chainRateUnits, List.length_flatMap]

/-- The chain's rate units from block `b`, absorb cursor `cA` onwards — the source
`extractCandidate` slices a round's message out of. -/
def chainUnitsFrom (inputs : List (CanonicalSpongeState U)) (b cA : Nat) : List U :=
  (chainRateUnits (inputs.drop b)).drop cA

/-- One lazy-absorb step of the unit-level sponge position walk, on the triple
`(chain block index, absorb cursor, squeeze cursor)`.

Absorbing `k > 0` units from absorb cursor `cA` crosses `(cA + k - 1) / R` block boundaries, leaves
the absorb cursor at `(cA + k - 1) % R + 1`, and re-arms the squeeze cursor at `R`.
`DuplexSponge.absorb s []` is a complete no-op, hence the `k = 0` identity branch. -/
def absorbStepPos (p : ℕ × ℕ × ℕ) (k : ℕ) : ℕ × ℕ × ℕ :=
  if k = 0 then p
  else (p.1 + (p.2.1 + k - 1) / SpongeSize.R, (p.2.1 + k - 1) % SpongeSize.R + 1, SpongeSize.R)

/-- One lazy-squeeze step of the unit-level sponge position walk, on the triple
`(chain block index, absorb cursor, squeeze cursor)`.

Squeezing `k > 0` units from squeeze cursor `cS` crosses `(cS + k - 1) / R` block boundaries, leaves
the squeeze cursor at `(cS + k - 1) % R + 1`, and resets the absorb cursor to `0` (so the next
message overwrites the last output block in place).  `DuplexSponge.squeeze s 0` is a complete
no-op — it does not even reset `absorbPos` — hence the `k = 0` identity branch. -/
def squeezeStepPos (p : ℕ × ℕ × ℕ) (k : ℕ) : ℕ × ℕ × ℕ :=
  if k = 0 then p
  else (p.1 + (p.2.2 + k - 1) / SpongeSize.R, 0, (p.2.2 + k - 1) % SpongeSize.R + 1)

@[simp] lemma absorbStepPos_zero (p : ℕ × ℕ × ℕ) : absorbStepPos p 0 = p := ite_eq_left rfl

/-- Unfolding `absorbStepPos` at a nonzero length, with the `- 1` already discharged. -/
lemma absorbStepPos_succ (p : ℕ × ℕ × ℕ) (k : ℕ) :
    absorbStepPos p (k + 1)
      = (p.1 + (p.2.1 + k) / SpongeSize.R, (p.2.1 + k) % SpongeSize.R + 1, SpongeSize.R) := by
  have hk : p.2.1 + (k + 1) - 1 = p.2.1 + k := by omega
  rw [absorbStepPos, ite_eq_right (Nat.succ_ne_zero k), hk]

@[simp] lemma squeezeStepPos_zero (p : ℕ × ℕ × ℕ) : squeezeStepPos p 0 = p := ite_eq_left rfl

/-- Unfolding `squeezeStepPos` at a nonzero length, with the `- 1` already discharged. -/
lemma squeezeStepPos_succ (p : ℕ × ℕ × ℕ) (k : ℕ) :
    squeezeStepPos p (k + 1)
      = (p.1 + (p.2.2 + k) / SpongeSize.R, 0, (p.2.2 + k) % SpongeSize.R + 1) := by
  have hk : p.2.2 + (k + 1) - 1 = p.2.2 + k := by omega
  rw [squeezeStepPos, ite_eq_right (Nat.succ_ne_zero k), hk]

/-- Supporting definition for **[CO25, Construction 4.4]**. **The honest sponge walk's position
triple after the first `i` rounds.**

Start at `(0, 0, R)` — what `DuplexSponge.start` produces — absorb the `δ` salt units, then take
one step per round: absorb the prover message on a `.P_to_V` round, squeeze the verifier message on
a
`.V_to_P` round. -/
def walkPos (δ : ℕ) (i : Fin (n + 1)) : ℕ × ℕ × ℕ :=
  Fin.induction (absorbStepPos (0, 0, SpongeSize.R) δ)
    (fun i ih =>
      match hDir : pSpec.dir i with
      | .P_to_V => absorbStepPos ih (proverMessageSize (pSpec := pSpec) ⟨i, hDir⟩)
      | .V_to_P => squeezeStepPos ih (verifierMessageSize (pSpec := pSpec) ⟨i, hDir⟩))
    i

@[simp] lemma walkPos_zero (δ : ℕ) :
    walkPos (pSpec := pSpec) δ 0 = absorbStepPos (0, 0, SpongeSize.R) δ := by
  rw [walkPos]
  simp only [Fin.induction_zero]

/-- A prover-message round absorbs `ℓ_P` units. -/
lemma walkPos_succ_proverMessage (δ : ℕ) (i : Fin n) (hDir : pSpec.dir i = .P_to_V) :
    walkPos (pSpec := pSpec) δ i.succ
      = absorbStepPos (walkPos (pSpec := pSpec) δ i.castSucc)
          (proverMessageSize (pSpec := pSpec) ⟨i, hDir⟩) := by
  rw [walkPos]
  simp only [Fin.induction_succ]
  rw [← walkPos]
  split
  · rfl
  · next h => exact absurd (h.symm.trans hDir) (by simp)

/-- A verifier message round squeezes `ℓ_V` units. -/
lemma walkPos_succ_verifierMessage (δ : ℕ) (i : Fin n) (hDir : pSpec.dir i = .V_to_P) :
    walkPos (pSpec := pSpec) δ i.succ
      = squeezeStepPos (walkPos (pSpec := pSpec) δ i.castSucc)
          (verifierMessageSize (pSpec := pSpec) ⟨i, hDir⟩) := by
  rw [walkPos]
  simp only [Fin.induction_succ]
  rw [← walkPos]
  split
  · next h => exact absurd (h.symm.trans hDir) (by simp)
  · rfl

/-! #### Per-round vocabulary -/

/-- The chain block index round `i`'s prover message ends in — i.e. the position reached after
every round strictly before the verifier message `i`. -/
def roundEndBlock (i : pSpec.ChallengeIdx) : Nat := (walkPos (pSpec := pSpec) δ i.1.castSucc).1

/-- The absorb cursor left inside `roundEndBlock i` once round `i`'s prover message is absorbed.
`= R` exactly when that last block is completely filled. -/
def roundEndCursor (i : pSpec.ChallengeIdx) : Nat := (walkPos (pSpec := pSpec) δ i.1.castSucc).2.1

/-- **[CO25, §5.2 Step 4(a)iii.D]** BackTrack Step 4(a).iii.D: **the number of input states an
exact-fit chain for round `i` has.**

The chain ends exactly when round `i`'s message has been absorbed, so it carries the input states
`s_{in,0}, …, s_{in,roundEndBlock i}` — one more than the block index. -/
def exactFitBlocks (i : pSpec.ChallengeIdx) : Nat := roundEndBlock (δ := δ) i + 1

/-- The chain block index reached after round `i`'s verifier message squeeze. -/
def roundSqueezeEndBlock (i : pSpec.ChallengeIdx) : Nat :=
  (walkPos (pSpec := pSpec) δ i.1.succ).1

/-- The number of permutation calls round `i`'s verifier message squeeze makes. -/
def roundSqueezeCalls (i : pSpec.ChallengeIdx) : Nat :=
  roundSqueezeEndBlock (δ := δ) i - roundEndBlock (δ := δ) i

/-- The permutation calls *strictly inside* round `i`'s verifier message squeeze — all but the last.

The last call's output block is the one round `i+1`'s prover message overwrites, so `s_{in,q+1}` and
`s_{out,q}` need not agree there; every earlier pair does, since squeezing never writes. -/
def roundSqueezeInnerCalls (i : pSpec.ChallengeIdx) : Nat := roundSqueezeCalls (δ := δ) i - 1

/-- The `(chain block index, absorb cursor)` at which round `i`'s prover message starts, i.e. the
position reached after every round strictly before that message.  `(0, 0)` when round `i` has no
preceding message. -/
def roundProverMessageWindowStart (i : pSpec.ChallengeIdx) : Nat × Nat :=
  match lastProverMessageBefore? (pSpec := pSpec) i with
  | some j =>
      ((walkPos (pSpec := pSpec) δ j.1.castSucc).1, (walkPos (pSpec := pSpec) δ j.1.castSucc).2.1)
  | none => (0, 0)

/-- **[CO25, §5.2]** BackTrack Step 4(a).i block pointer: the chain block round `i`'s
message starts in. -/
def blockOffset (i : pSpec.ChallengeIdx) : Nat := (roundProverMessageWindowStart (δ := δ) i).1

/-- The absorb cursor inside `blockOffset i` at which round `i`'s message starts.  Nonzero exactly
when the message continues inside a block another operation already wrote part of. -/
def roundProverMessageCursor (i : pSpec.ChallengeIdx) : Nat :=
  (roundProverMessageWindowStart (δ := δ) i).2

/-- `ℓ_P(i)` — characters of the round-`i` prover message (`0` if the round has none). -/
def roundProverMessageChars (i : pSpec.ChallengeIdx) : Nat :=
  (lastProverMessageBefore? (pSpec := pSpec) i).elim 0 fun msgIdx => proverMessageSize msgIdx

/-- The initial salt absorb or a nonempty prover message supplies an absorb boundary.
BackTrack checks the untouched rate suffix at this boundary before squeezing. -/
def roundHasAbsorbBoundary (i : pSpec.ChallengeIdx) : Prop :=
  (i.1 : ℕ) = 0 ∨ 0 < roundProverMessageChars (pSpec := pSpec) i

instance (i : pSpec.ChallengeIdx) : Decidable (roundHasAbsorbBoundary (pSpec := pSpec) i) :=
  inferInstanceAs (Decidable ((i.1 : ℕ) = 0 ∨ 0 < roundProverMessageChars (pSpec := pSpec) i))

/-- **[CO25, §5.2]** BackTrack Step 4(a).iii.A message window, at unit granularity: `len` rate units
of the chain starting at absorb cursor `cA` inside chain block `b`. Unlike a block window this needs
no separate "block remainder" side condition. -/
def chainProverMessageWindowUnits (inputs : List (CanonicalSpongeState U)) (b cA len : Nat) :
    List U :=
  (chainUnitsFrom inputs b cA).take len

omit [DecidableEq U] in
@[simp] lemma chainUnitsFrom_length (inputs : List (CanonicalSpongeState U)) (b cA : Nat) :
    (chainUnitsFrom (U := U) inputs b cA).length = (inputs.length - b) * SpongeSize.R - cA := by
  simp [chainUnitsFrom, chainRateUnits]

omit [DecidableEq U] in
@[simp] lemma chainProverMessageWindowUnits_length (inputs : List (CanonicalSpongeState U))
    (b cA len : Nat) :
    (chainProverMessageWindowUnits (U := U) inputs b cA len).length
      = min len ((inputs.length - b) * SpongeSize.R - cA) := by
  simp [chainProverMessageWindowUnits]

/-! #### Invariants of the walk -/

/-- A nonempty `absorb` re-arms the squeeze cursor at the full rate.  (An empty one is a complete
no-op, so it leaves the squeeze cursor alone.) -/
lemma absorbStepPos_squeezeCursor (p : ℕ × ℕ × ℕ) {k : ℕ} (hk : k ≠ 0) :
    (absorbStepPos p k).2.2 = SpongeSize.R := by
  rw [absorbStepPos, ite_eq_right hk]

/-- The absorb cursor stays in `[0, R]`. -/
lemma absorbStepPos_absorbCursor_le (p : ℕ × ℕ × ℕ) (k : ℕ) (h : p.2.1 ≤ SpongeSize.R) :
    (absorbStepPos p k).2.1 ≤ SpongeSize.R := by
  have hR : 0 < SpongeSize.R := Nat.pos_of_neZero _
  rw [absorbStepPos]
  split
  · exact h
  · exact Nat.succ_le_of_lt (Nat.mod_lt _ hR)

/-- The absorb cursor stays in `[0, R]` across a squeeze (which resets it to `0`). -/
lemma squeezeStepPos_absorbCursor_le (p : ℕ × ℕ × ℕ) (k : ℕ) (h : p.2.1 ≤ SpongeSize.R) :
    (squeezeStepPos p k).2.1 ≤ SpongeSize.R := by
  rw [squeezeStepPos]
  split
  · exact h
  · exact Nat.zero_le _

/-- The chain block index never decreases across an absorb. -/
lemma le_absorbStepPos_fst (p : ℕ × ℕ × ℕ) (k : ℕ) : p.1 ≤ (absorbStepPos p k).1 := by
  rw [absorbStepPos]; split <;> simp

/-- The chain block index never decreases across a squeeze. -/
lemma le_squeezeStepPos_fst (p : ℕ × ℕ × ℕ) (k : ℕ) : p.1 ≤ (squeezeStepPos p k).1 := by
  rw [squeezeStepPos]; split <;> simp

/-- Walk invariant: the absorb cursor is always in `[0, R]`. -/
lemma walkPos_absorbCursor_le (δ : ℕ) (i : Fin (n + 1)) :
    (walkPos (pSpec := pSpec) δ i).2.1 ≤ SpongeSize.R := by
  induction i using Fin.induction with
  | zero =>
      rw [walkPos_zero]
      exact absorbStepPos_absorbCursor_le _ _ (Nat.zero_le _)
  | succ i ih =>
      cases hDir : pSpec.dir i with
      | P_to_V =>
        rw [walkPos_succ_proverMessage δ i hDir]; exact absorbStepPos_absorbCursor_le _ _ ih
      | V_to_P =>
        rw [walkPos_succ_verifierMessage δ i hDir]; exact squeezeStepPos_absorbCursor_le _ _ ih

/-- One round never decreases the chain block index. -/
lemma walkPos_fst_le_succ (δ : ℕ) (i : Fin n) :
    (walkPos (pSpec := pSpec) δ i.castSucc).1 ≤ (walkPos (pSpec := pSpec) δ i.succ).1 := by
  cases hDir : pSpec.dir i with
  | P_to_V => rw [walkPos_succ_proverMessage δ i hDir]; exact le_absorbStepPos_fst _ _
  | V_to_P => rw [walkPos_succ_verifierMessage δ i hDir]; exact le_squeezeStepPos_fst _ _

/-- The chain block index is monotone in the round. -/
lemma walkPos_fst_mono (δ : ℕ) {i j : Fin (n + 1)} (h : i.1 ≤ j.1) :
    (walkPos (pSpec := pSpec) δ i).1 ≤ (walkPos (pSpec := pSpec) δ j).1 := by
  exact (Fin.monotone_iff_le_succ (f := fun i => (walkPos (pSpec := pSpec) δ i).1)).mpr
    (walkPos_fst_le_succ δ) h

/-- `exactFitBlocks i - 1` is `roundEndBlock i`; kept as a `simp` bridge for arithmetic goals. -/
@[simp] lemma exactFitBlocks_sub_one (i : pSpec.ChallengeIdx) :
    exactFitBlocks (δ := δ) i - 1 = roundEndBlock (δ := δ) i := rfl

/-! #### Machine-checked sanity values

The two hand-computed duplex runs that exposed the block-level over-count, replayed through
`absorbStepPos` / `squeezeStepPos` at the concrete geometry `R = 2`.  These are stated over the
pure-`ℕ` step functions rather than over `walkPos`, since `numSaltBlocks` / `Lₚᵢ` / `Lᵥᵢ` go
through `Nat.ceil` on `ℚ` and are not kernel-reducible. -/

end SpongeWalkVocabulary

end BacktrackProcedure

end DuplexSpongeFS.Backtrack
