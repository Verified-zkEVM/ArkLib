/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Nondegeneracy
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceDataStructures

/-!
# Backtracking sequence family and procedure

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
  [HasMessageSize pSpec] [HasChallengeSize pSpec]
  {δ : Nat}

section CoreDefinitions
/-- A backtracking sequence (Definition 5.3) for a given hash-duplex-sponge oracle trace `tr` and
  final duplex-sponge state `s` consists of the following data:
- An input statement `𝕩`
- A list `inputState = [sᵢₙ, ...]` of input states
- A list `outputState = [sₒᵤₜ, ...]` of output states

subject to the following conditions:
- The last of the input states is the given final state
- There is one more input state than output state
- The statement is queried with the hash, and returns the capacity of the first input state
  `(hash, 𝕩, inputState[0].capacitySegment) ∈ tr` -/
structure BacktrackSequence (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) where
  /-- `𝕩^(k) ∈ {0,1}^≤n` — input statement for this backtracking sequence. -/
  stmt : StmtIn
  /-- `[s_{in,0}^(k), …, s_{in,m_k}^(k)]` — input sponge states of the chain; length `m_k + 1`. -/
  inputState : List (CanonicalSpongeState U)
  /-- `[s_{out,0}^(k), …, s_{out,m_k-1}^(k)]` — output sponge states; one shorter than inputs. -/
  outputState : List (CanonicalSpongeState U)

  /-- `|inputState| = |outputState| + 1` -/
  inputState_length_eq_outputState_length_succ : inputState.length = outputState.length + 1

  /-- `inputState[m_k] = s` — last input equals the given final state.
    CO25 Def 5.3 condition (a). -/
  last_inputState_eq_state : inputState[inputState.length - 1] = state

  /-- `(h, 𝕩, inputState[0].capacitySegment) ∈ tr` — hash query anchors capacity.
    CO25 Def 5.3 condition (b). -/
  hash_in_trace : ⟨.inl stmt, (Vector.drop inputState[0] SpongeSize.R)⟩ ∈ trace

  /-- **input-output states agree with p**: For all `ι < m_k`, either
    `(p, s_{in,ι}, s_{out,ι}) ∈ tr` or `(p⁻¹, s_{out,ι}, s_{in,ι}) ∈ tr`.
    CO25 Def 5.3 condition (c). -/
  permute_or_inv_in_trace : ∀ i : Fin outputState.length,
    ⟨.inr (.inl inputState[i]), outputState[i]⟩ ∈ trace
    ∨ ⟨.inr (.inr outputState[i]), inputState[i]⟩ ∈ trace

  /-- **the capacity segment is shared across queries**: `s_{C,out,ι} = s_{C,in,ι+1}`
    for all `ι < m_k`. CO25 Def 5.3 condition (d). -/
  capacitySegment_output_eq_input : ∀ i : Fin outputState.length,
    outputState[i].capacitySegment = inputState[i.val + 1].capacitySegment

  /-- **input capacities form a simple path**: no capacity segment occurs twice among
    `s_{in,0}, …, s_{in,m_k}`. This strengthens CO25 Def 5.3 condition (e), which only
    excludes adjacent self-loops, and supplies the pairwise-distinctness assumed by the
    `BackTrack` runtime argument. Together with `capacitySegment_output_eq_input`, it implies
    `s_{C,in,ι} ≠ s_{C,out,ι}` for every `ι < m_k`. -/
  inputCapacities_nodup :
    (inputState.map CanonicalSpongeState.capacitySegment).Nodup

noncomputable section

/-- Capacity segments visited by the input-state path of a backtrack sequence. -/
def BacktrackSequence.inputCapacities
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) : List (Vector U SpongeSize.C) :=
  seq.inputState.map CanonicalSpongeState.capacitySegment

/-- The original local no-self-loop condition of CO25 Def 5.3 follows from the strengthened
simple-path condition: the output capacity at step `i` is the next input capacity. -/
lemma BacktrackSequence.capacitySegment_input_ne_output
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) (i : Fin seq.outputState.length) :
    (seq.inputState[i.val]'(by
      rw [seq.inputState_length_eq_outputState_length_succ]
      omega)).capacitySegment ≠ seq.outputState[i].capacitySegment := by
  have hi : i.val < seq.inputState.length := by
    rw [seq.inputState_length_eq_outputState_length_succ]
    omega
  have hiSucc : i.val + 1 < seq.inputState.length := by
    rw [seq.inputState_length_eq_outputState_length_succ]
    omega
  intro hLoop
  have hAdjacent :
      (seq.inputState.map CanonicalSpongeState.capacitySegment)[i.val]'(by simpa using hi) =
      (seq.inputState.map CanonicalSpongeState.capacitySegment)[i.val + 1]'(by
        simpa using hiSucc) := by
    simpa using
      hLoop.trans (seq.capacitySegment_output_eq_input i)
  have hIndex : i.val = i.val + 1 :=
    (seq.inputCapacities_nodup.getElem_inj_iff (i := i.val) (hi := by simpa using hi)
      (j := i.val + 1) (hj := by simpa using hiSucc)).mp hAdjacent
  omega

/-- The flattened sequence of states: `[s_{in,0}, s_{out,0}, s_{in,1}, s_{out,1}, ..., s]`. -/
def BacktrackSequence.flattenStateSequence
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) : List (CanonicalSpongeState U) :=
  (seq.inputState.zip seq.outputState).foldr (fun p acc => p.1 :: p.2 :: acc) [state]

noncomputable def matchesEntry
    (entry x : (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
      (duplexSpongeChallengeOracle StmtIn U).Range t) : Bool := by
  classical
  exact decide (x = entry)

noncomputable def matchesEitherEntry
    (entryA entryB x : (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
      (duplexSpongeChallengeOracle StmtIn U).Range t) : Bool := by
  classical
  exact decide (x = entryA ∨ x = entryB)

/-- First-occurrence index of an entry in a trace. -/
def firstOccurrenceIndex
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entry : (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
      (duplexSpongeChallengeOracle StmtIn U).Range t)
    (hEntry : entry ∈ trace) : Fin trace.length := by
  classical
  exact ⟨trace.findIdx (matchesEntry entry), List.findIdx_lt_length_of_exists
    ⟨entry, hEntry, by simp [matchesEntry]⟩⟩

/-- First-occurrence index of EITHER entryA or entryB in a trace. -/
def firstOccurrenceOfEither
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entryA entryB : (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
      (duplexSpongeChallengeOracle StmtIn U).Range t)
    (hEntry : entryA ∈ trace ∨ entryB ∈ trace) : Fin trace.length := by
  classical
  exact ⟨trace.findIdx (matchesEitherEntry entryA entryB),
    List.findIdx_lt_length_of_exists (by
      rcases hEntry with hA | hB
      · exact ⟨entryA, hA, by simp [matchesEitherEntry]⟩
      · exact ⟨entryB, hB, by simp [matchesEitherEntry]⟩)⟩

/-- The associated indices (first occurrences in the trace) for a backtracking sequence
This calculate `J_BT(tr,s)` from a lawful backtracking sequence `S_BT(tr,s)`. -/
def BacktrackSequence.Index (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (seq : BacktrackSequence trace state) :
    Fin trace.length × (Fin seq.inputState.length → Fin (trace.length + 1)) := by
  classical
    have hInputStateNonempty : 0 < seq.inputState.length := by
      rw [seq.inputState_length_eq_outputState_length_succ]
      exact Nat.succ_pos _
    let inputState0 : CanonicalSpongeState U := -- first sponge state after the hash query
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

variable {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
  {state : CanonicalSpongeState U}

/-- `firstOccurrenceIndex` indexes the given entry. -/
lemma firstOccurrenceIndex_get
    (entry : (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
      (duplexSpongeChallengeOracle StmtIn U).Range t) (hEntry : entry ∈ trace) :
    trace.get (firstOccurrenceIndex trace entry hEntry) = entry := by
  classical
  rw [List.get_eq_getElem]
  have h := of_decide_eq_true (List.findIdx_getElem (xs := trace)
    (p := matchesEntry entry)
    (w := (firstOccurrenceIndex trace entry hEntry).isLt))
  with_unfolding_all exact h

/-- No earlier position than `firstOccurrenceIndex` carries the entry. -/
lemma firstOccurrenceIndex_not_mem_take
    (entry : (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
      (duplexSpongeChallengeOracle StmtIn U).Range t) (hEntry : entry ∈ trace) :
    entry ∉ trace.take (firstOccurrenceIndex trace entry hEntry).val := by
  classical
  intro hmem
  rw [List.mem_take_iff_getElem] at hmem
  obtain ⟨m, hm, hget⟩ := hmem
  have hmlt : m < (firstOccurrenceIndex trace entry hEntry).val :=
    lt_of_lt_of_le hm (min_le_left _ _)
  have hfalse := List.not_of_lt_findIdx (p := matchesEntry entry) hmlt
  simp only [matchesEntry, decide_eq_false_iff_not] at hfalse
  exact hfalse hget

/-- `firstOccurrenceOfEither` indexes one of the two entries. -/
lemma firstOccurrenceOfEither_get
    (entryA entryB : (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
      (duplexSpongeChallengeOracle StmtIn U).Range t)
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
    (entryA entryB : (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
      (duplexSpongeChallengeOracle StmtIn U).Range t)
    (hEntry : entryA ∈ trace ∨ entryB ∈ trace) :
    entryA ∉ trace.take (firstOccurrenceOfEither trace entryA entryB hEntry).val ∧
    entryB ∉ trace.take (firstOccurrenceOfEither trace entryA entryB hEntry).val := by
  classical
  constructor <;>
  · intro hmem
    rw [List.mem_take_iff_getElem] at hmem
    obtain ⟨m, hm, hget⟩ := hmem
    have hmlt : m < (firstOccurrenceOfEither trace entryA entryB hEntry).val :=
      lt_of_lt_of_le hm (min_le_left _ _)
    have hfalse := List.not_of_lt_findIdx
      (p := matchesEitherEntry entryA entryB) hmlt
    simp only [matchesEitherEntry, decide_eq_false_iff_not] at hfalse
    simp only [not_or] at hfalse
    first
      | exact hfalse.1 hget
      | exact hfalse.2 hget

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
  rw [dif_pos i.isLt]
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
  rw [dif_neg (by omega)]

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

/-- CO25 Def 5.3 `S_BT(tr, s)` — maximal family of backtrack sequences
(Eq. 9 & BackTrack §5.2 Step 2, Eq. 11): a finite set of `BacktrackSequence` pairs
`(s_{in,ι}, s_{out,ι})` starting at an initial `StmtIn` and ending at sponge state `s`,
with no sequence strictly containing another. -/
structure BacktrackSequenceFamily (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) where
  /-- `S_BT(tr, s)` — finite set of backtrack sequences (CO25 Def 5.3). -/
  seqFamily : Finset (BacktrackSequence trace state)
  /-- Maximality: no `s ≠ s'` with `s ⊆ s'` both in `S_BT` (CO25 Def 5.3 maximality).
  Subsequence is defined over the flattened sequence of states. -/
  maximality : ∀ s ∈ seqFamily, ∀ s' ∈ seqFamily, s ≠ s' →
    ¬ (s.stmt = s'.stmt ∧ s.flattenStateSequence.Sublist s'.flattenStateSequence)

/-- Definition 5.3: `S_BT(tr,s)` family of backtracking sequences. -/
abbrev S_BT
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) :=
  BacktrackSequenceFamily trace state

/-- Extensionality for `BacktrackSequence`: two sequences are equal once their three data fields
(`stmt`, `inputState`, `outputState`) agree.  The remaining fields are `Prop`-valued, so they are
equal by proof irrelevance. -/
@[ext]
lemma BacktrackSequence.ext
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    {s₁ s₂ : BacktrackSequence trace state}
    (hstmt : s₁.stmt = s₂.stmt)
    (hin : s₁.inputState = s₂.inputState)
    (hout : s₁.outputState = s₂.outputState) : s₁ = s₂ := by
  cases s₁; cases s₂
  simp only at hstmt hin hout
  subst hstmt; subst hin; subst hout
  rfl

/-- Definition 5.4: index list payload attached to one sequence. -/
abbrev BacktrackIndexList
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) :=
  Fin trace.length × (Fin seq.inputState.length → Fin (trace.length + 1))

open Classical in
/-- Definition 5.4: `J_BT(tr,s)` — the image of `S_BT(tr,s)` under `BacktrackSequence.Index`.
Every sequence in `S_BT` is paired with its unique index list; no sequence is omitted. -/
def J_BT
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (family : BacktrackSequenceFamily trace state) :
    Finset (Sigma fun seq : BacktrackSequence trace state => BacktrackIndexList trace seq) :=
  family.seqFamily.image (fun seq => ⟨seq, BacktrackSequence.Index trace state seq⟩)

end
end CoreDefinitions

section BacktrackProcedure

variable [DecidableEq StmtIn] [DecidableEq U] {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- BackTrack §5.2 Step 4.D output tuple `(i, 𝕩, τ, (α̂_1,…,α̂_i))` stored in `Outs`. -/
    -- if it fails the filter (e.g. bad salt/messages), return `none`
structure BacktrackOutput where
  roundIdx : pSpec.ChallengeIdx
  stmt : StmtIn
  salt : Vector U δ
  /-- `(α̂_1, …, α̂_i)` — encoded messages up to challenge `i`, indexed by message index. -/
  encodedMessages : pSpec.EncodedMessagesBefore U roundIdx.1.castSucc

section S_BT_BacktrackComputation

/- Design note (CO25 §5.2): we deliberately provide **no executable enumeration** of the full
backtrack-sequence family `S_BT(tr, s)` (Definition 5.3). The executable `backTrack` below uses
the single-chain linear scan with scan-time fork detection — CO25's own "look for at most one
element" optimization (line 1056). Downstream proofs (`BadEvents`, `AbortAnalysis`) quantify
over `S_BT` as an explicit structure hypothesis and never need to compute the family.

The raw bidirectional `tr_∇.p` may contain an inverse-query-rooted decoy predecessor that
branches the linear scan without defining a valid hash-anchored sequence. Because the scan
returns `err` immediately on a capacity fork, the simulator must use `backTrackFwd`, which
restricts candidates to mappings whose first raw occurrence was a forward `p` query. -/

/-- Paper §5.2 partial-cap-segment matching for `BackTrack`: enumerate all distinct
`(stateIn, stateOut)` pairs in `tr_∇.p` whose output capacity matches the next input capacity.
The linear scan separately rejects self-loops and repeated input capacities as invalid candidates.

Black-box over `[LawfulTraceTable T_P ...]` via `TraceTableOps.entries`; both forward and inverse
permutation directions already collapse into the same bidirectional `tr_∇.p`
(cf. `TraceNabla.ofQueryLog` dispatch). -/
-- TODO: Replace this linear `entries` scan with a conflict-aware, logarithmic lookup by output
-- capacity, as required by CO25 Eq. 13.
def predecessorCandidates
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (nextInputCap : Vector U SpongeSize.C) :
    List (CanonicalSpongeState U × CanonicalSpongeState U) := by
  exact ((TraceTableOps.entries (V := CanonicalSpongeState U) trΔ.p).filterMap fun pair =>
    let stateOut := pair.2
    if stateOut.capacitySegment = nextInputCap then some pair else none).dedup

/-! ### Linear-scan helpers (CO25 §5.2 BackTrack "look for at most one element" optimization)

The paper's Algorithm 1 enumerates all maximal sequences then post-filters. CO25 line 1056 notes
the procedure can equivalently `look for at most one element` — i.e. abort on scan-time forks.
This is faithful only once the candidate source is restricted to mappings from which a
hash-anchored chain can be built; use `backTrackFwd` when modelling the simulator. -/

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

/-- Paper §5.2 Step 4 hash anchor lookup: collect distinct statements whose stored capacity
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
structure PartialBacktrackSequence (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
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

  inputCapacities_nodup :
    (inputState.map CanonicalSpongeState.capacitySegment).Nodup

def emptyPartialSequence (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (targetState : CanonicalSpongeState U) :
    PartialBacktrackSequence trace targetState targetState :=
  { inputState := [targetState]
    outputState := []
    inputState_length_eq_outputState_length_succ := rfl
    first_inputState_eq_head := rfl
    last_inputState_eq_state := rfl
    permute_or_inv_in_trace := by intro i; exact i.elim0
    capacitySegment_output_eq_input := by intro i; exact i.elim0
    inputCapacities_nodup := by simp only [List.map_singleton, List.nodup_singleton] }

def prependPartialSequence
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (targetState seq_head : CanonicalSpongeState U)
    (s_in s_out : CanonicalSpongeState U)
    (seq : PartialBacktrackSequence trace seq_head targetState)
    (hMatch : s_out.capacitySegment = seq_head.capacitySegment)
    (hEntry : ⟨.inr (.inl s_in), s_out⟩ ∈ trace ∨ ⟨.inr (.inr s_out), s_in⟩ ∈ trace)
    (hFresh : s_in.capacitySegment ∉
      seq.inputState.map CanonicalSpongeState.capacitySegment) :
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
    inputCapacities_nodup := by
      simpa using List.nodup_cons.mpr ⟨hFresh, seq.inputCapacities_nodup⟩ }

def completeBacktrackSequence
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
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
    inputCapacities_nodup := seq.inputCapacities_nodup }

/-! ### Bridge lemmas: `classifyLookup` + `filterMap` → entry membership -/

omit [SpongeSize] in
lemma classifyLookup_filterMap_singleton_mem {α β : Type _} [DecidableEq β]
    (l : List α) (f : α → Option β) (b : β)
    (h : classifyLookup (l.filterMap f).dedup = .unique b) :
    ∃ a ∈ l, f a = some b := by
  have hMemDedup : b ∈ (l.filterMap f).dedup := by
    have : (l.filterMap f).dedup = [b] := by
      cases h' : (l.filterMap f).dedup with
      | nil => rw [h'] at h; unfold classifyLookup at h; contradiction
      | cons hd tl =>
        cases tl with
        | nil =>
            rw [h'] at h; unfold classifyLookup at h
            injection h with hEq; subst hEq; rfl
        | cons _ _ => rw [h'] at h; unfold classifyLookup at h; contradiction
    rw [this]; exact .head ..
  exact List.mem_filterMap.mp (List.mem_dedup.mp hMemDedup)

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
  split at hEq
  · next hCap =>
      injection hEq with hInj; subst hInj
      have hMem' := (Prod.eta pair).symm ▸ hMem
      rw [hCap] at hMem'; exact hMem'
  · contradiction

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
inductive LinearScanResult (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
  (targetState : CanonicalSpongeState U) where
  | forkErr
  | noResult
  | done (seq : BacktrackSequence trace targetState)

/-- CO25 §5.2 BackTrack linear backwards scan: from `currentState`, classify the predecessor
candidates in `tr_∇.p`. `[]` ends the scan; `[pred]` continues; `_::_::_` is a fork and produces
`.forkErr`.
Self-loops and revisits of an input capacity violate the simple-path condition of Definition 5.3,
so they invalidate only the current candidate and result in `.noResult`.
Structurally recursive on `fuel`; the caller supplies `fuel = depthBound`.
Uses a tail-recursive accumulator `acc` to build the sequence by prepending. -/
def linearScanBackwards
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (fuel : Nat) (currentState targetState : CanonicalSpongeState U)
    (acc : PartialBacktrackSequence trace currentState targetState) :
    LinearScanResult trace targetState :=
  match fuel with
  | 0 => .noResult
  | fuel' + 1 =>
    -- Look up predecessor in `tr_∇.p` (CO25 §5.2 Step 2.b)
    match hClsPred : classifyLookup (predecessorCandidates (T_P := T_P) (U := U) trΔ
      currentState.capacitySegment) with
    | .noMatch =>
        -- Not in `tr_∇.p`, check `tr_∇.h` (CO25 §5.2 Step 2.c)
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
        -- Found unique predecessor `p / p⁻¹` (CO25 §5.2 Step 2.b)
        let s_in := pred.1
        let s_out := pred.2
        if hNoLoop : s_in.capacitySegment = s_out.capacitySegment then
          .noResult -- Invalid candidate: adjacent capacities must be distinct
        else
          if hVisited : s_in.capacitySegment ∈
              acc.inputState.map CanonicalSpongeState.capacitySegment then
            .noResult -- Invalid candidate: input capacities must form a simple path
          else
            have hMatch : s_out.capacitySegment = currentState.capacitySegment :=
              (pred_unique_mem_and_cap trΔ currentState.capacitySegment s_in s_out hClsPred).2
            have hEntry : ⟨.inr (.inl s_in), s_out⟩ ∈ trace ∨
              ⟨.inr (.inr s_out), s_in⟩ ∈ trace := by
              have hMem : (s_in, s_out) ∈
                TraceTableOps.entries (V := CanonicalSpongeState U) trΔ.p :=
                (pred_unique_mem_and_cap trΔ currentState.capacitySegment s_in s_out hClsPred).1
              exact h_trΔ.2 _ _ hMem
            -- Prepend to sequence and continue scanning (CO25 §5.2 Step 2.b)
            let acc' := prependPartialSequence trace targetState currentState
              s_in s_out acc hMatch hEntry hVisited
            linearScanBackwards trace trΔ h_trΔ fuel' s_in targetState acc'
    | .conflict => .forkErr -- `L_p` collision → `E_fork`

end S_BT_BacktrackComputation

def challengeIdxList : List pSpec.ChallengeIdx :=
  (List.finRange n).filterMap fun i =>
    if h : pSpec.dir i = .V_to_P then some (⟨i, h⟩ : pSpec.ChallengeIdx) else none

def messageIdxList : List pSpec.MessageIdx :=
  (List.finRange n).filterMap fun i =>
    if h : pSpec.dir i = .P_to_V then some (⟨i, h⟩ : pSpec.MessageIdx) else none

def messageIdxListBefore (i : pSpec.ChallengeIdx) : List pSpec.MessageIdx :=
  messageIdxList.filter fun j => decide (j.1 < i.1)

/-- Try to assemble exactly `len` elements from `xs` into a `Vector U len`. Returns
`some ⟨v, hLen⟩` carrying a proof that `xs` actually had at least `len` elements, so callers
can use `do`-notation while still recovering the length bound. -/
def vectorOfListExact
    (len : Nat) (xs : List U) : Option { _v : Vector U len // len ≤ xs.length } := by
  let ys := xs.take len
  if hLen : ys.length = len then
    refine some ⟨⟨ys.toArray, ?_⟩, ?_⟩
    · simp only [List.size_toArray]
      exact hLen
    · have hle : (xs.take len).length ≤ xs.length := List.length_take_le' _ _
      rw [hLen] at hle
      exact hle
  else
    exact none

/-! ### Absorb layout of the duplex sponge (BackTrack §5.2 Steps 3–4)

BackTrack must decide whether the last input state `s_{in,m}` of a chain is the input of the
first permutation call of some challenge squeeze, and if so read back the absorbed salt and
messages. Which rate units of which chain input hold absorbed data is fixed by the protocol
schedule and by the duplex sponge of Construction 3.3 (`DuplexSponge.absorb`/`squeeze`). Two
properties of that sponge decide the layout:

- `Absorb` does not reset the absorbing index, so the salt `τ` and `α̂_1` are one absorbed
  stream `τ ‖ α̂_1`, packed into `⌈(δ + ℓ_P(1)) / r⌉` rate blocks;
- `Squeeze` resets the absorbing index without a permutation call, so the first block of
  `α̂_{i+1}` overwrites the last squeeze output of round `i`: a round costs
  `L_P(i) + L_V(i) - 1` permutation calls after the first.

`SpongeLayout` replays the schedule symbolically: it records only *how many leading rate units*
`w_b` of each permutation input `s_{in,b}` were overwritten by absorbed data. Every other rate
unit of `s_{in,b}` is inherited, from `s_{out,b-1}` for `b ≥ 1` and from the `Start` state
`(0^r, s_C)` for `b = 0`, and BackTrack checks it. Every rate unit of every chain input is
therefore either returned as data or compared, so the output tuple determines the chain.

**Paper discrepancy (CO25 §5.2 Steps 3–4).** The printed pointer
`L_ptr(i) := L_δ + Σ_{ι<i} (L_P(ι) + L_V(ι))` and the windows of Step 3 and Steps 4(a)iii.A–E
place `τ` and `α̂_1` in separate blocks and charge `L_P(i) + L_V(i)` calls per round. Neither
holds for Construction 3.3. Under the nondegenerate schedule the challenge-`i` squeeze input is
`s_{in,j_i}` with `j_1 = ⌈(δ + ℓ_P(1)) / r⌉ - 1` and `j_{i+1} = j_i + L_V(i) + L_P(i+1) - 1`. -/

/-- Symbolic position of the duplex sponge of Construction 3.3 that tracks where absorbed data
lands, not the data itself. -/
structure SpongeLayout where
  /-- `w_b` for every permutation input `s_{in,b}` issued so far: the number of leading rate
  units of `s_{in,b}` that absorbed data overwrote since the previous permutation call. -/
  written : List Nat
  /-- The number of leading rate units of the current, not yet permuted, state that absorbed
  data overwrote. -/
  cur : Nat
  /-- The absorbing index `i_A` of the sponge. -/
  absorbPos : Nat
  /-- The squeezing index `i_S` of the sponge. -/
  squeezePos : Nat

/-- `DS.Start`: no permutation input yet, `i_A = 0`, `i_S = r`. -/
def SpongeLayout.start : SpongeLayout := ⟨[], 0, 0, SpongeSize.R⟩

/-- One permutation call on the current state. -/
def SpongeLayout.permute (c : SpongeLayout) : SpongeLayout :=
  { c with written := c.written ++ [c.cur], cur := 0 }

/-- `DuplexSponge.absorb` of `ℓ` units: a full rate (`i_A = r`) is permuted before the next unit
is written at `i_A`. -/
def SpongeLayout.absorb : SpongeLayout → Nat → SpongeLayout
  | c, 0 => { c with squeezePos := SpongeSize.R }
  | c, ℓ + 1 =>
    let c := if c.absorbPos = SpongeSize.R then { c.permute with absorbPos := 0 } else c
    SpongeLayout.absorb
      { c with cur := c.absorbPos + 1, absorbPos := c.absorbPos + 1,
               squeezePos := SpongeSize.R } ℓ

/-- `DuplexSponge.squeeze` of `ℓ` units: each unit resets `i_A`, and an exhausted rate
(`i_S = r`) is permuted before the unit is read. -/
def SpongeLayout.squeeze : SpongeLayout → Nat → SpongeLayout
  | c, 0 => c
  | c, ℓ + 1 =>
    let c := { c with absorbPos := 0 }
    let c := if c.squeezePos = SpongeSize.R then { c.permute with squeezePos := 0 } else c
    SpongeLayout.squeeze { c with squeezePos := c.squeezePos + 1 } ℓ

/-- The layout after `Start`, `Absorb(τ)` and the protocol steps with flat index below `k`, in
the order of `Messages.deriveTranscriptDSFSSalted`. -/
def layoutBefore (k : Nat) : SpongeLayout :=
  (List.finRange n).foldl (fun c j =>
    if j.val < k then
      if h : pSpec.dir j = .P_to_V then
        c.absorb (messageSize (⟨j, h⟩ : pSpec.MessageIdx))
      else
        c.squeeze (challengeSize (⟨j, by cases hd : pSpec.dir j <;> simp_all⟩ :
          pSpec.ChallengeIdx))
    else c) (SpongeLayout.start.absorb δ)

/-- The overwritten-prefix lengths `(w_0, …, w_j)` of the permutation inputs up to and including
`s_{in,j}`, the input of the first permutation call of the challenge-`i` squeeze. It is `none`
when that squeeze does not start with a permutation call, which a `NondegenerateRounds`
schedule excludes. -/
def challengeSqueezeLayout (i : pSpec.ChallengeIdx) : Option (List Nat) :=
  let c := layoutBefore (pSpec := pSpec) (δ := δ) i.1.val
  if 0 < challengeSize i ∧ c.squeezePos = SpongeSize.R then some (c.written ++ [c.cur])
  else none

/-- The number of units absorbed before protocol step `k`: the salt and every earlier message. -/
def absorbedLengthBefore (k : Nat) : Nat :=
  ((messageIdxList (pSpec := pSpec)).filter fun j => decide (j.1.val < k)).foldl
    (fun acc j => acc + messageSize j) δ

/-- `∀ b ≤ m`, the rate units of `s_{in,b}` past its overwritten prefix `w_b` equal those of
the preceding state: `s_{R,out,b-1}` for `b ≥ 1`, and `0^r` (from `Start`) for `b = 0`. On
success, returns the absorbed stream `s_{R,in,0}[0 : w_0] ‖ ⋯ ‖ s_{R,in,m}[0 : w_m]`. -/
def BacktrackSequence.absorbedUnits
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) (ws : List Nat) : Option (List U) := do
  guard (ws.length = seq.inputState.length)
  let mut units : List U := []
  for (b, w) in (List.range ws.length).zip ws do
    let sIn ← seq.inputState[b]?
    let prev : List U ← if b = 0 then pure (List.replicate SpongeSize.R 0)
      else (seq.outputState[b - 1]?).map (·.rateSegment.toList)
    guard (sIn.rateSegment.toList.drop w = prev.drop w)
    units := units ++ sIn.rateSegment.toList.take w
  return units

/-- BackTrack §5.2 Steps 3–4 for one chain, against the absorb layout of Construction 3.3.

The chain `s_{in,0}, …, s_{in,m}` is accepted for challenge `i` exactly when `s_{in,m}` is the
input of the first permutation call of the challenge-`i` squeeze (`challengeSqueezeLayout`)
and every rate unit that the absorbed data did not overwrite is inherited
(`BacktrackSequence.absorbedUnits`). The absorbed stream is then split into `τ` and
`α̂_1, …, α̂_i`. A state that starts no challenge squeeze, including an absorb input or a later
squeeze input, gives `none`. -/
def BacktrackSequence.extractCandidate
    (state : CanonicalSpongeState U)
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (seq : BacktrackSequence (trace := trace) (state := state)) :
    Option (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := do
  let (i, ws) ← (challengeIdxList (pSpec := pSpec)).findSome? fun i =>
    match challengeSqueezeLayout (pSpec := pSpec) (δ := δ) i with
    | some ws => if ws.length = seq.inputState.length then some (i, ws) else none
    | none => none
  let units ← seq.absorbedUnits ws
  guard (units.length = absorbedLengthBefore (pSpec := pSpec) (δ := δ) i.1.val)
  let ⟨salt, _⟩ ← vectorOfListExact (U := U) δ units
  return { roundIdx := i, stmt := seq.stmt, salt := salt,
           encodedMessages := fun j => Vector.ofFn fun t =>
             units.getD (absorbedLengthBefore (pSpec := pSpec) (δ := δ) j.val.1.val + t.val) 0 }

/-- CO25 §5.2 BackTrack with the line-1056 "look for at most one element" optimization.

Performs a single backwards linear scan from `state` along `tr_∇.p`:
- `predecessorCandidates` empty → terminate scan at the current state (chain start).
- `predecessorCandidates` singleton → continue.
- `predecessorCandidates` two or more → scan-time fork → return `err`.
- A singleton that repeats an input capacity → invalid candidate → return `noResult`.

After the scan, `hashAnchorCandidates` is classified the same way over `tr_∇.h`. Finally
`extractCandidate` checks the chain against the absorb layout; its `none` becomes `noResult`.
Proving that the remaining scan-time conflict errors imply the corresponding paper fork events
requires the canonical-completeness/refinement argument stated in Claim 5.19. -/
def linearBackTrack
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (state : CanonicalSpongeState U)
    (depthBound : Nat := trace.length + 1) :
    ExperimentOutput (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := by
  exact
    match linearScanBackwards trace trΔ h_trΔ depthBound state state
      (emptyPartialSequence trace state) with
    | .forkErr => ExperimentOutput.err
    | .noResult => ExperimentOutput.noResult
    | .done seq =>
        match seq.extractCandidate (pSpec := pSpec) (δ := δ) (StmtIn := StmtIn) (U := U)
            (state := state) (trace := trace) with
        | none => ExperimentOutput.noResult
        | some out => ExperimentOutput.some out

/-- The backtracking procedure in Section 5.2, which takes in:
- the query-answer trace for the oracle `(h, p, p⁻¹)`
- a state (vector of `N` units)

And returns one of the following:
- `ExperimentOutput.noResult` — paper-`none` (no elements found in Outs)
- `ExperimentOutput.err` — paper-`err` (multiple elements in Outs, ambiguous)
- `ExperimentOutput.some out` — paper-success (unique tuple `(i, 𝕩, τ, (α̂_1, …, α̂_i))` in Outs)

Implementation: delegates to `linearBackTrack` (CO25 §5.2 line 1056 optimization). Downstream
proofs (BadEvents, AbortAnalysis) quantify over the family structure `S_BT` as an explicit
hypothesis — no family enumeration is computed (see the design note in
`section S_BT_BacktrackComputation`).

This is the unrestricted scan. It can branch on inverse-query-rooted decoy predecessors that
CO25's hash-anchored family never contains; the simulator and StdTrace use `backTrackFwd`. -/
def backTrack
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (state : CanonicalSpongeState U)
    (depthBound : Nat := trace.length + 1) :
    ExperimentOutput (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  linearBackTrack (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound

/-! ## FIX-BT — `BackTrack` over forward-first permutation pairs

**The defect this repairs.**  `tr_∇.p` is bidirectional: an inverse query `p⁻¹(t) = s'` records
the normalized pair `(s', t)` (`ProverTransform.d2sHandleInversePermQuery`).  A three-query
prover can therefore manufacture a *decoy* predecessor for free:

1. `p(a₀) → cur`  — records `(a₀, cur)`;
2. `p⁻¹(t) → s'` with `t ≠ cur` but `t.capacitySegment = cur.capacitySegment` — records `(s', t)`;
3. `p(cur)`.

At step 3, `predecessorCandidates tr_∇ cur.capacitySegment` returns both `(a₀, cur)` and
`(s', t)`; the scan classifies a fork and `backTrack` returns `err`, so `D2SQuery` aborts with
probability 1.  The paper's `BackTrack` does not: its chain family `S_BT` (CO25 Def. 5.3)
requires a **hash anchor** — condition (b), `(h, 𝕩, s_{in,0}.capacitySegment) ∈ tr` — and the
`p⁻¹`-rooted chain through `(s', t)` has none, so it is not a member of the family and never
reaches the `Outs` post-filter.  Def. 5.7's event `E` cannot absorb the difference either:
`isDuplicatedPriorCapacity` charges the *answer* capacity of every query, whereas `t` — the
**input** of the `p⁻¹` query — is adversary-chosen; strengthening `E` to charge it would
falsify the proved `BadEventDS.lemma_5_8` bound.

**The repair.**  Restrict Step 2(b) to the mappings whose first raw occurrence is a forward `p`
query (`DSTraceStorage.buildForwardPermutationIndex`).  Those are exactly the mappings a
hash-anchored chain built from the simulator's own forward queries can consist of, so the
executable single-chain scan now branches only where the paper's family does.  The unrestricted
`backTrack` is deliberately left intact: it is the object the audit counterexample is stated
about, and it remains the right notion for a caller whose trace is `p⁻¹`-free — see
`backTrackFwd_eq_backTrack_of_forwardOnly`.

**Implementation staging.**  The current code reconstructs the forward-first index from the
completed trace, keeping the corrected semantics explicit and proof-friendly.  Once the
correctness proofs stabilize, we plan to maintain the equivalent index incrementally as trace
entries arrive.  This will recover the paper's runtime without changing the `backTrackFwd`
interface or its candidate set. -/

section ForwardFirstBackTrack

/-- CO25 §5.2 `BackTrack`, run against the **forward-first** sub-index of `tr_∇.p`.

This is what `D2SQuery` (`ProverTransform.d2sHandleForwardPermQuery`) and StdTrace
(`TraceTransform.stdTraceHandlePQuery`) call.  On a `p⁻¹`-free trace it agrees with `backTrack`
definitionally-after-rewriting (`backTrackFwd_eq_backTrack_of_hasNoInversePermQuery`). -/
def backTrackFwd
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (state : CanonicalSpongeState U)
    (depthBound : Nat := trace.length + 1) :
    ExperimentOutput (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  backTrack (δ := δ) (pSpec := pSpec) trace
    { trΔ with p := buildForwardPermutationIndex trace trΔ.p }
    h_trΔ.forwardIndex state depthBound

/-- `backTrack` reads `tr_∇` only through `entries`, and the provenance argument only through
`Prop`-valued fields of the reconstructed sequence, so equal tables give equal results. -/
lemma backTrack_congr_trΔ
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {trΔ₁ trΔ₂ : TraceNabla T_H T_P StmtIn U}
    (h₁ : trΔ₁.IsSubsetOfQueryLog trace) (h₂ : trΔ₂.IsSubsetOfQueryLog trace)
    (hEq : trΔ₁ = trΔ₂) (state : CanonicalSpongeState U) (depthBound : Nat) :
    backTrack (δ := δ) (pSpec := pSpec) trace trΔ₁ h₁ state depthBound
      = backTrack (δ := δ) (pSpec := pSpec) trace trΔ₂ h₂ state depthBound := by
  subst hEq
  rfl

/-- **FIX-BT bridge.**  When every mapping stored in `tr_∇.p` is forward-first in `trace`, the
forward-first restriction drops nothing and `backTrackFwd` *is* `backTrack`. -/
theorem backTrackFwd_eq_backTrack_of_forwardOnly
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {trΔ : TraceNabla T_H T_P StmtIn U}
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (state : CanonicalSpongeState U) (depthBound : Nat)
    (hfwd : ∀ pair ∈ TraceTableOps.entries (V := CanonicalSpongeState U) trΔ.p,
      PermutationForwardFirst trace pair.1 pair.2) :
    backTrackFwd (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound
      = backTrack (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound := by
  unfold backTrackFwd
  exact backTrack_congr_trΔ _ _ (by rw [buildForwardPermutationIndex_eq_self hfwd]) _ _

/-- The form the consumers use: on a trace with no `p⁻¹` occurrence at all — the honest verifier
walk and every rate-only simulator walk — `backTrackFwd` and `backTrack` coincide. -/
theorem backTrackFwd_eq_backTrack_of_hasNoInversePermQuery
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {trΔ : TraceNabla T_H T_P StmtIn U}
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (state : CanonicalSpongeState U) (depthBound : Nat)
    (hno : HasNoInversePermQuery (StmtIn := StmtIn) trace) :
    backTrackFwd (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound
      = backTrack (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound :=
  backTrackFwd_eq_backTrack_of_forwardOnly (δ := δ) (pSpec := pSpec) h_trΔ state depthBound
    (TraceNabla.forwardFirst_entries_of_hasNoInversePermQuery hno h_trΔ)

end ForwardFirstBackTrack

end BacktrackProcedure

end DuplexSpongeFS.Backtrack
