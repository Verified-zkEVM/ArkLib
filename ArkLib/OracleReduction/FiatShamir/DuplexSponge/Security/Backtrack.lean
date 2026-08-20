/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BacktrackSchedule
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceDataStructures

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

  /-- **no “loops” across query and answer capacity segments**: `s_{C,in,ι} ≠ s_{C,out,ι}`
    for all `ι < m_k`. CO25 Def 5.3 condition (e). -/
  capacitySegment_input_ne_output : ∀ i : Fin outputState.length,
    inputState[i].capacitySegment ≠ outputState[i].capacitySegment

noncomputable section

/-- The flattened sequence of states: `[s_{in,0}, s_{out,0}, s_{in,1}, s_{out,1}, ..., s]`. -/
def BacktrackSequence.flattenStateSequence
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) : List (CanonicalSpongeState U) :=
  (seq.inputState.zip seq.outputState).foldr (fun p acc => p.1 :: p.2 :: acc) [state]

/-- First-occurrence index of an entry in a trace. -/
private def firstOccurrenceIndex
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entry : duplexSpongeTraceEntry)
    (hEntry : entry ∈ trace) : Fin trace.length := by
  classical
  exact ⟨trace.findIdx (fun x => decide (x = entry)), List.findIdx_lt_length_of_exists
    ⟨entry, hEntry, decide_eq_true rfl⟩⟩

/-- First-occurrence index of EITHER entryA or entryB in a trace. -/
private def firstOccurrenceOfEither
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entryA entryB : duplexSpongeTraceEntry)
    (hEntry : entryA ∈ trace ∨ entryB ∈ trace) : Fin trace.length := by
  classical
  exact ⟨trace.findIdx (fun x => decide (x = entryA ∨ x = entryB)),
    List.findIdx_lt_length_of_exists (by
      rcases hEntry with hA | hB
      · exact ⟨entryA, hA, decide_eq_true (Or.inl rfl)⟩
      · exact ⟨entryB, hB, decide_eq_true (Or.inr rfl)⟩)⟩

/-- The associated indices (first occurrences in the trace) for a backtracking sequence
This calculate `J_BT(tr,s)` from a lawful backtracking sequence `S_BT(tr,s)`. -/
def BacktrackSequence.Index (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (seq : BacktrackSequence trace state) :
    Fin trace.length × (Fin seq.inputState.length → Fin (trace.length + 1)) :=
  by
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
private lemma firstOccurrenceIndex_get
    (entry : duplexSpongeTraceEntry) (hEntry : entry ∈ trace) :
    trace.get (firstOccurrenceIndex trace entry hEntry) = entry := by
  classical
  rw [List.get_eq_getElem]
  have h := List.findIdx_getElem (xs := trace) (p := fun x => decide (x = entry))
    (w := (firstOccurrenceIndex trace entry hEntry).isLt)
  simpa using h

/-- No earlier position than `firstOccurrenceIndex` carries the entry. -/
private lemma firstOccurrenceIndex_not_mem_take
    (entry : duplexSpongeTraceEntry) (hEntry : entry ∈ trace) :
    entry ∉ trace.take (firstOccurrenceIndex trace entry hEntry).val := by
  classical
  intro hmem
  rw [List.mem_take_iff_getElem] at hmem
  obtain ⟨m, hm, hget⟩ := hmem
  have hmlt : m < (firstOccurrenceIndex trace entry hEntry).val :=
    lt_of_lt_of_le hm (min_le_left _ _)
  have hfalse := List.not_of_lt_findIdx (p := fun x => decide (x = entry)) hmlt
  rw [decide_eq_false_iff_not] at hfalse
  exact hfalse hget

/-- `firstOccurrenceOfEither` indexes one of the two entries. -/
private lemma firstOccurrenceOfEither_get
    (entryA entryB : duplexSpongeTraceEntry) (hEntry : entryA ∈ trace ∨ entryB ∈ trace) :
    trace.get (firstOccurrenceOfEither trace entryA entryB hEntry) = entryA ∨
    trace.get (firstOccurrenceOfEither trace entryA entryB hEntry) = entryB := by
  classical
  rw [List.get_eq_getElem]
  have h := List.findIdx_getElem (xs := trace)
    (p := fun x => decide (x = entryA ∨ x = entryB))
    (w := (firstOccurrenceOfEither trace entryA entryB hEntry).isLt)
  simpa only [decide_eq_true_eq] using h

/-- No earlier position than `firstOccurrenceOfEither` carries either entry. -/
private lemma firstOccurrenceOfEither_not_mem_take
    (entryA entryB : duplexSpongeTraceEntry) (hEntry : entryA ∈ trace ∨ entryB ∈ trace) :
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
      (p := fun x => decide (x = entryA ∨ x = entryB)) hmlt
    rw [decide_eq_false_iff_not] at hfalse
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

/-- A valid sequence `extension` strictly extends `seq` when it has the same hash anchor and
contains `seq`'s flattened state walk as a proper sublist. -/
def BacktrackSequence.StrictlyExtends
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq extension : BacktrackSequence trace state) : Prop :=
  seq.stmt = extension.stmt ∧
  seq.flattenStateSequence.Sublist extension.flattenStateSequence ∧ seq ≠ extension

/-- The simple-walk side condition of revised Definition 5.3: no input capacity is visited
twice. This is a semantic condition on candidate chains; the linear scan must prove that its
visited-capacity accumulator realizes it. -/
def BacktrackSequence.HasDistinctInputCapacities
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) : Prop :=
  (seq.inputState.map CanonicalSpongeState.capacitySegment).Nodup

/-- A backtrack sequence is maximal exactly when no other valid sequence strictly extends it.
This quantifies over all inhabitants of `BacktrackSequence trace state`, not merely over a
chosen finite subfamily. -/
def BacktrackSequence.IsMaximal
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) : Prop :=
  seq.HasDistinctInputCapacities ∧
    ∀ extension : BacktrackSequence trace state,
      extension.HasDistinctInputCapacities → ¬ seq.StrictlyExtends extension

/-- CO25 Def. 5.3 `S_BT(tr, s)` — the complete finite family of maximal backtrack sequences
(Eq. 8 & BackTrack §5.2 Step 2, Eq. 10). A member is a valid chain ending at `s`; conversely,
every maximal valid chain belongs to the family. The completeness direction is essential: an
arbitrary antichain would not denote the paper's `S_BT` and could not witness all ambiguity
events used by Claim 5.19. -/
structure BacktrackSequenceFamily (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) where
  /-- `S_BT(tr, s)` — finite set of backtrack sequences (CO25 Def. 5.3). -/
  seqFamily : Finset (BacktrackSequence trace state)
  /-- Exact realization of Def. 5.3: membership is equivalent to maximality among all valid
  backtrack sequences, not just among the elements already present in `seqFamily`. -/
  complete : ∀ seq : BacktrackSequence trace state,
    seq ∈ seqFamily ↔ seq.IsMaximal

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

/- Design note (CO25 §5.2): Definition 5.3 is the exhaustive semantic family `S_BT(tr, s)`.
The linear scan below is only a proposed implementation optimization. It may reject a partial
branch before that branch has reached a hash anchor and passed the stateful parser; therefore it
is **not** interchangeable with the semantic algorithm merely because the paper later permits
stopping after two surviving `Outs` entries. A future refinement theorem must prove that every
scan-time `forkErr` yields two surviving semantic candidates (or an inversion witness). Until
then, downstream paper proofs must reason about `S_BT`, not about the scan's early exit. -/

/-- Paper §5.2 partial-cap-segment matching for `BackTrack`: enumerate all `(stateIn, stateOut)`
pairs in `tr_∇.p` whose `stateOut.capacitySegment` equals `nextInput.capacitySegment`, with the
no-loop guard `stateIn.cap ≠ stateOut.cap`.

Black-box over `[LawfulTraceTable T_P ...]` via `TraceTableOps.entries`; both forward and inverse
permutation directions already collapse into the same bidirectional `tr_∇.p`
(cf. `TraceNabla.ofQueryLog` dispatch). -/
private def predecessorCandidates
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (nextInputCap : Vector U SpongeSize.C) :
    List (CanonicalSpongeState U × CanonicalSpongeState U) := by
  exact (TraceTableOps.entries (V := CanonicalSpongeState U) trΔ.p).filterMap fun pair =>
    let stateOut := pair.2
    if stateOut.capacitySegment = nextInputCap then
      some pair
    else
      none

/-- A normalized pair is eligible for the executable reverse walk precisely when the first
occurrence of that pair in either permutation direction is a forward `p` query.  This is the
paper's `tr_∇.p.fwdcapoutlu` restriction.  In particular, an inverse-origin pair is not a
backward predecessor merely because the capacity of its *query* happens to match the current
capacity. -/
def ForwardFirst
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (sIn sOut : CanonicalSpongeState U) : Prop :=
  ∃ k : Nat,
    (trace)[k]? = some ⟨.inr (.inl sIn), sOut⟩ ∧
    ∀ j < k,
      (trace)[j]? ≠ some ⟨.inr (.inl sIn), sOut⟩ ∧
        (trace)[j]? ≠ some ⟨.inr (.inr sOut), sIn⟩

/-- Paper §5.2 `p.fwdcapoutlu`: the reverse capacity lookup used by the executable BackTrack
walk.  It considers only forward-first normalized pairs; unrestricted reverse lookup is unsound
because distinct inverse queries may share an output *query* capacity without witnessing `E`.
The balanced-tree implementation stores this forward-first subset explicitly; this list-level
definition is its extensional specification. -/
private noncomputable def forwardPredecessorCandidates
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (nextInputCap : Vector U SpongeSize.C) :
    List (CanonicalSpongeState U × CanonicalSpongeState U) := by
  classical
  exact (TraceTableOps.entries (V := CanonicalSpongeState U) trΔ.p).filterMap fun pair =>
    if pair.2.capacitySegment = nextInputCap ∧ ForwardFirst trace pair.1 pair.2 then
      some pair
    else
      none

/-! ### Linear-scan helpers (CO25 §5.2 BackTrack "look for at most one element" optimization)

The paper's Algorithm 1 enumerates all maximal sequences then post-filters. CO25 line 1056 notes
the procedure can equivalently `look for at most one element` — i.e. abort on scan-time forks.
The required refinement is deliberately kept explicit: it must show that a lookup conflict of
the normalized, duplicate-free live table yields the paper's ambiguity witness.  This is not a
property of an arbitrary `TraceTableOps` implementation or of a raw trace reconstructed with
duplicate insertions. -/

/-- Three-way classification of lookup results, used to detect scan-time forks. -/
private inductive LookupResult (α : Type _) where
  | noMatch
  | unique (a : α)
  | conflict

private def classifyLookup {α : Type _} (xs : List α) : LookupResult α :=
  match xs with
  | [] => .noMatch
  | [a] => .unique a
  | _ :: _ :: _ => .conflict

/-- Paper §5.2 Step 4 hash anchor lookup: filter `tr_∇.h.entries` for statements whose stored
capacity matches the chain's initial capacity. Multiple matches indicate `E_fork,h,p`. -/
private def hashAnchorCandidates
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (cap : Vector U SpongeSize.C) : List StmtIn := by
  classical
  exact (TraceTableOps.entries (V := Vector U SpongeSize.C) trΔ.h).filterMap fun pair =>
    if pair.2 = cap then some pair.1 else none

/-- The table invariant needed by the linear ``look for at most one'' optimization.

The paper-level bad-event argument establishes this for a reusable D2S normal state: stored
pairs have no duplicates, and two stored permutation (respectively hash) answers cannot have the
same capacity unless they are the same pair. It is deliberately stated independently of a raw
trace, because rebuilding a table from a raw trace with `add` may retain harmless repeated
occurrences and does not satisfy this invariant. -/
def SearchUnambiguous (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U) : Prop :=
  (TraceTableOps.entries trΔ.p).Nodup ∧
  (TraceTableOps.entries trΔ.h).Nodup ∧
  (∀ pair₁ ∈ TraceTableOps.entries trΔ.p, ∀ pair₂ ∈ TraceTableOps.entries trΔ.p,
    ForwardFirst trace pair₁.1 pair₁.2 → ForwardFirst trace pair₂.1 pair₂.2 →
      pair₁.2.capacitySegment = pair₂.2.capacitySegment → pair₁ = pair₂) ∧
  (∀ pair₁ ∈ TraceTableOps.entries trΔ.h, ∀ pair₂ ∈ TraceTableOps.entries trΔ.h,
    pair₁.2 = pair₂.2 → pair₁ = pair₂)

private lemma classifyLookup_ne_conflict_of_nodup_of_all_eq
    {α : Type _} {xs : List α}
    (hNodup : xs.Nodup)
    (hAllEq : ∀ a ∈ xs, ∀ b ∈ xs, a = b) :
    classifyLookup xs ≠ .conflict := by
  intro hConflict
  cases xs with
  | nil => simp [classifyLookup] at hConflict
  | cons a xs =>
      cases xs with
      | nil => simp [classifyLookup] at hConflict
      | cons b xs =>
          have hab : a = b := hAllEq a (by simp) b (by simp)
          subst b
          have hNotMem : a ∉ a :: xs := (List.nodup_cons.mp hNodup).1
          exact hNotMem (by simp)

private lemma forwardPredecessorCandidates_nodup
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (cap : Vector U SpongeSize.C)
    (hNodup : (TraceTableOps.entries trΔ.p).Nodup) :
    (forwardPredecessorCandidates trace trΔ cap).Nodup := by
  classical
  unfold forwardPredecessorCandidates
  apply List.Nodup.filterMap _ hNodup
  intro pair₁ pair₂ pair h₁ h₂
  change (if pair₁.2.capacitySegment = cap ∧ ForwardFirst trace pair₁.1 pair₁.2
    then some pair₁ else none) = some pair at h₁
  change (if pair₂.2.capacitySegment = cap ∧ ForwardFirst trace pair₂.1 pair₂.2
    then some pair₂ else none) = some pair at h₂
  split at h₁ <;> try contradiction
  next _ =>
    injection h₁ with hPair₁
    split at h₂ <;> try contradiction
    next _ =>
      injection h₂ with hPair₂
      exact hPair₁.trans hPair₂.symm

private lemma forwardPredecessorCandidates_all_eq
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (cap : Vector U SpongeSize.C)
    (hUnique : ∀ pair₁ ∈ TraceTableOps.entries trΔ.p,
      ∀ pair₂ ∈ TraceTableOps.entries trΔ.p,
      ForwardFirst trace pair₁.1 pair₁.2 → ForwardFirst trace pair₂.1 pair₂.2 →
        pair₁.2.capacitySegment = pair₂.2.capacitySegment → pair₁ = pair₂) :
    ∀ pair₁ ∈ forwardPredecessorCandidates trace trΔ cap,
      ∀ pair₂ ∈ forwardPredecessorCandidates trace trΔ cap, pair₁ = pair₂ := by
  classical
  intro pair₁ h₁ pair₂ h₂
  unfold forwardPredecessorCandidates at h₁ h₂
  rcases List.mem_filterMap.mp h₁ with ⟨source₁, hSource₁, hMap₁⟩
  rcases List.mem_filterMap.mp h₂ with ⟨source₂, hSource₂, hMap₂⟩
  change (if source₁.2.capacitySegment = cap ∧ ForwardFirst trace source₁.1 source₁.2
    then some source₁ else none) = some pair₁ at hMap₁
  change (if source₂.2.capacitySegment = cap ∧ ForwardFirst trace source₂.1 source₂.2
    then some source₂ else none) = some pair₂ at hMap₂
  split at hMap₁ <;> try contradiction
  next hEligible₁ =>
    injection hMap₁ with hPair₁
    subst pair₁
    split at hMap₂ <;> try contradiction
    next hEligible₂ =>
      injection hMap₂ with hPair₂
      subst pair₂
      exact hUnique source₁ hSource₁ source₂ hSource₂ hEligible₁.2 hEligible₂.2
        (hEligible₁.1.trans hEligible₂.1.symm)

private lemma hashAnchorCandidates_nodup
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (cap : Vector U SpongeSize.C)
    (hNodup : (TraceTableOps.entries trΔ.h).Nodup) :
    (hashAnchorCandidates trΔ cap).Nodup := by
  unfold hashAnchorCandidates
  apply List.Nodup.filterMap _ hNodup
  intro pair₁ pair₂ stmt h₁ h₂
  change (if pair₁.2 = cap then some pair₁.1 else none) = some stmt at h₁
  change (if pair₂.2 = cap then some pair₂.1 else none) = some stmt at h₂
  split at h₁ <;> try contradiction
  next hCap₁ =>
    injection h₁ with hStmt₁
    split at h₂ <;> try contradiction
    next hCap₂ =>
      injection h₂ with hStmt₂
      apply Prod.ext
      · exact hStmt₁.trans hStmt₂.symm
      · exact hCap₁.trans hCap₂.symm

private lemma hashAnchorCandidates_all_eq
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (cap : Vector U SpongeSize.C)
    (hUnique : ∀ pair₁ ∈ TraceTableOps.entries trΔ.h,
      ∀ pair₂ ∈ TraceTableOps.entries trΔ.h,
      pair₁.2 = pair₂.2 → pair₁ = pair₂) :
    ∀ stmt₁ ∈ hashAnchorCandidates trΔ cap,
      ∀ stmt₂ ∈ hashAnchorCandidates trΔ cap, stmt₁ = stmt₂ := by
  intro stmt₁ h₁ stmt₂ h₂
  unfold hashAnchorCandidates at h₁ h₂
  rcases List.mem_filterMap.mp h₁ with ⟨source₁, hSource₁, hMap₁⟩
  rcases List.mem_filterMap.mp h₂ with ⟨source₂, hSource₂, hMap₂⟩
  split at hMap₁ <;> try contradiction
  next hCap₁ =>
    injection hMap₁ with hStmt₁
    subst stmt₁
    split at hMap₂ <;> try contradiction
    next hCap₂ =>
      injection hMap₂ with hStmt₂
      subst stmt₂
      have hPair := hUnique source₁ hSource₁ source₂ hSource₂ (hCap₁.trans hCap₂.symm)
      exact congrArg Prod.fst hPair

private lemma forwardPredecessor_lookup_ne_conflict
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (cap : Vector U SpongeSize.C)
    (hUnambiguous : SearchUnambiguous trace trΔ) :
    classifyLookup (forwardPredecessorCandidates trace trΔ cap) ≠ .conflict :=
  classifyLookup_ne_conflict_of_nodup_of_all_eq
    (forwardPredecessorCandidates_nodup trace trΔ cap hUnambiguous.1)
    (forwardPredecessorCandidates_all_eq trace trΔ cap hUnambiguous.2.2.1)

private lemma hash_lookup_ne_conflict
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (cap : Vector U SpongeSize.C)
    (hUnambiguous : SearchUnambiguous trace trΔ) :
    classifyLookup (hashAnchorCandidates trΔ cap) ≠ .conflict :=
  classifyLookup_ne_conflict_of_nodup_of_all_eq
    (hashAnchorCandidates_nodup trΔ cap hUnambiguous.2.1)
    (hashAnchorCandidates_all_eq trΔ cap hUnambiguous.2.2.2)

/-! ### Helper lemmas connecting `trΔ.h`/`trΔ.p` entries to the original `trace`

The key insight: by `LawfulTraceTable.toMultiSet_ofEntries`, membership in `entries`
is equivalent to membership in the abstract multiset model. By `toMultiSet_add`,
each fold step adds exactly one pair to the multiset. So induction on the trace
connects multiset membership back to the original trace entry. -/

/-- An intermediate data structure representing a partially constructed backtrack sequence.
It carries all incremental properties of a valid chain from `head` to
`targetState`, without the hash anchor. This allows us to construct the sequence
iteratively via prepending (`::`), making structural induction proofs trivial. -/
private structure PartialBacktrackSequence (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
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

private def emptyPartialSequence (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
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

private def prependPartialSequence
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
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

private def completeBacktrackSequence
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
    capacitySegment_input_ne_output := seq.capacitySegment_input_ne_output }

/-! ### Bridge lemmas: `classifyLookup` + `filterMap` → entry membership -/

omit [SpongeSize] in
private lemma classifyLookup_filterMap_singleton_mem {α β : Type _}
    (l : List α) (f : α → Option β) (b : β)
    (h : classifyLookup (l.filterMap f) = .unique b) :
    ∃ a ∈ l, f a = some b := by
  have : b ∈ l.filterMap f := by
    have : l.filterMap f = [b] := by
      cases h' : l.filterMap f with
      | nil => rw [h'] at h; unfold classifyLookup at h; contradiction
      | cons hd tl =>
        cases tl with
        | nil =>
            rw [h'] at h; unfold classifyLookup at h
            injection h with hEq; subst hEq; rfl
        | cons _ _ => rw [h'] at h; unfold classifyLookup at h; contradiction
    rw [this]; exact .head ..
  exact List.mem_filterMap.mp this

private lemma hash_unique_mem_entries
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

private lemma forwardPred_unique_mem_and_cap
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (cap : Vector U SpongeSize.C)
    (s_in s_out : CanonicalSpongeState U)
    (h : classifyLookup (forwardPredecessorCandidates trace trΔ cap) = .unique (s_in, s_out)) :
    (s_in, s_out) ∈ TraceTableOps.entries (V := CanonicalSpongeState U) trΔ.p ∧
      s_out.capacitySegment = cap ∧ ForwardFirst trace s_in s_out := by
  unfold forwardPredecessorCandidates at h
  classical
  have ⟨pair, hMem, hEq⟩ := classifyLookup_filterMap_singleton_mem
      (TraceTableOps.entries (V := CanonicalSpongeState U) trΔ.p)
      (fun pair => if pair.2.capacitySegment = cap ∧ ForwardFirst trace pair.1 pair.2
        then some pair else none) (s_in, s_out) h
  split at hEq
  · next hEligible =>
      injection hEq with hInj; subst hInj
      exact ⟨hMem, hEligible.1.symm ▸ rfl, hEligible.2⟩
  · contradiction

/-- Output of a linear backwards scan: either a fork was detected, or the scan terminated
with an optional BacktrackSequence. -/
private inductive LinearScanResult (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
  (targetState : CanonicalSpongeState U) where
  | forkErr
  | noResult
  | done (seq : BacktrackSequence trace targetState)

/-- CO25 §5.2 BackTrack linear backwards scan: from `currentState`, classify the predecessor
candidates in `tr_∇.p`. `[]` ends the scan; `[pred]` continues; `_::_::_` is a fork → `.forkErr`.

A self-loop or a repeated input capacity is an invalid candidate chain: it violates the
simple-capacity-walk side condition of Definition 5.3. It is not an ambiguity between two valid
`Outs` entries, so those branches return `.noResult`. `.forkErr` is reserved for an actual
multiple-match lookup.
Structurally recursive on `fuel`; the caller supplies `fuel = depthBound`.
Uses a tail-recursive accumulator `acc` to build the sequence by prepending. -/
private noncomputable def linearScanBackwards
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (fuel : Nat) (currentState targetState : CanonicalSpongeState U)
    (vCap : List (Vector U SpongeSize.C))
    (acc : PartialBacktrackSequence trace currentState targetState) :
    LinearScanResult trace targetState :=
  match fuel with
  | 0 => .noResult
  | fuel' + 1 =>
    -- Look up predecessor in `tr_∇.p` (CO25 §5.2 Step 2.b)
    match hClsPred : classifyLookup (forwardPredecessorCandidates (T_P := T_P) (U := U) trace trΔ
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
          .noResult -- invalid candidate: Def. 5.3(e)
        else
          have hNoLoop' : s_in.capacitySegment ≠ s_out.capacitySegment := hNoLoop
          if s_in.capacitySegment ∈ vCap then
            .noResult -- invalid candidate: repeated input capacity
          else
            have hMatch : s_out.capacitySegment = currentState.capacitySegment :=
              (forwardPred_unique_mem_and_cap trace trΔ currentState.capacitySegment s_in s_out
                hClsPred).2.1
            have hEntry : ⟨.inr (.inl s_in), s_out⟩ ∈ trace := by
              obtain ⟨_, hForward, _⟩ :=
                (forwardPred_unique_mem_and_cap trace trΔ currentState.capacitySegment s_in s_out
                  hClsPred).2.2
              exact List.mem_iff_getElem?.mpr ⟨_, hForward⟩
            -- Prepend to sequence and continue scanning (CO25 §5.2 Step 2.b)
            let acc' := prependPartialSequence trace targetState currentState
              s_in s_out acc hMatch (Or.inl hEntry) hNoLoop'
            linearScanBackwards trace trΔ h_trΔ fuel' s_in targetState
              (s_in.capacitySegment :: vCap) acc'
    | .conflict => .forkErr -- `L_p` collision → `E_fork`

private theorem linearScanBackwards_ne_fork_of_searchUnambiguous
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (hUnambiguous : SearchUnambiguous trace trΔ)
    (fuel : Nat) (currentState targetState : CanonicalSpongeState U)
    (vCap : List (Vector U SpongeSize.C))
    (acc : PartialBacktrackSequence trace currentState targetState) :
    linearScanBackwards trace trΔ h_trΔ fuel currentState targetState vCap acc ≠ .forkErr := by
  induction fuel generalizing currentState vCap acc with
  | zero => simp [linearScanBackwards]
  | succ fuel ih =>
      simp only [linearScanBackwards]
      split
      case h_1 hPred =>
        split
        case h_1 => simp
        case h_2 => simp
        case h_3 hHash =>
          exact (hash_lookup_ne_conflict trace trΔ currentState.capacitySegment hUnambiguous hHash).elim
      case h_2 pred hPred =>
        split
        case isTrue => simp
        case isFalse hLoop =>
          split
          case isTrue => simp
          case isFalse hSeen =>
            apply ih
      case h_3 hPred =>
        exact (forwardPredecessor_lookup_ne_conflict trace trΔ currentState.capacitySegment
          hUnambiguous hPred).elim

end S_BT_BacktrackComputation

/-- One actual interaction in protocol order.  This deliberately does not
pair a challenge with a single message: `ProtocolSpec` permits consecutive
prover-message or verifier-challenge rounds, and the stateful replay must
preserve every `Absorb` and `Squeeze` call. -/
private inductive StatefulOperation where
  | message (idx : pSpec.MessageIdx)
  | challenge (idx : pSpec.ChallengeIdx)

/-- The complete protocol action stream, in increasing round order. -/
private def statefulOperations : List (StatefulOperation (pSpec := pSpec)) :=
  (List.finRange n).map fun i =>
    match h : pSpec.dir i with
    | .P_to_V => StatefulOperation.message ⟨i, h⟩
    | .V_to_P => StatefulOperation.challenge ⟨i, h⟩

/-- Forget the dependent index while retaining the action and public length
needed by the generic stateful scheduler. -/
private def StatefulOperation.phaseShape : StatefulOperation (pSpec := pSpec) →
    ScheduleCursor.PhaseShape
  | .message idx => .absorb (messageSize idx)
  | .challenge idx => .squeeze (challengeSize idx)

/-- The generic phase schedule replayed by the parser.  Its entries stay in
lockstep with `statefulOperations`, so schedule cardinality and query-budget
lemmas apply to the same layout used for candidate extraction. -/
private def statefulPhaseShapes : List ScheduleCursor.PhaseShape :=
  (statefulOperations (pSpec := pSpec)).map StatefulOperation.phaseShape

/-- BackTrack §5.2 Step 1: initialize the input-state list for a candidate chain. -/
private def backtrackStep1Init
    (state : CanonicalSpongeState U)
    (steps : List (CanonicalSpongeState U × CanonicalSpongeState U)) :
    List (CanonicalSpongeState U) :=
  (steps.map Prod.fst) ++ [state]

private def guardH (P : Prop) [Decidable P] : Option (PLift P) :=
  if h : P then some ⟨h⟩ else none

/-- Try to assemble exactly `len` elements from `xs` into a `Vector U len`. Returns
`some ⟨v, hLen⟩` carrying a proof that `xs` actually had at least `len` elements, so callers
can use `do`-notation while still recovering the length bound. -/
private def vectorOfListExact
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

/-- Read one rate coordinate named by the stateful layout.  A missing query
input or a rate offset outside the rate segment invalidates the candidate.
The terminal `in_m` is intentionally readable: it is the input to the query
currently being classified by BackTrack. -/
private def BacktrackSequence.readRateLocation
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state)
    (loc : ScheduleCursor.RateLocation) : Option U := do
  let stateIn ← seq.inputState[loc.queryIndex]?
  stateIn.rateSegment.toList[loc.rateOffset]?

/-- Recover source units in their layout order.  This is the extraction side of
the stateful BackTrack repair: salt and encoded prover messages are no longer
read from a static interval of query blocks. -/
private def BacktrackSequence.readRateLocations
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state)
    (locations : List ScheduleCursor.RateLocation) : Option (List U) :=
  locations.mapM seq.readRateLocation

/-- Generated untouched-coordinate frame check for one input-rate coordinate.
Written locations are unconstrained here because they are the salt/message
source values.  Every other coordinate is either zero in the start state or
the corresponding coordinate of the preceding permutation output. -/
private def BacktrackSequence.frameHoldsAt
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state)
    (writes : List ScheduleCursor.RateLocation)
    (queryIndex rateOffset : ℕ) : Bool :=
  if ⟨queryIndex, rateOffset⟩ ∈ writes then true else
    match seq.inputState[queryIndex]? with
    | some stateIn =>
        match stateIn.rateSegment.toList[rateOffset]? with
        | none => false
        | some unitIn =>
            if queryIndex = 0 then
              if unitIn = (0 : U) then true else false
            else
              match seq.outputState[queryIndex - 1]? with
              | none => false
              | some stateOut =>
                  match stateOut.rateSegment.toList[rateOffset]? with
                  | some unitOut => if unitIn = unitOut then true else false
                  | none => false
    | none => false

/-- Validate all untouched coordinates of every input state present in the
backtrack chain.  This uniformly subsumes the old salt-suffix, message-suffix,
and squeeze-window equality checks. -/
private def BacktrackSequence.checkFrames
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state)
    (writes : List ScheduleCursor.RateLocation) : Bool :=
  (List.range seq.inputState.length).all fun queryIndex =>
    (List.range SpongeSize.R).all fun rateOffset =>
      seq.frameHoldsAt writes queryIndex rateOffset

/-- Stateful replacement for CO25 §5.2 Steps 3--4.

The parser starts with `Start`'s cursor `(q,a,s) = (0,0,r)`, absorbs the salt,
and then replays *every* protocol operation.  It extracts salt/message units
from the generated write locations and validates all other rate coordinates by
the untouched-coordinate frame rule.  Thus no candidate boundary is inferred
from the old scalar `L_ptr`: a candidate exists precisely when the terminal
permutation input is the first query of a nonempty verifier squeeze.

This is intentionally stricter than the historical `constructCandidateSalt` +
`extractCandidate` pair, whose static block intervals assume every phase uses
its ceiling number of rate blocks. -/
private def BacktrackSequence.extractCandidateStateful
    (state : CanonicalSpongeState U)
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (seq : BacktrackSequence (trace := trace) (state := state)) :
    Option (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  let initialCursor : ScheduleCursor :=
    { queryIndex := 0, absorbOffset := 0, squeezeOffset := SpongeSize.R }
  let operations := statefulOperations (pSpec := pSpec)
  let phases := statefulPhaseShapes (pSpec := pSpec)
  let schedule := ScheduleCursor.buildPhaseSchedule SpongeSize.R initialCursor δ phases
  let writes := schedule.saltLocations ++
    schedule.phaseLayouts.flatMap ScheduleCursor.PhaseLayout.sourceLocations
  if !seq.checkFrames writes then
    none
  else
    match seq.readRateLocations schedule.saltLocations with
    | none => none
    | some saltUnits =>
      match vectorOfListExact (U := U) δ saltUnits with
      | none => none
      | some ⟨salt, _⟩ =>
        let terminalQuery := seq.inputState.length - 1
        let rec go : List (StatefulOperation (pSpec := pSpec)) →
            List ScheduleCursor.PhaseLayout →
            List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx)) →
            Option (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          | [], _, _ => none
          | _, [], _ => none
          | operation :: operations, layout :: layouts, acc =>
              match operation with
              | .message msgIdx =>
                  match seq.readRateLocations layout.sourceLocations with
                  | none => none
                  | some messageUnits =>
                    match vectorOfListExact (U := U) (messageSize msgIdx) messageUnits with
                    | none => none
                    | some ⟨encoded, _⟩ =>
                        go operations layouts (acc ++ [⟨msgIdx, encoded⟩])
              | .challenge challengeIdx =>
                  if layout.firstSqueezeQuery = some terminalQuery then
                    if _hNonempty : 0 < challengeSize (pSpec := pSpec) challengeIdx then
                      let messages : pSpec.EncodedMessagesBefore U challengeIdx.1.castSucc :=
                        fun ⟨msgIdx, _⟩ =>
                          match acc.findSome? (fun entry =>
                              if h : entry.1 = msgIdx then some (h ▸ entry.2) else none) with
                          | some encoded => encoded
                          | none => Vector.replicate (messageSize msgIdx) (0 : U)
                      some
                        { roundIdx := challengeIdx, stmt := seq.stmt, salt := salt,
                          encodedMessages := messages }
                    else
                      none
                  else
                    go operations layouts acc
        go operations schedule.phaseLayouts []

/-- Candidate implementation of a linear backwards scan.

Performs a single backwards linear scan from `state` along `tr_∇.p`:
- `predecessorCandidates` empty → terminate scan at the current state (chain start).
- `predecessorCandidates` singleton → continue.
- `predecessorCandidates` two or more → scan-time fork → return `err`.

After the scan, `hashAnchorCandidates` is classified the same way over `tr_∇.h`. Finally the
stateful layout parser is run; its `none` becomes `noResult`. This is not yet the executable
realization of the paper algorithm: the required parser/branch-completeness refinement theorem
is intentionally a separate obligation. -/
private noncomputable def linearBackTrack
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (state : CanonicalSpongeState U)
    (depthBound : Nat := trace.length + 1) :
    ExperimentOutput (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := by
  exact
    match linearScanBackwards trace trΔ h_trΔ depthBound state state
      [state.capacitySegment] (emptyPartialSequence trace state) with
    | .forkErr => ExperimentOutput.err
    | .noResult => ExperimentOutput.noResult
    | .done seq =>
        match seq.extractCandidateStateful (pSpec := pSpec) (δ := δ) (StmtIn := StmtIn) (U := U)
            (state := state) (trace := trace) with
        | none => ExperimentOutput.noResult
        | some out => ExperimentOutput.some out

/-- The current executable candidate for the backtracking procedure in Section 5.2, which takes in:
- the query-answer trace for the oracle `(h, p, p⁻¹)`
- a state (vector of `N` units)

And returns one of the following:
- `ExperimentOutput.noResult` — paper-`none` (no elements found in Outs)
- `ExperimentOutput.err` — paper-`err` (multiple elements in Outs, ambiguous)
- `ExperimentOutput.some out` — paper-success (unique tuple `(i, 𝕩, τ, (α̂_1, …, α̂_i))` in Outs)

Implementation status: delegates to `linearBackTrack`. The paper-facing algorithm is the
exhaustive `S_BT`-and-`Outs` construction; this scan becomes an implementation of it only after
the separate branch-completeness/parser-refinement theorem is proved. -/
noncomputable def backTrack
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (state : CanonicalSpongeState U)
    (depthBound : Nat := trace.length + 1) :
    ExperimentOutput (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  linearBackTrack (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound

/-- The executable scan has no `.err` outcome once its live normalized table has one candidate
per output capacity and one hash anchor per capacity.  Invalid cyclic branches are already
classified as `noResult` by the scan; hence only an actual multiple-match lookup could produce
`.err`, and `SearchUnambiguous` rules that out. -/
theorem backTrack_ne_err_of_searchUnambiguous
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (hUnambiguous : SearchUnambiguous trace trΔ)
    (state : CanonicalSpongeState U)
    (depthBound : Nat := trace.length + 1) :
    backTrack (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound ≠
      ExperimentOutput.err := by
  unfold backTrack linearBackTrack
  generalize hScan :
    linearScanBackwards trace trΔ h_trΔ depthBound state state [state.capacitySegment]
      (emptyPartialSequence trace state) = result
  cases result with
  | forkErr =>
      exact (linearScanBackwards_ne_fork_of_searchUnambiguous trace trΔ h_trΔ hUnambiguous
        depthBound state state [state.capacitySegment] (emptyPartialSequence trace state) hScan).elim
  | noResult => simp
  | done seq =>
      cases hOut : seq.extractCandidateStateful (pSpec := pSpec) (δ := δ) (StmtIn := StmtIn)
        (U := U) (state := state) (trace := trace) <;> simp [hOut]

end BacktrackProcedure

end DuplexSpongeFS.Backtrack
