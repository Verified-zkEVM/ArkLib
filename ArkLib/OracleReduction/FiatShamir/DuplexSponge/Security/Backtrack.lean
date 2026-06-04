/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceDataStructures

/-!
# Backtracking sequence family and procedure

This file contains the backtracking sequence family and procedure for the analysis of duplex sponge
Fiat-Shamir, following Section 5.2 in the paper.

- `BacktrackSequence`: a single backtrack sequence
- `S_BT/BacktrackSequenceFamily`: a set of lawful backtrack sequences of a `(h,p,p⁻¹)`-trace
  - `BacktrackSequenceFamily.backtrackCompute`: the backtrack algorithm to compute all backtrack
    sequences from the query trace `tr`.
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

noncomputable section CoreDefinitions

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

/-- CO25 Def 5.3 `S_BT(tr, s)` — maximal family of backtrack sequences
(Eq. 8 & BackTrack §5.2 Step 2, Eq. 10): a finite set of `BacktrackSequence` pairs
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

/-- Definition 5.4: index list payload attached to one sequence. -/
abbrev BacktrackIndexList
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) :=
  Fin trace.length × (Fin seq.inputState.length → Fin (trace.length + 1))

open Classical in
/-- Definition 5.4: `J_BT(tr,s)` — the image of `S_BT(tr,s)` under `BacktrackSequence.Index`.
Every sequence in `S_BT` is paired with its unique index list; no sequence is omitted. -/
noncomputable def J_BT
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (family : BacktrackSequenceFamily trace state) :
    Finset (Sigma fun seq : BacktrackSequence trace state => BacktrackIndexList trace seq) :=
  family.seqFamily.image (fun seq => ⟨seq, BacktrackSequence.Index trace state seq⟩)

end CoreDefinitions

noncomputable section BacktrackProcedure

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

private inductive BuildBacktrackResult (U : Type) [SpongeUnit U] [SpongeSize] where
  | err
  | ok (stepFamilies : List (List (CanonicalSpongeState U × CanonicalSpongeState U)))

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

/-! ### Linear-scan helpers (CO25 §5.2 BackTrack "look for at most one element" optimization)

The paper's Algorithm 1 enumerates all maximal sequences then post-filters. CO25 line 1056 notes
the procedure can equivalently `look for at most one element` — i.e. abort on scan-time forks.
A scan-time fork strictly implies an `E_fork,p`/`E_fork,h,p`/`E_fork` event, so returning `err`
on a fork is a strict over-approximation of the paper's post-filter `err` condition and the
soundness bound of CO25 Theorem 5.19 is preserved. -/

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

/-! ### Helper lemmas connecting `trΔ.h`/`trΔ.p` entries to the original `trace`

The key insight: by `LawfulTraceTable.toMultiSet_ofEntries`, membership in `entries`
is equivalent to membership in the abstract multiset model. By `toMultiSet_add`,
each fold step adds exactly one pair to the multiset. So induction on the trace
connects multiset membership back to the original trace entry. -/

/-- An intermediate data structure representing a partially constructed backtrack sequence.
It carries all incremental properties of a valid chain from `head` to `targetState`, without the hash anchor.
This allows us to construct the sequence iteratively via prepending (`::`), making structural induction proofs trivial. -/
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

private noncomputable def prependPartialSequence
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

private noncomputable def completeBacktrackSequence
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

private lemma classifyLookup_filterMap_singleton_mem {α β : Type _} [DecidableEq β]
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

private lemma pred_unique_mem_and_cap
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
private inductive LinearScanResult (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
  (targetState : CanonicalSpongeState U) where
  | forkErr
  | noResult
  | done (seq : BacktrackSequence trace targetState)

/-- CO25 §5.2 BackTrack linear backwards scan: from `currentState`, classify the predecessor
candidates in `tr_∇.p`. `[]` ends the scan; `[pred]` continues; `_::_::_` is a fork → `.forkErr`.
Loops in capacity segment are detected using `vCap` and result in `.forkErr`.
Structurally recursive on `fuel`; the caller supplies `fuel = depthBound`.
Uses a tail-recursive accumulator `acc` to build the sequence by prepending. -/
private def linearScanBackwards
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
          .forkErr -- Self-loop → `E_inv`
        else
          have hNoLoop' : s_in.capacitySegment ≠ s_out.capacitySegment := hNoLoop
          if s_in.capacitySegment ∈ vCap then
            .forkErr -- Cycle detected
          else
            have hMatch : s_out.capacitySegment = currentState.capacitySegment :=
              (pred_unique_mem_and_cap trΔ currentState.capacitySegment s_in s_out hClsPred).2
            have hEntry : ⟨.inr (.inl s_in), s_out⟩ ∈ trace ∨ ⟨.inr (.inr s_out), s_in⟩ ∈ trace := by
              have hMem : (s_in, s_out) ∈
                TraceTableOps.entries (V := CanonicalSpongeState U) trΔ.p :=
                (pred_unique_mem_and_cap trΔ currentState.capacitySegment s_in s_out hClsPred).1
              exact h_trΔ.2 _ _ hMem
            -- Prepend to sequence and continue scanning (CO25 §5.2 Step 2.b)
            let acc' := prependPartialSequence trace targetState currentState
              s_in s_out acc hMatch hEntry hNoLoop'
            linearScanBackwards trace trΔ h_trΔ fuel' s_in targetState
              (s_in.capacitySegment :: vCap) acc'
    | .conflict => .forkErr -- `L_p` collision → `E_fork`

/-- BackTrack §5.2 Step 2: A concrete backtrack algorithm to exhausively scan an
and compute a valid sequence family `S_BT(tr, s)`. -/
private def BacktrackSequenceFamily.sequenceScan
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (depthBound : Nat)
    (state : CanonicalSpongeState U) :
    BuildBacktrackResult U :=
  -- scan backwards
  let rec go (fuel : Nat) (current : CanonicalSpongeState U)
      (stepsRev : List (CanonicalSpongeState U × CanonicalSpongeState U)) :
      BuildBacktrackResult U :=
    match fuel with
    | 0 => .err
    | fuel + 1 =>
      let preds := predecessorCandidates (T_P := T_P) (U := U) trΔ current.capacitySegment
      let validPreds := preds.filter (fun p => p.1.capacitySegment ≠ p.2.capacitySegment)
      match validPreds with
      | [] => .ok [stepsRev.reverse]
      | _ =>
        let rec collect
            (remaining : List (CanonicalSpongeState U × CanonicalSpongeState U))
            (acc : List (List (CanonicalSpongeState U × CanonicalSpongeState U))) :
            BuildBacktrackResult U :=
          match remaining with
          | [] => .ok acc
          | pred :: rest =>
            match go fuel pred.1 (pred :: stepsRev) with
            | .err => .err
            | .ok childFamilies => collect rest (acc ++ childFamilies)
        collect preds []
  go depthBound state []

/-- BackTrack §5.2 Step 2: A concrete backtrack algorithm to exhausively scan an
and compute a valid sequence family `S_BT(tr, s)`. -/
private def BacktrackSequenceFamily.compute
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (state : CanonicalSpongeState U) (depthBound : Nat) :
    BacktrackSequenceFamily (trace := trace) (state := state):=
  sorry

end S_BT_BacktrackComputation

/-- CO25 Eq. 6 — `L_δ = ⌈δ / r⌉`: number of rate blocks for the salt. -/
private def Lδ : Nat := Nat.ceil ((δ : ℚ) / SpongeSize.R)

private def challengeIdxList : List pSpec.ChallengeIdx :=
  (Finset.univ : Finset pSpec.ChallengeIdx).toList

def messageIdxListBefore (i : pSpec.ChallengeIdx) : List pSpec.MessageIdx :=
  ((Finset.univ : Finset pSpec.MessageIdx).filter (fun j => j.1 < i.1)).toList

private def challengeIdxListBefore (i : pSpec.ChallengeIdx) : List pSpec.ChallengeIdx :=
  ((Finset.univ : Finset pSpec.ChallengeIdx).filter (fun j => j.1 < i.1)).toList

private def lastMessageBefore? (i : pSpec.ChallengeIdx) : Option pSpec.MessageIdx :=
  (messageIdxListBefore (pSpec := pSpec) i).getLast?

private def sumMessageBlocksBefore (i : pSpec.ChallengeIdx) : Nat :=
  (messageIdxListBefore (pSpec := pSpec) i).foldl (fun acc j => acc + pSpec.Lₚᵢ j) 0

private def sumChallengeBlocksBefore (i : pSpec.ChallengeIdx) : Nat :=
  (challengeIdxListBefore (pSpec := pSpec) i).foldl (fun acc j => acc + pSpec.Lᵥᵢ j) 0



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
    (len : Nat) (xs : List U) : Option { v : Vector U len // len ≤ xs.length } := by
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

/-- `rateUnitsOf xs` — concatenation of every rate-segment in a list of sponge states.
For a `BacktrackSequence`, applied to `inputState`, this is the full sequence
`s_{R,in,0} ‖ s_{R,in,1} ‖ ⋯ ‖ s_{R,in,m_k}` of all sponge rate units (CO25 §5.2 Step 3). -/
private def rateUnitsOf (xs : List (CanonicalSpongeState U)) : List U :=
  xs.foldl (fun acc s => acc ++ s.rateSegment.toList) []

/-- The concatenated rate units of a `BacktrackSequence`'s `inputState` chain
(CO25 §5.2 Step 3 salt source). -/
private def BacktrackSequence.rateUnits
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) : List U :=
  rateUnitsOf seq.inputState

/-- Generalized form: rate-segment concatenation over any state list with any accumulator. -/
private lemma rateConcat_length_aux
    (xs : List (CanonicalSpongeState U)) (acc : List U) :
    (xs.foldl (fun acc s => acc ++ s.rateSegment.toList) acc).length =
      acc.length + xs.length * SpongeSize.R := by
  induction xs generalizing acc with
  | nil => simp
  | cons x ys ih =>
    rw [List.foldl_cons, ih (acc ++ x.rateSegment.toList)]
    have hRate : x.rateSegment.toList.length = SpongeSize.R := by
      simp [Vector.length_toList]
    rw [List.length_append, hRate, List.length_cons]
    ring

/-- `|rateUnitsOf xs| = |xs| · R` — reusable helper for `Lδ` block-count bounds. -/
private lemma rateUnitsOf_length (xs : List (CanonicalSpongeState U)) :
    (rateUnitsOf (U := U) xs).length = xs.length * SpongeSize.R := by
  unfold rateUnitsOf
  have := rateConcat_length_aux (U := U) xs []
  rw [List.length_nil, Nat.zero_add] at this
  exact this

/-- `|seq.rateUnits| = |seq.inputState| · R`. -/
private lemma BacktrackSequence.rateUnits_length
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) :
    seq.rateUnits.length = seq.inputState.length * SpongeSize.R := by
  unfold BacktrackSequence.rateUnits
  exact rateUnitsOf_length _

/-- CO25 Eq. 6 — `δ > R ⟹ Lδ ≥ 2`. -/
private lemma Lδ_ge_two_of_gt_R (h : SpongeSize.R < δ) : 2 ≤ Lδ (δ := δ) := by
  unfold Lδ
  have hR_pos : (0 : ℚ) < (SpongeSize.R : ℚ) := by
    have : 0 < SpongeSize.R := Nat.pos_of_neZero _
    exact_mod_cast this
  have hδ_gt : (1 : ℚ) < (δ : ℚ) / (SpongeSize.R : ℚ) := by
    rw [lt_div_iff₀ hR_pos]
    have : (SpongeSize.R : ℚ) < (δ : ℚ) := by exact_mod_cast h
    linarith
  -- `⌈x⌉ ≥ 2` when `x > 1`.
  exact Nat.add_one_le_iff.mpr (Nat.lt_ceil.mpr (by exact_mod_cast hδ_gt))

/-- From `δ ≤ |seq.rateUnits|`, the rate-block count of an `inputState`
chain satisfies `Lδ ≤ |inputState|`. -/
private lemma Lδ_le_inputState_length
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state)
    (h : δ ≤ seq.rateUnits.length) :
    Lδ (δ := δ) ≤ seq.inputState.length := by
  rw [BacktrackSequence.rateUnits_length] at h
  -- Now `h : δ ≤ |inputState| * R`. Show `⌈δ/R⌉ ≤ |inputState|`.
  unfold Lδ
  have hR_pos : (0 : ℚ) < (SpongeSize.R : ℚ) := by
    have : 0 < SpongeSize.R := Nat.pos_of_neZero _
    exact_mod_cast this
  refine Nat.ceil_le.mpr ?_
  rw [div_le_iff₀ hR_pos]
  have : (δ : ℚ) ≤ (seq.inputState.length : ℚ) * (SpongeSize.R : ℚ) := by
    have := h
    exact_mod_cast this
  exact this

/-- BackTrack §5.2 Step 4(a).iii.A — assemble the encoded i-th prover message:
  `α̂_i^(k) := concat_rate_segs(s_{R,in,L_ptr(i)}, …, s_{R,in,L_ptr(i)+L_P(i)-1})[0 : ℓ_P(i)]
              ∈ Σ^{ℓ_P(i)}`  (CO25 Eq. 11).

Char-based view: take the rate chars from `L_P(i)` consecutive input states (each
contributing `r` chars), then keep the first `ℓ_P(i)` chars of the concatenation. -/
private def BacktrackSequence.assembleEncodedMessage
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state)
    (L_ptr lpCur : Nat) (msgIdx : pSpec.MessageIdx) :
    Option (Vector U (messageSize msgIdx)) := do
  let blockUnits :=
    ((seq.inputState.drop L_ptr).take lpCur).foldl
      (fun acc s => acc ++ s.rateSegment.toList) []
  let ⟨v, _⟩ ← vectorOfListExact (U := U) (messageSize msgIdx) blockUnits
  return v

/-- BackTrack §5.2 Step 4(a).iii.E — verifier squeeze window check.

Char-based view: for a verifier squeeze starting at block `squeezeStart` of length
`lvCur` blocks (= `lvCur · r` chars), consecutive squeeze blocks must agree on their
rate segments — i.e. for each `k' ∈ [lvCur)`,
  `s_{R,out, squeezeStart+k'}  =  s_{R,in, squeezeStart+k'+1}`. -/
private def BacktrackSequence.checkSqueezeWindow
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state)
    (squeezeStart lvCur : Nat) : Bool := Id.run do
  let mut ok : Bool := true
  for k' in List.range lvCur do
    let outIdx := squeezeStart + k'
    let inIdx := squeezeStart + 1 + k'
    match seq.outputState[outIdx]?, seq.inputState[inIdx]? with
    | some sOut, some sIn =>
      if sOut.rateSegment ≠ sIn.rateSegment then ok := false
    | _, _ => ok := false
  return ok

/-- BackTrack §5.2 Step 3 (per-sequence): extract candidate salt `∈ U^δ` and validate
the rate-suffix consistency of the last absorb block.

- Concatenates the rate segments of all input states `[s_{in,0}, …, s_{in,m_k}]` and
  slices off exactly `δ` elements.  Returns `none` if length is insufficient.
- When `δ > r`, additionally checks `s_{R,in,L_δ-1}[δ mod r : r] = s_{R,out,L_δ-2}[δ mod r : r]`
  (CO25 Step 3 remainder condition).  Returns `none` if the check fails. -/
private def BacktrackSequence.constructCandidateSalt
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) :
    Option (Vector U δ) := do
  -- 1. Assemble all sponge-rate units across input blocks; `vectorOfListExact` returns the
  --    salt together with the proof `δ ≤ |seq.rateUnits|`.
  let ⟨saltₖ, hLen⟩ ← vectorOfListExact (U := U) δ seq.rateUnits
  -- 2. From the length bound, derive `Lδ ≤ |inputState|`.
  have hLδ_le : Lδ (δ := δ) ≤ seq.inputState.length :=
    Lδ_le_inputState_length (δ := δ) seq hLen
  -- 3. CO25 Step 3 salt remainder check: case-split on `δ ≤ R`.
  if hδR : δ ≤ SpongeSize.R then
    -- No remainder to check; just return the salt.
    return saltₖ
  else
    -- `δ > R` ⟹ `Lδ ≥ 2`, so `Lδ - 1` and `Lδ - 2` are valid indices.
    have hLδ_ge2 : 2 ≤ Lδ (δ := δ) := Lδ_ge_two_of_gt_R (Nat.lt_of_not_le hδR)
    have h_in_bound : Lδ (δ := δ) - 1 < seq.inputState.length := by omega
    have h_out_bound : Lδ (δ := δ) - 2 < seq.outputState.length := by
      rw [seq.inputState_length_eq_outputState_length_succ] at hLδ_le
      omega
    --- Check `non-overwritten rate suffix consistency` of the last pair
    let sIn := seq.inputState.get ⟨Lδ (δ := δ) - 1, h_in_bound⟩
    let sOut := seq.outputState.get ⟨Lδ (δ := δ) - 2, h_out_bound⟩
    if h_cons : sIn.rateSegment.toList.drop (δ % SpongeSize.R) =
          sOut.rateSegment.toList.drop (δ % SpongeSize.R) then
      return saltₖ
    else
      none

/-- BackTrack §5.2 Step 4: Parse the protocol rounds to extract and validate messages. -/
private def BacktrackSequence.extractCandidate
    (state : CanonicalSpongeState U)
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (seq : BacktrackSequence (trace := trace) (state := state))
    (salt : Vector U δ) :
    Option (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := Id.run do
  -- `m_k + 1 = |inputState^(k)|` — number of permutation calls reconstructed for this sequence.
  let m_plus_1 := seq.inputState.length
  -- Accumulator `(α̂_1^(k), …, α̂_{i-1}^(k))` built across the loop iterations.
  -- Each entry `⟨msgIdx, v⟩` carries the encoded message `α̂_{msgIdx} ∈ Σ^{ℓ_P(msgIdx)}`.
  let mut encodedAcc : List
      (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx)) := []
  -- Step 4(a): For every i ∈ [k] = {1, …, k}.
  for i in challengeIdxList (pSpec := pSpec) do
    let L_P_before := sumMessageBlocksBefore (pSpec := pSpec) i
    let L_V_before := sumChallengeBlocksBefore (pSpec := pSpec) i
    -- Step 4(a).i — block pointer at round `i`:
    --   `L_ptr(i) := L_δ + Σ_{j<i} L_P(j) + Σ_{j<i} L_V(j)`  (CO25 Eq. 6/7).
    let L_ptr := Lδ (δ := δ) + L_P_before + L_V_before
    let msgIdx? := lastMessageBefore? (pSpec := pSpec) i
    -- `L_P(i) := ⌈ℓ_P(i) / r⌉` — permutation blocks needed for the i-th prover message.
    let lpCur := msgIdx?.elim 0 (fun msgIdx => pSpec.Lₚᵢ msgIdx)
    -- `ℓ_P(i) := messageSize msgIdx` — char-length of the i-th prover message in `Σ`.
    let msgSizeUnits := msgIdx?.elim 0 (fun msgIdx => messageSize msgIdx)
    -- Step 4(a).ii — guard `L_ptr(i) + L_P(i) ≤ m_k + 1`.
    -- (Otherwise the chain is too short to host this message window.)
    if L_ptr + lpCur > m_plus_1 then
      return none -- not enough rate blocks to host the i-th message ⇒ remove from S_BT
    -- Step 4(a).iii.A — assemble `α̂_i^(k) ∈ Σ^{ℓ_P(i)}` via `assembleEncodedMessage`
    -- (CO25 Eq. 11). Returns `none` if the rate-block window has fewer than `ℓ_P(i)` chars.
    match msgIdx? with
    | some msgIdx =>
      match seq.assembleEncodedMessage L_ptr lpCur msgIdx with
      | some v => encodedAcc := encodedAcc ++ [⟨msgIdx, v⟩]
      | none => return none -- not enough units in this block window ⇒ remove from S_BT
    | none => pure ()
    -- Step 4(a).iii.B — define the message-remainder rate suffix:
    --   `z_i^(k) := s_{R,in,L_ptr(i)+L_P(i)-1}[ℓ_P(i) mod r : r]  ∈ Σ^{r − (ℓ_P(i) mod r)}`.
    -- Char-based view: the `r − (ℓ_P(i) mod r)` chars of the last absorbed input-rate block
    -- that did NOT contribute to `α̂_i^(k)`.
    --
    -- Step 4(a).iii.C — check that `z_i^(k)` equals the corresponding suffix of the
    -- last output-rate block:
    --   `z_i^(k)  ?=  s_{R,out,L_ptr(i)+L_P(i)-1}[ℓ_P(i) mod r : r]`.
    -- (CO25 Step 4(a).iii.C remainder check; in chars, the unused tail of the in/out rate
    -- blocks must agree, since the permutation only XORs the first `ℓ_P(i) mod r` chars.)
    if 0 < lpCur then
      let msgEndIdx := L_ptr + lpCur - 1
      if h_bounds : msgEndIdx < m_plus_1 ∧ msgEndIdx < seq.outputState.length then
        let z_i := (seq.inputState.get ⟨msgEndIdx, h_bounds.1⟩).rateSegment.toList.drop
          (msgSizeUnits % SpongeSize.R)
        let outSuffix := (seq.outputState.get ⟨msgEndIdx, h_bounds.2⟩).rateSegment.toList.drop
          (msgSizeUnits % SpongeSize.R)
        if z_i ≠ outSuffix then
          return none -- B/C remainder check failed ⇒ remove from S_BT
      else
        return none
    -- Step 4(a).iii.D — exact fit: `L_ptr(i) + L_P(i) = m_k + 1`.
    -- Char-based view: the chain ends exactly after the i-th message is absorbed; no
    -- challenge squeeze follows. Store the output tuple
    --   `(i, 𝕩^(k), τ^(k), (α̂_1^(k), …, α̂_i^(k)))` in `Outs`.
    if L_ptr + lpCur == m_plus_1 then
      let acc := encodedAcc
      let msgs : pSpec.EncodedMessagesBefore U i.1.castSucc :=
        fun ⟨j, _⟩ =>
          match acc.findSome? (fun p => if h : p.1 = j then some (h ▸ p.2) else none) with
          | some v => v
          | none => Vector.replicate (messageSize j) (0 : U)
      return some { roundIdx := i, stmt := seq.stmt, salt := salt, encodedMessages := msgs }
    -- Step 4(a).iii.E — verifier squeeze window check via `checkSqueezeWindow`
    -- on the range `[L_ptr(i)+L_P(i), L_ptr(i)+L_P(i)+L_V(i))` (CO25 Step 4(a).iii.E).
    let lvCur := pSpec.Lᵥᵢ i
    if L_ptr + lpCur + lvCur < m_plus_1 then
      if not (seq.checkSqueezeWindow (L_ptr + lpCur) lvCur) then
        return none -- E squeeze window check failed ⇒ remove from S_BT
    else
      -- Step 4(a).iii.F — neither D (exact fit) nor E (squeeze fits) applies.
      -- Char-based view: `L_ptr(i) + L_P(i) < m_k + 1 < L_ptr(i) + L_P(i) + L_V(i) + 1`,
      -- so the chain is mid-squeeze with not enough blocks remaining ⇒ invalid.
      return none
  -- Exhausted all rounds without hitting Step D — sequence is invalid.
  return none

/-- CO25 §5.2 BackTrack with the line-1056 "look for at most one element" optimization.

Performs a single backwards linear scan from `state` along `tr_∇.p`:
- `predecessorCandidates` empty → terminate scan at the current state (chain start).
- `predecessorCandidates` singleton → continue.
- `predecessorCandidates` two or more → scan-time fork → return `err`.

After the scan, `hashAnchorCandidates` is classified the same way over `tr_∇.h`. Finally the
existing `constructCandidateSalt` + `extractCandidate` extractors are run; their `none` becomes
`noResult`. Scan-time forks are a strict over-approximation of CO25 `E_fork,p ∪ E_fork,h,p ⊆
E_fork`, so the soundness bound of Theorem 5.19 is preserved. -/
private noncomputable def linearBackTrack
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (state : CanonicalSpongeState U)
    (depthBound : Nat := trace.length + 1) :
    ExperimentOutput (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := by
  exact
    match linearScanBackwards trace trΔ h_trΔ depthBound state state [state.capacitySegment] (emptyPartialSequence trace state) with
    | .forkErr => ExperimentOutput.err
    | .noResult => ExperimentOutput.noResult
    | .done seq =>
        match seq.constructCandidateSalt (δ := δ) with
        | none => ExperimentOutput.noResult
        | some salt =>
          match seq.extractCandidate (pSpec := pSpec) (δ := δ) (StmtIn := StmtIn) (U := U)
              (state := state) (trace := trace) (salt := salt) with
          | none => ExperimentOutput.noResult
          | some out => ExperimentOutput.some out

open Classical in
/-- The backtracking procedure in Section 5.2, which takes in:
- the query-answer trace for the oracle `(h, p, p⁻¹)`
- a state (vector of `N` units)

And returns one of the following:
- `ExperimentOutput.noResult` — paper-`none` (no elements found in Outs)
- `ExperimentOutput.err` — paper-`err` (multiple elements in Outs, ambiguous)
- `ExperimentOutput.some out` — paper-success (unique tuple `(i, 𝕩, τ, (α̂_1, …, α̂_i))` in Outs)

Implementation: delegates to `linearBackTrack` (CO25 §5.2 line 1056 optimization). The legacy
paper-spec `BacktrackSequenceFamily.compute` is retained for downstream proofs (BadEvents,
AbortAnalysis) which quantify over `S_BT.seqFamily`; the executable surface here uses the
linear scan, which is a strict over-approximation under the bad-event analysis. -/
def backTrack
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (state : CanonicalSpongeState U)
    (depthBound : Nat := trace.length + 1) :
    ExperimentOutput (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  linearBackTrack (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound

end BacktrackProcedure

end DuplexSpongeFS.Backtrack
