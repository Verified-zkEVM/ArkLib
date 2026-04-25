/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceDataStructures

/-!
# Lookahead sequence family and procedure

This file contains the lookahead sequence family and procedure for the analysis of duplex sponge
Fiat-Shamir, following Section 5.3 in the paper.

## Paper-faithful black-box `tr_∇.p` access

Following CO25 §5.3, `LookAhead` consults the simulator's permutation table `tr_∇.p` exclusively
through the operational interface `TraceTableOps.inlu`. Concretely:

* `successorCandidates trΔp s` collapses to `tr_∇.p.inlu(s)` plus the no-loop guard
  `cap(s) ≠ cap(s')`. When `inlu = ⟂` (zero **or** multiple matches), the procedure terminates
  the chain — matching the paper's Algorithm 2 spec.
* `LookaheadSequence trΔp state` carries an `inlu`-membership invariant, so callers reason about
  the abstract `Multiset (K × V)` model rather than the raw `forwardPermutationOracle` query log.

By parameterizing every step over `[LawfulTraceTable T_P ...]`, the executable procedure and the
soundness lemmas built atop `LookaheadSequence` are entirely independent of the concrete trace
representation; swapping the list-backed default for an `RBMap`-backed implementation requires no
proof changes.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

open Section52

variable {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]
  [HasChallengeSize pSpec]

noncomputable section

/-- A look-ahead sequence (Equation 14) over a black-box permutation table `tr_∇.p` and an
  initial state, consists of:
- A list of `(s_in, s_out)` query-answer pairs,

subject to the following conditions:
- The list is nonempty
- The first input state is the given initial state
- Every pair appears as a unique forward lookup in `tr_∇.p`, i.e. `inlu trΔp s_in = some s_out`
- Consecutive pairs are linked by output/input equality
- No-loop: `cap(s_in) ≠ cap(s_out)` at every step
-/
structure LookaheadSequence
    {T_P : Type}
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔp : T_P)
    (state : CanonicalSpongeState U) where
  /-- The list of query-answer pairs `(s_in, s_out)` forming this look-ahead chain. -/
  pairs : List (CanonicalSpongeState U × CanonicalSpongeState U)
  /-- A look-ahead sequence is nonempty in the `.found` branch. -/
  nonempty : pairs ≠ []
  /-- The first input state in the chain is the given initial state. -/
  first_inputState_eq_state : pairs.head?.map Prod.fst = some state
  /-- Every query-answer pair in the chain is a unique forward lookup in `tr_∇.p`. -/
  inputOutput_via_inlu : ∀ pair ∈ pairs,
    TraceTableOps.inlu (V := CanonicalSpongeState U) trΔp pair.1 = some pair.2
  /-- Consecutive pairs are linked by output/input equality. -/
  outputState_eq_next_inputState : List.IsChain (fun a b => a.2 = b.1) pairs
  /-- No loop across query and answer capacity segments at each step. -/
  capacitySegment_inputState_ne_outputState : ∀ pair ∈ pairs,
    pair.1.capacitySegment ≠ pair.2.capacitySegment

variable {T_P : Type}
  [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]

def LookaheadSequence.inputState
    {trΔp : T_P}
    {state : CanonicalSpongeState U} (seq : LookaheadSequence trΔp state) :
    List (CanonicalSpongeState U) :=
  seq.pairs.map Prod.fst

def LookaheadSequence.outputState
    {trΔp : T_P}
    {state : CanonicalSpongeState U} (seq : LookaheadSequence trΔp state) :
    List (CanonicalSpongeState U) :=
  seq.pairs.map Prod.snd

lemma LookaheadSequence.inputState_length_eq_outputState_length
    {trΔp : T_P}
    {state : CanonicalSpongeState U} (seq : LookaheadSequence trΔp state) :
    seq.inputState.length = seq.outputState.length := by
  simp [LookaheadSequence.inputState, LookaheadSequence.outputState]

/-- A family of look-ahead sequences (Equation 14), parametrized by a black-box permutation
  table `tr_∇.p`, an initial state, and a challenge round index `i`, is defined as a finite set
  of look-ahead sequences such that:
- no two sequences are strict subsets of each other
- the length of any sequence is at most `Lᵥ(i)` (number of permutation calls for round `i`) -/
structure LookaheadSequenceFamily
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) where
  /-- The family of look-ahead sequences, defined as a finite set -/
  seqFamily : Finset (LookaheadSequence trΔp state)
  /-- Maximality condition on distinct elements: no strict containment between two sequences,
  defined in terms of
    - the input states are not a strict subset of each other, or
    - the output states are not a strict subset of each other -/
  maximality : ∀ s ∈ seqFamily, ∀ s' ∈ seqFamily,
    s ≠ s' →
      ¬ (s.inputState ⊆ s'.inputState) ∨ ¬ (s'.outputState ⊆ s.outputState)
  /-- The length of any sequence is at most `Lᵥ(i)` -/
  length_le_numPermQueriesChallenge : ∀ s ∈ seqFamily, s.inputState.length ≤ pSpec.Lᵥᵢ i

/-- Successor candidates from `tr_∇.p` (paper §5.3 Algorithm 2 line "next ← inlu(p, current)").
Returns a singleton `[next]` when the unique forward lookup succeeds and `cap` does not loop;
otherwise `[]` (i.e. paper-`⟂`/skip). Multiple matches collapse to `[]` via `inlu`'s uniqueness
law — the paper-`err` case is detected only at the maximal-family level. -/
private def successorCandidates
    (trΔp : T_P) (current : CanonicalSpongeState U) :
    List (CanonicalSpongeState U) :=
  match TraceTableOps.inlu (V := CanonicalSpongeState U) trΔp current with
  | none => []
  | some next =>
    if current.capacitySegment = next.capacitySegment then []
    else [next]

private inductive BuildLookaheadResult (U : Type) [SpongeUnit U] [SpongeSize] where
  | err
  | none
  | found (outputState : List (CanonicalSpongeState U))

private def buildLookaheadOutputStates
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (maxSteps : Nat) :
    BuildLookaheadResult U :=
  let rec go (fuel : Nat) (current : CanonicalSpongeState U)
      (outputRev : List (CanonicalSpongeState U)) :
      BuildLookaheadResult U :=
    match fuel with
    | 0 =>
      if outputRev = [] then .none else .found outputRev.reverse
    | fuel + 1 =>
      match successorCandidates (T_P := T_P) (U := U) trΔp current with
      | [] =>
        if outputRev = [] then .none else .found outputRev.reverse
      | [next] => go fuel next (next :: outputRev)
      | _ :: _ :: _ => .err
  go maxSteps state []

private lemma mem_successorCandidates_iff
    (trΔp : T_P) (current next : CanonicalSpongeState U) :
    next ∈ successorCandidates (T_P := T_P) (U := U) trΔp current ↔
      TraceTableOps.inlu (V := CanonicalSpongeState U) trΔp current = some next ∧
        current.capacitySegment ≠ next.capacitySegment := by
  unfold successorCandidates
  cases hLookup :
      TraceTableOps.inlu (V := CanonicalSpongeState U) trΔp current with
  | none =>
      constructor
      · intro hMem
        exact (List.not_mem_nil hMem).elim
      · rintro ⟨hSome, _⟩
        cases hSome
  | some v =>
      by_cases hCap : current.capacitySegment = v.capacitySegment
      · simp only [hCap, ↓reduceIte, List.not_mem_nil, false_iff, not_and, not_not]
        intro hSome
        have hvn : v = next := Option.some.inj hSome
        subst hvn
        rfl
      · simp only [hCap, ↓reduceIte, List.mem_singleton]
        constructor
        · intro hMem
          subst hMem
          exact ⟨rfl, hCap⟩
        · rintro ⟨hSome, _⟩
          exact (Option.some.inj hSome).symm

private def singletonLookaheadSequence
    (trΔp : T_P)
    (state next : CanonicalSpongeState U)
    (hInlu : TraceTableOps.inlu (V := CanonicalSpongeState U) trΔp state = some next)
    (hNoLoop : state.capacitySegment ≠ next.capacitySegment) :
    LookaheadSequence trΔp state :=
  { pairs := [(state, next)]
    nonempty := by simp
    first_inputState_eq_state := by simp
    inputOutput_via_inlu := by
      intro pair hPair
      have hPair' : pair = (state, next) := List.mem_singleton.mp hPair
      subst hPair'
      exact hInlu
    outputState_eq_next_inputState := by simp
    capacitySegment_inputState_ne_outputState := by
      intro pair hPair
      have hPair' : pair = (state, next) := List.mem_singleton.mp hPair
      subst hPair'
      exact hNoLoop }

private def prependLookaheadSequence
    (trΔp : T_P)
    (state next : CanonicalSpongeState U)
    (hInlu : TraceTableOps.inlu (V := CanonicalSpongeState U) trΔp state = some next)
    (hNoLoop : state.capacitySegment ≠ next.capacitySegment)
    (tail : LookaheadSequence trΔp next) :
    LookaheadSequence trΔp state :=
  { pairs := (state, next) :: tail.pairs
    nonempty := by simp
    first_inputState_eq_state := by simp
    inputOutput_via_inlu := by
      intro pair hPair
      rcases List.mem_cons.mp hPair with hEq | hRest
      · subst hEq
        exact hInlu
      · exact tail.inputOutput_via_inlu pair hRest
    outputState_eq_next_inputState := by
      cases hPairs : tail.pairs with
      | nil =>
          exact (tail.nonempty hPairs).elim
      | cons head rest =>
          have hHead : head.1 = next := by
            have hHd := tail.first_inputState_eq_state
            rw [hPairs] at hHd
            simp at hHd
            exact hHd
          have hTailChain : List.IsChain (fun a b => a.2 = b.1) (head :: rest) := by
            have hCh := tail.outputState_eq_next_inputState
            rw [hPairs] at hCh
            exact hCh
          exact List.IsChain.cons_cons hHead.symm hTailChain
    capacitySegment_inputState_ne_outputState := by
      intro pair hPair
      rcases List.mem_cons.mp hPair with hEq | hRest
      · subst hEq
        exact hNoLoop
      · exact tail.capacitySegment_inputState_ne_outputState pair hRest }

private structure LookaheadCandidate
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (maxSteps : Nat) where
  seq : LookaheadSequence trΔp state
  length_le : seq.pairs.length ≤ maxSteps

private def buildLookaheadCandidates
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (maxSteps : Nat) :
    List (LookaheadCandidate (T_P := T_P) (U := U) trΔp state maxSteps) := by
  classical
  let rec go (fuel : Nat) (current : CanonicalSpongeState U) :
      List (LookaheadCandidate (T_P := T_P) (U := U) trΔp current fuel) :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      let succs := successorCandidates (T_P := T_P) (U := U) trΔp current
      let buildFromNext (next : CanonicalSpongeState U) :
          List (LookaheadCandidate (T_P := T_P) (U := U) trΔp current (fuel + 1)) :=
        if hInlu :
            TraceTableOps.inlu (V := CanonicalSpongeState U) trΔp current = some next then
          if hNoLoop : current.capacitySegment ≠ next.capacitySegment then
            let singletonSeq :=
              singletonLookaheadSequence (T_P := T_P) (U := U)
                trΔp current next hInlu hNoLoop
            let singletonCandidate :
                LookaheadCandidate (T_P := T_P) (U := U) trΔp current (fuel + 1) :=
              { seq := singletonSeq
                length_le := by
                  have hSingletonLen : singletonSeq.pairs.length = 1 := by
                    simp [singletonSeq, singletonLookaheadSequence]
                  have hOneLe : 1 ≤ fuel + 1 := Nat.succ_le_succ (Nat.zero_le fuel)
                  exact hSingletonLen ▸ hOneLe }
            let tailCandidates := go fuel next
            let extendedCandidates :=
              tailCandidates.map fun
                  (tail : LookaheadCandidate (T_P := T_P) (U := U) trΔp next fuel) =>
                let seq :=
                  prependLookaheadSequence (T_P := T_P) (U := U)
                    trΔp current next hInlu hNoLoop tail.seq
                have hLen : seq.pairs.length ≤ fuel + 1 := by
                  have hSeqLen : seq.pairs.length = tail.seq.pairs.length + 1 := by
                    unfold seq
                    simp [prependLookaheadSequence]
                  have hTailSucc : tail.seq.pairs.length + 1 ≤ fuel + 1 :=
                    Nat.succ_le_succ tail.length_le
                  exact hSeqLen ▸ hTailSucc
                { seq := seq
                  length_le := hLen }
            singletonCandidate :: extendedCandidates
          else
            []
        else
          []
      List.flatten (succs.map buildFromNext)
  exact go maxSteps state

private def computeAllLookaheadSequences
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (maxSteps : Nat) :
    Finset (LookaheadSequence trΔp state) := by
  classical
  exact
    ((buildLookaheadCandidates (T_P := T_P) (U := U) trΔp state maxSteps).map
      (fun cand => cand.seq)).toFinset

private lemma inputState_length_eq_pairs_length
    {trΔp : T_P}
    {state : CanonicalSpongeState U} (seq : LookaheadSequence trΔp state) :
    seq.inputState.length = seq.pairs.length := by
  simp [LookaheadSequence.inputState]

private lemma allLookaheadSequences_length_bound
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (maxSteps : Nat)
    (s : LookaheadSequence trΔp state)
    (hs : s ∈ computeAllLookaheadSequences (T_P := T_P) (U := U) trΔp state maxSteps) :
    s.inputState.length ≤ maxSteps := by
  classical
  unfold computeAllLookaheadSequences at hs
  have hsList :
      s ∈ (buildLookaheadCandidates (T_P := T_P) (U := U) trΔp state maxSteps).map
        (fun cand => cand.seq) := List.mem_toFinset.mp hs
  rcases List.mem_map.mp hsList with ⟨cand, hCandMem, hCandEq⟩
  have hCandInputLen : cand.seq.inputState.length = cand.seq.pairs.length := by
    exact inputState_length_eq_pairs_length (T_P := T_P) (U := U) cand.seq
  have hCandLe : cand.seq.inputState.length ≤ maxSteps := hCandInputLen ▸ cand.length_le
  have hSeqLen : s.inputState.length = cand.seq.inputState.length := by
    rw [← hCandEq]
  exact hSeqLen.trans_le hCandLe

/-- Procedure to compute the lookahead sequence family (Equation 14) over a black-box `tr_∇.p`. -/
def computeLookaheadSequenceFamily
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) :
    LookaheadSequenceFamily trΔp state i :=
  by
    classical
    let maxSteps := pSpec.Lᵥᵢ i
    let allSeqs := computeAllLookaheadSequences (T_P := T_P) (U := U) trΔp state maxSteps
    let isMaximal : LookaheadSequence trΔp state → Prop := fun s =>
      ∀ s' ∈ allSeqs, s ≠ s' →
        ¬ (s.inputState ⊆ s'.inputState) ∨ ¬ (s'.outputState ⊆ s.outputState)
    let maxFamily := allSeqs.filter isMaximal
    exact
      { seqFamily := maxFamily
        maximality := by
          intro s hs s' hs' hneq
          have hsMax : isMaximal s := (Finset.mem_filter.mp hs).2
          have hsAll : s' ∈ allSeqs := (Finset.mem_filter.mp hs').1
          exact hsMax s' hsAll hneq
        length_le_numPermQueriesChallenge := by
          intro s hs
          have hsAll : s ∈ allSeqs := (Finset.mem_filter.mp hs).1
          exact allLookaheadSequences_length_bound (T_P := T_P) (U := U)
            trΔp state maxSteps s hsAll }

private lemma challengeSize_le_Lvi_mul_R (i : pSpec.ChallengeIdx) :
    challengeSize i ≤ pSpec.Lᵥᵢ i * SpongeSize.R := by
  have hceil : ((challengeSize i : ℚ) / SpongeSize.R) ≤ (pSpec.Lᵥᵢ i : ℚ) := by
    simpa [ProtocolSpec.numPermQueriesChallenge] using
      (Nat.le_ceil ((challengeSize i : ℚ) / SpongeSize.R))
  have hRnonneg : (0 : ℚ) ≤ SpongeSize.R := by
    exact_mod_cast (Nat.zero_le SpongeSize.R)
  have hmul :
      ((challengeSize i : ℚ) / SpongeSize.R) * SpongeSize.R
        ≤ (pSpec.Lᵥᵢ i : ℚ) * SpongeSize.R :=
    mul_le_mul_of_nonneg_right hceil hRnonneg
  have hRne : (SpongeSize.R : ℚ) ≠ 0 := by
    exact_mod_cast (show SpongeSize.R ≠ 0 from NeZero.ne SpongeSize.R)
  have hleft :
      ((challengeSize i : ℚ) / SpongeSize.R) * SpongeSize.R = (challengeSize i : ℚ) := by
    field_simp [hRne]
  have hq : (challengeSize i : ℚ) ≤ (pSpec.Lᵥᵢ i : ℚ) * SpongeSize.R := by
    simpa [hleft] using hmul
  exact_mod_cast hq

private def sampleArrayExact :
    (m : Nat) → OracleComp (Unit →ₒ U) {xs : Array U // xs.size = m}
  | 0 => pure ⟨#[], rfl⟩
  | m + 1 => do
      let u ← liftM (query (spec := (Unit →ₒ U)) ())
      let ⟨xs, hxs⟩ ← sampleArrayExact m
      pure ⟨xs.push u, by simp [hxs]⟩

private def sampleRateVector : OracleComp (Unit →ₒ U) (Vector U SpongeSize.R) := do
  let ⟨xs, hxs⟩ ← sampleArrayExact (U := U) SpongeSize.R
  pure ⟨xs, hxs⟩

private def sampleRateVectorsExact :
    (m : Nat) → OracleComp (Unit →ₒ U) {blocks : List (Vector U SpongeSize.R) // blocks.length = m}
  | 0 => pure ⟨[], rfl⟩
  | m + 1 => do
      let head ← sampleRateVector (U := U)
      let ⟨tail, htail⟩ ← sampleRateVectorsExact m
      pure ⟨head :: tail, by simp [htail]⟩

private lemma length_flatten_vector_toList (blocks : List (Vector U SpongeSize.R)) :
    (List.flatten (blocks.map Vector.toList)).length = blocks.length * SpongeSize.R := by
  induction blocks with
  | nil => simp
  | cons x xs ih =>
      simp [ih, Nat.right_distrib, Nat.add_comm]

private def takeVector (n : Nat) (xs : List U) (h : n ≤ xs.length) : Vector U n :=
  Vector.ofFn (fun j => xs[j.1]'(Nat.lt_of_lt_of_le j.2 h))

/-- The lookahead procedure in Section 5.3, polymorphic over the black-box `tr_∇.p` table.

Takes:
- `trΔp` — the simulator's permutation table `tr_∇.p` (any `LawfulTraceTable`),
- `state` — initial permutation state,
- `i` — challenge round index.

Performs a probabilistic computation (uniform unit sampling for missing blocks) returning:
- `none` (paper-`⟂` / skip),
- `err` (paper failure — multiple maximal sequences),
- an encoded verifier challenge (`Vector U (challengeSize i)`).
-/
def lookAhead
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) :
    OptionT (OracleComp (Unit →ₒ U)) (Option (Vector U (challengeSize i))) := do
  let maxSteps := pSpec.Lᵥᵢ i
  let family :=
    computeLookaheadSequenceFamily (T_P := T_P) (U := U) (pSpec := pSpec) trΔp state i
  match hFamilyList : family.seqFamily.toList with
  | [] =>
    -- `none` in the paper.
    return Option.none
  | [seq] =>
    -- Single maximal sequence.
    let outputState := seq.outputState
    let knownBlocks : List (Vector U SpongeSize.R) :=
      outputState.map CanonicalSpongeState.rateSegment
    have hSeqMemList : seq ∈ family.seqFamily.toList := by
      rw [hFamilyList]
      simp
    have hSeqMem : seq ∈ family.seqFamily := Finset.mem_toList.mp hSeqMemList
    have hInputLenLe : seq.inputState.length ≤ maxSteps :=
      family.length_le_numPermQueriesChallenge seq hSeqMem
    have hKnownLenEqInputLen : knownBlocks.length = seq.inputState.length := by
      have hKnownLenEqOutputLen : knownBlocks.length = seq.outputState.length := by
        simp [knownBlocks, outputState]
      have hOutputLenEqInputLen : seq.outputState.length = seq.inputState.length := by
        exact (LookaheadSequence.inputState_length_eq_outputState_length
          (T_P := T_P) (U := U) seq).symm
      exact hKnownLenEqOutputLen.trans hOutputLenEqInputLen
    have hKnownLenLeMax : knownBlocks.length ≤ maxSteps := hKnownLenEqInputLen ▸ hInputLenLe
    let missingBlocks := maxSteps - knownBlocks.length
    let ⟨randomBlocks, hRandomLen⟩ ← liftM (sampleRateVectorsExact (U := U) missingBlocks)
    let allBlocks := knownBlocks ++ randomBlocks
    let units : List U := List.flatten (allBlocks.map Vector.toList)
    have hMax_le_allBlocks : maxSteps ≤ allBlocks.length := by
      simp [allBlocks, missingBlocks, hRandomLen, Nat.add_sub_of_le hKnownLenLeMax]
    have hMaxR_le_units : maxSteps * SpongeSize.R ≤ units.length := by
      have hmul : maxSteps * SpongeSize.R ≤ allBlocks.length * SpongeSize.R :=
        Nat.mul_le_mul_right SpongeSize.R hMax_le_allBlocks
      have hUnitsLen : units.length = allBlocks.length * SpongeSize.R := by
        simpa [units] using (length_flatten_vector_toList (U := U) allBlocks)
      simpa [hUnitsLen] using hmul
    have hChal_le_units : challengeSize i ≤ units.length := by
      have hChal_le_maxR : challengeSize i ≤ maxSteps * SpongeSize.R := by
        simpa [maxSteps] using challengeSize_le_Lvi_mul_R (pSpec := pSpec) i
      exact le_trans hChal_le_maxR hMaxR_le_units
    return Option.some (takeVector (U := U) (challengeSize i) units hChal_le_units)
  | _ :: _ :: _ =>
    -- `err` in the paper.
    failure

end

end DuplexSpongeFS
