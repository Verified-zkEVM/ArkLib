/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs

/-!
# Lookahead sequence family and procedure

This file contains the lookahead sequence family and procedure for the analysis of duplex sponge
Fiat-Shamir, following Section 5.3 in the paper.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

variable {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasChallengeSize pSpec]

noncomputable section

/-- A look-ahead sequence (Equation 14) of a given trace of forward permutation queries, and an
  initial state, consists of:
- A list of input states
- A list of output states

subject to the following conditions:
- The two list of states have the same length
- The first input state is the given initial state
  ...

TODO: refactor this to cut down on data (can just omit output states?) -/
structure LookaheadSequence (trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U)))
    (state : CanonicalSpongeState U) where
  /-- The list of query-answer pairs `(s_in, s_out)` forming this look-ahead chain. -/
  pairs : List (CanonicalSpongeState U × CanonicalSpongeState U)
  /-- A look-ahead sequence is nonempty in the `.found` branch. -/
  nonempty : pairs ≠ []
  /-- The first input state in the chain is the given initial state. -/
  first_inputState_eq_state : pairs.head?.map Prod.fst = some state
  /-- Every query-answer pair in the chain appears in the trace. -/
  inputOutput_in_trace : ∀ pair ∈ pairs, ⟨pair.1, pair.2⟩ ∈ trace
  /-- Consecutive pairs are linked by output/input equality. -/
  outputState_eq_next_inputState : List.IsChain (fun a b => a.2 = b.1) pairs
  /-- No loop across query and answer capacity segments at each step. -/
  capacitySegment_inputState_ne_outputState : ∀ pair ∈ pairs,
    pair.1.capacitySegment ≠ pair.2.capacitySegment

def LookaheadSequence.inputState
    {trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U))}
    {state : CanonicalSpongeState U} (seq : LookaheadSequence trace state) :
    List (CanonicalSpongeState U) :=
  seq.pairs.map Prod.fst

def LookaheadSequence.outputState
    {trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U))}
    {state : CanonicalSpongeState U} (seq : LookaheadSequence trace state) :
    List (CanonicalSpongeState U) :=
  seq.pairs.map Prod.snd

lemma LookaheadSequence.inputState_length_eq_outputState_length
    {trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U))}
    {state : CanonicalSpongeState U} (seq : LookaheadSequence trace state) :
    seq.inputState.length = seq.outputState.length := by
  simp [LookaheadSequence.inputState, LookaheadSequence.outputState]

/-- A family of look-ahead sequences (Equation 14), parametrized by a trace of forward permutation
  queries, an initial state, and a challenge round index `i`, is defined as a finite set of
  look-ahead sequences such that:
- no two sequences are strict subsets of each other
- the length of any sequence is at most `Lᵥ(i)` (number of permutation calls for round `i`) -/
structure LookaheadSequenceFamily
    (trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U)))
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) where
  /-- The family of look-ahead sequences, defined as a finite set -/
  seqFamily : Finset (LookaheadSequence trace state)
  /-- Maximality condition on distinct elements: no strict containment between two sequences,
  defined in terms of
    - the input states are not a strict subset of each other, or
    - the output states are not a strict subset of each other -/
  maximality : ∀ s ∈ seqFamily, ∀ s' ∈ seqFamily,
    s ≠ s' →
      ¬ (s.inputState ⊆ s'.inputState) ∨ ¬ (s'.outputState ⊆ s.outputState)
  /-- The length of any sequence is at most `Lᵥ(i)` -/
  length_le_numPermQueriesChallenge : ∀ s ∈ seqFamily, s.inputState.length ≤ pSpec.Lᵥᵢ i

private def successorCandidates
    (trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U)))
    (current : CanonicalSpongeState U) : List (CanonicalSpongeState U) :=
  by
    classical
    exact trace.filterMap fun entry =>
      match entry with
      | ⟨stateIn, stateOut⟩ =>
        if hIn : stateIn = current then
          if hLoop : stateIn.capacitySegment = stateOut.capacitySegment then
            none
          else
            some stateOut
        else
          none

private inductive BuildLookaheadResult (U : Type) [SpongeUnit U] [SpongeSize] where
  | err
  | none
  | found (outputState : List (CanonicalSpongeState U))

private def buildLookaheadOutputStates
    (trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U)))
    (state : CanonicalSpongeState U) (maxSteps : Nat) :
    BuildLookaheadResult U :=
  let rec go (fuel : Nat) (current : CanonicalSpongeState U)
      (outputRev : List (CanonicalSpongeState U)) :
      BuildLookaheadResult U :=
    match fuel with
    | 0 =>
      if outputRev = [] then .none else .found outputRev.reverse
    | fuel + 1 =>
      let succs := successorCandidates (U := U) trace current
      match succs with
      | [] =>
        if outputRev = [] then .none else .found outputRev.reverse
      | [next] => go fuel next (next :: outputRev)
      | _ :: _ :: _ => .err
  go maxSteps state []

private lemma mem_successorCandidates_iff
    (trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U)))
    (current next : CanonicalSpongeState U) :
    next ∈ successorCandidates (U := U) trace current ↔
      ⟨current, next⟩ ∈ trace ∧ current.capacitySegment ≠ next.capacitySegment := by
  classical
  unfold successorCandidates
  simp [List.mem_filterMap, and_comm]

private def singletonLookaheadSequence
    (trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U)))
    (state next : CanonicalSpongeState U)
    (hInTrace : ⟨state, next⟩ ∈ trace)
    (hNoLoop : state.capacitySegment ≠ next.capacitySegment) :
    LookaheadSequence trace state :=
  { pairs := [(state, next)]
    nonempty := by simp
    first_inputState_eq_state := by simp
    inputOutput_in_trace := by
      intro pair hPair
      have hPair' : pair = (state, next) := by simpa using hPair
      subst hPair'
      simpa using hInTrace
    outputState_eq_next_inputState := by simp
    capacitySegment_inputState_ne_outputState := by
      intro pair hPair
      have hPair' : pair = (state, next) := by simpa using hPair
      subst hPair'
      simpa using hNoLoop }

private def prependLookaheadSequence
    (trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U)))
    (state next : CanonicalSpongeState U)
    (hInTrace : ⟨state, next⟩ ∈ trace)
    (hNoLoop : state.capacitySegment ≠ next.capacitySegment)
    (tail : LookaheadSequence trace next) :
    LookaheadSequence trace state :=
  { pairs := (state, next) :: tail.pairs
    nonempty := by simp
    first_inputState_eq_state := by simp
    inputOutput_in_trace := by
      intro pair hPair
      have hMem : pair = (state, next) ∨ pair ∈ tail.pairs := by simpa using hPair
      cases hMem with
      | inl hEq =>
          subst hEq
          simpa using hInTrace
      | inr hTail =>
          exact tail.inputOutput_in_trace pair hTail
    outputState_eq_next_inputState := by
      cases hPairs : tail.pairs with
      | nil =>
          cases (tail.nonempty hPairs)
      | cons head rest =>
          have hHead : head.1 = next := by
            simpa [hPairs] using tail.first_inputState_eq_state
          have hTailChain : List.IsChain (fun a b => a.2 = b.1) (head :: rest) := by
            simpa [hPairs] using tail.outputState_eq_next_inputState
          simpa [hPairs, List.IsChain, hHead] using hTailChain
    capacitySegment_inputState_ne_outputState := by
      intro pair hPair
      have hMem : pair = (state, next) ∨ pair ∈ tail.pairs := by simpa using hPair
      cases hMem with
      | inl hEq =>
          subst hEq
          simpa using hNoLoop
      | inr hTail =>
          exact tail.capacitySegment_inputState_ne_outputState pair hTail }

private structure LookaheadCandidate
    (trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U)))
    (state : CanonicalSpongeState U) (maxSteps : Nat) where
  seq : LookaheadSequence trace state
  length_le : seq.pairs.length ≤ maxSteps

private def buildLookaheadCandidates
    (trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U)))
    (state : CanonicalSpongeState U) (maxSteps : Nat) :
    List (LookaheadCandidate (U := U) trace state maxSteps) := by
  classical
  let rec go (fuel : Nat) (current : CanonicalSpongeState U) :
      List (LookaheadCandidate (U := U) trace current fuel) :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      let succs := successorCandidates (U := U) trace current
      let buildFromNext (next : CanonicalSpongeState U) :
          List (LookaheadCandidate (U := U) trace current (fuel + 1)) :=
        if hInTrace : ⟨current, next⟩ ∈ trace then
          if hNoLoop : current.capacitySegment ≠ next.capacitySegment then
            let singletonSeq :=
              singletonLookaheadSequence (U := U) trace current next hInTrace hNoLoop
            let singletonCandidate :
                LookaheadCandidate (U := U) trace current (fuel + 1) :=
              { seq := singletonSeq
                length_le := by
                  have hSingletonLen : singletonSeq.pairs.length = 1 := by
                    simp [singletonSeq, singletonLookaheadSequence]
                  have hOneLe : 1 ≤ fuel + 1 := Nat.succ_le_succ (Nat.zero_le fuel)
                  exact hSingletonLen ▸ hOneLe }
            let tailCandidates := go fuel next
            let extendedCandidates :=
              tailCandidates.map fun (tail : LookaheadCandidate (U := U) trace next fuel) =>
                let seq :=
                  prependLookaheadSequence (U := U) trace current next hInTrace hNoLoop tail.seq
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
    (trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U)))
    (state : CanonicalSpongeState U) (maxSteps : Nat) :
    Finset (LookaheadSequence trace state) := by
  classical
  exact
    ((buildLookaheadCandidates (U := U) trace state maxSteps).map
      (fun cand => cand.seq)).toFinset

private lemma inputState_length_eq_pairs_length
    {trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U))}
    {state : CanonicalSpongeState U} (seq : LookaheadSequence trace state) :
    seq.inputState.length = seq.pairs.length := by
  simp [LookaheadSequence.inputState]

private lemma allLookaheadSequences_length_bound
    (trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U)))
    (state : CanonicalSpongeState U) (maxSteps : Nat)
    (s : LookaheadSequence trace state)
    (hs : s ∈ computeAllLookaheadSequences (U := U) trace state maxSteps) :
    s.inputState.length ≤ maxSteps := by
  classical
  unfold computeAllLookaheadSequences at hs
  have hsList :
      s ∈ (buildLookaheadCandidates (U := U) trace state maxSteps).map
        (fun cand => cand.seq) := List.mem_toFinset.mp hs
  rcases List.mem_map.mp hsList with ⟨cand, hCandMem, hCandEq⟩
  have hCandInputLen : cand.seq.inputState.length = cand.seq.pairs.length := by
    exact inputState_length_eq_pairs_length (U := U) cand.seq
  have hCandLe : cand.seq.inputState.length ≤ maxSteps := hCandInputLen ▸ cand.length_le
  have hSeqLen : s.inputState.length = cand.seq.inputState.length := by
    rw [← hCandEq]
  exact hSeqLen.trans_le hCandLe

/-- Procedure to compute the lookahead sequence family (Equation 14)

TODO: nail down exactly what this is; can it fail? -/
def computeLookaheadSequenceFamily
    (trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U)))
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) :
    LookaheadSequenceFamily trace state i :=
  by
    classical
    let maxSteps := pSpec.Lᵥᵢ i
    let allSeqs := computeAllLookaheadSequences (U := U) trace state maxSteps
    let isMaximal : LookaheadSequence trace state → Prop := fun s =>
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
          exact allLookaheadSequences_length_bound (U := U) trace state maxSteps s hsAll }

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

/-- The lookahead procedure in Section 5.2, which takes in:
- A query-answer trace for the oracle `p`
- A permutation state (vector of `N` units)
- A round index `i` for a challenge round

Then performs a probabilistic computation (allowing to sample units uniformly at random) returning
one of the following:
- `none`
- `err`
- An encoded verifier's challenge (vector of `chalSize i` units)

TODO: figure out the best way to encode the two errors (currently we encode `err` as the failure of
OracleComp, and `none` as `Option.none` inside)
-/
def lookAhead (_fwdPermTrace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U)))
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) :
    OptionT (OracleComp (Unit →ₒ U)) (Option (Vector U (challengeSize i))) := do
  let maxSteps := pSpec.Lᵥᵢ i
  let family := computeLookaheadSequenceFamily (pSpec := pSpec) _fwdPermTrace state i
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
        exact (LookaheadSequence.inputState_length_eq_outputState_length (U := U) seq).symm
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
