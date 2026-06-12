/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceDataStructures

/-!
# Lookahead sequence family and procedure

This file contains the lookahead sequence family `S_LA(tr_∇.p, s, i)` and the procedure
`LookAhead(tr_∇.p, s, i)` from CO25 §5.3.

## Declaration order (top-to-bottom, matching CO25 §5.3 Algorithm 2)

1. **Paper structures** — `LookaheadSequence` (Eq. 13 chain), `LookaheadSequenceFamily`
   (the maximal family), and the abbrev `S_LA(tr_∇.p, s, i)`.
2. **§5.3 Step 1** — `LookAheadSequenceFamily.compute` parses `tr_∇.p` into the maximal family `S_LA(tr_∇.p, s, i)`.
   Internal helpers: `successorCandidates`, `singletonLookaheadSequence`,
   `prependLookaheadSequence`, `LookaheadCandidate`, `buildLookaheadCandidates`,
   `enumerateLookaheadCandidates`.
3. **§5.3 Step 2** — `lookAhead` dispatches on `|S_LA|`: `err` (multiple), `none` (empty),
   or a sampled `Vector U (challengeSize i)` (single).  Internal helpers: `sampleArrayExact`,
   `sampleRateVector`, `sampleRateVectorsExact`, `takeVector`, plus the size lemma
   `challengeSize_le_Lvi_mul_R`.

## Paper-faithful black-box `tr_∇.p` access

`LookAhead` enumerates the query-answer entries in the simulator's permutation table `tr_∇.p`.
This preserves the paper's branching behavior: zero successors means `none`, while multiple
maximal successor chains survive into `S_LA` and make Step 2 return `err`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.Lookahead

open DSTraceStorage

variable {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]
  [HasChallengeSize pSpec]

noncomputable section

/-! ## §5.3 paper structures — `LookaheadSequence`, `S_LA(tr_∇.p, s, i)` -/

/-- A look-ahead sequence (Equation 13) over a black-box permutation table `tr_∇.p` and an
  initial state, consists of:
- A list of `(s_in, s_out)` query-answer pairs,

subject to the following conditions:
- The list is nonempty
- The first input state is the given initial state
- Every pair appears in the query-answer entries of `tr_∇.p`
- Consecutive pairs are linked by output/input equality
- No-loop: `cap(s_in) ≠ cap(s_out)` at every step
-/
structure LookaheadSequence
    {T_P : Type}
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔp : T_P)
    (state : CanonicalSpongeState U) where
  /-- `S_LA^(k)` chain (LookAhead §5.3 Step 1, Eq. 13): `(s_{in,ι}, s_{out,ι})` pairs. -/
  pairs : List (CanonicalSpongeState U × CanonicalSpongeState U)
  /-- `ℓ ≥ 1` — non-empty chain (`.found` branch of LookAhead §5.3 Step 2.c). -/
  nonempty : pairs ≠ []
  /-- `s_{in,0} = state` — LookAhead §5.3 Step 1(b). -/
  first_inputState_eq_state : pairs.head?.map Prod.fst = some state
  /-- `(s_{in,ι}, s_{out,ι}) ∈ tr_∇.p` — LookAhead §5.3 Step 1(c) query-answer membership. -/
  inputOutput_mem_entries : ∀ pair ∈ pairs,
    pair ∈ TraceTableOps.entries (V := CanonicalSpongeState U) trΔp
  /-- `s_{out,ι-1} = s_{in,ι}` — LookAhead §5.3 Step 1(c) consecutive linkage. -/
  outputState_eq_next_inputState : List.IsChain (fun a b => a.2 = b.1) pairs
  /-- `cap(s_{in,ι}) ≠ cap(s_{out,ι})` — LookAhead §5.3 Step 1(d) no-loop guard. -/
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

/-- The flattened sequence of states: `[s_{in,0}, s_{out,0}, s_{in,1}, s_{out,1}, ...]`. -/
def LookaheadSequence.flattenStateSequence
    {trΔp : T_P}
    {state : CanonicalSpongeState U} (seq : LookaheadSequence trΔp state) :
    List (CanonicalSpongeState U) :=
  -- `state` is already included (`seq.pairs[0].1`)
  seq.pairs.foldr (fun p acc => p.1 :: p.2 :: acc) []

/-- A family of look-ahead sequences (Equation 13), parametrized by a black-box permutation
  table `tr_∇.p`, an initial state, and a challenge round index `i`, is defined as a finite set
  of look-ahead sequences such that:
- no two sequences are strict subsets of each other
- the length of any sequence is at most `Lᵥ(i)` (number of permutation calls for round `i`) -/
structure LookaheadSequenceFamily
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) where
  /-- `S_LA` — the finite family of look-ahead sequences (LookAhead §5.3 Step 1). -/
  seqFamily : Finset (LookaheadSequence trΔp state)
  /-- LookAhead §5.3 Step 1(e) maximality: no sequence strictly contains another.
  Subsequence is defined over the flattened sequence of states. -/
  maximality : ∀ s ∈ seqFamily, ∀ s' ∈ seqFamily,
    s ≠ s' →
      ¬ (s.flattenStateSequence.Sublist s'.flattenStateSequence)
  /-- `m_k ≤ L_V(i)` — LookAhead §5.3 Step 1(a) length bound. -/
  length_le_numPermQueriesChallenge : ∀ s ∈ seqFamily, s.inputState.length ≤ pSpec.Lᵥᵢ i

/-- CO25 §5.3 abbreviation: `S_LA(tr_∇.p, s, i)`, the maximal lookahead
sequence family produced by LookAhead Step 1.

Parallel to `S_BT(tr, s)` in `Backtrack.lean`. -/
abbrev S_LA
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) :=
  LookaheadSequenceFamily (pSpec := pSpec) trΔp state i

/-! ## §5.3 Step 1 — Parse `tr_∇.p` into the maximal family `S_LA(tr_∇.p, s, i)` (Eq. 13) -/

/-- Successor candidates from the query-answer entries of `tr_∇.p`.

Unlike `TraceTableOps.inlu`, this keeps all forward matches so multiple successor chains reach
`S_LA` and are reported as paper-`err` by Step 2. -/
private def successorCandidates
    (trΔp : T_P) (current : CanonicalSpongeState U) :
    List (CanonicalSpongeState U) := by
  classical
  exact (TraceTableOps.entries (V := CanonicalSpongeState U) trΔp).filterMap fun pair =>
    if pair.1 = current then
      some pair.2
    else none

private def singletonLookaheadSequence
    (trΔp : T_P)
    (state next : CanonicalSpongeState U)
    (hEntry : (state, next) ∈ TraceTableOps.entries (V := CanonicalSpongeState U) trΔp)
    (hNoLoop : state.capacitySegment ≠ next.capacitySegment) :
    LookaheadSequence trΔp state :=
  { pairs := [(state, next)]
    nonempty := by simp
    first_inputState_eq_state := by simp
    inputOutput_mem_entries := by
      intro pair hPair
      have hPair' : pair = (state, next) := List.mem_singleton.mp hPair
      subst hPair'
      exact hEntry
    outputState_eq_next_inputState := by simp
    capacitySegment_inputState_ne_outputState := by
      intro pair hPair
      have hPair' : pair = (state, next) := List.mem_singleton.mp hPair
      subst hPair'
      exact hNoLoop }

set_option linter.flexible false in
private def prependLookaheadSequence
    (trΔp : T_P)
    (state next : CanonicalSpongeState U)
    (hEntry : (state, next) ∈ TraceTableOps.entries (V := CanonicalSpongeState U) trΔp)
    (hNoLoop : state.capacitySegment ≠ next.capacitySegment)
    (tail : LookaheadSequence trΔp next) :
    LookaheadSequence trΔp state :=
  { pairs := (state, next) :: tail.pairs
    nonempty := by simp
    first_inputState_eq_state := by simp
    inputOutput_mem_entries := by
      intro pair hPair
      rcases List.mem_cons.mp hPair with hEq | hRest
      · subst hEq
        exact hEntry
      · exact tail.inputOutput_mem_entries pair hRest
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

private lemma inputState_length_eq_pairs_length
    {trΔp : T_P}
    {state : CanonicalSpongeState U} (seq : LookaheadSequence trΔp state) :
    seq.inputState.length = seq.pairs.length := by
  simp [LookaheadSequence.inputState]

/-- CO25 §5.3 Algorithm 2 **Step 1** — parse `tr_∇.p` into the maximal family
`S_LA(tr_∇.p, s, i)` (Eq. 13). -/
def LookAheadSequenceFamily.compute
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) :
    S_LA (pSpec := pSpec) trΔp state i := sorry

/-! ## §5.3 Step 2 — Final output dispatch on `|S_LA|`: `err` / `none` / sampled vector -/

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
      let u ← query (spec := (Unit →ₒ U)) ()
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

omit [SpongeUnit U] [DecidableEq U] in
private lemma length_flatten_vector_toList (blocks : List (Vector U SpongeSize.R)) :
    (List.flatten (blocks.map Vector.toList)).length = blocks.length * SpongeSize.R := by
  induction blocks with
  | nil => simp
  | cons x xs ih =>
      simp [ih, Nat.right_distrib, Nat.add_comm]

private def takeVector (n : Nat) (xs : List U) (h : n ≤ xs.length) : Vector U n :=
  Vector.ofFn (fun j => xs[j.1]'(Nat.lt_of_lt_of_le j.2 h))

/-- CO25 §5.3 Step 2(c) — given a single maximal lookahead sequence of length `m₁ ≤ L_V(i)`,
sample the `L_V(i) - m₁` missing rate blocks uniformly from `Σ^r`, concatenate with the known
output-rate blocks, and return the first `ℓ_V(i)` units as `ρ̂_i ∈ Σ^{ℓ_V(i)}`. -/
private def sampleChallengeFromSequence
    {trΔp : T_P}
    {state : CanonicalSpongeState U}
    (seq : LookaheadSequence trΔp state)
    (i : pSpec.ChallengeIdx)
    (hInputLenLe : seq.inputState.length ≤ pSpec.Lᵥᵢ i) :
    OracleComp (Unit →ₒ U) (Vector U (challengeSize i)) := do
  -- `L_V(i)` — total number of permutation calls in the verifier squeeze window for round `i`.
  let maxSteps := pSpec.Lᵥᵢ i
  -- `knownBlocks = [s_{R,out,0}^{(1)}, …, s_{R,out,m₁-1}^{(1)}]` — the `m₁` output-rate
  -- segments already determined by the unique maximal sequence `S_LA^{(1)}`.
  let knownBlocks : List (Vector U SpongeSize.R) :=
    seq.outputState.map CanonicalSpongeState.rateSegment
  -- `|knownBlocks| = |inputState| = m₁` (output and input lists have equal length by
  -- `LookaheadSequence.inputState_length_eq_outputState_length`).
  have hKnownLenEqInputLen : knownBlocks.length = seq.inputState.length := by
    have hKnownLenEqOutputLen : knownBlocks.length = seq.outputState.length := by
      simp [knownBlocks]
    have hOutputLenEqInputLen : seq.outputState.length = seq.inputState.length := by
      exact (LookaheadSequence.inputState_length_eq_outputState_length
        (T_P := T_P) (U := U) seq).symm
    exact hKnownLenEqOutputLen.trans hOutputLenEqInputLen
  -- `m₁ ≤ L_V(i)` (from the family length bound).
  have hKnownLenLeMax : knownBlocks.length ≤ maxSteps := hKnownLenEqInputLen ▸ hInputLenLe
  -- `L_V(i) - m₁` — number of additional random rate blocks to sample.
  let missingBlocks := maxSteps - knownBlocks.length
  -- Sample `s_{R,out,m₁}^{(1)}, …, s_{R,out,L_V(i)-1}^{(1)} ←$ U(Σ^r)`.
  let ⟨randomBlocks, hRandomLen⟩ ← sampleRateVectorsExact (U := U) missingBlocks
  -- `allBlocks = [s_{R,out,0}^{(1)}, …, s_{R,out,L_V(i)-1}^{(1)}]` — full output-rate list.
  let allBlocks := knownBlocks ++ randomBlocks
  -- `units = s_{R,out,0}^{(1)} ‖ s_{R,out,1}^{(1)} ‖ ⋯ ‖ s_{R,out,L_V(i)-1}^{(1)}` —
  -- concatenation of all `L_V(i)` rate blocks into a flat unit list.
  let units : List U := List.flatten (allBlocks.map Vector.toList)
  -- `|allBlocks| ≥ L_V(i)` (known `m₁` + sampled `L_V(i) - m₁`).
  have hMax_le_allBlocks : maxSteps ≤ allBlocks.length := by
    simp [allBlocks, missingBlocks, hRandomLen, Nat.add_sub_of_le hKnownLenLeMax]
  -- `|units| ≥ L_V(i) · r` (each rate block contributes exactly `r` units).
  have hMaxR_le_units : maxSteps * SpongeSize.R ≤ units.length := by
    have hmul : maxSteps * SpongeSize.R ≤ allBlocks.length * SpongeSize.R :=
      Nat.mul_le_mul_right SpongeSize.R hMax_le_allBlocks
    have hUnitsLen : units.length = allBlocks.length * SpongeSize.R := by
      exact length_flatten_vector_toList (U := U) allBlocks |>.symm ▸ rfl
    rw [hUnitsLen]; exact hmul
  -- `ℓ_V(i) ≤ L_V(i) · r ≤ |units|` — the challenge size fits within the concatenated units.
  have hChal_le_units : challengeSize i ≤ units.length := by
    have hChal_le_maxR : challengeSize i ≤ maxSteps * SpongeSize.R := by
      exact challengeSize_le_Lvi_mul_R (pSpec := pSpec) i
    exact le_trans hChal_le_maxR hMaxR_le_units
  -- Return `ρ̂_i := units[0 : ℓ_V(i)] ∈ Σ^{ℓ_V(i)}`.
  pure (takeVector (U := U) (challengeSize i) units hChal_le_units)

/-! ### Bridge lemma: `successorCandidates` → entry membership -/

private lemma successor_singleton_mem_entries
    (trΔp : T_P) (current next : CanonicalSpongeState U)
    (h : successorCandidates (T_P := T_P) (U := U) trΔp current = [next]) :
    (current, next) ∈ TraceTableOps.entries (V := CanonicalSpongeState U) trΔp := by
  unfold successorCandidates at h
  classical
  have hMem : next ∈ (TraceTableOps.entries (V := CanonicalSpongeState U) trΔp).filterMap
      (fun pair => if pair.1 = current then some pair.2 else none) := by rw [h]; exact .head ..
  obtain ⟨pair, hPairMem, hPairEq⟩ := List.mem_filterMap.mp hMem
  split at hPairEq
  · next hCurr =>
      have hSnd : pair.2 = next := by injection hPairEq
      have hPairEq' : pair = (current, next) := Prod.ext hCurr hSnd
      rw [hPairEq'] at hPairMem; exact hPairMem
  · contradiction

/-! ### Linear-scan helpers (CO25 §5.3 Algorithm 2 line 1107 "search stops on conflicting chains")

The paper's Algorithm 2 enumerates the maximal family then post-filters. CO25 line 1107 states
"the search stops if it encounters two conflicting chains" — i.e. scan-time fork → return `err`
directly. This is paper-faithful: scan-time fork detection coincides with `E_fork,p`. -/


/-- Output of linear forwards scan: either a fork was detected, or scan terminated with an optional sequence. -/
private inductive LinearForwardScanResult {T_P : Type} [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔp : T_P) (state : CanonicalSpongeState U) where
  | forkErr
  | done (seq? : Option (LookaheadSequence trΔp state))

/-- CO25 §5.3 LookAhead linear forwards scan: from `current`, classify successor candidates in
`tr_∇.p`. `[]` ends scan; `[next]` continues; `_::_::_` → `.forkErr`. -/
private def linearScanForwards
    (trΔp : T_P) (fuel : Nat) (current : CanonicalSpongeState U) :
    LinearForwardScanResult (U := U) trΔp current :=
  match fuel with
  | 0 => .done none
  | fuel' + 1 =>
    -- Look up successor in `tr_∇.p` (CO25 §5.3)
    let succs := successorCandidates (T_P := T_P) (U := U) trΔp current
    match hSuccs : succs with
    | [] => .done none -- No successor, sequence ends
    | [next] =>
        -- Found unique successor (CO25 §5.3 maximal sequence)
        if hNoLoop : current.capacitySegment = next.capacitySegment then
          .forkErr -- Self-loop → `E_inv`
        else
          have hNoLoop' : current.capacitySegment ≠ next.capacitySegment := hNoLoop
          have hEntry : (current, next) ∈ TraceTableOps.entries trΔp :=
            successor_singleton_mem_entries trΔp current next hSuccs
          match linearScanForwards trΔp fuel' next with
          | .forkErr => .forkErr
          | .done none =>
              .done (some (singletonLookaheadSequence (T_P := T_P) (U := U)
                trΔp current next hEntry hNoLoop'))
          | .done (some tailSeq) =>
              .done (some (prependLookaheadSequence (T_P := T_P) (U := U) trΔp
                current next hEntry hNoLoop' tailSeq))
    | _ :: _ :: _ => .forkErr -- `tr_∇.p` collision → `E_prp`

private lemma linearScanForwards_seq_length_le
    (trΔp : T_P) (fuel : Nat) (current : CanonicalSpongeState U)
    {seq : LookaheadSequence trΔp current}
    (hScan : linearScanForwards (T_P := T_P) (U := U) trΔp fuel current = .done (some seq)) :
    seq.pairs.length ≤ fuel := by
  induction fuel generalizing current seq with
  | zero => simp [linearScanForwards] at hScan
  | succ fuel' ih =>
      simp only [linearScanForwards] at hScan
      -- body matches on successorCandidates result
      split at hScan
      · -- succs = []: .done none, contradiction
        simp at hScan
      · next next hSuccEq => -- succs = [next]
          split at hScan
          · -- loop detected: .forkErr, contradiction
            simp at hScan
          · -- no loop: match on recursive result
            split at hScan
            · -- recursive .forkErr, contradiction
              simp at hScan
            · -- recursive .done none: singleton sequence, pairs.length = 1 ≤ fuel' + 1
              injection hScan with hEq
              injection hEq with hEq2
              subst hEq2
              exact Nat.succ_le_succ (Nat.zero_le fuel')
            · next tailSeq hTailScan =>
              -- recursive .done (some tailSeq): prepend, length = tailLen + 1 ≤ fuel' + 1
              injection hScan with hEq
              injection hEq with hEq2
              subst hEq2
              have hTailLen := ih next hTailScan
              exact Nat.succ_le_succ hTailLen
      · -- succs = _ :: _ :: _: .forkErr, contradiction
        simp at hScan

/-- `linearLookAhead` uses the linear scan to return either a challenge vector or
`err` directly (paper-faithful). Replaces the exhaustive `LookAheadSequenceFamily.compute` family
enumeration for the executable surface. -/
private def linearLookAhead
    (trΔp : T_P) (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) :
    OracleComp (Unit →ₒ U) (ExperimentOutput (Vector U (challengeSize i))) := do
  let maxSteps := pSpec.Lᵥᵢ i
  match hScan : linearScanForwards (T_P := T_P) (U := U) trΔp maxSteps state with
  | .forkErr => pure ExperimentOutput.err
  | .done none => pure ExperimentOutput.noResult
  | .done (some seq) =>
      have hLen : seq.inputState.length ≤ pSpec.Lᵥᵢ i := by
        -- scan-invariant: `pairs.length ≤ maxSteps = pSpec.Lᵥᵢ i`.
        rw [inputState_length_eq_pairs_length]
        exact linearScanForwards_seq_length_le trΔp maxSteps state hScan
      let rhoHat ← sampleChallengeFromSequence (T_P := T_P) (U := U) (pSpec := pSpec)
        (seq := seq) (i := i) (hInputLenLe := hLen)
      pure (ExperimentOutput.some rhoHat)

/-- CO25 §5.3 Algorithm 2 — `LookAhead(tr_∇.p, s, i)`, polymorphic over any
`[LawfulTraceTable T_P ...]` for `tr_∇.p`.

Inputs:
- `trΔp` — the simulator's permutation table `tr_∇.p`,
- `state` — initial permutation state `s = (s_R, s_C) ∈ Σ^{r+c}`,
- `i` — challenge round index `i ∈ [k]`.

Output: a probabilistic computation returning either
- `ExperimentOutput.err` — multiple maximal lookahead sequences (paper Step 2(a)),
- `ExperimentOutput.noResult` — empty `S_LA` (paper Step 2(b)),
- `ExperimentOutput.some ρ̂_i` — single maximal sequence; the missing rate blocks
  `s_{R,out,m_1}, …, s_{R,out,L_V(i)-1}` are sampled uniformly from `Σ^r` and the prefix
  of length `ℓ_V(i)` is returned (paper Step 2(c)).

Implementation: delegates to `linearLookAhead`, which performs CO25 line-1107's scan-time
fork-detection optimization. The paper-spec `LookAheadSequenceFamily.compute` family is retained
for downstream proofs (BadEvents, AbortAnalysis). -/
def lookAhead
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) :
    OracleComp (Unit →ₒ U) (ExperimentOutput (Vector U (challengeSize i))) :=
  linearLookAhead (pSpec := pSpec) trΔp state i

end

end DuplexSpongeFS.Lookahead
