/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.TraceDataStructures

/-!
# Lookahead sequence family and procedure

This file contains the lookahead sequence family `S_LA(tr_∇.p, s, i)` and the procedure
`LookAhead(tr_∇.p, s, i)` from [CO25, §5.3].

## Declaration order

1. **Admissible chains ([CO25, §5.3, Step 1]).** `LookaheadSequence` records a nonempty
   linked sequence of table pairs with no capacity self-loop. `LookaheadSequenceFamily`
   and `S_LA` describe supplied bounded antichains; they do not assert exhaustiveness
   or global maximality. `successorCandidates` supplies the distinct successor lookup.
2. **Output sampling (Step 2(c)).** `sampleRateVectorsExact`, `takeVector` and
   `sampleVerifierMessageFromSequence` retain the `m` recorded output-rate blocks,
   sample `L_V(i) - m` fresh blocks, and truncate to `ℓ_V(i)` alphabet elements.
3. **Executable procedure.** `linearScanForwards` follows successors for at most
   `L_V(i)` steps. `linearLookAhead` and `lookAhead` dispatch on its result:
   * `.forkErr` gives `err`;
   * `.done none` gives `noResult`;
   * `.done (some seq)` samples the vector described in Step 2(c).

## Correspondence with the paper

Under successor uniqueness, `linearScanForwards_eq_none_or_maximalChain` in `LookAheadSpec.lean`
(in namespace `DuplexSpongeFS.Hyb0Hyb1`) proves that the scan either finds no admissible
bounded chain or returns the unique longest one. Its prefix comparison implements
Claim 5.20's chain argument; the characterization feeds both no-error and output-value
proofs used in Claim 5.21. No executable enumeration of the chain family is needed.

## Table access and conflicting successors

The procedure reads `tr_∇.p` through `TraceTableOps.entries`; `successorCandidates`
deduplicates the recorded outputs for a given input. Multiple distinct raw successors
cause an error before capacity self-loops are filtered. Thus the maximal-chain
correspondence is conditional on successor uniqueness, not an equivalence on arbitrary
inconsistent tables. This local conflict test is not the BackTrack event `E_fork,p`.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.Lookahead

open DSTraceStorage

variable {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]
  [HasVerifierMessageSize pSpec]

section

/-! ## §5.3 paper structures — `LookaheadSequence`, `S_LA(tr_∇.p, s, i)` -/

/-- **[CO25, §5.3, Eq. (16)]** A look-ahead sequence (Equation 16) over a black-box permutation
  table `tr_∇.p` and an initial state, consists of:
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
  /-- `S_LA^(k)` chain (LookAhead §5.3 Step 1, Eq. (16)): `(s_{in,ι}, s_{out,ι})` pairs. -/
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

/-- **[CO25, §5.3, Eq. (16)]** Supplied finite family of lookahead sequences from `s`,
each of length at most `L_V(i)`. The flattened state lists form an antichain within the
family; this does not require global maximality or exhaustiveness. -/
structure LookaheadSequenceFamily
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) where
  /-- `S_LA` — the finite family of look-ahead sequences (LookAhead §5.3 Step 1). -/
  seqFamily : Finset (LookaheadSequence trΔp state)
  /-- Distinct family members have incomparable flattened state lists under sublist inclusion. -/
  maximality : ∀ s ∈ seqFamily, ∀ s' ∈ seqFamily,
    s ≠ s' →
      ¬ (s.flattenStateSequence.Sublist s'.flattenStateSequence)
  /-- `m_k ≤ L_V(i)` — LookAhead §5.3 Step 1(a) length bound. -/
  length_le_numPermQueriesVerifierMessage : ∀ s ∈ seqFamily, s.inputState.length ≤ pSpec.Lᵥᵢ i

/-- **[CO25, §5.3]** `S_LA(tr_∇.p, s, i)`: the supplied lookahead-family type. -/
abbrev S_LA
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) :=
  LookaheadSequenceFamily (pSpec := pSpec) trΔp state i

/-! ## §5.3 — Executable successor scan -/

/-- Distinct successor candidates from the query-answer entries of `tr_∇.p`.

Unlike `TraceTableOps.inlu`, this retains all distinct matches so the scan can distinguish
no successor from conflicting successors. -/
-- TODO: Replace this linear `entries` scan with a conflict-aware, logarithmic lookup by input
-- state, as required by [CO25, Eq. (17)].
def successorCandidates
    (trΔp : T_P) (current : CanonicalSpongeState U) :
    List (CanonicalSpongeState U) :=
  ((TraceTableOps.entries (V := CanonicalSpongeState U) trΔp).filterMap fun pair =>
    if pair.1 = current then
      some pair.2
    else none).dedup

/-- The successor enumeration records precisely the table pairs with the given input. -/
lemma mem_successorCandidates_iff_mem_entries (p : T_P) (s next : CanonicalSpongeState U) :
    next ∈ successorCandidates (T_P := T_P) (U := U) p s ↔
      (s, next) ∈ TraceTableOps.entries (V := CanonicalSpongeState U) p := by
  classical
  simp only [successorCandidates, List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨q, hq, hEq⟩
    split at hEq
    · next hs => rw [← Option.some.inj hEq, ← hs]; simpa using hq
    · exact absurd hEq (by simp)
  · intro hmem
    exact ⟨(s, next), hmem, by simp⟩

/-- A singleton successor enumeration is exactly a successful conflict-free table lookup. -/
lemma successorCandidates_eq_singleton_iff_inlu (p : T_P) (s next : CanonicalSpongeState U) :
    successorCandidates (T_P := T_P) (U := U) p s = [next] ↔
      TraceTableOps.inlu p s = some next := by
  classical
  rw [LawfulTraceTable.inlu_eq_some]
  simp only [← TraceTableOps.mem_entries_iff_mem_toMultiSet,
    ← mem_successorCandidates_iff_mem_entries]
  constructor
  · intro h
    simp [h]
  · rintro ⟨hmem, hunique⟩
    apply List.Perm.eq_singleton
    apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_dedup _) (by simp)
    ext t
    simp only [List.mem_toFinset, List.mem_singleton]
    exact ⟨fun ht => hunique t ht, fun ht => ht ▸ hmem⟩

def singletonLookaheadSequence
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

def prependLookaheadSequence
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
            simpa only [List.head?_cons, Option.map_some, Option.some.injEq] using hHd
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

lemma inputState_length_eq_pairs_length
    {trΔp : T_P}
    {state : CanonicalSpongeState U} (seq : LookaheadSequence trΔp state) :
    seq.inputState.length = seq.pairs.length := by
  simp [LookaheadSequence.inputState]

/-! ## §5.3, Step 2(c) — Complete the recorded verifier-message blocks

For a returned chain with `m ≤ L_V(i)` pairs:
1. Keep its `m` output-rate blocks, in chain order.
2. Sample `L_V(i) - m` fresh uniform rate blocks.
3. Concatenate and retain the first `ℓ_V(i)` alphabet elements.

The later scan and dispatch definitions choose this sampling branch without enumerating `S_LA`.
-/

lemma verifierMessageSize_le_Lvi_mul_R (i : pSpec.ChallengeIdx) :
    verifierMessageSize i ≤ pSpec.Lᵥᵢ i * SpongeSize.R := by
  have hceil : ((verifierMessageSize i : ℚ) / SpongeSize.R) ≤ (pSpec.Lᵥᵢ i : ℚ) := by
    change ((verifierMessageSize i : ℚ) / SpongeSize.R) ≤
      (Nat.ceil ((verifierMessageSize i : ℚ) / SpongeSize.R) : ℚ)
    exact Nat.le_ceil ((verifierMessageSize i : ℚ) / SpongeSize.R)
  have hRnonneg : (0 : ℚ) ≤ SpongeSize.R := by
    exact_mod_cast (Nat.zero_le SpongeSize.R)
  have hmul :
      ((verifierMessageSize i : ℚ) / SpongeSize.R) * SpongeSize.R
        ≤ (pSpec.Lᵥᵢ i : ℚ) * SpongeSize.R :=
    mul_le_mul_of_nonneg_right hceil hRnonneg
  have hRne : (SpongeSize.R : ℚ) ≠ 0 := by
    exact_mod_cast (show SpongeSize.R ≠ 0 from NeZero.ne SpongeSize.R)
  have hleft :
      ((verifierMessageSize i : ℚ) / SpongeSize.R) * SpongeSize.R =
        (verifierMessageSize i : ℚ) := by
    field_simp [hRne]
  have hq : (verifierMessageSize i : ℚ) ≤ (pSpec.Lᵥᵢ i : ℚ) * SpongeSize.R := by
    simpa [hleft] using hmul
  exact_mod_cast hq

def sampleArrayExact :
    (m : Nat) → OracleComp (Unit →ₒ U) {xs : Array U // xs.size = m}
  | 0 => pure ⟨#[], rfl⟩
  | m + 1 => do
      let u ← query (spec := (Unit →ₒ U)) ()
      let ⟨xs, hxs⟩ ← sampleArrayExact m
      pure ⟨xs.push u, by simp [hxs]⟩

def sampleRateVector : OracleComp (Unit →ₒ U) (Vector U SpongeSize.R) := do
  let ⟨xs, hxs⟩ ← sampleArrayExact (U := U) SpongeSize.R
  pure ⟨xs, hxs⟩

def sampleRateVectorsExact :
    (m : Nat) → OracleComp (Unit →ₒ U) {blocks : List (Vector U SpongeSize.R) // blocks.length = m}
  | 0 => pure ⟨[], rfl⟩
  | m + 1 => do
      let head ← sampleRateVector (U := U)
      let ⟨tail, htail⟩ ← sampleRateVectorsExact m
      pure ⟨head :: tail, by simp [htail]⟩

omit [SpongeUnit U] [DecidableEq U] in
lemma length_flatten_vector_toList (blocks : List (Vector U SpongeSize.R)) :
    (List.flatten (blocks.map Vector.toList)).length = blocks.length * SpongeSize.R := by
  induction blocks with
  | nil => simp
  | cons x xs ih =>
      simp [ih, Nat.right_distrib, Nat.add_comm]

def takeVector (n : Nat) (xs : List U) (h : n ≤ xs.length) : Vector U n :=
  Vector.ofFn (fun j => xs[j.1]'(Nat.lt_of_lt_of_le j.2 h))

/-- **[CO25, §5.3]** Step 2(c) — given a lookahead sequence of length `m₁ ≤ L_V(i)`,
sample the `L_V(i) - m₁` missing rate blocks uniformly from `Σ^r`, concatenate with the known
output-rate blocks, and return the first `ℓ_V(i)` units as `ρ̂_i ∈ Σ^{ℓ_V(i)}`. -/
def sampleVerifierMessageFromSequence
    {trΔp : T_P}
    {state : CanonicalSpongeState U}
    (seq : LookaheadSequence trΔp state)
    (i : pSpec.ChallengeIdx)
    (hInputLenLe : seq.inputState.length ≤ pSpec.Lᵥᵢ i) :
    OracleComp (Unit →ₒ U) (Vector U (verifierMessageSize i)) := do
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
  -- `ℓ_V(i) ≤ L_V(i) · r ≤ |units|` — the verifier message size fits within the concatenated units.
  have hVMsg_le_units : verifierMessageSize i ≤ units.length := by
    have hVMsg_le_maxR : verifierMessageSize i ≤ maxSteps * SpongeSize.R := by
      exact verifierMessageSize_le_Lvi_mul_R (pSpec := pSpec) i
    exact le_trans hVMsg_le_maxR hMaxR_le_units
  -- Return `ρ̂_i := units[0 : ℓ_V(i)] ∈ Σ^{ℓ_V(i)}`.
  pure (takeVector (U := U) (verifierMessageSize i) units hVMsg_le_units)

/-! ### Bridge lemma: `successorCandidates` → entry membership -/

lemma successor_singleton_mem_entries
    (trΔp : T_P) (current next : CanonicalSpongeState U)
    (h : successorCandidates (T_P := T_P) (U := U) trΔp current = [next]) :
    (current, next) ∈ TraceTableOps.entries (V := CanonicalSpongeState U) trΔp := by
  unfold successorCandidates at h
  classical
  have hMemDedup : next ∈
      ((TraceTableOps.entries (V := CanonicalSpongeState U) trΔp).filterMap
        (fun pair => if pair.1 = current then some pair.2 else none)).dedup := by
    rw [h]
    exact .head ..
  have hMem : next ∈ (TraceTableOps.entries (V := CanonicalSpongeState U) trΔp).filterMap
      (fun pair => if pair.1 = current then some pair.2 else none) :=
    List.mem_dedup.mp hMemDedup
  obtain ⟨pair, hPairMem, hPairEq⟩ := List.mem_filterMap.mp hMem
  split at hPairEq
  · next hCurr =>
      have hSnd : pair.2 = next := by injection hPairEq
      have hPairEq' : pair = (current, next) := Prod.ext hCurr hSnd
      rw [hPairEq'] at hPairMem; exact hPairMem
  · contradiction

/-! ### Linear-scan helpers

A lookup with multiple distinct successors returns `forkErr`. Successor uniqueness
excludes this branch on good traces. This local conflict test is not identified
with the paper's BackTrack fork event. -/

/-- Output of linear forwards scan: either a fork was detected,
or scan terminated with an optional sequence. -/
inductive LinearForwardScanResult {T_P : Type}
  [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔp : T_P) (state : CanonicalSpongeState U) where
  | forkErr
  | done (seq? : Option (LookaheadSequence trΔp state))

/-- **[CO25, §5.3]** LookAhead linear forwards scan: from `current`, classify successor candidates
in `tr_∇.p`. `[]` ends the scan; `[next]` continues unless it is a self-loop, which terminates the
current candidate; `_::_::_` produces `.forkErr`. -/
def linearScanForwards
    (trΔp : T_P) (fuel : Nat) (current : CanonicalSpongeState U) :
    LinearForwardScanResult (U := U) trΔp current :=
  match fuel with
  | 0 => .done none
  | fuel' + 1 =>
    -- Look up successor in `tr_∇.p` ([CO25, §5.3])
    let succs := successorCandidates (T_P := T_P) (U := U) trΔp current
    match hSuccs : succs with
    | [] => .done none -- No successor, sequence ends
    | [next] =>
        -- Found unique successor ([CO25, §5.3] maximal sequence)
        if hLoop : current.capacitySegment = next.capacitySegment then
          .done none -- Step 1(d): terminate here; a forward self-loop is an `E_p` case
        else
          have hNoLoop : current.capacitySegment ≠ next.capacitySegment := hLoop
          have hEntry : (current, next) ∈ TraceTableOps.entries trΔp :=
            successor_singleton_mem_entries trΔp current next hSuccs
          match linearScanForwards trΔp fuel' next with
          | .forkErr => .forkErr
          | .done none =>
              .done (some (singletonLookaheadSequence (T_P := T_P) (U := U)
                trΔp current next hEntry hNoLoop))
          | .done (some tailSeq) =>
              .done (some (prependLookaheadSequence (T_P := T_P) (U := U) trΔp
                current next hEntry hNoLoop tailSeq))
    | _ :: _ :: _ => .forkErr -- Conflicting recorded successors

lemma linearScanForwards_seq_length_le
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
          · -- Self-loop returns `.done none`, contradicting `.done (some seq)`.
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

/-- **[CO25, §5.3]** Scan at most `L_V(i)` successor pairs. Conflicting successors return
`err`; an empty chain returns `noResult`. For a nonempty chain, sample the missing rate blocks
and return `ρ̂ᵢ ∈ Σ^{ℓ_V(i)}`. No supplied family is enumerated. -/
def linearLookAhead
    (trΔp : T_P) (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) :
    OracleComp (Unit →ₒ U) (ExperimentOutput (Vector U (verifierMessageSize i))) := do
  let maxSteps := pSpec.Lᵥᵢ i
  match hScan : linearScanForwards (T_P := T_P) (U := U) trΔp maxSteps state with
  | .forkErr => pure ExperimentOutput.err
  | .done none => pure ExperimentOutput.noResult
  | .done (some seq) =>
      have hLen : seq.inputState.length ≤ pSpec.Lᵥᵢ i := by
        -- scan-invariant: `pairs.length ≤ maxSteps = pSpec.Lᵥᵢ i`.
        rw [inputState_length_eq_pairs_length]
        exact linearScanForwards_seq_length_le trΔp maxSteps state hScan
      let rhoHat_i ← sampleVerifierMessageFromSequence (T_P := T_P) (U := U) (pSpec := pSpec)
        (seq := seq) (i := i) (hInputLenLe := hLen)
      pure (ExperimentOutput.some rhoHat_i)

/-- **[CO25, §5.3]** `LookAhead(tr_∇.p, s, i)`: scan from full state `s` and return
`err`, `noResult`, or an encoded verifier message `ρ̂ᵢ ∈ Σ^{ℓ_V(i)}`. Missing rate blocks
are sampled through `Unit →ₒ U`. Delegates to `linearLookAhead`; supplied chain families
are separate specifications, not computed by this procedure. -/
def lookAhead
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) :
    OracleComp (Unit →ₒ U) (ExperimentOutput (Vector U (verifierMessageSize i))) :=
  linearLookAhead (pSpec := pSpec) trΔp state i

end

end DuplexSpongeFS.Lookahead
