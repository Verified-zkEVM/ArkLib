/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.Backtrack.Basic

/-!
# BackTrack: candidate extraction and the procedure

[CO25, §5.2 Steps 3–4] (`constructCandidateSalt`, `extractCandidate`), `linearBackTrack`,
`backTrack`, and the forward-first variant `backTrackFwd`.

The step labels used in this file and by its consumers (`Step 3`, `Step 4(a).i`–`iii.F`) follow
[CO25, §5.2]: Step 3 extracts the salt and Step 4(a) replays the absorb and squeeze cursors
round by round. The labels `Step 2(b)/(c)` name the pieces of the Lean scan, whose predecessor
and hash-anchor lookups realize Definition 5.3 and the time-complexity paragraph of §5.2.
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

section BacktrackProcedure

variable [DecidableEq StmtIn] [DecidableEq U] {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]

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

/-- `rateUnitsOf xs` — concatenation of every rate-segment in a list of permutation states.
For a `BacktrackSequence`, applied to `inputState`, this is the full sequence
`s_{R,in,0} ‖ s_{R,in,1} ‖ ⋯ ‖ s_{R,in,m_k}` of all sponge rate units [CO25, §5.2 Step 3]. -/
def rateUnitsOf (xs : List (CanonicalSpongeState U)) : List U :=
  xs.foldl (fun acc s => acc ++ s.rateSegment.toList) []

/-- The concatenated rate units of a `BacktrackSequence`'s `inputState` chain
([CO25, §5.2 Step 3] salt source). -/
def BacktrackSequence.rateUnits
    {trace : QueryLog (duplexSpongeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) : List U :=
  rateUnitsOf seq.inputState

/-- BackTrack Step 4(a).iii.A — assemble the encoded i-th prover message
[CO25, §5.2 Step 4(a)iii.A], at
**unit** granularity:
  `α̂_i^(k) := (concat_rate_segs(s_{R,in,b}, s_{R,in,b+1}, …)[cA :])[0 : ℓ_P(i)] ∈ Σ^{ℓ_P(i)}`.

The message starts at absorb cursor `cA` inside chain block `b` (`roundProverMessageWindowStart i`),
not at a block boundary: under the lazy overwrite-mode duplex a message continues inside whatever
partially filled block the preceding operation left, and after a squeeze it overwrites the last
output block from position `0`. -/
def BacktrackSequence.assembleEncodedProverMessage
    {trace : QueryLog (duplexSpongeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state)
    (b cA : Nat) (msgIdx : pSpec.MessageIdx) :
    Option (Vector U (proverMessageSize msgIdx)) := do
  let ⟨v, _⟩ ←
    vectorOfListExact (U := U) (proverMessageSize msgIdx) (chainUnitsFrom seq.inputState b cA)
  return v

/-- BackTrack Step 4(a).iii.E ([CO25, §5.2 Step 4(a)iii.E]) — verifier squeeze window check.

Char-based view: for a verifier squeeze starting at block `squeezeStart` of length
`lvCur` blocks (= `lvCur · r` chars), consecutive squeeze blocks must agree on their
rate segments — i.e. for each `k' ∈ [lvCur)`,
  `s_{R,out, squeezeStart+k'}  =  s_{R,in, squeezeStart+k'+1}`. -/
def BacktrackSequence.checkSqueezeWindow
    {trace : QueryLog (duplexSpongeOracle StmtIn U)}
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

/-- BackTrack Step 3 ([CO25, §5.2 Step 3]): extract the candidate salt `∈ U^δ`.

Concatenates the rate segments of all input states `[s_{in,0}, …, s_{in,m_k}]` and slices off
exactly the first `δ` units.  Returns `none` if the chain is too short.

As in [CO25, §5.2 Step 3], there is no separate salt-remainder check
`s_{R,in,L_δ-1}[δ mod r : r] = s_{R,out,L_δ-2}[δ mod r : r]`: under the lazy
overwrite-mode duplex the salt occupies units `[0, δ)` of the chain outright. When the prover
starts and `r ∤ δ`, its first message continues inside the same block, so that suffix need not
be inherited. An unconditional salt-remainder check could reject an honest chain.
The remainder check of [CO25, §5.2 Step 4(a)iii.C] subsumes it.
When the verifier starts, `extractCandidate` checks the suffix at the initial salt boundary. -/
def BacktrackSequence.constructCandidateSalt
    {trace : QueryLog (duplexSpongeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) :
    Option (Vector U δ) := do
  let ⟨saltₖ, _⟩ ← vectorOfListExact (U := U) δ seq.rateUnits
  return saltₖ

/-- Look up one previously assembled encoded message by its protocol index. -/
def findCandidateProverMessage
    (acc : List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (proverMessageSize msgIdx)))
    (j : pSpec.MessageIdx) : Option (Vector U (proverMessageSize j)) :=
  acc.findSome? fun p =>
    if h : p.1 = j then some (h ▸ p.2 : Vector U (proverMessageSize j)) else none

/-- Every message required by an exact-fit candidate has actually been assembled. -/
def candidateProverMessagesPresent
    (acc : List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (proverMessageSize msgIdx)))
    (i : pSpec.ChallengeIdx) : Prop :=
  ∀ j : pSpec.ProverMessageIdxBefore i.1.castSucc, (findCandidateProverMessage acc j.1).isSome

instance instDecidableCandidateProverMessagesPresent
    (acc : List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (proverMessageSize msgIdx)))
    (i : pSpec.ChallengeIdx) : Decidable (candidateProverMessagesPresent acc i) := by
  unfold candidateProverMessagesPresent
  infer_instance

/-- The assembled message tuple. The default branch is unreachable whenever
`candidateProverMessagesPresent acc i`; keeping it proof-irrelevant makes the executable output
stable. -/
def candidateProverMessages
    (acc : List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (proverMessageSize msgIdx)))
    (i : pSpec.ChallengeIdx) : pSpec.EncodedProverMessagesBefore U i.1.castSucc := fun j =>
  match findCandidateProverMessage acc j.1 with
  | some v => v
  | none => Vector.replicate (proverMessageSize j.1) (0 : U)

/-- BackTrack Step 4 ([CO25, §5.2 Step 4], the replay): parse the protocol rounds to extract
and validate messages. -/
def BacktrackSequence.extractCandidate
    (state : CanonicalSpongeState U)
    (trace : QueryLog (duplexSpongeOracle StmtIn U))
    (seq : BacktrackSequence (trace := trace) (state := state))
    (salt : Vector U δ) :
    Option (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := Id.run do
  -- `m_k + 1 = |inputState^(k)|` — number of permutation calls reconstructed for this sequence.
  let m_k_plus_1 := seq.inputState.length
  -- Accumulator `(α̂_1^(k), …, α̂_{i-1}^(k))` built across the loop iterations.
  -- Each entry `⟨msgIdx, v⟩` carries the encoded message `α̂_{msgIdx} ∈ Σ^{ℓ_P(msgIdx)}`.
  let mut alphaHat_acc : List
      (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (proverMessageSize msgIdx)) := []
  -- Step 4(a): For every i ∈ [k] = {1, …, k}.
  for i in verifierMessageIdxList (pSpec := pSpec) do
    -- Step 4(a).i — the unit-level position pointers of round `i` (the paper's cursor replay),
    -- read off the honest sponge walk `walkPos`:
    --   `blockOffset i` / `roundProverMessageCursor i` — where round `i`'s message *starts*;
    --   `roundEndBlock i` / `roundEndCursor i`   — where it *ends*;
    --   `exactFitBlocks i = roundEndBlock i + 1` — the chain length of an exact fit.
    let fit := exactFitBlocks (δ := δ) i
    let msgIdx? := lastProverMessageBefore? (pSpec := pSpec) i
    let endBlock := roundEndBlock (δ := δ) i
    let endCursor := roundEndCursor (δ := δ) i
    -- Step 4(a).ii — guard `exactFitBlocks(i) ≤ m_k + 1`.
    -- (Otherwise the chain is too short to host this message window.)
    if fit > m_k_plus_1 then
      return none -- not enough rate units to host the i-th message ⇒ remove from S_BT
    -- Step 4(a).iii.A — assemble `α̂_i^(k) ∈ Σ^{ℓ_P(i)}` via `assembleEncodedProverMessage`
    -- [CO25, §5.2 Step 4(a)iii.A], from the unit window starting at cursor
    -- `roundProverMessageCursor i` inside block `blockOffset i`.  Returns `none` if that window has
    -- fewer than `ℓ_P(i)` chars.
    match msgIdx? with
    | some msgIdx =>
      match seq.assembleEncodedProverMessage (blockOffset (δ := δ) i)
          (roundProverMessageCursor (δ := δ) i) msgIdx with
      | some v => alphaHat_acc := alphaHat_acc ++ [⟨msgIdx, v⟩]
      | none => return none -- not enough units in this window ⇒ remove from S_BT
    | none => pure ()
    -- Step 4(a).iii.B — define the message-remainder rate suffix:
    --   `z_i^(k) := s_{R,in,endBlock}[endCursor : r]  ∈ Σ^{r − endCursor}`.
    -- Char-based view: the chars of the last absorbed input-rate block that did NOT contribute
    -- to `α̂_i^(k)` — and, since nothing has written them since the last permutation, they are
    -- inherited verbatim from that permutation's output.
    --
    -- Step 4(a).iii.C — check that `z_i^(k)` equals the corresponding suffix of the
    -- **previous** output-rate block, or of `Start`'s all-zero rate when there is no previous
    -- block.  The absorb-epoch check has two branches, both required when `endCursor < r`:
    --   `s_{R,in,b}[endCursor : r]  =  0^(r − endCursor)`         if `b = 0`,
    --   `s_{R,in,b}[endCursor : r]  =  s_{R,out,b−1}[endCursor : r]`  if `b > 0`.
    -- The `b = 0` comparand is legitimate because `DuplexSponge.start` builds its state as
    -- `Vector.replicate r 0 ++ cap`, so block `0`'s rate is `salt ‖ message-prefix` followed by
    -- zeros.  This is the paper's remainder check [CO25, §5.2 Step 4(a)iii.C],
    -- which pairs `s_{R,in,b}[i_A : r]` with `s_{R,out,b−1}[i_A : r]` (zeros when `b = 0`); the
    -- exact-fit case has no `s_out,m_k` to compare against (Definition 5.3, Eq. (9): the chain
    -- ends on an input state).
    --
    -- The check applies only when the final block is partial (`endCursor ≠ r`): a full final
    -- block overwrites the entire rate, leaving no inherited remainder. At an initial verifier
    -- message, the boundary comes from the salt alone, including an empty salt.
    if roundHasAbsorbBoundary (pSpec := pSpec) i ∧ endCursor ≠ SpongeSize.R then
      if h_bounds : endBlock < m_k_plus_1 ∧ 0 < endBlock ∧
          endBlock - 1 < seq.outputState.length then
        let z_i := (seq.inputState.get ⟨endBlock, h_bounds.1⟩).rateSegment.toList.drop endCursor
        let outSuffix := (seq.outputState.get
            ⟨endBlock - 1, h_bounds.2.2⟩).rateSegment.toList.drop endCursor
        if z_i ≠ outSuffix then
          return none -- B/C remainder check failed ⇒ remove from S_BT
      else if h_zero : endBlock = 0 ∧ 0 < m_k_plus_1 then
        -- `b = 0`: the message still lives in the chain's first block, whose rate `Start`
        -- zeroed, so the untouched tail must be `0^(r − endCursor)`.
        let z_i := (seq.inputState.get ⟨0, h_zero.2⟩).rateSegment.toList.drop endCursor
        if z_i ≠ List.replicate (SpongeSize.R - endCursor) (0 : U) then
          return none -- B/C zero-remainder check failed ⇒ remove from S_BT
      else
        -- Neither comparand exists (the chain is too short to host this block at all). Skip:
        -- removal from `S_BT` happens only on a *failed* check, never on a missing comparand
        -- (this was the Step-D-unreachable bug: rejecting here killed every exact-fit
        -- candidate, since `s_out,m_k` never exists).
        pure ()
    -- Step 4(a).iii.D — exact fit: `exactFitBlocks(i) = m_k + 1`.
    -- Char-based view: the chain ends exactly after the i-th prover message is absorbed; no
    -- verifier message squeeze follows. Store the output tuple
    --   `(i, 𝕩^(k), τ^(k), (α̂_1^(k), …, α̂_i^(k)))` in `Outs`.
    if fit == m_k_plus_1 then
      let acc := alphaHat_acc
      if candidateProverMessagesPresent acc i then
        return some { roundIdx := i, stmt := seq.stmt, salt := salt,
                      encodedProverMessages := candidateProverMessages acc i }
      else
        return none -- an unassembled prefix message makes this candidate invalid
    -- Step 4(a).iii.E — verifier squeeze window check via `checkSqueezeWindow`.
    -- Round `i`'s squeeze makes `roundSqueezeCalls i` permutation calls, at input states
    -- `s_in,endBlock … s_in,endBlock+roundSqueezeCalls i−1`.  Squeezing never writes, so
    -- `s_in,q+1 = s_out,q` for every call *strictly inside* the squeeze; the **last** call's
    -- output block is the one round `i+1`'s message overwrites, so it is excluded — hence
    -- `roundSqueezeInnerCalls i = roundSqueezeCalls i − 1` pairs.
    if roundSqueezeEndBlock (δ := δ) i < m_k_plus_1 then
      if not (seq.checkSqueezeWindow endBlock (roundSqueezeInnerCalls (δ := δ) i)) then
        return none -- E squeeze window check failed ⇒ remove from S_BT
    else
      -- Step 4(a).iii.F — neither D (exact fit) nor E (squeeze fits) applies: the chain is
      -- mid-squeeze with not enough blocks remaining ⇒ invalid.
      return none
  -- Exhausted all rounds without hitting Step D — sequence is invalid.
  return none

/-- **[CO25, §5.2]** Reconstruct one candidate by scanning backwards from `state`.
Conflicting predecessors or capacity loops return `err`; a missing anchor or exhausted fuel
returns `noResult`. A completed chain is parsed for salt and encoded prover messages;
failed parsing also returns `noResult`. This executable scan does not enumerate `S_BT`. -/
def linearBackTrack
    (trace : QueryLog (duplexSpongeOracle StmtIn U))
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
        match seq.constructCandidateSalt (δ := δ) with
        | none => ExperimentOutput.noResult
        | some salt =>
          match seq.extractCandidate (pSpec := pSpec) (δ := δ) (StmtIn := StmtIn) (U := U)
              (state := state) (trace := trace) (salt := salt) with
          | none => ExperimentOutput.noResult
          | some out => ExperimentOutput.some out

/-- **[CO25, §5.2]** Unrestricted backtracking scan on the supplied trace table.
Returns `err`, `noResult`, or a reconstructed tuple `(i, x, τ, (α̂₁, …, α̂ₘᵢ))`, where
`mᵢ` counts prover messages before verifier position `i`. The oracle wrapper and trace
translator use `backTrackFwd` to exclude inverse-first competing predecessors. -/
def backTrack
    (trace : QueryLog (duplexSpongeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (state : CanonicalSpongeState U)
    (depthBound : Nat := trace.length + 1) :
    ExperimentOutput (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  linearBackTrack (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound

/-! ## `BackTrack` over forward-first permutation pairs

The unrestricted scan can encounter competing predecessors introduced by inverse queries:
`p(a₀) = cur` and `p⁻¹(t) = s'`, with distinct `t` and `cur` sharing a capacity, place both
`(a₀, cur)` and `(s', t)` in the bidirectional table. A later scan from `cur` then branches.
The inverse input capacity is adversary-chosen, so it cannot be charged as a fresh random
answer collision.

`backTrackFwd` filters to pairs whose first occurrence is forward. This is the implemented
repair used by the hybrid proofs, not an enumeration of the paper's hash-anchored families.
The index is rebuilt from the trace; no paper running-time guarantee is asserted here.
The unrestricted scan remains available for comparison and agrees on inverse-free traces. -/

section ForwardFirstBackTrack

/-- **[CO25, §5.2]** `BackTrack`, run against the **forward-first** sub-index of `tr_∇.p`.

Differs from the paper: only forward-first pairs of `tr_∇.p` are searched (the BackTrack fix).

This is what `D2SQuery` (`ProverTransform.d2sHandleForwardPermQuery`) and StdTrace
(`TraceTransform.stdTraceHandlePQuery`) call.  On a `p⁻¹`-free trace it agrees with `backTrack`
definitionally-after-rewriting (`backTrackFwd_eq_backTrack_of_hasNoInversePermQuery`). -/
def backTrackFwd
    (trace : QueryLog (duplexSpongeOracle StmtIn U))
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
    {trace : QueryLog (duplexSpongeOracle StmtIn U)}
    {trΔ₁ trΔ₂ : TraceNabla T_H T_P StmtIn U}
    (h₁ : trΔ₁.IsSubsetOfQueryLog trace) (h₂ : trΔ₂.IsSubsetOfQueryLog trace)
    (hEq : trΔ₁ = trΔ₂) (state : CanonicalSpongeState U) (depthBound : Nat) :
    backTrack (δ := δ) (pSpec := pSpec) trace trΔ₁ h₁ state depthBound
      = backTrack (δ := δ) (pSpec := pSpec) trace trΔ₂ h₂ state depthBound := by
  subst hEq
  rfl

/-- Supporting lemma for **[CO25, §5.2]**. When every mapping stored in `tr_∇.p`
is forward-first in `trace`, the forward-first restriction drops nothing and `backTrackFwd` *is*
`backTrack`. -/
theorem backTrackFwd_eq_backTrack_of_forwardOnly
    {trace : QueryLog (duplexSpongeOracle StmtIn U)}
    {trΔ : TraceNabla T_H T_P StmtIn U}
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (state : CanonicalSpongeState U) (depthBound : Nat)
    (hfwd : ∀ pair ∈ TraceTableOps.entries (V := CanonicalSpongeState U) trΔ.p,
      PermutationForwardFirst trace pair.1 pair.2) :
    backTrackFwd (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound
      = backTrack (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound := by
  unfold backTrackFwd
  exact backTrack_congr_trΔ _ _ (by rw [buildForwardPermutationIndex_eq_self hfwd]) _ _

end ForwardFirstBackTrack

end BacktrackProcedure

end DuplexSpongeFS.Backtrack
