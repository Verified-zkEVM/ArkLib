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
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

open Section52

variable {StmtIn : Type} [DecidableEq StmtIn]
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]
  [HasMessageSize pSpec] [HasChallengeSize pSpec]

noncomputable section

/-- Definition 5.2 (paper-facing): `(h,p,p⁻¹)` query-answer trace type. -/
abbrev Trace5_2 (StmtIn : Type) (U : Type) [SpongeUnit U] [SpongeSize] :=
  QueryLog (duplexSpongeChallengeOracle StmtIn U)

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

  /-- `|inputState| = |outputState| + 1` — CO25 Def 5.3 condition (a). -/
  inputState_length_eq_outputState_length_succ : inputState.length = outputState.length + 1

  /-- `inputState[m_k] = s` — last input equals the given final state.
    CO25 Def 5.3 condition (b). -/
  last_inputState_eq_state : inputState[inputState.length - 1] = state

  /-- `(h, 𝕩, inputState[0].capacitySegment) ∈ tr` — hash query anchors capacity.
    CO25 Def 5.3 condition (c). -/
  hash_in_trace : ⟨.inl stmt, (Vector.drop inputState[0] SpongeSize.R)⟩ ∈ trace

  /-- For all `ι < m_k`, either `(p, s_{in,ι}, s_{out,ι}) ∈ tr`
    or `(p⁻¹, s_{out,ι}, s_{in,ι}) ∈ tr`. CO25 Def 5.3 condition (d). -/
  permute_or_inv_in_trace : ∀ i : Fin outputState.length,
    ⟨.inr (.inl inputState[i]), outputState[i]⟩ ∈ trace
    ∨ ⟨.inr (.inr outputState[i]), inputState[i]⟩ ∈ trace

  /-- `s_{out,ι}.capacitySegment = s_{in,ι+1}.capacitySegment` — capacity threads through chain.
    CO25 Def 5.3 condition (e). -/
  capacitySegment_output_eq_input : ∀ i : Fin outputState.length,
    outputState[i].capacitySegment = inputState[i.val + 1].capacitySegment

  /-- `s_{in,ι}.capacitySegment ≠ s_{out,ι}.capacitySegment` — each step is a genuine permutation.
    CO25 Def 5.3 condition (f). -/
  capacitySegment_input_ne_output : ∀ i : Fin outputState.length,
    inputState[i].capacitySegment ≠ outputState[i].capacitySegment

/-- First-occurrence index of an entry in a trace. -/
private def firstOccurrenceIndex
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U))
    (hEntry : entry ∈ trace) : Fin trace.length := by
  classical
  let idxSet : Finset (Fin trace.length) :=
    Finset.filter (fun j => List.get trace j = entry) Finset.univ
  have hNonempty : idxSet.Nonempty := by
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hEntry
    refine ⟨j, ?_⟩
    exact Finset.mem_filter.mpr ⟨by simp, hj⟩
  exact idxSet.min' hNonempty

/-- The associated indices (first occurrences in the trace) for a backtracking sequence -/
def BacktrackSequence.Index (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (seq : BacktrackSequence trace state) :
    Fin trace.length × (Fin seq.inputState.length → Fin (trace.length + 1)) :=
  by
    classical
    have hInputStateNonempty : 0 < seq.inputState.length := by
      rw [seq.inputState_length_eq_outputState_length_succ]
      exact Nat.succ_pos _
    let inputState0 : CanonicalSpongeState U := seq.inputState[0]'hInputStateNonempty
    have hHashInTrace :
        ⟨.inl seq.stmt, (Vector.drop inputState0 SpongeSize.R)⟩ ∈ trace := by
      simpa [inputState0] using seq.hash_in_trace
    let hashIdx : Fin trace.length :=
      firstOccurrenceIndex (StmtIn := StmtIn) (U := U)
        trace
        ⟨.inl seq.stmt, (Vector.drop inputState0 SpongeSize.R)⟩
        hHashInTrace
    let embedTraceIdx : Fin trace.length → Fin (trace.length + 1) := fun j =>
      ⟨j.1, Nat.lt_succ_of_lt j.2⟩
    let permIdx : Fin seq.outputState.length → Fin trace.length := fun i =>
      let inputIdx : Fin seq.inputState.length :=
        ⟨i.1, by
          have hi : i.1 < seq.outputState.length + 1 :=
            Nat.lt_succ_of_lt i.2
          rw [seq.inputState_length_eq_outputState_length_succ]
          exact hi⟩
      if hPerm : ⟨.inr (.inl seq.inputState[inputIdx]), seq.outputState[i]⟩ ∈ trace then
        firstOccurrenceIndex (StmtIn := StmtIn) (U := U)
          trace
          ⟨.inr (.inl seq.inputState[inputIdx]), seq.outputState[i]⟩
          hPerm
      else
        let hInv : ⟨.inr (.inr seq.outputState[i]), seq.inputState[inputIdx]⟩ ∈ trace :=
          (seq.permute_or_inv_in_trace i).resolve_left hPerm
        firstOccurrenceIndex (StmtIn := StmtIn) (U := U)
          trace
          ⟨.inr (.inr seq.outputState[i]), seq.inputState[inputIdx]⟩
          hInv
    exact (hashIdx, fun i =>
      if h : i.1 < seq.outputState.length then
        embedTraceIdx (permIdx ⟨i.1, h⟩)
      else
        ⟨trace.length, Nat.lt_succ_self trace.length⟩)

/-- Paper §5.2 partial-cap-segment matching for `BackTrack`: enumerate all `(stateIn, stateOut)`
pairs in `tr_∇.p` whose `stateOut.capacitySegment` equals `nextInput.capacitySegment`, with the
no-loop guard `stateIn.cap ≠ stateOut.cap`.

Black-box over `[LawfulTraceTable T_P ...]` via `TraceTableOps.entries`; both forward and inverse
permutation directions already collapse into the same bidirectional `tr_∇.p`
(cf. `TraceNabla.ofQueryLog` dispatch). -/
private def predecessorCandidates
    {T_P : Type}
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔp : T_P)
    (nextInput : CanonicalSpongeState U) :
    List (CanonicalSpongeState U × CanonicalSpongeState U) := by
  classical
  exact (TraceTableOps.entries (V := CanonicalSpongeState U) trΔp).filterMap fun pair =>
    let stateIn := pair.1
    let stateOut := pair.2
    if stateOut.capacitySegment = nextInput.capacitySegment then
      if stateIn.capacitySegment = stateOut.capacitySegment then
        none
      else
        some (stateIn, stateOut)
    else
      none

private inductive BuildBacktrackResult (U : Type) [SpongeUnit U] [SpongeSize] where
  | err
  | ok (stepFamilies : List (List (CanonicalSpongeState U × CanonicalSpongeState U)))

private def buildBacktrackSteps
    {T_P : Type}
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔp : T_P) (fuelBound : Nat)
    (state : CanonicalSpongeState U) :
    BuildBacktrackResult U :=
  let rec go (fuel : Nat) (current : CanonicalSpongeState U)
      (stepsRev : List (CanonicalSpongeState U × CanonicalSpongeState U)) :
      BuildBacktrackResult U :=
    match fuel with
    | 0 => .err
    | fuel + 1 =>
      let preds := predecessorCandidates (T_P := T_P) (U := U) trΔp current
      match preds with
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
  go fuelBound state []

/-- CO25 Def 5.3 `S_BT(tr, s)` — maximal family of backtrack sequences (BackTrack §5.2 Step 2,
Eq. 10): finite set of `BacktrackSequence` pairs `(s_{in,ι}, s_{out,ι})` rooted at `state`,
with no sequence strictly containing another. -/
structure BacktrackSequenceFamily (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) where
  /-- `S_BT(tr, s)` — finite set of backtrack sequences (CO25 Def 5.3). -/
  seqFamily : Finset (BacktrackSequence trace state)
  /-- Maximality: no `s ≠ s'` with `s ⊆ s'` both in `S_BT` (CO25 Def 5.3 maximality). -/
  maximality : ∀ s ∈ seqFamily, ∀ s' ∈ seqFamily, s ≠ s' →
    ¬ (s.stmt = s'.stmt ∧ s.inputState ⊆ s'.inputState ∧ s'.outputState ⊆ s.outputState)

/-- Definition 5.3 (paper-facing): `S_BT(tr,s)` family of backtracking sequences. -/
abbrev S_BT
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) :=
  BacktrackSequenceFamily trace state

/-- Definition 5.4 (paper-facing): index list payload attached to one sequence. -/
abbrev BacktrackIndexList
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) :=
  Fin trace.length × (Fin seq.inputState.length → Fin (trace.length + 1))

/-- Definition 5.4 (paper-facing): `J_BT(tr,s)` index lists associated to `S_BT(tr,s)`. -/
def J_BT
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {state : CanonicalSpongeState U}
    (family : BacktrackSequenceFamily trace state) :
    Set (Sigma fun seq : BacktrackSequence trace state => BacktrackIndexList trace seq) :=
  fun x => x.1 ∈ family.seqFamily ∧ x.2 = BacktrackSequence.Index trace state x.1

/--
Section 5.1 paper-facing auxiliary trace data structure `tr_∇`:
- `hLog` stores hash-query entries,
- `pLog` stores forward-permutation entries,
- `pinvLog` stores inverse-permutation entries.
-/
structure TraceDelta where
  hLog : QueryLog (StmtIn →ₒ Vector U SpongeSize.C)                -- `tr_∇.h` hash-query log
  pLog : QueryLog (forwardPermutationOracle (CanonicalSpongeState U))  -- `tr_∇.p` forward
  pinvLog : QueryLog (backwardPermutationOracle (CanonicalSpongeState U)) -- `tr_∇.p` inverse

/-- Build the paper-facing `tr_∇` projection from a full duplex-sponge trace. -/
def buildTraceDelta
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    TraceDelta (StmtIn := StmtIn) (U := U) :=
  { hLog := trace.filterMap fun entry =>
      match entry with
      | ⟨.inl stmt, capSeg⟩ => some ⟨stmt, capSeg⟩
      | _ => none
    pLog := trace.filterMap fun entry =>
      match entry with
      | ⟨.inr (.inl stateIn), stateOut⟩ => some ⟨stateIn, stateOut⟩
      | _ => none
    pinvLog := trace.filterMap fun entry =>
      match entry with
      | ⟨.inr (.inr stateOut), stateIn⟩ => some ⟨stateOut, stateIn⟩
      | _ => none }

/-- BackTrack §5.2 Step 4.D output tuple `(i, 𝕩, τ, (α̂_1,…,α̂_i))` stored in `Outs`.

`absorbedRatePrefix` holds all absorbed rate blocks as a raw list (framework-independent);
`parsedTuple?` slices it into salt `τ` (Step 3) and encoded messages `α̂_j` (Step 4.a.iii.A). -/
structure BacktrackOutput where
  stmt : StmtIn                                                      -- `𝕩` instance (Step 4.D)
  round : Fin (n + 1)                                                -- `i ∈ [k]` round (Step 4.D)
  absorbedRatePrefix : List (Vector U SpongeSize.R) -- rate blocks (Steps 3, 4.a.iii.A)
  stepPairs : List (CanonicalSpongeState U × CanonicalSpongeState U) -- S_BT chain (Step 2, Eq. 10)

/-- Geometric invariants for a BackTrack §5.2 Step 4 candidate (chain-length,
rate-segment alignment, no-loop, capacity threading). -/
def BacktrackOutput.paperShapeValid
    (out : BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U)) : Prop :=
  0 < out.absorbedRatePrefix.length ∧
    out.round.1 + 1 = out.absorbedRatePrefix.length ∧
    out.stepPairs.length + 1 = out.absorbedRatePrefix.length ∧
    out.stepPairs.map (fun pair => pair.1.rateSegment) = out.absorbedRatePrefix.dropLast ∧
    (∀ pair ∈ out.stepPairs, pair.1.capacitySegment ≠ pair.2.capacitySegment) ∧
    (∀ pair ∈ out.stepPairs.zip out.stepPairs.tail,
      pair.1.2.capacitySegment = pair.2.1.capacitySegment)

/-- Boolean executable check for `BacktrackOutput.paperShapeValid`. -/
def BacktrackOutput.paperShapeValidb
    (out : BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U)) : Bool := by
  classical
  exact decide (BacktrackOutput.paperShapeValid (StmtIn := StmtIn) (n := n) (U := U) out)

private def backtrackOutputValid
    (out : BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U)) : Bool :=
  BacktrackOutput.paperShapeValidb (StmtIn := StmtIn) (n := n) (U := U) out

/-- Parser/validation parameters for BackTrack §5.2 Step 3 (salt extraction). -/
structure BacktrackParseParams where
  saltUnits : Nat := 0  -- `δ`: salt size in `U`-units (BackTrack §5.2 Step 3)

private def BacktrackParseParams.saltBlocks
    (params : BacktrackParseParams) : Nat :=
  Nat.ceil ((params.saltUnits : ℚ) / SpongeSize.R)

private def challengeIdxList : List pSpec.ChallengeIdx :=
  (Finset.univ : Finset pSpec.ChallengeIdx).toList

private def challengeIdxListUpTo (i : pSpec.ChallengeIdx) : List pSpec.ChallengeIdx :=
  ((Finset.univ : Finset pSpec.ChallengeIdx).filter (fun j => j.1 ≤ i.1)).toList

private def messageIdxListBefore (i : pSpec.ChallengeIdx) : List pSpec.MessageIdx :=
  ((Finset.univ : Finset pSpec.MessageIdx).filter (fun j => j.1 < i.1)).toList

private def challengeIdxListBefore (i : pSpec.ChallengeIdx) : List pSpec.ChallengeIdx :=
  ((Finset.univ : Finset pSpec.ChallengeIdx).filter (fun j => j.1 < i.1)).toList

private def lastMessageBefore? (i : pSpec.ChallengeIdx) : Option pSpec.MessageIdx :=
  (messageIdxListBefore (pSpec := pSpec) i).getLast?

private def sumMessageBlocksBefore (i : pSpec.ChallengeIdx) : Nat :=
  (messageIdxListBefore (pSpec := pSpec) i).foldl (fun acc j => acc + pSpec.Lₚᵢ j) 0

private def sumChallengeBlocksBefore (i : pSpec.ChallengeIdx) : Nat :=
  (challengeIdxListBefore (pSpec := pSpec) i).foldl (fun acc j => acc + pSpec.Lᵥᵢ j) 0

private def rateSuffixEqFrom
    (offset : Nat)
    (lhs rhs : Vector U SpongeSize.R) : Bool := by
  classical
  exact decide (lhs.toList.drop offset = rhs.toList.drop offset)

private def parserCheckMessageRemainder
    (inputRates outputRates : List (Vector U SpongeSize.R))
    (msgSizeUnits : Nat) (msgEndIdx : Nat) : Bool :=
  match inputRates[msgEndIdx]?, outputRates[msgEndIdx]? with
  | some inRate, some outRate =>
      rateSuffixEqFrom (U := U) (msgSizeUnits % SpongeSize.R) inRate outRate
  | _, _ => false

private def parserCheckSaltRemainder
    (params : BacktrackParseParams)
    (inputRates outputRates : List (Vector U SpongeSize.R)) : Bool :=
  if SpongeSize.R < params.saltUnits then
    let lDelta := params.saltBlocks
    let inIdx := lDelta - 1
    let outIdx := lDelta - 2
    match inputRates[inIdx]?, outputRates[outIdx]? with
    | some inRate, some outRate =>
        rateSuffixEqFrom (U := U) (params.saltUnits % SpongeSize.R) inRate outRate
    | _, _ => false
  else
    true

private def parserCheckSqueezeWindow
    (inputRates outputRates : List (Vector U SpongeSize.R))
    (startIdx : Nat) (numBlocks : Nat) : Bool := by
  classical
  let rec go (k : Nat) : Bool :=
    match k with
    | 0 => true
    | k' + 1 =>
        let outIdx := startIdx + k'
        let inIdx := startIdx + 1 + k'
        match outputRates[outIdx]?, inputRates[inIdx]? with
        | some outRate, some inRate =>
            if decide (outRate = inRate) then
              go k'
            else
              false
        | _, _ => false
  exact go numBlocks

private def candidateRoundFromParser
    (params : BacktrackParseParams)
    (out : BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U)) :
    Option pSpec.ChallengeIdx := by
  let inputRates := out.absorbedRatePrefix
  let outputRates := out.stepPairs.map (fun pair => pair.2.rateSegment)
  let mPlus1 := inputRates.length
  let saltRemainderOk :=
    parserCheckSaltRemainder (U := U) params inputRates outputRates
  if !saltRemainderOk then
    exact none
  else
    let rec scan (remaining : List pSpec.ChallengeIdx) : Option pSpec.ChallengeIdx :=
      match remaining with
      | [] => none
      | i :: rest =>
          let lpBefore := sumMessageBlocksBefore (pSpec := pSpec) i
          let lvBefore := sumChallengeBlocksBefore (pSpec := pSpec) i
          let lPtr := params.saltBlocks + lpBefore + lvBefore
          let msgIdx? := lastMessageBefore? (pSpec := pSpec) i
          let lpCur := msgIdx?.elim 0 (fun msgIdx => pSpec.Lₚᵢ msgIdx)
          if hTooLong : lPtr + lpCur > mPlus1 then
            none
          else if hExact : lPtr + lpCur = mPlus1 then
            some i
          else
            let msgRemainderOk :=
              if hLpPos : 0 < lpCur then
                let msgEndIdx := lPtr + lpCur - 1
                let msgSizeUnits := msgIdx?.elim 0 (fun msgIdx => messageSize msgIdx)
                parserCheckMessageRemainder
                  (U := U) inputRates outputRates msgSizeUnits msgEndIdx
              else
                true
            if !msgRemainderOk then
              none
            else
              let lvCur := pSpec.Lᵥᵢ i
              if hNeedSqueeze : lPtr + lpCur + lvCur < mPlus1 then
                let squeezeStart := lPtr + lpCur
                let squeezeOk :=
                  parserCheckSqueezeWindow
                    (U := U) inputRates outputRates squeezeStart lvCur
                if squeezeOk then
                  scan rest
                else
                  none
              else
                none
    exact scan (challengeIdxList (pSpec := pSpec))

private def backtrackOutputValidWithParser
    (params : BacktrackParseParams)
    (out : BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U)) : Bool := by
  match
      candidateRoundFromParser
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) params out with
  | some parsedRound =>
      let parsedRoundFin : Fin (n + 1) := ⟨parsedRound.1, Nat.lt_succ_of_lt parsedRound.1.2⟩
      exact BacktrackOutput.paperShapeValidb (StmtIn := StmtIn) (n := n) (U := U)
        { out with round := parsedRoundFin }
  | none => exact false

private def vectorOfListExact
    (len : Nat) (xs : List U) : Option (Vector U len) := by
  let ys := xs.take len
  if hLen : ys.length = len then
    exact some ⟨ys.toArray, by simpa using hLen⟩
  else
    exact none

private def encodedMessageAtChallenge
    (params : BacktrackParseParams)
    (out : BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U))
    (i : pSpec.ChallengeIdx) :
    Option (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx)) := by
  match lastMessageBefore? (pSpec := pSpec) i with
  | none =>
      exact none
  | some msgIdx =>
      let lpBefore := sumMessageBlocksBefore (pSpec := pSpec) i
      let lvBefore := sumChallengeBlocksBefore (pSpec := pSpec) i
      let lPtr := params.saltBlocks + lpBefore + lvBefore
      let lpCur := pSpec.Lₚᵢ msgIdx
      let rateBlocks := (out.absorbedRatePrefix.drop lPtr).take lpCur
      let unitBlocks := rateBlocks.foldl (fun acc block => acc ++ block.toList) []
      match vectorOfListExact (U := U) (messageSize msgIdx) unitBlocks with
      | some msgVec => exact some ⟨msgIdx, msgVec⟩
      | none => exact none

/-- Executable check for the paper branch condition
`∀ ι ≤ i, α̂_ι ∈ Im(φ_ι)` on one `BackTrack` candidate output. -/
def backtrackOutputMessagesInImage
    (params : BacktrackParseParams)
    (roundIdx : pSpec.ChallengeIdx)
    (inImage : (msgIdx : pSpec.MessageIdx) → Vector U (messageSize msgIdx) → Bool)
    (out : BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U)) : Bool := by
  match
      candidateRoundFromParser
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) params out with
  | none =>
      exact false
  | some parsedRound =>
      if hRound : parsedRound = roundIdx then
        let roundsToCheck := challengeIdxListUpTo (pSpec := pSpec) roundIdx
        exact roundsToCheck.all fun j =>
          match encodedMessageAtChallenge (pSpec := pSpec) (U := U) params out j with
          | some ⟨msgIdx, msgVec⟩ =>
              inImage msgIdx msgVec
          | none =>
              match lastMessageBefore? (pSpec := pSpec) j with
              | none => true
              | some _ => false
      else
        exact false

/-- BackTrack §5.2 Step 4.D output parsed into named components. -/
structure ParsedBacktrackTuple where
  roundIdx : pSpec.ChallengeIdx  -- `i ∈ [k]` round index (Step 4.D)
  stmt : StmtIn                  -- `𝕩` instance (Step 4.D)
  salt : List U                  -- `τ ∈ Σ^δ` salt (Step 3)
  /-- `(α̂_1,…,α̂_i)` encoded prover messages (BackTrack §5.2 Step 4.a.iii.A). -/
  encodedMessages : List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx))

/-- Recover the paper-facing tuple components from a `BackTrack` output candidate. -/
def BacktrackOutput.parsedTuple?
    (params : BacktrackParseParams)
    (out : BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U)) :
    Option (ParsedBacktrackTuple (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) := by
  match
      candidateRoundFromParser
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) params out with
  | none =>
      exact none
  | some roundIdx =>
      let allUnits : List U :=
        out.absorbedRatePrefix.foldl (fun acc block => acc ++ block.toList) []
      let salt := allUnits.take params.saltUnits
      let encodedMessages :=
        (challengeIdxListUpTo (pSpec := pSpec) roundIdx).filterMap fun j =>
          encodedMessageAtChallenge (pSpec := pSpec) (U := U) params out j
      exact some
        { roundIdx := roundIdx
          stmt := out.stmt
          salt := salt
          encodedMessages := encodedMessages }

/-- The backtracking procedure in Section 5.2, which takes in:
- the query-answer trace for the oracle `(h, p, p⁻¹)`
- a state (vector of `N` units)

And returns one of the following:
- `none`
- `err`
- A result consisting of:
  - an input statement,
  - a round index `i ≤ n`,
  - recovered absorbed rate blocks (from which one can parse salt and encoded prover messages)

NOTE: we do _not_ define the extra data structure `tr▵` as in the paper, as that is entirely derived
from the actual trace and is only present for efficiency (which we do not plan to reason about)

Implementation note: this executable surface now enforces structural tuple-shape checks used by
downstream reductions (exact round/prefix alignment plus capacity-chain coherence across recovered
steps), together with Algorithm 1 Item 3/4 parser-level checks (salt remainder, block offsets,
message remainder consistency, and verifier-squeeze window consistency).

TODO: figure out the best way to encode the two errors (currently we encode `err` as the failure of
OracleComp, and `none` as `Option.none` inside) -/
def backTrack {T_H T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (fuelBound : Nat)
    (state : CanonicalSpongeState U) :
    OptionT Option (BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U)) :=
  match buildBacktrackSteps (T_P := T_P) (U := U) trΔ.p fuelBound state with
  | .err =>
    -- `err` in the paper.
    OptionT.mk none
  | .ok stepFamilies =>
    let rawOuts :
        List (BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U)) :=
      stepFamilies.foldr (fun steps acc =>
        let inputStates : List (CanonicalSpongeState U) := (steps.map Prod.fst) ++ [state]
        let outsForSteps :=
          match inputStates.head? with
          | none =>
            -- Unreachable because `inputStates` is always nonempty.
            []
          | some startState =>
            if hSteps : steps.length ≤ n then
              -- Paper §5.2: `tr_∇.h.outlu(cap)` returns the unique stmt with that capacity, or
              -- ⟂ on zero/multiple matches (collapsed here to the empty list, paper-`none`).
              let hashStmts :=
                (Section52.TraceTableOps.outlu trΔ.h startState.capacitySegment).toList
              let i : Fin (n + 1) := ⟨steps.length, Nat.lt_succ_of_le hSteps⟩
              let absorbedRatePrefix := inputStates.map CanonicalSpongeState.rateSegment
              hashStmts.map fun stmt => ⟨stmt, i, absorbedRatePrefix, steps⟩
            else
              -- Backtrack candidates beyond the protocol round bound are discarded.
              []
        outsForSteps ++ acc) []
    let params : BacktrackParseParams := {}
    let outs := rawOuts.filterMap fun out =>
      match
          candidateRoundFromParser
            (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) params out with
      | some parsedRound =>
          let parsedRoundFin : Fin (n + 1) := ⟨parsedRound.1, Nat.lt_succ_of_lt parsedRound.1.2⟩
          let out' : BacktrackOutput (StmtIn := StmtIn) (n := n) (U := U) :=
            { out with round := parsedRoundFin }
          if
              backtrackOutputValidWithParser
                (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) params out'
          then
            some out'
          else
            none
      | none => none
    match outs with
    | [] =>
      -- `none` in the paper.
      failure
    | [out] =>
      return out
    | _ :: _ :: _ =>
      -- More than one valid candidate output: `err` in the paper.
      OptionT.mk none

end

end DuplexSpongeFS
