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

namespace DuplexSpongeFS.Backtrack

open DSTraceStorage

variable {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [HasChallengeSize pSpec]
  {δ : Nat}

noncomputable section

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
    [DecidableEq U]
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
    [DecidableEq U]
    {T_P : Type}
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔp : T_P) (depthBound : Nat)
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
  go depthBound state []

/-- CO25 Def 5.3 `S_BT(tr, s)` — maximal family of backtrack sequences
(Eq. 8 & BackTrack §5.2 Step 2, Eq. 10): a finite set of `BacktrackSequence` pairs
`(s_{in,ι}, s_{out,ι})` starting at an initial `StmtIn` and ending at sponge state `s`,
with no sequence strictly containing another. -/
structure BacktrackSequenceFamily (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) where
  /-- `S_BT(tr, s)` — finite set of backtrack sequences (CO25 Def 5.3). -/
  seqFamily : Finset (BacktrackSequence trace state)
  /-- Maximality: no `s ≠ s'` with `s ⊆ s'` both in `S_BT` (CO25 Def 5.3 maximality). -/
  maximality : ∀ s ∈ seqFamily, ∀ s' ∈ seqFamily, s ≠ s' →
    ¬ (s.stmt = s'.stmt ∧ s.inputState ⊆ s'.inputState ∧ s.outputState ⊆ s'.outputState)

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

private structure RawBacktrackOutput where
  stmt : StmtIn
  absorbedRatePrefix : List (Vector U SpongeSize.R)
  stepPairs : List (CanonicalSpongeState U × CanonicalSpongeState U)

/-- BackTrack §5.2 Step 4.D output tuple `(i, 𝕩, τ, (α̂_1,…,α̂_i))` stored in `Outs`. -/
structure BacktrackOutput where
  roundIdx : pSpec.ChallengeIdx
  stmt : StmtIn
  salt : Vector U δ
  /-- `(α̂_1, …, α̂_i)` — encoded messages up to challenge `i`, indexed by message index. -/
  encodedMessages : pSpec.EncodedMessagesUpTo U roundIdx.1.castSucc

/-- Geometric invariants for a BackTrack §5.2 Step 4 candidate (chain-length,
rate-segment alignment, no-loop, capacity threading). -/
private def RawBacktrackOutput.paperShapeValid
    (out : RawBacktrackOutput (StmtIn := StmtIn) (U := U)) : Prop :=
  0 < out.absorbedRatePrefix.length ∧
    out.stepPairs.length + 1 = out.absorbedRatePrefix.length ∧
    out.stepPairs.map (fun pair => pair.1.rateSegment) = out.absorbedRatePrefix.dropLast ∧
    (∀ pair ∈ out.stepPairs, pair.1.capacitySegment ≠ pair.2.capacitySegment) ∧
    (∀ pair ∈ out.stepPairs.zip out.stepPairs.tail,
      pair.1.2.capacitySegment = pair.2.1.capacitySegment)

/-- Boolean executable check for `RawBacktrackOutput.paperShapeValid`. -/
private def RawBacktrackOutput.paperShapeValidb
    (out : RawBacktrackOutput (StmtIn := StmtIn) (U := U)) : Bool := by
  classical
  exact decide (RawBacktrackOutput.paperShapeValid (StmtIn := StmtIn) (U := U) out)

/-- CO25 Eq. 6 — `L_δ = ⌈δ / r⌉`: number of rate blocks for the salt. -/
private def Lδ : Nat := Nat.ceil ((δ : ℚ) / SpongeSize.R)

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
    (inputRates outputRates : List (Vector U SpongeSize.R)) : Bool :=
  if SpongeSize.R < δ then
    let inIdx := Lδ (δ := δ) - 1
    let outIdx := Lδ (δ := δ) - 2
    match inputRates[inIdx]?, outputRates[outIdx]? with
    | some inRate, some outRate =>
        rateSuffixEqFrom (U := U) (δ % SpongeSize.R) inRate outRate
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
    (out : RawBacktrackOutput (StmtIn := StmtIn) (U := U)) :
    Option pSpec.ChallengeIdx := by
  let inputRates := out.absorbedRatePrefix
  let outputRates := out.stepPairs.map (fun pair => pair.2.rateSegment)
  let mPlus1 := inputRates.length
  let saltRemainderOk :=
    parserCheckSaltRemainder (U := U) (δ := δ) inputRates outputRates
  if !saltRemainderOk then
    exact none
  else
    let rec scan (remaining : List pSpec.ChallengeIdx) : Option pSpec.ChallengeIdx :=
      match remaining with
      | [] => none
      | i :: rest =>
          let lpBefore := sumMessageBlocksBefore (pSpec := pSpec) i
          let lvBefore := sumChallengeBlocksBefore (pSpec := pSpec) i
          let lPtr := Lδ (δ := δ) + lpBefore + lvBefore
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
    (out : RawBacktrackOutput (StmtIn := StmtIn) (U := U)) : Bool := by
  match
      candidateRoundFromParser
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (δ := δ) out with
  | some parsedRound =>
      exact RawBacktrackOutput.paperShapeValidb (StmtIn := StmtIn) (U := U)
        out
  | none => exact false

-- TODO: duplicate of TraceTransform.lean's local helper. Consider moving to a shared module.
private def vectorOfListExact
    (len : Nat) (xs : List U) : Option (Vector U len) := by
  let ys := xs.take len
  if hLen : ys.length = len then
    exact some ⟨ys.toArray, by simpa using hLen⟩
  else
    exact none

private def encodedMessageAtChallenge
    (out : RawBacktrackOutput (StmtIn := StmtIn) (U := U))
    (i : pSpec.ChallengeIdx) :
    Option (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx)) := by
  match lastMessageBefore? (pSpec := pSpec) i with
  | none =>
      exact none
  | some msgIdx =>
      let lpBefore := sumMessageBlocksBefore (pSpec := pSpec) i
      let lvBefore := sumChallengeBlocksBefore (pSpec := pSpec) i
      let lPtr := Lδ (δ := δ) + lpBefore + lvBefore
      let lpCur := pSpec.Lₚᵢ msgIdx
      let rateBlocks := (out.absorbedRatePrefix.drop lPtr).take lpCur
      let unitBlocks := rateBlocks.foldl (fun acc block => acc ++ block.toList) []
      match vectorOfListExact (U := U) (messageSize msgIdx) unitBlocks with
      | some msgVec => exact some ⟨msgIdx, msgVec⟩
      | none => exact none

private def encodedMessagesUpTo?
    (roundIdx : pSpec.ChallengeIdx)
    (out : RawBacktrackOutput (StmtIn := StmtIn) (U := U)) :
    Option (pSpec.EncodedMessagesUpTo U roundIdx.1.castSucc) :=
  let rec collect
      (rounds : List pSpec.ChallengeIdx) :
      Option (List (Sigma fun msgIdx : pSpec.MessageIdx => Vector U (messageSize msgIdx))) :=
    match rounds with
    | [] => some []
    | j :: rest =>
        match lastMessageBefore? (pSpec := pSpec) j with
        | none => collect rest
        | some _ =>
            match encodedMessageAtChallenge (pSpec := pSpec) (U := U) (δ := δ) out j,
                collect rest with
            | some msg, some msgs => some (msg :: msgs)
            | _, _ => none
  match collect (challengeIdxListUpTo (pSpec := pSpec) roundIdx) with
  | none => none
  | some msgs =>
    some (fun j _ =>
      match msgs.findSome? (fun p => if h : p.1 = j then some (h ▸ p.2) else none) with
      | some vec => vec
      | none => Vector.replicate (messageSize j) (0 : U))

/-- Executable check for the paper branch condition
`∀ ι ≤ i, α̂_ι ∈ Im(φ_ι)` on one parsed `BackTrack` output. -/
def backtrackOutputMessagesInImage
    (inImage : (msgIdx : pSpec.MessageIdx) → Vector U (messageSize msgIdx) → Bool)
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Bool :=
  let before := messageIdxListBefore (pSpec := pSpec) out.roundIdx
  (before.pmap
      (fun j (hmem : j ∈ before) =>
        let hlt := (Finset.mem_filter.mp (Finset.mem_toList.mp hmem)).2
        inImage j (out.encodedMessages j hlt))
      (fun _ hj => hj)).all id

/-- Recover the paper-facing tuple components from a raw internal candidate. -/
private def RawBacktrackOutput.parsedTuple?
    (out : RawBacktrackOutput (StmtIn := StmtIn) (U := U)) :
    Option (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := by
  match
      candidateRoundFromParser
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (δ := δ) out with
  | none =>
      exact none
  | some roundIdx =>
      let allUnits : List U :=
        out.absorbedRatePrefix.foldl (fun acc block => acc ++ block.toList) []
      match vectorOfListExact (U := U) δ allUnits with
      | none => exact none
      | some salt =>
          match encodedMessagesUpTo?
              (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (δ := δ) roundIdx out with
          | none => exact none
          | some encodedMessages =>
              exact some
                { roundIdx := roundIdx
                  stmt := out.stmt
                  salt := salt
                  encodedMessages := encodedMessages }

/-- BackTrack §5.2 Step 1: initialize the input-state list for a candidate chain. -/
private def backtrackStep1Init
    (state : CanonicalSpongeState U)
    (steps : List (CanonicalSpongeState U × CanonicalSpongeState U)) :
    List (CanonicalSpongeState U) :=
  (steps.map Prod.fst) ++ [state]

/-- BackTrack §5.2 Step 2: compute `S_BT(tr, s)` as maximal predecessor chains. -/
private def backtrackStep2ComputeSBT
    [DecidableEq U]
    {T_P : Type}
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔp : T_P)
    (depthBound : Nat)
    (state : CanonicalSpongeState U) :
    BuildBacktrackResult U :=
  buildBacktrackSteps (T_P := T_P) (U := U) trΔp depthBound state

/-- BackTrack §5.2 Step 3: recover candidate statements/salts from `tr_∇.h.outlu`. -/
private def backtrackStep3CandidateSalt
    [DecidableEq StmtIn]
    [DecidableEq U]
    {T_H : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    (trΔh : T_H)
    (state : CanonicalSpongeState U)
    (stepFamilies : List (List (CanonicalSpongeState U × CanonicalSpongeState U))) :
    List (RawBacktrackOutput (StmtIn := StmtIn) (U := U)) :=
  stepFamilies.foldr (fun steps acc =>
    let inputStates := backtrackStep1Init (U := U) state steps
    let outsForSteps :=
      match inputStates.head? with
      | none =>
        -- Unreachable because Step 1 appends `state`.
        []
      | some startState =>
        -- Paper §5.2: `tr_∇.h.outlu(cap)` returns the unique statement, or `⊥`.
        let hashStmts :=
          (TraceTableOps.outlu trΔh startState.capacitySegment).toList
        let absorbedRatePrefix := inputStates.map CanonicalSpongeState.rateSegment
        hashStmts.map fun stmt => ⟨stmt, absorbedRatePrefix, steps⟩
    outsForSteps ++ acc) []

/-- BackTrack §5.2 Step 4: parser checks and assembly of paper output tuples. -/
private def backtrackStep4CandidateMessages
    (rawOuts : List (RawBacktrackOutput (StmtIn := StmtIn) (U := U))) :
    List (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  rawOuts.filterMap fun out =>
    match
        candidateRoundFromParser
          (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (δ := δ) out with
    | some _ =>
        if
            backtrackOutputValidWithParser
              (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (δ := δ) out
        then
          RawBacktrackOutput.parsedTuple?
            (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (δ := δ) out
        else
          none
    | none => none

/-- BackTrack §5.2 Step 5: select the unique tuple, return paper-`none`, or paper-`err`. -/
private def backtrackStep5Select
    (outs : List (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) :
    OptionT Option (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  match outs with
  | [] =>
      -- `none` in the paper.
      failure
  | [out] =>
      return out
  | _ :: _ :: _ =>
      -- More than one valid candidate output: `err` in the paper.
      OptionT.mk none

/-- The backtracking procedure in Section 5.2, which takes in:
- the query-answer trace for the oracle `(h, p, p⁻¹)`
- a state (vector of `N` units)

And returns one of the following:
- `none`
- `err`
- the unique paper tuple `(i, 𝕩, τ, (α̂_1, …, α̂_i))` in `Outs`

Implementation note: this executable surface enforces capacity-chain coherence across recovered
steps, together with Algorithm 1 Item 3/4 parser-level checks (salt remainder, block offsets,
message remainder consistency, and verifier-squeeze window consistency).

TODO: replace the temporary `OptionT Option` carrier with a dedicated result enum once callers need
to distinguish paper-`err` from paper-`none` at the type level. -/
def backTrack [DecidableEq StmtIn] [DecidableEq U] {T_H T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (depthBound : Nat)
    (state : CanonicalSpongeState U) :
    OptionT Option (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  match backtrackStep2ComputeSBT (T_P := T_P) (U := U) trΔ.p depthBound state with
  | .err =>
    -- `err` in the paper.
    OptionT.mk none
  | .ok stepFamilies =>
    let rawOuts :=
      backtrackStep3CandidateSalt
        (StmtIn := StmtIn) (U := U) trΔ.h state stepFamilies
    let outs :=
      backtrackStep4CandidateMessages
        (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) rawOuts
    backtrackStep5Select (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) outs

end

end DuplexSpongeFS.Backtrack
