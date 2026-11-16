/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.Backtrack.Algorithm

/-!
# BackTrack: honest-chain reconstruction

The positive (`.some`) direction of `BackTrack` on chains of the honest shape.
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

/-! ## Honest-chain reconstruction

Public API describing what `backTrack` does on the query-answer chains produced by an *honest*
duplex-sponge execution (`deriveTranscriptDSFS`-style: a statement hash query, then salt
absorb blocks, then per-round prover-message-absorb and verifier message-squeeze blocks, each
permutation query's output capacity feeding the next input capacity).

Consumers: `hyb1_hyb2_indistinguishability`'s verifier-phase per-round query budget
(obligation (V)) and
`hyb3_hyb4_indistinguishability`'s round induction, both of which need to know
that the honest verifier's
`BackTrack` calls never abort, reconstruct exactly the absorbed prefix, and therefore key the
`gᵢ`-query deterministically.

The interface is deliberately phrased over `tr_∇` (`predecessorEntries` / `hashAnchorStmts`)
rather than over the sponge semantics: the scan only ever reads those two lookups, so a consumer
discharges the hypotheses by describing its `tr_∇` tables, and the sponge-level "honest absorb
chain" content lives entirely in the consumer's own invariant. -/

section HonestChainReconstruction

variable {trace : QueryLog (duplexSpongeOracle StmtIn U)}

/-- `predecessorEntries tr_∇ c` — public view of the `BackTrack` scan's Step 2(b) candidate set at
capacity `c`: all distinct `(s_in, s_out)` pairs recorded in `tr_∇.p` whose **output** capacity
segment is `c`. `BackTrack` continues the backwards scan iff this list is a singleton, and
terminates the chain iff it is empty. -/
def predecessorEntries (trΔ : TraceNabla T_H T_P StmtIn U) (cap : Vector U SpongeSize.C) :
    List (CanonicalSpongeState U × CanonicalSpongeState U) :=
  ((TraceTableOps.entries (V := CanonicalSpongeState U) trΔ.p).filterMap fun pair =>
    if pair.2.capacitySegment = cap then some pair else none).dedup

/-- `hashAnchorStmts tr_∇ c` — public view of the `BackTrack` scan's Step 2(c) hash-anchor
candidates at capacity `c`: all statements `𝕩` with `('h', 𝕩, c) ∈ tr_∇.h`.  The scan anchors the
chain iff this list is a singleton. -/
def hashAnchorStmts (trΔ : TraceNabla T_H T_P StmtIn U) (cap : Vector U SpongeSize.C) :
    List StmtIn :=
  ((TraceTableOps.entries (V := Vector U SpongeSize.C) trΔ.h).filterMap fun pair =>
    if pair.2 = cap then some pair.1 else none).dedup

lemma predecessorCandidates_eq_predecessorEntries
    (trΔ : TraceNabla T_H T_P StmtIn U) (cap : Vector U SpongeSize.C) :
    predecessorCandidates (T_H := T_H) (StmtIn := StmtIn) trΔ cap
      = predecessorEntries trΔ cap := rfl

lemma hashAnchorCandidates_eq_hashAnchorStmts
    (trΔ : TraceNabla T_H T_P StmtIn U) (cap : Vector U SpongeSize.C) :
    hashAnchorCandidates (T_P := T_P) trΔ cap = hashAnchorStmts trΔ cap := by
  classical rfl

/-- `HonestScanPrefix tr_∇ 𝕩 rem cur` — the `BackTrack` backwards scan starting at `cur` walks
exactly the pair list `rem` (nearest predecessor first) and anchors at the hash entry of `𝕩`.

This is the reusable shape of an **honest duplex-sponge chain** as `BackTrack` sees it:
`rem = [(s_{m-1}, s_{out,m-1}), …, (s_0, s_{out,0})]` lists the reconstructed permutation steps
from the queried state back to the chain start `s_0`, whose capacity is the one returned by the
statement hash query `h(𝕩)`.

Consumers build this from their own sponge invariant: the honest execution issues
`h(𝕩)` once, then a linear sequence of permutation queries whose output capacity is the
next input capacity, so each `predecessorEntries` lookup along the chain is a singleton and the
lookup at the start is empty. -/
inductive HonestScanPrefix (trΔ : TraceNabla T_H T_P StmtIn U) (stmt : StmtIn) :
    List (CanonicalSpongeState U × CanonicalSpongeState U) → CanonicalSpongeState U → Prop where
  /-- Chain start: no permutation predecessor, and a unique hash anchor carrying `𝕩`. -/
  | anchor {cur : CanonicalSpongeState U}
      (hNoPred : predecessorEntries trΔ cur.capacitySegment = [])
      (hHash : hashAnchorStmts trΔ cur.capacitySegment = [stmt]) :
      HonestScanPrefix trΔ stmt [] cur
  /-- One reconstructed permutation step `(s_in, s_out)` with `s_out.cap = cur.cap`, unique in
  `tr_∇.p` and loop-free (`s_in.cap ≠ s_out.cap`, [CO25, Def 5.3 (e)]). -/
  | step {cur s_in s_out : CanonicalSpongeState U}
      {rem : List (CanonicalSpongeState U × CanonicalSpongeState U)}
      (hPred : predecessorEntries trΔ cur.capacitySegment = [(s_in, s_out)])
      (hNoLoop : s_in.capacitySegment ≠ s_out.capacitySegment)
      (hRest : HonestScanPrefix trΔ stmt rem s_in) :
      HonestScanPrefix trΔ stmt ((s_in, s_out) :: rem) cur

/-- A hash-anchored path in the supplied index, listed nearest predecessor first.
Unlike `HonestScanPrefix`, this mathematical relation requires only membership: it neither
assumes unique lookups nor executes a search. Competing paths and overlapping anchors are allowed.
The forward-first index determines which permutation edges are eligible. -/
inductive AnchoredChain (trΔ : TraceNabla T_H T_P StmtIn U) (stmt : StmtIn) :
    List (CanonicalSpongeState U × CanonicalSpongeState U) → CanonicalSpongeState U → Prop where
  | anchor {cur : CanonicalSpongeState U}
      (hHash : stmt ∈ hashAnchorStmts trΔ cur.capacitySegment) :
      AnchoredChain trΔ stmt [] cur
  | step {cur s_in s_out : CanonicalSpongeState U}
      {rem : List (CanonicalSpongeState U × CanonicalSpongeState U)}
      (hPred : (s_in, s_out) ∈ predecessorEntries trΔ cur.capacitySegment)
      (hNoLoop : s_in.capacitySegment ≠ s_out.capacitySegment)
      (hRest : AnchoredChain trΔ stmt rem s_in) :
      AnchoredChain trΔ stmt ((s_in, s_out) :: rem) cur

/-- The executable scan's stronger certificate supplies an anchored path. -/
lemma HonestScanPrefix.anchoredChain
    {trΔ : TraceNabla T_H T_P StmtIn U} {stmt : StmtIn}
    {rem : List (CanonicalSpongeState U × CanonicalSpongeState U)}
    {state : CanonicalSpongeState U} (h : HonestScanPrefix trΔ stmt rem state) :
    AnchoredChain trΔ stmt rem state := by
  induction h with
  | anchor _ hHash => exact .anchor (by rw [hHash]; simp)
  | step hPred hLoop _ ih => exact .step (by rw [hPred]; simp) hLoop ih

/-- The input-state list `[s_0, …, s_m]` reconstructed by a `HonestScanPrefix rem state`
([CO25, Def 5.3] `inputState`), in paper order (chain start first, queried state last). -/
def HonestScanPrefix.inputStates
    (rem : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (state : CanonicalSpongeState U) : List (CanonicalSpongeState U) :=
  (rem.map Prod.fst).reverse ++ [state]

/-- The output-state list `[s_{out,0}, …, s_{out,m-1}]` reconstructed by a
`HonestScanPrefix rem state` ([CO25, Def 5.3] `outputState`), in paper order. -/
def HonestScanPrefix.outputStates
    (rem : List (CanonicalSpongeState U × CanonicalSpongeState U)) :
    List (CanonicalSpongeState U) :=
  (rem.map Prod.snd).reverse

omit [DecidableEq StmtIn] [DecidableEq U] in
@[simp] lemma HonestScanPrefix.inputStates_length
    (rem : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (state : CanonicalSpongeState U) :
    (HonestScanPrefix.inputStates rem state).length = rem.length + 1 := by
  simp [HonestScanPrefix.inputStates]

omit [DecidableEq StmtIn] [DecidableEq U] in
@[simp] lemma HonestScanPrefix.outputStates_length
    (rem : List (CanonicalSpongeState U × CanonicalSpongeState U)) :
    (HonestScanPrefix.outputStates (U := U) rem).length = rem.length := by
  simp [HonestScanPrefix.outputStates]

omit [SpongeSize] [DecidableEq StmtIn] [DecidableEq U] in
lemma classifyLookup_of_eq_nil {α : Type _} {xs : List α} (h : xs = []) :
    classifyLookup xs = .noMatch := by subst h; rfl

omit [SpongeSize] [DecidableEq StmtIn] [DecidableEq U] in
lemma classifyLookup_of_eq_singleton {α : Type _} {xs : List α} {a : α} (h : xs = [a]) :
    classifyLookup xs = .unique a := by subst h; rfl

/-- The backwards linear scan follows an `HonestScanPrefix` to the end and returns the
reconstructed `BacktrackSequence`, for **any** starting accumulator. -/
lemma linearScanBackwards_done_of_honestScanPrefix
    {trΔ : TraceNabla T_H T_P StmtIn U} (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    {state : CanonicalSpongeState U} {stmt : StmtIn}
    {rem : List (CanonicalSpongeState U × CanonicalSpongeState U)}
    {cur : CanonicalSpongeState U}
    (hchain : HonestScanPrefix trΔ stmt rem cur) :
    ∀ {fuel : ℕ}, rem.length < fuel →
    ∀ {vCap : List (Vector U SpongeSize.C)},
      (∀ p ∈ rem, p.1.capacitySegment ∉ vCap) →
      (rem.map fun p => p.1.capacitySegment).Nodup →
    ∀ acc : PartialBacktrackSequence trace cur state,
      ∃ seq : BacktrackSequence trace state,
        linearScanBackwards trace trΔ h_trΔ fuel cur state vCap acc = .done seq ∧
        seq.stmt = stmt ∧
        seq.inputState = (rem.map Prod.fst).reverse ++ acc.inputState ∧
        seq.outputState = (rem.map Prod.snd).reverse ++ acc.outputState := by
  induction hchain with
  | @anchor cur hNoPred hHash =>
      intro fuel hfuel vCap _ _ acc
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hcp : classifyLookup (predecessorCandidates (T_H := T_H) trΔ cur.capacitySegment)
          = .noMatch :=
        classifyLookup_of_eq_nil
          (by rw [predecessorCandidates_eq_predecessorEntries]; exact hNoPred)
      have hch : classifyLookup (hashAnchorCandidates (T_P := T_P) trΔ cur.capacitySegment)
          = .unique stmt :=
        classifyLookup_of_eq_singleton
          (by rw [hashAnchorCandidates_eq_hashAnchorStmts]; exact hHash)
      simp only [linearScanBackwards]
      split <;> rename_i heq <;> rw [hcp] at heq <;> cases heq
      split <;> rename_i heq <;> rw [hch] at heq <;> cases heq
      exact ⟨_, rfl, rfl, by simp [completeBacktrackSequence],
        by simp [completeBacktrackSequence]⟩
  | @step cur s_in s_out rem hPred hNoLoop hRest ih =>
      intro fuel hfuel vCap hFresh hNodup acc
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hcp : classifyLookup (predecessorCandidates (T_H := T_H) trΔ cur.capacitySegment)
          = .unique (s_in, s_out) :=
        classifyLookup_of_eq_singleton
          (by rw [predecessorCandidates_eq_predecessorEntries]; exact hPred)
      have hmem : s_in.capacitySegment ∉ vCap := hFresh (s_in, s_out) (List.mem_cons_self ..)
      have hNodupCons :
          (s_in.capacitySegment :: rem.map fun p => p.1.capacitySegment).Nodup := by
        exact hNodup
      have hNodup' : (rem.map fun p => p.1.capacitySegment).Nodup := hNodupCons.of_cons
      have hFresh' : ∀ p ∈ rem, p.1.capacitySegment ∉ s_in.capacitySegment :: vCap := by
        intro p hp hmem'
        rcases List.mem_cons.mp hmem' with h | h
        · exact (List.nodup_cons.mp hNodupCons).1
            (h ▸ List.mem_map_of_mem (f := fun p => p.1.capacitySegment) hp)
        · exact hFresh p (List.mem_cons_of_mem _ hp) h
      have hfuel' : rem.length < fuel' := by simp only [List.length_cons] at hfuel; omega
      simp only [linearScanBackwards]
      split <;> rename_i heq <;> rw [hcp] at heq <;> cases heq
      simp only [dite_eq_right hNoLoop, ite_eq_right hmem]
      obtain ⟨seq, h1, h2, h3, h4⟩ := ih hfuel' hFresh' hNodup' _
      exact ⟨seq, h1, h2, by rw [h3]; simp [prependPartialSequence],
        by rw [h4]; simp [prependPartialSequence]⟩

/-- Top-level form of `linearScanBackwards_done_of_honestScanPrefix`: the scan `backTrack` actually
runs (start state `= target state`, empty accumulator, `vCap = [state.cap]`) reconstructs the chain
`rem` in full. -/
lemma linearScanBackwards_top_of_honestScanPrefix
    {trΔ : TraceNabla T_H T_P StmtIn U} (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    {state : CanonicalSpongeState U} {stmt : StmtIn}
    {rem : List (CanonicalSpongeState U × CanonicalSpongeState U)}
    (hchain : HonestScanPrefix trΔ stmt rem state)
    {depthBound : ℕ} (hfuel : rem.length < depthBound)
    (hFresh : ∀ p ∈ rem, p.1.capacitySegment ≠ state.capacitySegment)
    (hNodup : (rem.map fun p => p.1.capacitySegment).Nodup) :
    ∃ seq : BacktrackSequence trace state,
      linearScanBackwards trace trΔ h_trΔ depthBound state state [state.capacitySegment]
          (emptyPartialSequence trace state) = .done seq ∧
      seq.stmt = stmt ∧
      seq.inputState = HonestScanPrefix.inputStates rem state ∧
      seq.outputState = HonestScanPrefix.outputStates rem := by
  obtain ⟨seq, h1, h2, h3, h4⟩ :=
    linearScanBackwards_done_of_honestScanPrefix h_trΔ hchain hfuel
      (vCap := [state.capacitySegment])
      (fun p hp hmem => hFresh p hp (List.mem_singleton.mp hmem)) hNodup
      (emptyPartialSequence trace state)
  refine ⟨seq, h1, h2, ?_, ?_⟩
  · rw [h3]; simp [HonestScanPrefix.inputStates, emptyPartialSequence]
  · rw [h4]; simp [HonestScanPrefix.outputStates, emptyPartialSequence]

/-- Once the backwards scan has succeeded with `seq`, `backTrack` is exactly the Step-3 salt
extraction followed by the Step-4 round parse of `seq`. -/
lemma backTrack_eq_of_scan_done
    {trΔ : TraceNabla T_H T_P StmtIn U} {h_trΔ : trΔ.IsSubsetOfQueryLog trace}
    {state : CanonicalSpongeState U} {depthBound : ℕ}
    {seq : BacktrackSequence trace state}
    (hscan : linearScanBackwards trace trΔ h_trΔ depthBound state state [state.capacitySegment]
      (emptyPartialSequence trace state) = .done seq) :
    backTrack (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound =
      (match seq.constructCandidateSalt (δ := δ) with
        | none => ExperimentOutput.noResult
        | some salt =>
          match BacktrackSequence.extractCandidate (pSpec := pSpec) (δ := δ)
              state trace seq salt with
          | none => ExperimentOutput.noResult
          | some out => ExperimentOutput.some out) := by
  unfold backTrack linearBackTrack
  rw [hscan]
  rfl

/-- **Honest chains never make `BackTrack` abort.**

[CO25, §5.4 Item 4(b)] turns `BackTrack = err` into an abort of `D2SQuery`; on a chain of the honest
shape the scan finds a unique predecessor at every step and a unique hash anchor at the start, so
no scan-time fork is ever detected.  Consumers (`hyb1_hyb2_indistinguishability` (V),
`hyb3_hyb4_indistinguishability`) use
this to rule out the abort branch of `d2sQueryStep` along the honest verifier walk.

This is *independent* of [CO25, Claim 5.19] (`AbortAnalysis.lean`, not yet formalized): it is a
deterministic statement about one `tr_∇`, not a probability bound. -/
theorem backTrack_ne_err_of_honestScanPrefix
    {trΔ : TraceNabla T_H T_P StmtIn U} (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    {state : CanonicalSpongeState U} {stmt : StmtIn}
    {rem : List (CanonicalSpongeState U × CanonicalSpongeState U)}
    (hchain : HonestScanPrefix trΔ stmt rem state)
    {depthBound : ℕ} (hfuel : rem.length < depthBound)
    (hFresh : ∀ p ∈ rem, p.1.capacitySegment ≠ state.capacitySegment)
    (hNodup : (rem.map fun p => p.1.capacitySegment).Nodup) :
    backTrack (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound ≠ .err := by
  obtain ⟨seq, hscan, _, _, _⟩ :=
    linearScanBackwards_top_of_honestScanPrefix h_trΔ hchain hfuel hFresh hNodup
  rw [backTrack_eq_of_scan_done (pSpec := pSpec) (δ := δ) hscan]
  split
  · simp
  · split <;> simp

/-! ### Vocabulary for the Step 4(a) round parse

`exactFitBlocks i` is the chain length `BackTrack`'s Step 4(a).iii.D compares against `m_k + 1`;
it, `blockOffset`, `roundProverMessageCursor`, `roundEndBlock`, `roundEndCursor` and
`roundSqueezeInnerCalls` are defined up in `section SpongeWalkVocabulary`, since
`extractCandidate` itself is phrased in them.  They are public so that consumers can *state* the
round hypotheses of the `extractCandidate` characterization without reaching into this file. -/

-- `ForInStep.value` extracts the payload of a `ForInStep`, whichever branch it took.

omit [SpongeSize] [DecidableEq StmtIn] [DecidableEq U] in
/-- Loop-invariant principle for `Id`-monad `for` loops over a list: a predicate preserved by
every step (whether the step `yield`s or is `done`) holds of the loop's final accumulator. -/
lemma forIn_id_invariant {α β : Type} (P : β → Prop) (f : α → β → Id (ForInStep β))
    (l : List α) (hstep : ∀ a ∈ l, ∀ b, P b → P (ForInStep.value (f a b))) :
    ∀ b : β, P b → P (forIn l b f) := by
  intro b hb
  rw [List.forIn_eq_foldlM]
  change P (ForInStep.value (Id.run _))
  rw [List.idRun_foldlM]
  apply List.foldlRecOn (motive := fun state : ForInStep β => P state.value)
    (b := ForInStep.yield b) l _ hb
  intro state hs a ha
  cases state with
  | done state => exact hs
  | yield state => exact hstep a ha state hs

/-! ### The Step 4(a) loop body as a plain function

`extractCandidate`'s `for` loop body, normalized into three proof-support functions so that
proofs can rewrite it one branch point at a time. The executable specification and its
step-by-step inline comments remain in `Algorithm`. `extractCandidate_eq_forIn` identifies
the loop with this body (by `rfl`). -/

/-- Accumulator of the Step 4(a) loop: the encoded messages assembled so far. -/
abbrev StepAcc (pSpec : ProtocolSpec n) (U : Type) [SpongeUnit U] [HasProverMessageSize pSpec] :=
  List ((msgIdx : pSpec.MessageIdx) × Vector U (proverMessageSize msgIdx))

/-- Loop state of the Step 4(a) loop: the early-return slot and the accumulator. -/
abbrev StepState (δ : Nat) (StmtIn : Type) (pSpec : ProtocolSpec n) (U : Type) [SpongeUnit U]
    [HasProverMessageSize pSpec] :=
  Option (Option (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) ×
    StepAcc pSpec U

/-- Step 4(a).iii.D–F of round `i`, after the message has been assembled into `acc`. -/
def extractStepTail {state : CanonicalSpongeState U} (seq : BacktrackSequence trace state)
    (salt : Vector U δ) (i : pSpec.ChallengeIdx) (acc : StepAcc pSpec U) :
    ForInStep (StepState δ StmtIn pSpec U) :=
  if (exactFitBlocks (δ := δ) i == seq.inputState.length) = true then
    if candidateProverMessagesPresent acc i then
      .done (some (some { roundIdx := i, stmt := seq.stmt, salt := salt,
                          encodedProverMessages := candidateProverMessages acc i }), acc)
    else .done (some none, acc)
  else if roundSqueezeEndBlock (δ := δ) i < seq.inputState.length then
    if (!seq.checkSqueezeWindow (roundEndBlock (δ := δ) i)
        (roundSqueezeInnerCalls (δ := δ) i)) = true then
      .done (some none, acc)
    else .yield (none, acc)
  else .done (some none, acc)

/-- Step 4(a).iii.B/C of round `i` (the remainder checks), followed by `extractStepTail`. -/
def extractStepRemainder {state : CanonicalSpongeState U} (seq : BacktrackSequence trace state)
    (salt : Vector U δ) (i : pSpec.ChallengeIdx) (acc : StepAcc pSpec U) :
    ForInStep (StepState δ StmtIn pSpec U) :=
  if roundHasAbsorbBoundary (pSpec := pSpec) i ∧ roundEndCursor (δ := δ) i ≠ SpongeSize.R then
    if h : roundEndBlock (δ := δ) i < seq.inputState.length ∧ 0 < roundEndBlock (δ := δ) i ∧
        roundEndBlock (δ := δ) i - 1 < seq.outputState.length then
      if (seq.inputState.get ⟨roundEndBlock (δ := δ) i, h.1⟩).rateSegment.toList.drop
            (roundEndCursor (δ := δ) i) ≠
          (seq.outputState.get ⟨roundEndBlock (δ := δ) i - 1, h.2.2⟩).rateSegment.toList.drop
            (roundEndCursor (δ := δ) i) then
        .done (some none, acc)
      else extractStepTail seq salt i acc
    else if h : roundEndBlock (δ := δ) i = 0 ∧ 0 < seq.inputState.length then
      if (seq.inputState.get ⟨0, h.2⟩).rateSegment.toList.drop (roundEndCursor (δ := δ) i) ≠
          List.replicate (SpongeSize.R - roundEndCursor (δ := δ) i) (0 : U) then
        .done (some none, acc)
      else extractStepTail seq salt i acc
    else extractStepTail seq salt i acc
  else extractStepTail seq salt i acc

/-- The whole Step 4(a) loop body at round `i`. -/
def extractStep {state : CanonicalSpongeState U} (seq : BacktrackSequence trace state)
    (salt : Vector U δ) (i : pSpec.ChallengeIdx) (acc : StepAcc pSpec U) :
    ForInStep (StepState δ StmtIn pSpec U) :=
  if exactFitBlocks (δ := δ) i > seq.inputState.length then .done (some none, acc)
  else
    match lastProverMessageBefore? (pSpec := pSpec) i with
    | some msgIdx =>
      match seq.assembleEncodedProverMessage (blockOffset (δ := δ) i)
          (roundProverMessageCursor (δ := δ) i) msgIdx with
      | some v => extractStepRemainder seq salt i (acc ++ [⟨msgIdx, v⟩])
      | none => .done (some none, acc)
    | none => extractStepRemainder seq salt i acc

omit [DecidableEq StmtIn] in
/-- `extractCandidate` is the `for` loop over `extractStep`. -/
lemma extractCandidate_eq_forIn {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) (salt : Vector U δ) :
    BacktrackSequence.extractCandidate (pSpec := pSpec) (δ := δ) state trace seq salt =
      Break.runK (forIn (m := Id) (verifierMessageIdxList (pSpec := pSpec))
          ((none, []) : StepState δ StmtIn pSpec U)
          (fun i r => extractStep seq salt i r.2)).1
        (fun _ => none) (fun a => a) := rfl

omit [DecidableEq StmtIn] in
/-- A tuple produced by the Step 4(a).iii.D–F tail is the round's own exact-fit tuple. -/
lemma extractStepTail_spec {state : CanonicalSpongeState U}
    {seq : BacktrackSequence trace state} {salt : Vector U δ} {i : pSpec.ChallengeIdx}
    {acc : StepAcc pSpec U}
    {o : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (h : (ForInStep.value (extractStepTail seq salt i acc)).1 = some (some o)) :
    o.roundIdx = i ∧ o.stmt = seq.stmt ∧ o.salt = salt ∧
      exactFitBlocks (δ := δ) i = seq.inputState.length := by
  unfold extractStepTail at h
  split_ifs at h with h1 <;> cases h
  exact ⟨rfl, rfl, rfl, beq_iff_eq.mp h1⟩

omit [DecidableEq StmtIn] in
/-- `extractStepTail_spec`, through the Step 4(a).iii.B/C remainder checks. -/
lemma extractStepRemainder_spec {state : CanonicalSpongeState U}
    {seq : BacktrackSequence trace state} {salt : Vector U δ} {i : pSpec.ChallengeIdx}
    {acc : StepAcc pSpec U}
    {o : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (h : (ForInStep.value (extractStepRemainder seq salt i acc)).1 = some (some o)) :
    o.roundIdx = i ∧ o.stmt = seq.stmt ∧ o.salt = salt ∧
      exactFitBlocks (δ := δ) i = seq.inputState.length := by
  unfold extractStepRemainder at h
  split_ifs at h
  all_goals first | cases h | exact extractStepTail_spec h

omit [DecidableEq StmtIn] in
/-- A tuple produced by the Step 4(a) loop body at round `i` is round `i`'s exact-fit tuple. -/
lemma extractStep_spec {state : CanonicalSpongeState U}
    {seq : BacktrackSequence trace state} {salt : Vector U δ} {i : pSpec.ChallengeIdx}
    {acc : StepAcc pSpec U}
    {o : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (h : (ForInStep.value (extractStep seq salt i acc)).1 = some (some o)) :
    o.roundIdx = i ∧ o.stmt = seq.stmt ∧ o.salt = salt ∧
      exactFitBlocks (δ := δ) i = seq.inputState.length := by
  unfold extractStep at h
  repeat' split at h
  all_goals first | cases h | exact extractStepRemainder_spec h

omit [DecidableEq StmtIn] in
lemma extractCandidate_spec
    {state : CanonicalSpongeState U} (seq : BacktrackSequence trace state)
    (salt : Vector U δ)
    {out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (h : BacktrackSequence.extractCandidate (pSpec := pSpec) (δ := δ) state trace seq salt
      = some out) :
    out.roundIdx ∈ verifierMessageIdxList (pSpec := pSpec) ∧ out.stmt = seq.stmt ∧ out.salt = salt ∧
      exactFitBlocks (δ := δ) out.roundIdx = seq.inputState.length := by
  revert h
  rw [extractCandidate_eq_forIn]
  refine forIn_id_invariant
    (P := fun r : StepState δ StmtIn pSpec U =>
      Break.runK r.1 (fun _ => none) (fun a => a) = some out →
        out.roundIdx ∈ verifierMessageIdxList (pSpec := pSpec) ∧ out.stmt = seq.stmt ∧
          out.salt = salt ∧
          exactFitBlocks (δ := δ) out.roundIdx = seq.inputState.length)
    _ _ ?_ _ ?_
  · intro i hi r _ hcon
    rcases hv : (ForInStep.value (extractStep seq salt i r.2)).1 with _ | _ | o
    · rw [hv] at hcon; cases hcon
    · rw [hv] at hcon; cases hcon
    · rw [hv] at hcon
      cases hcon
      obtain ⟨h1, h2, h3, h4⟩ := extractStep_spec hv
      subst h1
      exact ⟨hi, h2, h3, h4⟩
  · intro hcon; cases hcon

/-- **What a successful `BackTrack` reports on an honest chain.**

If `BackTrack` succeeds on a chain of the honest shape then the tuple it returns carries the
chain's own anchoring statement, its round index is a verifier message index of the protocol, and
that round index is pinned by the *chain length*: `exactFitBlocks i = m_k + 1`.

Consumer `hyb1_hyb2_indistinguishability` (V): the Item 4(e)i `gᵢ`-query key of the honest
verifier walk therefore has
a round index determined by how many permutation queries have happened so far — which is what
makes the per-round charging of one fresh verifier message-slot query legitimate.

Consumer `hyb3_hyb4_indistinguishability`: this identifies the reported
round with the round the
honest schedule is in. -/
theorem backTrack_some_spec_of_honestScanPrefix
    {trΔ : TraceNabla T_H T_P StmtIn U} (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    {state : CanonicalSpongeState U} {stmt : StmtIn}
    {rem : List (CanonicalSpongeState U × CanonicalSpongeState U)}
    (hchain : HonestScanPrefix trΔ stmt rem state)
    {depthBound : ℕ} (hfuel : rem.length < depthBound)
    (hFresh : ∀ p ∈ rem, p.1.capacitySegment ≠ state.capacitySegment)
    (hNodup : (rem.map fun p => p.1.capacitySegment).Nodup)
    {out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hout : backTrack (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound
      = .some out) :
    out.stmt = stmt ∧ out.roundIdx ∈ verifierMessageIdxList (pSpec := pSpec) ∧
      exactFitBlocks (δ := δ) out.roundIdx = rem.length + 1 := by
  obtain ⟨seq, hscan, hs, hin, _⟩ :=
    linearScanBackwards_top_of_honestScanPrefix h_trΔ hchain hfuel hFresh hNodup
  rw [backTrack_eq_of_scan_done (pSpec := pSpec) (δ := δ) hscan] at hout
  split at hout
  · exact absurd hout (by simp)
  · rename_i salt _
    split at hout
    · exact absurd hout (by simp)
    · rename_i o hext
      simp only [ExperimentOutput.some.injEq] at hout
      subst hout
      obtain ⟨hmem, hstmt, _, hfit⟩ := extractCandidate_spec (δ := δ) seq salt hext
      refine ⟨by rw [hstmt, hs], hmem, ?_⟩
      rw [hfit, hin, HonestScanPrefix.inputStates_length]

/-- **`BackTrack` returns `noResult` at absorb positions.**

If the honest chain's length matches *no* round's exact-fit block count — which is exactly the
situation at a salt-absorb block or at a message-absorb block strictly inside a round's window —
then `BackTrack` returns `noResult`: not `err` (`backTrack_ne_err_of_honestScanPrefix`) and not
`some` (`backTrack_some_spec_of_honestScanPrefix` pins any success to a fitting round).

Consumers: `hyb1_hyb2_indistinguishability` (V) and
`hyb3_hyb4_indistinguishability` both need "absorb-position
permutation queries issue no `gᵢ`-query"; via [CO25, Item 4(c)] that is precisely this
`noResult`. -/
theorem backTrack_eq_noResult_of_honestScanPrefix
    {trΔ : TraceNabla T_H T_P StmtIn U} (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    {state : CanonicalSpongeState U} {stmt : StmtIn}
    {rem : List (CanonicalSpongeState U × CanonicalSpongeState U)}
    (hchain : HonestScanPrefix trΔ stmt rem state)
    {depthBound : ℕ} (hfuel : rem.length < depthBound)
    (hFresh : ∀ p ∈ rem, p.1.capacitySegment ≠ state.capacitySegment)
    (hNodup : (rem.map fun p => p.1.capacitySegment).Nodup)
    (hno : ∀ i ∈ verifierMessageIdxList (pSpec := pSpec),
      exactFitBlocks (δ := δ) i ≠ rem.length + 1) :
    backTrack (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound = .noResult := by
  rcases hbt : backTrack (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound with
    _ | _ | out
  · exact absurd hbt (backTrack_ne_err_of_honestScanPrefix h_trΔ hchain hfuel hFresh hNodup)
  · rfl
  · obtain ⟨_, hmem, hfit⟩ :=
      backTrack_some_spec_of_honestScanPrefix h_trΔ hchain hfuel hFresh hNodup hbt
    exact absurd hfit (hno _ hmem)

-- The private leaf lemmas below deliberately reuse the section-wide variable context; per-site
-- `omit` trimming would only add noise.  The `all_goals first | … | …` branch-closing chains
-- necessarily contain alternatives that are no-ops on some branches.

/-! ### The Step 4(a) round obligations and the positive (`.some`) direction

The per-round vocabulary (`exactFitBlocks`, `blockOffset`, `roundProverMessageCursor`,
`roundProverMessageChars`, `roundEndBlock`, `roundEndCursor`, `roundSqueezeEndBlock`,
`roundSqueezeInnerCalls`, `chainProverMessageWindowUnits`) lives in `section SpongeWalkVocabulary`
above.  `RoundPassesThrough` / `RoundExactFit` below bundle the obligations a consumer discharges
from its own sponge invariant. -/

omit [DecidableEq StmtIn] [DecidableEq U] [SpongeUnit U] [SpongeSize] in
lemma foldl_append_eq_flatMap {β : Type} (f : β → List U) (xs : List β) (acc : List U) :
    xs.foldl (fun acc s => acc ++ f s) acc = acc ++ xs.flatMap f := by
  simpa only [List.flatMap_def] using List.foldl_append_eq_append (l := xs) (f := f)

omit [DecidableEq StmtIn] [DecidableEq U] in
lemma rateUnitsOf_eq_chainRateUnits (xs : List (CanonicalSpongeState U)) :
    rateUnitsOf (U := U) xs = chainRateUnits xs := by
  simpa [rateUnitsOf, chainRateUnits] using
    foldl_append_eq_flatMap (U := U) (fun s => s.rateSegment.toList) xs []

omit [DecidableEq StmtIn] [DecidableEq U] [SpongeUnit U] [SpongeSize] in
lemma vectorOfListExact_isSome {len : Nat} {xs : List U} (h : len ≤ xs.length) :
    ∃ p, vectorOfListExact (U := U) len xs = some p := by
  have hlen : (xs.take len).length = len := by simp [Nat.min_eq_left h]
  unfold vectorOfListExact
  rw [dite_eq_left hlen]
  exact ⟨_, rfl⟩

omit [DecidableEq StmtIn] [DecidableEq U] [SpongeUnit U] [SpongeSize] in
/-- Value-level companion of `vectorOfListExact_isSome`: whenever the slice succeeds, the vector it
returns is literally the first `len` entries of the source list. -/
lemma vectorOfListExact_toList {len : Nat} {xs : List U}
    {p : { _v : Vector U len // len ≤ xs.length }}
    (h : vectorOfListExact (U := U) len xs = some p) : p.1.toList = xs.take len := by
  dsimp only [vectorOfListExact] at h
  split at h
  · cases h; rfl
  · simp at h

omit [DecidableEq StmtIn] [HasVerifierMessageSize pSpec] [DecidableEq U] in
lemma assembleEncodedProverMessage_isSome
    {state : CanonicalSpongeState U} {seq : BacktrackSequence trace state}
    {b cA : Nat} {msgIdx : pSpec.MessageIdx}
    (h : proverMessageSize msgIdx
      ≤ (chainProverMessageWindowUnits seq.inputState b cA (proverMessageSize msgIdx)).length) :
    ∃ v, seq.assembleEncodedProverMessage (pSpec := pSpec) b cA msgIdx = some v := by
  have h' : proverMessageSize msgIdx ≤ (chainUnitsFrom (U := U) seq.inputState b cA).length := by
    rw [chainProverMessageWindowUnits_length] at h
    rw [chainUnitsFrom_length]
    omega
  obtain ⟨p, hp⟩ := vectorOfListExact_isSome (U := U) h'
  simp only [BacktrackSequence.assembleEncodedProverMessage, hp]
  exact ⟨_, rfl⟩

omit [DecidableEq StmtIn] in
private lemma checkSqueezeWindow_eq_all {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) (start count : ℕ) :
    BacktrackSequence.checkSqueezeWindow seq start count = (List.range count).all (fun k =>
      match seq.outputState[start + k]?, seq.inputState[start + 1 + k]? with
      | some sOut, some sIn => decide (sOut.rateSegment = sIn.rateSegment)
      | _, _ => false) := by
  let test := fun k =>
    match seq.outputState[start + k]?, seq.inputState[start + 1 + k]? with
    | some sOut, some sIn => decide (sOut.rateSegment = sIn.rateSegment)
    | _, _ => false
  unfold BacktrackSequence.checkSqueezeWindow
  change (forIn (m := Id) (List.range count) true _) = _
  calc
    _ = (forIn (m := Id) (List.range count) true
        (fun k ok => pure (ForInStep.yield (ok && test k)))) := by
      congr 1
      funext k ok
      dsimp [test]
      split
      · rename_i sOut sIn hOut hIn
        by_cases h : sOut.rateSegment = sIn.rateSegment <;> simp_all
      · simp
    _ = _ := by
      rw [List.forIn_pure_yield_eq_foldl]
      change (List.range count).foldl (fun ok k => ok && test k) true = _
      have fold : ∀ (xs : List ℕ) (ok : Bool),
          xs.foldl (fun ok k => ok && test k) ok = (ok && xs.all test) := by
        intro xs
        induction xs with
        | nil => simp
        | cons k xs ih => intro ok; simp only [List.foldl_cons, ih, List.all_cons, Bool.and_assoc]
      exact fold _ true

omit [DecidableEq StmtIn] in
/-- Exact certificate for a passing squeeze window, including both lookup failures. -/
lemma checkSqueezeWindow_eq_true_iff {state : CanonicalSpongeState U}
    (seq : BacktrackSequence trace state) (start count : ℕ) :
    BacktrackSequence.checkSqueezeWindow seq start count = true ↔
      ∀ k < count, ∃ sOut sIn, seq.outputState[start + k]? = some sOut ∧
        seq.inputState[start + 1 + k]? = some sIn ∧ sOut.rateSegment = sIn.rateSegment := by
  rw [checkSqueezeWindow_eq_all, List.all_eq_true]
  simp only [List.mem_range]
  apply forall_congr'
  intro k
  apply imp_congr_right
  intro _
  rcases hOut : seq.outputState[start + k]? with _ | sOut <;>
    rcases hIn : seq.inputState[start + 1 + k]? with _ | sIn <;> simp_all

omit [DecidableEq StmtIn] in
lemma checkSqueezeWindow_eq_true
    {state : CanonicalSpongeState U} (seq : BacktrackSequence trace state)
    (squeezeStart lvCur : Nat)
    (h : ∀ k < lvCur, ∃ sOut sIn, seq.outputState[squeezeStart + k]? = some sOut ∧
      seq.inputState[squeezeStart + 1 + k]? = some sIn ∧ sOut.rateSegment = sIn.rateSegment) :
    seq.checkSqueezeWindow squeezeStart lvCur = true :=
  (checkSqueezeWindow_eq_true_iff seq squeezeStart lvCur).mpr h

omit [DecidableEq StmtIn] [DecidableEq U] in
lemma constructCandidateSalt_isSome
    {state : CanonicalSpongeState U} {seq : BacktrackSequence trace state}
    (hlen : δ ≤ (chainRateUnits seq.inputState).length) :
    ∃ salt, seq.constructCandidateSalt (δ := δ) = some salt := by
  have hlen' : δ ≤ seq.rateUnits.length := by
    have : seq.rateUnits = chainRateUnits seq.inputState :=
      rateUnitsOf_eq_chainRateUnits (U := U) seq.inputState
    rw [this]; exact hlen
  obtain ⟨⟨sv, hsv⟩, hp⟩ := vectorOfListExact_isSome (U := U) hlen'
  unfold BacktrackSequence.constructCandidateSalt
  -- `Option`-monad bind on a `some` is application.
  rw [hp]
  exact ⟨_, rfl⟩

omit [DecidableEq StmtIn] [DecidableEq U] in
/-- Value-level companion of `constructCandidateSalt_isSome` [CO25, §5.2 Step 3]: the
reconstructed salt is exactly the first `δ` rate units of the chain. -/
lemma constructCandidateSalt_toList
    {state : CanonicalSpongeState U} {seq : BacktrackSequence trace state} {s : Vector U δ}
    (h : seq.constructCandidateSalt (δ := δ) = some s) :
    s.toList = (chainRateUnits seq.inputState).take δ := by
  unfold BacktrackSequence.constructCandidateSalt at h
  rcases hp : vectorOfListExact (U := U) δ seq.rateUnits with _ | p
  · rw [hp] at h; simp at h
  · rw [hp] at h
    have hs : p.1 = s := by simpa using h
    rw [← hs, vectorOfListExact_toList hp, BacktrackSequence.rateUnits,
      rateUnitsOf_eq_chainRateUnits]

omit [DecidableEq StmtIn] [HasVerifierMessageSize pSpec] [DecidableEq U] in
/-- Value-level companion of `assembleEncodedProverMessage_isSome` [CO25, §5.2 Step 4(a)iii.A]: the
assembled message is literally the chain's round-`i` message window. -/
lemma assembleEncodedProverMessage_toList
    {state : CanonicalSpongeState U} {seq : BacktrackSequence trace state}
    {b cA : Nat} {msgIdx : pSpec.MessageIdx} {v : Vector U (proverMessageSize msgIdx)}
    (h : seq.assembleEncodedProverMessage (pSpec := pSpec) b cA msgIdx = some v) :
    v.toList = chainProverMessageWindowUnits seq.inputState b cA (proverMessageSize msgIdx) := by
  unfold BacktrackSequence.assembleEncodedProverMessage at h
  rcases hp : vectorOfListExact (U := U) (proverMessageSize msgIdx)
      (chainUnitsFrom seq.inputState b cA) with _ | p
  · rw [hp] at h; simp at h
  · rw [hp] at h
    have hs : p.1 = v := by simpa using h
    rw [← hs, vectorOfListExact_toList hp, chainProverMessageWindowUnits]

/-- Step 4(a).i positions depend on the verifier message round only through
`lastProverMessageBefore?`: two verifier message rounds whose last preceding prover message is the
same read the *same* chain window. -/
lemma blockOffset_roundProverMessageCursor_eq_of_lastProverMessageBefore
    {x : pSpec.ChallengeIdx} {j : pSpec.MessageIdx}
    (h : lastProverMessageBefore? (pSpec := pSpec) x = some j) :
    blockOffset (δ := δ) x = (walkPos (pSpec := pSpec) δ j.1.castSucc).1 ∧
      roundProverMessageCursor (δ := δ) x = (walkPos (pSpec := pSpec) δ j.1.castSucc).2.1 := by
  unfold blockOffset roundProverMessageCursor roundProverMessageWindowStart
  rw [h]
  exact ⟨rfl, rfl⟩

omit [SpongeSize] [DecidableEq StmtIn] [DecidableEq U] in
/-- **Deliverable 2** — evaluation principle for an `Id`-monad `for` loop that `yield`s through a
prefix and is `done` at the next element, threading an invariant forward.

`I l c` reads "the loop has consumed exactly the elements `l` and its accumulator is `c`".  Besides
recording that the prefix never fires `done`, this version carries `I` into the `done` step, so
`P` may talk about the accumulator the prefix built. -/
lemma forIn_id_prefix_done_inv {α β : Type} (P : β → Prop)
    (f : α → β → Id (ForInStep β)) (a : α) (post : List α) (pre : List α) :
    ∀ (I : List α → β → Prop) (b : β), I [] b →
      (∀ (l : List α) (x : α), l ++ [x] <+: pre → ∀ c, I l c →
        ∃ c', f x c = ForInStep.yield c' ∧ I (l ++ [x]) c') →
      (∀ c c', I pre c → f a c = ForInStep.yield c' → False) →
      (∀ c c', I pre c → f a c = ForInStep.done c' → P c') →
      P (forIn (pre ++ a :: post) b f) := by
  induction pre with
  | nil =>
      intro I b hb _ hd hP
      rw [List.nil_append, List.forIn_cons]
      cases hf : f a b with
      | done b' => exact hP b b' hb hf
      | yield b' => exact (hd b b' hb hf).elim
  | cons x l ih =>
      intro I b hb hstep hd hP
      rw [List.cons_append, List.forIn_cons]
      obtain ⟨b', hf, hI'⟩ := hstep [] x (by simp) b hb
      have hgoal := ih (fun m c => I (x :: m) c) b' hI'
        (fun m y hm c hc => hstep (x :: m) y (List.cons_prefix_cons.mpr ⟨rfl, hm⟩) c hc)
        hd hP
      rw [hf]
      exact hgoal

/-- **[CO25, §5.2]** BackTrack Step 4(a) obligations for a verifier message round the parse loop
must
**pass through**: the guard holds, the prover-message window assembles, the B/C remainder check does
not fire, the round is not the exact-fit round, and the round's squeeze window fits and is
consistent.

All positions are the corrected unit-level ones of `section SpongeWalkVocabulary`. -/
structure RoundPassesThrough (inputs outputs : List (CanonicalSpongeState U))
    (i : pSpec.ChallengeIdx) : Prop where
  /-- Step 4(a).ii guard `exactFitBlocks(i) ≤ m_k + 1`. -/
  guard : exactFitBlocks (δ := δ) i ≤ inputs.length
  /-- Step 4(a).iii.A: the round-`i` message window has at least `ℓ_P(i)` characters. -/
  assemble : ∀ msgIdx, lastProverMessageBefore? (pSpec := pSpec) i = some msgIdx →
    proverMessageSize msgIdx ≤ (chainProverMessageWindowUnits inputs (blockOffset (δ := δ) i)
      (roundProverMessageCursor (δ := δ) i) (proverMessageSize msgIdx)).length
  /-- Step 4(a).iii.B/C remainder consistency (vacuous when the message's last block is full).

  The `h₀ : 0 < roundEndBlock i` guard mirrors the `0 < endBlock` conjunct of
  `BacktrackSequence.extractCandidate`'s `h_bounds` branch: in `ℕ`, `0 - 1 = 0`, so without it the
  field would demand `inputs[0] ~ outputs[0]` at `roundEndBlock i = 0` — an input state and the
  output state of the *same* permutation call, which no honest chain satisfies.  The `b = 0` case
  is handled by `zeroRemainder` instead, exactly as the code's `h_zero` branch does. -/
  remainder : ¬(roundHasAbsorbBoundary (pSpec := pSpec) i ∧
      roundEndCursor (δ := δ) i ≠ SpongeSize.R) ∨
    ∀ (_h₀ : 0 < roundEndBlock (δ := δ) i)
      (h₁ : roundEndBlock (δ := δ) i < inputs.length)
      (h₂ : roundEndBlock (δ := δ) i - 1 < outputs.length),
      (inputs[roundEndBlock (δ := δ) i]'h₁).rateSegment.toList.drop (roundEndCursor (δ := δ) i)
        = (outputs[roundEndBlock (δ := δ) i - 1]'h₂).rateSegment.toList.drop
            (roundEndCursor (δ := δ) i)
  /-- Step 4(a).iii.B/C at the chain's **first** block (`b = 0`): `DuplexSponge.start` builds its
  state as `Vector.replicate r 0 ++ cap`, so block `0`'s rate is `salt ‖ message-prefix` followed
  by zeros and the untouched tail beyond the epoch's end cursor is literally `0^(r − i_A)`. -/
  zeroRemainder : ¬(roundHasAbsorbBoundary (pSpec := pSpec) i ∧
      roundEndCursor (δ := δ) i ≠ SpongeSize.R) ∨
    ∀ (h₁ : roundEndBlock (δ := δ) i = 0 ∧ 0 < inputs.length),
      (inputs[0]'h₁.2).rateSegment.toList.drop (roundEndCursor (δ := δ) i)
        = List.replicate (SpongeSize.R - roundEndCursor (δ := δ) i) (0 : U)
  /-- Step 4(a).iii.D does not fire at this round. -/
  notExactFit : exactFitBlocks (δ := δ) i ≠ inputs.length
  /-- Step 4(a).iii.E: the round's verifier message squeeze fits strictly inside the chain. -/
  squeezeFits : roundSqueezeEndBlock (δ := δ) i < inputs.length
  /-- Step 4(a).iii.E: every permutation call *strictly inside* the round-`i` squeeze pairs its
  output with the next input state.  The last call is excluded: its output block is the one
  round `i+1`'s message overwrites. -/
  squeezeAgrees : ∀ k < roundSqueezeInnerCalls (δ := δ) i, ∃ sOut sIn,
    outputs[roundEndBlock (δ := δ) i + k]? = some sOut ∧
    inputs[roundEndBlock (δ := δ) i + 1 + k]? = some sIn ∧
    sOut.rateSegment = sIn.rateSegment

/-- **[CO25, §5.2]** BackTrack Step 4(a) obligations at the round the parse loop **stops** at (Step
4(a).iii.D). -/
structure RoundExactFit (inputs outputs : List (CanonicalSpongeState U))
    (i : pSpec.ChallengeIdx) : Prop where
  /-- Step 4(a).iii.A: the round-`i` message window has at least `ℓ_P(i)` characters. -/
  assemble : ∀ msgIdx, lastProverMessageBefore? (pSpec := pSpec) i = some msgIdx →
    proverMessageSize msgIdx ≤ (chainProverMessageWindowUnits inputs (blockOffset (δ := δ) i)
      (roundProverMessageCursor (δ := δ) i) (proverMessageSize msgIdx)).length
  /-- Step 4(a).iii.B/C remainder consistency (vacuous when the message's last block is full). -/
  remainder : ¬(roundHasAbsorbBoundary (pSpec := pSpec) i ∧
      roundEndCursor (δ := δ) i ≠ SpongeSize.R) ∨
    ∀ (h₁ : roundEndBlock (δ := δ) i < inputs.length)
      (h₂ : roundEndBlock (δ := δ) i - 1 < outputs.length),
      (inputs[roundEndBlock (δ := δ) i]'h₁).rateSegment.toList.drop (roundEndCursor (δ := δ) i)
        = (outputs[roundEndBlock (δ := δ) i - 1]'h₂).rateSegment.toList.drop
            (roundEndCursor (δ := δ) i)
  /-- Step 4(a).iii.B/C at the chain's **first** block (`b = 0`): `DuplexSponge.start` builds its
  state as `Vector.replicate r 0 ++ cap`, so block `0`'s rate is `salt ‖ message-prefix` followed
  by zeros and the untouched tail beyond the epoch's end cursor is literally `0^(r − i_A)`. -/
  zeroRemainder : ¬(roundHasAbsorbBoundary (pSpec := pSpec) i ∧
      roundEndCursor (δ := δ) i ≠ SpongeSize.R) ∨
    ∀ (h₁ : roundEndBlock (δ := δ) i = 0 ∧ 0 < inputs.length),
      (inputs[0]'h₁.2).rateSegment.toList.drop (roundEndCursor (δ := δ) i)
        = List.replicate (SpongeSize.R - roundEndCursor (δ := δ) i) (0 : U)
  /-- Step 4(a).iii.D exact fit `exactFitBlocks(i) = m_k + 1`. -/
  exactFit : exactFitBlocks (δ := δ) i = inputs.length

omit [DecidableEq StmtIn] in
/-- Step 4(a).iii.E on a passed-through round: the loop yields with the accumulator unchanged. -/
lemma extractStepTail_of_pass {state : CanonicalSpongeState U}
    {seq : BacktrackSequence trace state} {salt : Vector U δ} {i : pSpec.ChallengeIdx}
    {acc : StepAcc pSpec U}
    (hnfit : exactFitBlocks (δ := δ) i ≠ seq.inputState.length)
    (hfits : roundSqueezeEndBlock (δ := δ) i < seq.inputState.length)
    (hsw : seq.checkSqueezeWindow (roundEndBlock (δ := δ) i)
      (roundSqueezeInnerCalls (δ := δ) i) = true) :
    extractStepTail seq salt i acc = .yield (none, acc) := by
  unfold extractStepTail
  simp [hnfit, hfits, hsw]

omit [DecidableEq StmtIn] in
/-- Step 4(a).iii.D on the exact-fit round. -/
lemma extractStepTail_of_exactFit {state : CanonicalSpongeState U}
    {seq : BacktrackSequence trace state} {salt : Vector U δ} {i : pSpec.ChallengeIdx}
    {acc : StepAcc pSpec U}
    (hexact : exactFitBlocks (δ := δ) i = seq.inputState.length) :
    extractStepTail seq salt i acc =
      if candidateProverMessagesPresent acc i then
        .done (some (some { roundIdx := i, stmt := seq.stmt, salt := salt,
                            encodedProverMessages := candidateProverMessages acc i }), acc)
      else .done (some none, acc) := by
  unfold extractStepTail
  simp [hexact]

omit [DecidableEq StmtIn] in
/-- Step 4(a).iii.B/C pass when the round's remainder obligations hold. -/
lemma extractStepRemainder_eq_tail {state : CanonicalSpongeState U}
    {seq : BacktrackSequence trace state} {salt : Vector U δ} {i : pSpec.ChallengeIdx}
    {acc : StepAcc pSpec U}
    (hremEq : ∀ (_h₀ : 0 < roundEndBlock (δ := δ) i)
      (h₁ : roundEndBlock (δ := δ) i < seq.inputState.length)
      (h₂ : roundEndBlock (δ := δ) i - 1 < seq.outputState.length),
      (roundHasAbsorbBoundary (pSpec := pSpec) i ∧
        roundEndCursor (δ := δ) i ≠ SpongeSize.R) →
      (seq.inputState[roundEndBlock (δ := δ) i]'h₁).rateSegment.toList.drop
          (roundEndCursor (δ := δ) i)
        = (seq.outputState[roundEndBlock (δ := δ) i - 1]'h₂).rateSegment.toList.drop
            (roundEndCursor (δ := δ) i))
    (hzeroEq : ∀ (h₁ : roundEndBlock (δ := δ) i = 0 ∧ 0 < seq.inputState.length),
      (roundHasAbsorbBoundary (pSpec := pSpec) i ∧
        roundEndCursor (δ := δ) i ≠ SpongeSize.R) →
      (seq.inputState[0]'h₁.2).rateSegment.toList.drop (roundEndCursor (δ := δ) i)
        = List.replicate (SpongeSize.R - roundEndCursor (δ := δ) i) (0 : U)) :
    extractStepRemainder seq salt i acc = extractStepTail seq salt i acc := by
  unfold extractStepRemainder
  split_ifs with hc hb hne hz hne'
  · exact absurd (hremEq hb.2.1 hb.1 hb.2.2 hc) hne
  · rfl
  · exact absurd (hzeroEq hz hc) hne'
  all_goals rfl

omit [DecidableEq StmtIn] in
/-- Step 4(a).ii/iii.A on a round without a preceding prover message. -/
lemma extractStep_of_none {state : CanonicalSpongeState U}
    {seq : BacktrackSequence trace state} {salt : Vector U δ} {i : pSpec.ChallengeIdx}
    {acc : StepAcc pSpec U}
    (hguard : exactFitBlocks (δ := δ) i ≤ seq.inputState.length)
    (hm : lastProverMessageBefore? (pSpec := pSpec) i = none) :
    extractStep seq salt i acc = extractStepRemainder seq salt i acc := by
  unfold extractStep
  rw [ite_eq_right (by omega)]
  split
  · simp_all
  · rfl

omit [DecidableEq StmtIn] in
/-- Step 4(a).ii/iii.A on a round whose preceding prover message assembles to `v`. -/
lemma extractStep_of_some {state : CanonicalSpongeState U}
    {seq : BacktrackSequence trace state} {salt : Vector U δ} {i : pSpec.ChallengeIdx}
    {acc : StepAcc pSpec U} {m : pSpec.MessageIdx} {v : Vector U (proverMessageSize m)}
    (hguard : exactFitBlocks (δ := δ) i ≤ seq.inputState.length)
    (hm : lastProverMessageBefore? (pSpec := pSpec) i = some m)
    (hv : seq.assembleEncodedProverMessage (blockOffset (δ := δ) i)
      (roundProverMessageCursor (δ := δ) i) m = some v) :
    extractStep seq salt i acc = extractStepRemainder seq salt i (acc ++ [⟨m, v⟩]) := by
  unfold extractStep
  rw [ite_eq_right (by omega)]
  split
  · rename_i m' hm'
    rw [hm] at hm'
    cases hm'
    rw [hv]
  · simp_all

omit [DecidableEq StmtIn] in
/-- **Content-level Step-4 characterization.**  If the Step-4 round parse passes through every
earlier verifier message index and exactly fits at `i`, `extractCandidate` succeeds at `i`; moreover
the tuple's salt is the one handed in, and every prover message the parse assembled is the chain's
own prover-message window. -/
lemma extractCandidate_eq_some_of_rounds'
    {state : CanonicalSpongeState U} (seq : BacktrackSequence trace state)
    (salt : Vector U δ) {i : pSpec.ChallengeIdx}
    {pre post : List pSpec.ChallengeIdx}
    (hsplit : verifierMessageIdxList (pSpec := pSpec) = pre ++ i :: post)
    (hcover : ∀ j : pSpec.ProverMessageIdxBefore i.1.castSucc,
      ∃ x ∈ pre ++ [i], lastProverMessageBefore? (pSpec := pSpec) x = some j.1)
    (hpre : ∀ x ∈ pre, RoundPassesThrough (δ := δ) seq.inputState seq.outputState x)
    (hfit : RoundExactFit (δ := δ) seq.inputState seq.outputState i) :
    ∃ out, BacktrackSequence.extractCandidate (pSpec := pSpec) (δ := δ) state trace seq salt
        = some out ∧ out.roundIdx = i ∧ out.stmt = seq.stmt ∧ out.salt = salt ∧
      ∀ x ∈ pre ++ [i], ∀ j : pSpec.MessageIdx,
        lastProverMessageBefore? (pSpec := pSpec) x = some j →
        ∀ hlt : (j.1 : ℕ) < (out.roundIdx.1 : ℕ),
          (out.encodedProverMessages ⟨j, hlt⟩).toList
            = chainProverMessageWindowUnits seq.inputState (blockOffset (δ := δ) x)
                (roundProverMessageCursor (δ := δ) x) (proverMessageSize j) := by
  rw [extractCandidate_eq_forIn, hsplit]
  -- the exact-fit round's tuple, once its accumulator carries every required message window
  have finish : ∀ acc : StepAcc pSpec U,
      (∀ p ∈ acc, p.2.toList = chainProverMessageWindowUnits seq.inputState
          (walkPos (pSpec := pSpec) δ p.1.1.castSucc).1
          (walkPos (pSpec := pSpec) δ p.1.1.castSucc).2.1 (proverMessageSize p.1)) →
      (∀ y ∈ pre ++ [i], ∀ j : pSpec.MessageIdx,
          lastProverMessageBefore? (pSpec := pSpec) y = some j → ∃ p ∈ acc, p.1 = j) →
      ∀ y ∈ pre ++ [i], ∀ j : pSpec.MessageIdx,
        lastProverMessageBefore? (pSpec := pSpec) y = some j →
        ∀ hlt : (j.1 : ℕ) < (i.1 : ℕ),
          (candidateProverMessages acc i ⟨j, hlt⟩).toList
            = chainProverMessageWindowUnits seq.inputState (blockOffset (δ := δ) y)
                (roundProverMessageCursor (δ := δ) y) (proverMessageSize j) := by
    intro acc hacc1 hacc2 y hy j hj hlt
    obtain ⟨p, hp, hpj⟩ := hacc2 y hy j hj
    obtain ⟨hb, hcA⟩ :=
      blockOffset_roundProverMessageCursor_eq_of_lastProverMessageBefore (δ := δ) hj
    unfold candidateProverMessages findCandidateProverMessage
    rw [hb, hcA]
    split
    · next w hX =>
        obtain ⟨q, hq, hqe⟩ := List.exists_of_findSome?_eq_some hX
        split at hqe
        · rename_i hqj
          simp only [Option.some.injEq] at hqe
          subst hqe
          obtain ⟨qf, qs⟩ := q
          dsimp only at hqj ⊢
          subst hqj
          exact hacc1 _ hq
        · exact absurd hqe (by simp)
    · next hX =>
        rw [List.findSome?_eq_none_iff] at hX
        have hpn := hX p hp
        rw [dite_eq_left hpj] at hpn
        exact absurd hpn (by simp)
  -- every message the exact-fit round needs has been assembled
  have present : ∀ acc : StepAcc pSpec U,
      (∀ y ∈ pre ++ [i], ∀ j : pSpec.MessageIdx,
          lastProverMessageBefore? (pSpec := pSpec) y = some j → ∃ p ∈ acc, p.1 = j) →
      candidateProverMessagesPresent acc i := by
    intro acc hacc2 j
    obtain ⟨x, hx, hj⟩ := hcover j
    obtain ⟨p, hp, hpj⟩ := hacc2 x hx j.1 hj
    unfold findCandidateProverMessage
    apply Option.ne_none_iff_isSome.mp
    intro hnone
    rw [List.findSome?_eq_none_iff] at hnone
    have hpnone := hnone p hp
    rw [dite_eq_left hpj] at hpnone
    exact absurd hpnone (by simp)
  -- Message assembly extends the same content/coverage certificate at every round.
  have assembleStep : ∀ (x : pSpec.ChallengeIdx) (l : List pSpec.ChallengeIdx)
      (c : StepAcc pSpec U),
      exactFitBlocks (δ := δ) x ≤ seq.inputState.length →
      (∀ m, lastProverMessageBefore? (pSpec := pSpec) x = some m →
        proverMessageSize m ≤ (chainProverMessageWindowUnits seq.inputState (blockOffset (δ := δ) x)
          (roundProverMessageCursor (δ := δ) x) (proverMessageSize m)).length) →
      (∀ p ∈ c, p.2.toList = chainProverMessageWindowUnits seq.inputState
          (walkPos (pSpec := pSpec) δ p.1.1.castSucc).1
          (walkPos (pSpec := pSpec) δ p.1.1.castSucc).2.1 (proverMessageSize p.1)) →
      (∀ y ∈ l, ∀ j : pSpec.MessageIdx,
          lastProverMessageBefore? (pSpec := pSpec) y = some j → ∃ p ∈ c, p.1 = j) →
      ∃ acc : StepAcc pSpec U,
        (∀ p ∈ acc, p.2.toList = chainProverMessageWindowUnits seq.inputState
          (walkPos (pSpec := pSpec) δ p.1.1.castSucc).1
          (walkPos (pSpec := pSpec) δ p.1.1.castSucc).2.1 (proverMessageSize p.1)) ∧
        (∀ y ∈ l ++ [x], ∀ j : pSpec.MessageIdx,
          lastProverMessageBefore? (pSpec := pSpec) y = some j → ∃ p ∈ acc, p.1 = j) ∧
        extractStep seq salt x c = extractStepRemainder seq salt x acc := by
    intro x l c hguard hasm hc1 hc2
    rcases hm : lastProverMessageBefore? (pSpec := pSpec) x with _ | m
    · refine ⟨c, hc1, ?_, extractStep_of_none hguard hm⟩
      intro y hy j hj
      rcases List.mem_append.mp hy with hy' | hy'
      · exact hc2 y hy' j hj
      · simp only [List.mem_singleton] at hy'
        subst hy'
        rw [hm] at hj
        exact absurd hj (by simp)
    · obtain ⟨v, hv⟩ := assembleEncodedProverMessage_isSome (hasm m hm)
      refine ⟨c ++ [⟨m, v⟩], ?_, ?_, extractStep_of_some hguard hm hv⟩
      · intro p hp
        rcases List.mem_append.mp hp with hp' | hp'
        · exact hc1 p hp'
        · simp only [List.mem_singleton] at hp'
          subst hp'
          obtain ⟨hb, hcA⟩ :=
            blockOffset_roundProverMessageCursor_eq_of_lastProverMessageBefore (δ := δ) hm
          simpa [← hb, ← hcA] using assembleEncodedProverMessage_toList hv
      · intro y hy j hj
        rcases List.mem_append.mp hy with hy' | hy'
        · obtain ⟨p, hp, hpj⟩ := hc2 y hy' j hj
          exact ⟨p, List.mem_append_left _ hp, hpj⟩
        · simp only [List.mem_singleton] at hy'
          subst hy'
          rw [hm] at hj
          exact ⟨⟨m, v⟩, List.mem_append_right _ (by simp), by simpa using hj⟩
  -- The exact-fit round's remaining loop body uses the accumulator assembled above.
  have fitRemainder : ∀ acc : StepAcc pSpec U,
      extractStepRemainder seq salt i acc = extractStepTail seq salt i acc := by
    intro acc
    exact extractStepRemainder_eq_tail
      (fun _ h₁ h₂ hc => (hfit.remainder.resolve_left (not_not_intro hc)) h₁ h₂)
      (fun h₁ hc => (hfit.zeroRemainder.resolve_left (not_not_intro hc)) h₁)
  refine forIn_id_prefix_done_inv
    (P := fun r : StepState δ StmtIn pSpec U =>
      ∃ out, Break.runK r.1 (fun _ => none) (fun a => a) = some out ∧ out.roundIdx = i ∧
        out.stmt = seq.stmt ∧ out.salt = salt ∧
        ∀ x ∈ pre ++ [i], ∀ j : pSpec.MessageIdx,
          lastProverMessageBefore? (pSpec := pSpec) x = some j →
          ∀ hlt : (j.1 : ℕ) < (out.roundIdx.1 : ℕ),
            (out.encodedProverMessages ⟨j, hlt⟩).toList
              = chainProverMessageWindowUnits seq.inputState (blockOffset (δ := δ) x)
                  (roundProverMessageCursor (δ := δ) x) (proverMessageSize j))
    _ i post pre
    (fun l r =>
      (∀ p ∈ r.2, p.2.toList = chainProverMessageWindowUnits seq.inputState
          (walkPos (pSpec := pSpec) δ p.1.1.castSucc).1
          (walkPos (pSpec := pSpec) δ p.1.1.castSucc).2.1 (proverMessageSize p.1)) ∧
      ∀ x ∈ l, ∀ j : pSpec.MessageIdx, lastProverMessageBefore? (pSpec := pSpec) x = some j →
        ∃ p ∈ r.2, p.1 = j)
    ⟨none, []⟩ ⟨by simp, by simp⟩ ?_ ?_ ?_
  · -- Every prefix round extends the certificate and then passes its remaining checks.
    intro l x hlx c hc
    obtain ⟨hguard, hasm, hrem, hzero, hnfit, hfits, hsq⟩ := hpre x (hlx.subset (by simp))
    obtain ⟨acc, hacc1, hacc2, hstep⟩ := assembleStep x l c.2 hguard hasm hc.1 hc.2
    refine ⟨⟨none, acc⟩, ?_, hacc1, hacc2⟩
    change extractStep seq salt x c.2 = _
    rw [hstep, extractStepRemainder_eq_tail (seq := seq) (salt := salt) (i := x)
      (fun h₀ h₁ h₂ hc => (hrem.resolve_left (not_not_intro hc)) h₀ h₁ h₂)
      (fun h₁ hc => (hzero.resolve_left (not_not_intro hc)) h₁),
      extractStepTail_of_pass hnfit hfits
        (checkSqueezeWindow_eq_true seq (roundEndBlock (δ := δ) x)
          (roundSqueezeInnerCalls (δ := δ) x) hsq)]
  · -- the exact-fit round can never `yield`
    intro c c' hc hcon
    obtain ⟨acc, _, hacc2, hstep⟩ :=
      assembleStep i pre c.2 (le_of_eq hfit.exactFit) hfit.assemble hc.1 hc.2
    change extractStep seq salt i c.2 = _ at hcon
    rw [hstep, fitRemainder, extractStepTail_of_exactFit hfit.exactFit,
      ite_eq_left (present acc hacc2)] at hcon
    cases hcon
  · -- and when it is `done` it carries the Step 4(a).iii.D tuple, with its content pinned
    intro c c' hc hcon
    obtain ⟨acc, hacc1, hacc2, hstep⟩ :=
      assembleStep i pre c.2 (le_of_eq hfit.exactFit) hfit.assemble hc.1 hc.2
    change extractStep seq salt i c.2 = _ at hcon
    rw [hstep, fitRemainder, extractStepTail_of_exactFit hfit.exactFit,
      ite_eq_left (present acc hacc2)] at hcon
    cases hcon
    exact ⟨_, rfl, rfl, rfl, rfl, finish acc hacc1 hacc2⟩

/-- **`BackTrack` succeeds at a squeeze position, with the reconstructed tuple's content pinned.**

On an honest chain whose Step-3 salt extraction succeeds and whose Step-4 round parse passes
through every earlier verifier message index and exactly fits at `i`, `BackTrack` returns `.some`
with round index `i` and the chain's own anchoring statement; moreover the reconstructed salt is the
chain's first `δ` rate units [CO25, §5.2 Step 3] and every prover message the Step-4 parse
assembled is the chain's own prover-message window [CO25, §5.2 Step 4(a)iii.A].  Those are the two
components that enter the key of the `gᵢ` verifier message query, so
`hyb3_hyb4_indistinguishability`'s round induction needs them to match what `Hyb_4`
reads. -/
theorem backTrack_eq_some_of_honestScanPrefix'
    {trΔ : TraceNabla T_H T_P StmtIn U} (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    {state : CanonicalSpongeState U} {stmt : StmtIn}
    {rem : List (CanonicalSpongeState U × CanonicalSpongeState U)}
    (hchain : HonestScanPrefix trΔ stmt rem state)
    {depthBound : ℕ} (hfuel : rem.length < depthBound)
    (hFresh : ∀ p ∈ rem, p.1.capacitySegment ≠ state.capacitySegment)
    (hNodup : (rem.map fun p => p.1.capacitySegment).Nodup)
    -- Step 3: the salt extraction succeeds
    (hsaltLen : δ ≤ (rem.length + 1) * SpongeSize.R)
    -- Step 4: the round parse walks to `i` and stops there
    {i : pSpec.ChallengeIdx} {pre post : List pSpec.ChallengeIdx}
    (hsplit : verifierMessageIdxList (pSpec := pSpec) = pre ++ i :: post)
    (hcover : ∀ j : pSpec.ProverMessageIdxBefore i.1.castSucc,
      ∃ x ∈ pre ++ [i], lastProverMessageBefore? (pSpec := pSpec) x = some j.1)
    (hpre : ∀ x ∈ pre, RoundPassesThrough (δ := δ) (HonestScanPrefix.inputStates rem state)
      (HonestScanPrefix.outputStates (U := U) rem) x)
    (hfit : RoundExactFit (δ := δ) (HonestScanPrefix.inputStates rem state)
      (HonestScanPrefix.outputStates (U := U) rem) i) :
    ∃ out, backTrack (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound = .some out ∧
      out.roundIdx = i ∧ out.stmt = stmt ∧
      out.salt.toList = (chainRateUnits (HonestScanPrefix.inputStates rem state)).take δ ∧
      ∀ x ∈ pre ++ [i], ∀ j : pSpec.MessageIdx,
        lastProverMessageBefore? (pSpec := pSpec) x = some j →
        ∀ hlt : (j.1 : ℕ) < (out.roundIdx.1 : ℕ),
          (out.encodedProverMessages ⟨j, hlt⟩).toList
            = chainProverMessageWindowUnits (HonestScanPrefix.inputStates rem state)
                (blockOffset (δ := δ) x) (roundProverMessageCursor (δ := δ) x)
                (proverMessageSize j) := by
  obtain ⟨seq, hscan, hs, hin, hout⟩ :=
    linearScanBackwards_top_of_honestScanPrefix h_trΔ hchain hfuel hFresh hNodup
  rw [backTrack_eq_of_scan_done (pSpec := pSpec) (δ := δ) hscan]
  obtain ⟨salt, hsalt⟩ := constructCandidateSalt_isSome (δ := δ) (seq := seq)
    (by rw [hin, chainRateUnits_length, HonestScanPrefix.inputStates_length]; exact hsaltLen)
  rw [hsalt]
  dsimp only
  obtain ⟨out, hex, hr, hst, hsl, hmsg⟩ :=
    extractCandidate_eq_some_of_rounds' (δ := δ) seq salt hsplit hcover
      (fun x hx => by rw [hin, hout]; exact hpre x hx)
      (by rw [hin, hout]; exact hfit)
  rw [hex]
  refine ⟨out, rfl, hr, by rw [hst, hs], ?_, ?_⟩
  · rw [hsl, ← hin]
    exact constructCandidateSalt_toList hsalt
  · intro x hx j hj hlt
    rw [hmsg x hx j hj hlt, hin]

end HonestChainReconstruction

end BacktrackProcedure

end DuplexSpongeFS.Backtrack
