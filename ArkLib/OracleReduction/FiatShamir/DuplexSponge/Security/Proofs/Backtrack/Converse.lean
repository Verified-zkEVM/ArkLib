/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.Backtrack.HonestChain

/-!
# BackTrack: the converse certificate

The certificate a successful `BackTrack` carries (key determinacy, [CO25, Claim 5.21]).
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

section HonestChainReconstruction

variable {trace : QueryLog (duplexSpongeOracle StmtIn U)}

/-! ### The converse direction: the certificate a successful `BackTrack` carries

`backTrack_eq_some_of_honestScanPrefix'` above is the *sufficient* direction: a chain of the
honest shape whose Step-4 obligations hold makes `BackTrack` succeed.  [CO25, Claim 5.21] needs the
*necessary* direction — from `backTrack … = .some out` **alone**, recover the reconstructed chain
and every check the Step-3/Step-4 extraction performed.  Together the two directions characterize
`backTrack`'s `.some` fiber exactly, and that is what pins the queried state: the scan sees only
`state.capacitySegment` (`HonestScanPrefix.eq_of_capacitySegment_eq`), so all of the chain's rate
material has to be pinned by the extraction checks recovered here.

Consumer: `KeyLemma.Hyb0Hyb1.KeyDeterminacy`. -/

section BacktrackConverse

omit [SpongeSize] in
/-- `classifyLookup` reports `noMatch` only on the empty candidate list. -/
lemma eq_nil_of_classifyLookup_noMatch {α : Type _} {xs : List α}
    (h : classifyLookup xs = .noMatch) : xs = [] := by
  match xs with
  | [] => rfl
  | [_] => exact absurd h (by simp [classifyLookup])
  | _ :: _ :: _ => exact absurd h (by simp [classifyLookup])

omit [SpongeSize] in
/-- `classifyLookup` reports `unique a` only on the singleton candidate list `[a]`. -/
lemma eq_singleton_of_classifyLookup_unique {α : Type _} {xs : List α} {a : α}
    (h : classifyLookup xs = .unique a) : xs = [a] := by
  match xs with
  | [] => exact absurd h (by simp [classifyLookup])
  | [b] =>
      have hb : b = a := by simpa [classifyLookup] using h
      rw [hb]
  | _ :: _ :: _ => exact absurd h (by simp [classifyLookup])

/-- **The backwards scan certifies an `HonestScanPrefix`** — converse of
`linearScanBackwards_done_of_honestScanPrefix`.

Every `.done` of the scan is a chain all of whose `predecessorEntries` lookups were singletons and
whose final lookup was empty with a unique hash anchor; the visited-capacity list additionally
certifies that the chain's input capacities are pairwise distinct and avoid `vCap`. -/
lemma linearScanBackwards_honestScanPrefix_of_done
    {trΔ : TraceNabla T_H T_P StmtIn U} (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    {state : CanonicalSpongeState U} (fuel : ℕ) :
    ∀ {cur : CanonicalSpongeState U} {vCap : List (Vector U SpongeSize.C)}
      {acc : PartialBacktrackSequence trace cur state}
      {seq : BacktrackSequence trace state},
      linearScanBackwards trace trΔ h_trΔ fuel cur state vCap acc = .done seq →
      ∃ rem : List (CanonicalSpongeState U × CanonicalSpongeState U),
        HonestScanPrefix trΔ seq.stmt rem cur ∧ rem.length < fuel ∧
        (∀ p ∈ rem, p.1.capacitySegment ∉ vCap) ∧
        (rem.map fun p => p.1.capacitySegment).Nodup ∧
        seq.inputState = (rem.map Prod.fst).reverse ++ acc.inputState ∧
        seq.outputState = (rem.map Prod.snd).reverse ++ acc.outputState := by
  induction fuel with
  | zero =>
      intro cur vCap acc seq h
      exact absurd h (by simp [linearScanBackwards])
  | succ f ih =>
      intro cur vCap acc seq h
      simp only [linearScanBackwards] at h
      split at h
      · -- Step 2(b) finds no predecessor: the chain must anchor here
        rename_i hcp
        split at h
        · exact absurd h (by simp)
        · rename_i stmt hch
          have hNoPred : predecessorEntries trΔ cur.capacitySegment = [] := by
            rw [← predecessorCandidates_eq_predecessorEntries (T_H := T_H)]
            exact eq_nil_of_classifyLookup_noMatch hcp
          have hHash : hashAnchorStmts trΔ cur.capacitySegment = [stmt] := by
            rw [← hashAnchorCandidates_eq_hashAnchorStmts (T_P := T_P)]
            exact eq_singleton_of_classifyLookup_unique hch
          injection h with hseq
          subst hseq
          exact ⟨[], HonestScanPrefix.anchor hNoPred hHash, Nat.succ_pos _, by simp, List.nodup_nil,
            by simp [completeBacktrackSequence], by simp [completeBacktrackSequence]⟩
        · exact absurd h (by simp)
      · -- Step 2(b) finds a unique predecessor: the scan continues
        rename_i pred hcp
        obtain ⟨s_in, s_out⟩ := pred
        have hPred : predecessorEntries trΔ cur.capacitySegment = [(s_in, s_out)] := by
          rw [← predecessorCandidates_eq_predecessorEntries (T_H := T_H)]
          exact eq_singleton_of_classifyLookup_unique hcp
        split at h
        · exact absurd h (by simp)
        · rename_i hNoLoop
          split at h
          · exact absurd h (by simp)
          · rename_i hFresh
            obtain ⟨rem, hchain, hlen, hvcap, hnodup, hin, hout⟩ := ih h
            refine ⟨(s_in, s_out) :: rem, HonestScanPrefix.step hPred hNoLoop hchain, by
              simpa using hlen, ?_, ?_, ?_, ?_⟩
            · intro p hp
              rcases List.mem_cons.mp hp with rfl | hp'
              · exact hFresh
              · exact fun hmem => hvcap p hp' (List.mem_cons_of_mem _ hmem)
            · refine List.nodup_cons.mpr ⟨?_, hnodup⟩
              intro hmem
              obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hmem
              exact hvcap p hp (hpe ▸ List.mem_cons_self ..)
            · rw [hin]; simp [prependPartialSequence]
            · rw [hout]; simp [prependPartialSequence]
      · exact absurd h (by simp)

/-- Top-level form of `linearScanBackwards_honestScanPrefix_of_done`: the scan `backTrack` runs
(start state `=` target state, empty accumulator, `vCap = [state.cap]`) certifies a chain whose
input states are exactly the reconstructed `inputStates`. -/
lemma linearScanBackwards_top_honestScanPrefix_of_done
    {trΔ : TraceNabla T_H T_P StmtIn U} (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    {state : CanonicalSpongeState U} {depthBound : ℕ} {seq : BacktrackSequence trace state}
    (hscan : linearScanBackwards trace trΔ h_trΔ depthBound state state [state.capacitySegment]
      (emptyPartialSequence trace state) = .done seq) :
    ∃ rem : List (CanonicalSpongeState U × CanonicalSpongeState U),
      HonestScanPrefix trΔ seq.stmt rem state ∧ rem.length < depthBound ∧
      (∀ p ∈ rem, p.1.capacitySegment ≠ state.capacitySegment) ∧
      (rem.map fun p => p.1.capacitySegment).Nodup ∧
      seq.inputState = HonestScanPrefix.inputStates rem state ∧
      seq.outputState = HonestScanPrefix.outputStates (U := U) rem := by
  obtain ⟨rem, hchain, hlen, hvcap, hnodup, hin, hout⟩ :=
    linearScanBackwards_honestScanPrefix_of_done h_trΔ depthBound hscan
  refine ⟨rem, hchain, hlen, ?_, hnodup, ?_, ?_⟩
  · intro p hp hmem
    exact hvcap p hp (List.mem_singleton.mpr hmem)
  · rw [hin]; simp [HonestScanPrefix.inputStates, emptyPartialSequence]
  · rw [hout]; simp [HonestScanPrefix.outputStates, emptyPartialSequence]

/-- `backTrack … = .some out` decomposes into its three successful stages: the scan is `.done`,
Step 3 extracts a salt, and Step 4 returns `out`. -/
lemma backTrack_eq_some_inv
    {trΔ : TraceNabla T_H T_P StmtIn U} {h_trΔ : trΔ.IsSubsetOfQueryLog trace}
    {state : CanonicalSpongeState U} {depthBound : ℕ}
    {out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hout : backTrack (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound = .some out) :
    ∃ (seq : BacktrackSequence trace state) (salt : Vector U δ),
      linearScanBackwards trace trΔ h_trΔ depthBound state state [state.capacitySegment]
          (emptyPartialSequence trace state) = .done seq ∧
      seq.constructCandidateSalt (δ := δ) = some salt ∧
      BacktrackSequence.extractCandidate (pSpec := pSpec) (δ := δ) state trace seq salt
        = some out := by
  unfold backTrack linearBackTrack at hout
  split at hout
  · exact absurd hout (by simp)
  · exact absurd hout (by simp)
  · rename_i seq hscan
    split at hout
    · exact absurd hout (by simp)
    · rename_i salt hsalt
      split at hout
      · exact absurd hout (by simp)
      · rename_i o hext
        refine ⟨seq, salt, hscan, hsalt, ?_⟩
        simp only [ExperimentOutput.some.injEq] at hout
        subst hout
        exact hext

omit [SpongeSize] in
/-- **Analysis principle for an `Id`-monad `for` loop that ends in a `done`.**  Dual of
`forIn_id_prefix_done_inv`: if the loop's result satisfies `P` and the initial accumulator does
not, the list splits at the element whose step fired `done`, every earlier element having
`yield`ed. -/
lemma forIn_id_done_split {α β : Type} (I : β → Prop) (P : β → Prop)
    (Y : α → Prop) (D : α → Prop) (f : α → β → Id (ForInStep β))
    (hyield : ∀ (x : α) (c c' : β), I c → f x c = ForInStep.yield c' → Y x ∧ I c')
    (hdone : ∀ (x : α) (c c' : β), I c → f x c = ForInStep.done c' → P c' → D x)
    (hbase : ∀ c : β, I c → ¬ P c) :
    ∀ (l : List α) (b : β), I b → P (forIn l b f) →
      ∃ (pre : List α) (x : α) (post : List α), l = pre ++ x :: post ∧
        (∀ y ∈ pre, Y y) ∧ D x := by
  intro l
  induction l with
  | nil =>
      intro b hb hP
      exact absurd hP (hbase b hb)
  | cons a l ih =>
      intro b hb hP
      cases hf : f a b with
      | done b' =>
          have hval : forIn (a :: l) b f = b' := by rw [List.forIn_cons, hf]; rfl
          rw [hval] at hP
          exact ⟨[], a, l, rfl, by simp, hdone a b b' hb hf hP⟩
      | yield b' =>
          have hval : forIn (a :: l) b f = forIn l b' f := by rw [List.forIn_cons, hf]; rfl
          rw [hval] at hP
          obtain ⟨hY, hI⟩ := hyield a b b' hb hf
          obtain ⟨pre, x, post, hsplit, hpre, hD⟩ := ih b' hI hP
          refine ⟨a :: pre, x, post, by rw [hsplit]; rfl, ?_, hD⟩
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact hY
          · exact hpre y hy'

omit [DecidableEq StmtIn] in
/-- **Converse of `checkSqueezeWindow_eq_true`** [CO25, §5.2 Step 4(a)iii.E]: a passing squeeze
window check certifies that every permutation call strictly inside the squeeze copied its output
rate block to the next input state. -/
lemma checkSqueezeWindow_spec
    {state : CanonicalSpongeState U} (seq : BacktrackSequence trace state)
    (squeezeStart lvCur : Nat) (h : seq.checkSqueezeWindow squeezeStart lvCur = true) :
    ∀ k < lvCur, ∃ sOut sIn, seq.outputState[squeezeStart + k]? = some sOut ∧
      seq.inputState[squeezeStart + 1 + k]? = some sIn ∧ sOut.rateSegment = sIn.rateSegment :=
  (checkSqueezeWindow_eq_true_iff seq squeezeStart lvCur).mp h

omit [DecidableEq StmtIn] in
/-- `checkSqueezeWindow_spec` in the shape the Step-4 loop leaves behind: the `if not (…)` guard
of Step 4(a).iii.E did not fire. -/
lemma checkSqueezeWindow_spec_of_not_not
    {state : CanonicalSpongeState U} (seq : BacktrackSequence trace state)
    (squeezeStart lvCur : Nat)
    (h : ¬ ((!seq.checkSqueezeWindow squeezeStart lvCur) = true)) :
    ∀ k < lvCur, ∃ sOut sIn, seq.outputState[squeezeStart + k]? = some sOut ∧
      seq.inputState[squeezeStart + 1 + k]? = some sIn ∧ sOut.rateSegment = sIn.rateSegment :=
  checkSqueezeWindow_spec seq squeezeStart lvCur (by simpa using h)

omit [HasVerifierMessageSize pSpec] [DecidableEq StmtIn] [DecidableEq U] in
/-- **Converse of `assembleEncodedProverMessage_isSome`**: a successful Step 4(a).iii.A assembly
certifies that the round's message window really has `ℓ_P(i)` characters. -/
lemma assembleEncodedProverMessage_length_le
    {state : CanonicalSpongeState U} {seq : BacktrackSequence trace state}
    {b cA : Nat} {msgIdx : pSpec.MessageIdx} {v : Vector U (proverMessageSize msgIdx)}
    (h : seq.assembleEncodedProverMessage (pSpec := pSpec) b cA msgIdx = some v) :
    proverMessageSize msgIdx
      ≤ (chainProverMessageWindowUnits seq.inputState b cA (proverMessageSize msgIdx)).length := by
  unfold BacktrackSequence.assembleEncodedProverMessage at h
  rcases hp : vectorOfListExact (U := U) (proverMessageSize msgIdx)
      (chainUnitsFrom seq.inputState b cA) with _ | p
  · rw [hp] at h; simp at h
  · have hle := p.2
    rw [chainUnitsFrom_length] at hle
    rw [chainProverMessageWindowUnits_length]
    omega

/-! ### Inverting the Step 4(a) loop body

Each of the three layers of `extractStep` either aborts with `done (some none, _)` or certifies
its own checks and hands over to the next layer. -/

omit [DecidableEq StmtIn] in
/-- Step 4(a).iii.D–F tail on a **yielding** round: the exact-fit test fails, the round's squeeze
fits inside the chain and its window check passes. -/
lemma extractStepTail_yield_inv {state : CanonicalSpongeState U}
    {seq : BacktrackSequence trace state} {salt : Vector U δ} {x : pSpec.ChallengeIdx}
    {acc : StepAcc pSpec U} {c' : StepState δ StmtIn pSpec U}
    (hf : extractStepTail seq salt x acc = .yield c') :
    c'.1 = none ∧ exactFitBlocks (δ := δ) x ≠ seq.inputState.length ∧
      roundSqueezeEndBlock (δ := δ) x < seq.inputState.length ∧
      ∀ k < roundSqueezeInnerCalls (δ := δ) x, ∃ sOut sIn,
        seq.outputState[roundEndBlock (δ := δ) x + k]? = some sOut ∧
        seq.inputState[roundEndBlock (δ := δ) x + 1 + k]? = some sIn ∧
        sOut.rateSegment = sIn.rateSegment := by
  unfold extractStepTail at hf
  split_ifs at hf with hbeq hpres hfits hchk
  cases hf
  exact ⟨rfl, by simpa using hbeq, hfits, checkSqueezeWindow_spec_of_not_not seq _ _ hchk⟩

omit [DecidableEq StmtIn] in
/-- Step 4(a).iii.D–F tail **returning a tuple**: the round is an exact fit and the tuple is the
round's own. -/
lemma extractStepTail_done_inv {state : CanonicalSpongeState U}
    {seq : BacktrackSequence trace state} {salt : Vector U δ} {x : pSpec.ChallengeIdx}
    {acc : StepAcc pSpec U} {c' : StepState δ StmtIn pSpec U}
    {o : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hf : extractStepTail seq salt x acc = .done c') (ho : c'.1 = some (some o)) :
    o.roundIdx = x ∧ exactFitBlocks (δ := δ) x = seq.inputState.length := by
  have h := extractStepTail_spec (seq := seq) (salt := salt) (i := x) (acc := acc) (o := o)
    (by rw [hf]; exact ho)
  exact ⟨h.1, h.2.2.2⟩

omit [DecidableEq StmtIn] in
/-- Step 4(a).iii.B/C: either the remainder checks abort the round, or they pass — certifying
the round's remainder obligations — and the tail runs. -/
lemma extractStepRemainder_inv {state : CanonicalSpongeState U}
    {seq : BacktrackSequence trace state} {salt : Vector U δ} {x : pSpec.ChallengeIdx}
    {acc : StepAcc pSpec U} :
    extractStepRemainder seq salt x acc = .done (some none, acc) ∨
      ((¬(roundHasAbsorbBoundary (pSpec := pSpec) x ∧
          roundEndCursor (δ := δ) x ≠ SpongeSize.R) ∨
        ∀ (_h₀ : 0 < roundEndBlock (δ := δ) x)
          (h₁ : roundEndBlock (δ := δ) x < seq.inputState.length)
          (h₂ : roundEndBlock (δ := δ) x - 1 < seq.outputState.length),
          (seq.inputState[roundEndBlock (δ := δ) x]'h₁).rateSegment.toList.drop
              (roundEndCursor (δ := δ) x)
            = (seq.outputState[roundEndBlock (δ := δ) x - 1]'h₂).rateSegment.toList.drop
                (roundEndCursor (δ := δ) x)) ∧
      (¬(roundHasAbsorbBoundary (pSpec := pSpec) x ∧
          roundEndCursor (δ := δ) x ≠ SpongeSize.R) ∨
        ∀ (h₁ : roundEndBlock (δ := δ) x = 0 ∧ 0 < seq.inputState.length),
          (seq.inputState[0]'h₁.2).rateSegment.toList.drop (roundEndCursor (δ := δ) x)
            = List.replicate (SpongeSize.R - roundEndCursor (δ := δ) x) (0 : U)) ∧
      extractStepRemainder seq salt x acc = extractStepTail seq salt x acc) := by
  unfold extractStepRemainder
  split_ifs with hc hb hne hz hne'
  · exact Or.inl rfl
  · refine Or.inr ⟨Or.inr fun h₀ h₁ h₂ => ?_, Or.inr fun h₁ => absurd h₁.1 (by omega), rfl⟩
    simpa only [List.get_eq_getElem] using not_not.mp hne
  · exact Or.inl rfl
  · refine Or.inr ⟨Or.inr fun h₀ h₁ h₂ => absurd ⟨h₁, h₀, h₂⟩ hb, Or.inr fun h₁ => ?_, rfl⟩
    simpa only [List.get_eq_getElem] using not_not.mp hne'
  · exact Or.inr ⟨Or.inr fun h₀ h₁ h₂ => absurd ⟨h₁, h₀, h₂⟩ hb, Or.inr fun h₁ => absurd h₁ hz,
      rfl⟩
  · exact Or.inr ⟨Or.inl hc, Or.inl hc, rfl⟩

omit [DecidableEq StmtIn] in
/-- Step 4(a).ii/iii.A: either the guard or the message assembly aborts the round, or both pass
— certifying the round's guard and assembly obligations — and the remainder checks run on the
extended accumulator. -/
lemma extractStep_inv {state : CanonicalSpongeState U}
    {seq : BacktrackSequence trace state} {salt : Vector U δ} {x : pSpec.ChallengeIdx}
    {c : StepAcc pSpec U} :
    extractStep seq salt x c = .done (some none, c) ∨
      ∃ acc : StepAcc pSpec U, exactFitBlocks (δ := δ) x ≤ seq.inputState.length ∧
        (∀ msgIdx, lastProverMessageBefore? (pSpec := pSpec) x = some msgIdx →
          proverMessageSize msgIdx ≤ (chainProverMessageWindowUnits seq.inputState
            (blockOffset (δ := δ) x) (roundProverMessageCursor (δ := δ) x)
            (proverMessageSize msgIdx)).length) ∧
        extractStep seq salt x c = extractStepRemainder seq salt x acc := by
  unfold extractStep
  split
  · exact Or.inl rfl
  · rename_i hguard
    split
    · rename_i m hm
      split
      · rename_i v hv
        refine Or.inr ⟨_, by omega, fun m' hm' => ?_, rfl⟩
        rw [hm] at hm'
        cases hm'
        exact assembleEncodedProverMessage_length_le hv
      · exact Or.inl rfl
    · rename_i hm
      exact Or.inr ⟨_, by omega, fun m' hm' => absurd (hm.symm.trans hm') (by simp), rfl⟩

omit [DecidableEq StmtIn] in
/-- **Converse of `extractCandidate_eq_some_of_rounds'`.**

A successful Step-4 parse certifies its own hypotheses: the reported round is where
`verifierMessageIdxList` was cut, every earlier verifier message round passed every Step-4(a) check
(`RoundPassesThrough`), and the reported round is an exact fit whose own checks passed
(`RoundExactFit`).

This is the half of key determinacy the backwards scan cannot supply: the scan reads only
`state.capacitySegment` (`HonestScanPrefix.eq_of_capacitySegment_eq`), so the rate material of the
reconstructed chain is pinned exclusively by the checks recovered here — Step 3's salt, Step
4(a).iii.A's prover-message windows, Step 4(a).iii.B/C's absorb remainder and Step 4(a).iii.E's
squeeze windows. -/
lemma extractCandidate_rounds_of_eq_some
    {state : CanonicalSpongeState U} (seq : BacktrackSequence trace state) (salt : Vector U δ)
    {out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (h : BacktrackSequence.extractCandidate (pSpec := pSpec) (δ := δ) state trace seq salt
      = some out) :
    ∃ pre post, verifierMessageIdxList (pSpec := pSpec) = pre ++ out.roundIdx :: post ∧
      (∀ x ∈ pre, RoundPassesThrough (δ := δ) seq.inputState seq.outputState x) ∧
      RoundExactFit (δ := δ) seq.inputState seq.outputState out.roundIdx := by
  have key : ∃ pre x post, verifierMessageIdxList (pSpec := pSpec) = pre ++ x :: post ∧
      (∀ y ∈ pre, RoundPassesThrough (δ := δ) seq.inputState seq.outputState y) ∧
      (x = out.roundIdx ∧ RoundExactFit (δ := δ) seq.inputState seq.outputState x) := by
    revert h
    rw [extractCandidate_eq_forIn]
    refine forIn_id_done_split
      (I := fun r : StepState δ StmtIn pSpec U => r.1 = none)
      (P := fun r : StepState δ StmtIn pSpec U =>
        Break.runK r.1 (fun _ => none) (fun a => a) = some out)
      (Y := fun y => RoundPassesThrough (δ := δ) seq.inputState seq.outputState y)
      (D := fun x => x = out.roundIdx ∧ RoundExactFit (δ := δ) seq.inputState seq.outputState x)
      _ ?_ ?_ ?_ _ _ rfl
    · -- a `yield` certifies `RoundPassesThrough`
      intro x c c' _ hf
      change extractStep seq salt x c.2 = _ at hf
      rcases extractStep_inv (seq := seq) (salt := salt) (x := x) (c := c.2) with
        habort | ⟨acc, hguard, hasm, hstep⟩
      · rw [habort] at hf; cases hf
      rw [hstep] at hf
      rcases extractStepRemainder_inv (seq := seq) (salt := salt) (x := x) (acc := acc) with
        habort | ⟨hrem, hzero, hrest⟩
      · rw [habort] at hf; cases hf
      rw [hrest] at hf
      obtain ⟨hc', hnfit, hfits, hsq⟩ := extractStepTail_yield_inv hf
      exact ⟨⟨hguard, hasm, hrem, hzero, hnfit, hfits, hsq⟩, hc'⟩
    · -- a `done` carrying a tuple certifies `RoundExactFit` at the reported round
      intro x c c' _ hf hP
      change extractStep seq salt x c.2 = _ at hf
      have ho : c'.1 = some (some out) := by
        rcases hc : c'.1 with _ | _ | o
        · rw [hc] at hP; cases hP
        · rw [hc] at hP; cases hP
        · rw [hc] at hP; cases hP; rfl
      rcases extractStep_inv (seq := seq) (salt := salt) (x := x) (c := c.2) with
        habort | ⟨acc, _, hasm, hstep⟩
      · rw [habort] at hf; cases hf; cases ho
      rw [hstep] at hf
      rcases extractStepRemainder_inv (seq := seq) (salt := salt) (x := x) (acc := acc) with
        habort | ⟨hrem, hzero, hrest⟩
      · rw [habort] at hf; cases hf; cases ho
      rw [hrest] at hf
      obtain ⟨hx, hexact⟩ := extractStepTail_done_inv hf ho
      refine ⟨hx.symm, hasm, ?_, hzero, hexact⟩
      rcases hrem with hrem | hrem
      · exact Or.inl hrem
      · refine Or.inr fun h₁ h₂ => hrem ?_ h₁ h₂
        have hlen := seq.inputState_length_eq_outputState_length_succ
        unfold exactFitBlocks at hexact
        omega
    · -- the initial accumulator carries no tuple
      intro c hc
      simp [hc]
  obtain ⟨pre, x, post, hsplit, hpre, hx, hfit⟩ := key
  subst hx
  exact ⟨pre, post, hsplit, hpre, hfit⟩

/-- **The full certificate a successful `BackTrack` carries** — the exact converse of
`backTrack_eq_some_of_honestScanPrefix'`.

`backTrack … state depthBound = .some out` implies that

* the backwards scan reconstructed a chain `rem` of the honest shape anchored at `out.stmt`,
  short enough for the fuel, whose input capacities are pairwise distinct and differ from
  `state`'s (`HonestScanPrefix`, freshness, `Nodup`);
* the chain's length is the exact-fit length of the reported round;
* `out.salt` is the chain's first `δ` rate units [CO25, §5.2 Step 3];
* the reported round is where the Step-4 parse loop cut `verifierMessageIdxList`, every earlier
  verifier message round passing every Step-4(a) check and the reported one being an exact fit
  (`RoundPassesThrough` / `RoundExactFit`).

Feeding the last item back into `extractCandidate_eq_some_of_rounds'` recovers the reconstructed
prover messages as well, which is how `KeyLemma.Hyb0Hyb1.KeyDeterminacy` pins every rate unit of the
chain: the backwards scan itself sees only `state.capacitySegment`
(`HonestScanPrefix.eq_of_capacitySegment_eq`), so the extraction checks listed here are the only
constraints the queried state's rate segment is under. -/
theorem backTrack_some_certificate
    {trΔ : TraceNabla T_H T_P StmtIn U} {h_trΔ : trΔ.IsSubsetOfQueryLog trace}
    {state : CanonicalSpongeState U} {depthBound : ℕ}
    {out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hout : backTrack (δ := δ) (pSpec := pSpec) trace trΔ h_trΔ state depthBound = .some out) :
    ∃ (rem : List (CanonicalSpongeState U × CanonicalSpongeState U))
      (pre post : List pSpec.ChallengeIdx),
      HonestScanPrefix trΔ out.stmt rem state ∧
      rem.length < depthBound ∧
      (∀ p ∈ rem, p.1.capacitySegment ≠ state.capacitySegment) ∧
      (rem.map fun p => p.1.capacitySegment).Nodup ∧
      exactFitBlocks (δ := δ) out.roundIdx = rem.length + 1 ∧
      out.salt.toList = (chainRateUnits (HonestScanPrefix.inputStates rem state)).take δ ∧
      verifierMessageIdxList (pSpec := pSpec) = pre ++ out.roundIdx :: post ∧
      (∀ x ∈ pre, RoundPassesThrough (δ := δ) (HonestScanPrefix.inputStates rem state)
        (HonestScanPrefix.outputStates (U := U) rem) x) ∧
      RoundExactFit (δ := δ) (HonestScanPrefix.inputStates rem state)
        (HonestScanPrefix.outputStates (U := U) rem) out.roundIdx := by
  obtain ⟨seq, salt, hscan, hsalt, hext⟩ := backTrack_eq_some_inv hout
  obtain ⟨rem, hchain, hlen, hfresh, hnodup, hin, hos⟩ :=
    linearScanBackwards_top_honestScanPrefix_of_done h_trΔ hscan
  obtain ⟨_, hstmt, hsl, hfit⟩ := extractCandidate_spec (δ := δ) seq salt hext
  obtain ⟨pre, post, hsplit, hpre, hfitr⟩ := extractCandidate_rounds_of_eq_some seq salt hext
  refine ⟨rem, pre, post, ?_, hlen, hfresh, hnodup, ?_, ?_, hsplit, ?_, ?_⟩
  · rw [hstmt]; exact hchain
  · rw [hfit, hin, HonestScanPrefix.inputStates_length]
  · rw [hsl, ← hin]; exact constructCandidateSalt_toList hsalt
  · intro x hx; rw [← hin, ← hos]; exact hpre x hx
  · rw [← hin, ← hos]; exact hfitr

end BacktrackConverse

end HonestChainReconstruction

end BacktrackProcedure

end DuplexSpongeFS.Backtrack
