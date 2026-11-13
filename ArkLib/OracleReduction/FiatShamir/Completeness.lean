/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.FiatShamir.Basic
public import ArkLib.OracleReduction.Security.RbrGame
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-!
# Completeness of the Fiat-Shamir transformation

Fixed tables preserve perfect completeness; a shared lazy random oracle preserves error.
-/

@[expose] public section

universe u v

open ProtocolSpec OracleComp OracleSpec

open scoped BigOperators

variable {n : ℕ}

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

section Execution

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

/-- Package the messages as the single message of the noninteractive protocol. -/
def ProtocolSpec.Messages.fsTranscript (messages : pSpec.Messages) :
    (⟨!v[.P_to_V], !v[pSpec.Messages]⟩ : ProtocolSpec 1).FullTranscript :=
  fun | ⟨0, _⟩ => messages

/-- Simulating a lifted base computation preserves the other state component. -/
lemma simulateQ_addLift_run_left {μ : Type → Type} [Monad μ] [LawfulMonad μ]
    {σ τ : Type} {κ : Type} {spec : OracleSpec κ}
    (left : QueryImpl oSpec (StateT σ μ)) (right : QueryImpl spec (StateT τ μ))
    {α : Type} (oa : OracleComp oSpec α) (s : σ) (t : τ) :
    (simulateQ (left.addLift right : QueryImpl (oSpec + spec) (StateT (σ × τ) μ))
      (liftM oa)).run (s, t) = (do
        let (a, s') ← (simulateQ left oa).run s
        pure (a, s', t)) := by
  rw [QueryImpl.simulateQ_addLift_liftM_left, StateT.run_liftLeft]

variable [samples : ∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- One FS round, interpreted with a fixed table, runs only the original base-oracle action. -/
lemma Prover.processRoundFS_simulate (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (j : Fin n) (messages : pSpec.MessagesUpTo j.castSucc) (stmt : StmtIn)
    (st : P.PrvState j.castSucc) (s : σ)
    (f : QueryImpl (srChallengeOracle StmtIn pSpec) Id) :
    (simulateQ (impl.addLift fsChallengeQueryImpl' :
      QueryImpl (oSpec + srChallengeOracle StmtIn pSpec)
        (StateT (σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))
      (P.processRoundFS j (pure (messages, stmt, st)))).run (s, f) =
      (match h : pSpec.dir j with
      | .V_to_P => do
        let (recv, s') ← (simulateQ impl (P.receiveChallenge ⟨j, h⟩ st)).run s
        pure ((messages.extend h, stmt, recv (f ⟨⟨j, h⟩, stmt, messages⟩)), s', f)
      | .P_to_V => do
        let ((msg, st'), s') ← (simulateQ impl (P.sendMessage ⟨j, h⟩ st)).run s
        pure ((messages.concat h msg, stmt, st'), s', f)) := by
  unfold processRoundFS
  simp only [pure_bind]
  split <;> rename_i h
  · split <;> rename_i h'
    · erw [simulateQ_bind, StateT.run_bind, simulateQ_addLift_run_left]
      simp only [bind_assoc, pure_bind]
      congr 1
    · cases h.symm.trans h'
  · split <;> rename_i h'
    · cases h.symm.trans h'
    · erw [simulateQ_bind, StateT.run_bind, simulateQ_addLift_run_left]
      simp only [bind_assoc, pure_bind]
      congr 1

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Separate the previous FS rounds from the current round. -/
lemma Prover.processRoundFS_bind (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (j : Fin n) (current : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
      (pSpec.MessagesUpTo j.castSucc × StmtIn × P.PrvState j.castSucc)) :
    P.processRoundFS j current = current >>= fun x => P.processRoundFS j (pure x) := by
  simp [processRoundFS]

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- One-step unfolding of the FS prover run. -/
lemma Prover.runToRoundFS_succ (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (j : Fin n) (stmt : StmtIn) (st : P.PrvState 0) :
    P.runToRoundFS j.succ stmt st = P.processRoundFS j (P.runToRoundFS j.castSucc stmt st) :=
  Fin.induction_succ _ _ _

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Reconstruction replays a transcript whenever its challenge keys return the recorded
answers without changing the simulation state. -/
lemma simulateQ_deriveTranscriptSRAux {μ : Type → Type} [Monad μ] [LawfulMonad μ]
    {ρ : Type} (handler : QueryImpl (oSpec + srChallengeOracle StmtIn pSpec) (StateT ρ μ))
    {k : Fin (n + 1)} (tr : pSpec.Transcript k) (stmt : StmtIn) (state : ρ)
    (hit : ∀ (i : Fin k) (h : pSpec.dir (i.castLE (by omega)) = .V_to_P),
      (handler (.inr ⟨⟨i.castLE (by omega), h⟩, stmt,
        tr.toMessagesUpTo.take i.castSucc⟩)).run state = pure (tr i, state))
    (j : Fin (k + 1)) :
    (simulateQ handler (tr.toMessagesUpTo.deriveTranscriptSRAux stmt k j)).run state =
      pure ((fun i : Fin j => tr (i.castLE (by omega))), state) := by
  induction j using Fin.induction with
  | zero =>
    erw [MessagesUpTo.deriveTranscriptSRAux_zero, simulateQ_pure, StateT.run_pure]
    congr 2
    funext i
    exact i.elim0
  | succ j ih =>
    erw [MessagesUpTo.deriveTranscriptSRAux_succ, simulateQ_bind, StateT.run_bind, ih,
      pure_bind]
    split <;> rename_i h
    · erw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, hit j h,
        pure_bind, simulateQ_pure, StateT.run_pure]
      congr 2
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · exact Transcript.concat_last _ _
      · exact Fin.snoc_castSucc ..
    · erw [simulateQ_pure, StateT.run_pure]
      congr 2
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · exact Transcript.concat_last _ _
      · exact Fin.snoc_castSucc ..

/-- Full verifier reconstruction replays the fixed table. -/
lemma simulateQ_deriveTranscriptFS (messages : pSpec.Messages) (stmt : StmtIn)
    (f : QueryImpl (srChallengeOracle StmtIn pSpec) Id) (s : σ) :
    (simulateQ (impl.addLift fsChallengeQueryImpl' :
      QueryImpl (oSpec + srChallengeOracle StmtIn pSpec)
        (StateT (σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))
      (messages.deriveTranscriptFS (oSpec := oSpec) stmt)).run (s, f) =
      pure (Messages.transcriptOfTable messages stmt f, s, f) := by
  let tr := MessagesUpTo.transcriptOfTable (k := Fin.last n) messages stmt f
  have hm : tr.toMessagesUpTo = messages := by
    funext i
    exact MessagesUpTo.transcriptOfTable_message _ _ _ i.1 i.2
  have replay := simulateQ_deriveTranscriptSRAux (μ := ProbComp)
    (impl.addLift fsChallengeQueryImpl') tr stmt (s, f) (j := Fin.last n)
  have hit (i : Fin (Fin.last n)) (h : pSpec.dir (i.castLE (by omega)) = .V_to_P) :
      ((impl.addLift fsChallengeQueryImpl' :
        QueryImpl (oSpec + srChallengeOracle StmtIn pSpec)
          (StateT (σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))
        (.inr ⟨⟨i.castLE (by omega), h⟩, stmt,
          tr.toMessagesUpTo.take i.castSucc⟩)).run (s, f) = pure (tr i, s, f) := by
    dsimp only [tr]
    erw [MessagesUpTo.transcriptOfTable_challenge _ _ _ _ h]
    simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inr]
    change (do let y ← pure (f _, f); pure (y.1, s, y.2)) = _
    simp only [pure_bind]
    congr 2
    congr 3
    exact congrArg (MessagesUpTo.take i.castSucc) hm
  have result := replay hit
  have eqRun := congrArg (fun msgs : pSpec.MessagesUpTo (Fin.last n) =>
    (simulateQ (impl.addLift fsChallengeQueryImpl' :
      QueryImpl (oSpec + srChallengeOracle StmtIn pSpec)
        (StateT (σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))
      (msgs.deriveTranscriptSRAux (oSpec := oSpec) stmt (Fin.last n) (Fin.last n))).run (s, f)) hm
  exact eqRun.symm.trans result

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- The transformed reduction executes the FS prover and reconstructs the same messages
before running the original verifier. No noninteractive challenge query is made. -/
lemma Reduction.fiatShamir_run_option
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn) :
    (R.fiatShamir.run stmt wit).run = (do
      let (messages, _, st) ← R.prover.runToRoundFS (Fin.last n) stmt (R.prover.input (stmt, wit))
      let ctx ← liftM (R.prover.output st)
      let tr ← messages.toMessages.deriveTranscriptFS (oSpec := oSpec) stmt
      let vr ← liftM (R.verifier.verify stmt tr).run
      pure (vr.map (fun v => ((messages.toMessages.fsTranscript, ctx), v))) :
        OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) _).liftComp
          (spec := oSpec + fsChallengeOracle StmtIn pSpec)
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(⟨!v[.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
              ProtocolSpec 1).Challenge]ₒ'challengeOracleInterface)
          (h := ⟨fun q => ⟨Sum.inl q.input, q.cont⟩⟩) := by
  let : ProverOnly
      (⟨!v[.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
      ProtocolSpec 1) := { prover_first' := rfl }
  erw [Reduction.run_run_eq_bind, Prover.run_of_prover_first stmt wit R.prover.fiatShamir]
  simp only [Verifier.run, Reduction.fiatShamir, Prover.fiatShamir, Verifier.fiatShamir,
    liftComp_eq_liftM, liftM_bind, liftM_pure, bind_assoc, pure_bind]
  simp only [← monadLift_liftM_OptionT, OptionT.run_bind, OptionT.run_monadLift,
    bind_assoc, Option.elimM, bind_map_left, Option.elim_some, monadLift_self, liftM_bind]
  congr 1
  funext x
  rcases x with ⟨messages, stmt', st⟩
  congr 1
  funext ctx
  congr 1
  funext tr
  congr 1
  funext vr
  cases vr <;> simp [Option.getM]
  rfl

/-- Every fixed-table prover execution is supported by the interactive prover execution,
with the same base-oracle state and the reconstructed transcript. -/
lemma Prover.runToRoundFS_support (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (s : σ)
    (f : QueryImpl (srChallengeOracle StmtIn pSpec) Id) (k : Fin (n + 1)) :
    ∀ z ∈ support ((simulateQ (impl.addLift fsChallengeQueryImpl' :
      QueryImpl (oSpec + srChallengeOracle StmtIn pSpec)
        (StateT (σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))
      (P.runToRoundFS k stmt (P.input (stmt, wit)))).run (s, f)),
      z.1.2.1 = stmt ∧ z.2.2 = f ∧
      ((z.1.1.transcriptOfTable stmt f, z.1.2.2), z.2.1) ∈
        support ((simulateQ (impl.addLift challengeQueryImpl :
          QueryImpl _ (StateT σ ProbComp)) (P.runToRound k stmt wit)).run s) := by
  induction k using Fin.induction with
  | zero =>
    intro z hz
    have hz' : z = ((default, stmt, P.input (stmt, wit)), s, f) :=
      eq_of_mem_support_pure _ hz
    subst z
    refine ⟨rfl, rfl, ?_⟩
    have ht : (default : pSpec.MessagesUpTo 0).transcriptOfTable stmt f = default :=
      Subsingleton.elim _ _
    simp [Prover.runToRound_zero_of_prover_first, ht]
  | succ j ih =>
    intro z hz
    erw [Prover.runToRoundFS_succ, Prover.processRoundFS_bind,
      simulateQ_bind, StateT.run_bind] at hz
    obtain ⟨⟨⟨messages, stmt', st⟩, s', f'⟩, hx, hz⟩ := mem_support_bind_peel _ _ hz
    obtain ⟨hstmt, hf, hOriginal⟩ := ih _ hx
    dsimp only at hstmt hf hOriginal hz
    subst stmt'
    subst f'
    rw [Prover.processRoundFS_simulate] at hz
    split at hz <;> rename_i hd
    · obtain ⟨⟨recv, s''⟩, hrecv, hz⟩ := mem_support_bind_peel _ _ hz
      have hz' := eq_of_mem_support_pure _ hz
      subst z
      refine ⟨rfl, rfl, ?_⟩
      rw [MessagesUpTo.transcriptOfTable_extend messages hd, Prover.runToRound_succ,
        Prover.processRound_of_dir_eq_V_to_P _ hd, simulateQ_bind, StateT.run_bind]
      apply (mem_support_bind_iff _ _ _).mpr
      refine ⟨((messages.transcriptOfTable stmt f, st), s'), hOriginal, ?_⟩
      erw [simulateQ_bind, simulateQ_addLift_challengeQueryImpl_getChallenge impl ⟨j, hd⟩,
        StateT.run_bind, StateT.run_monadLift]
      simp only [monadLift_self, bind_assoc, pure_bind]
      apply (mem_support_bind_iff _ _ _).mpr
      refine ⟨f ⟨⟨j, hd⟩, stmt, messages⟩, mem_support_uniformSample _, ?_⟩
      rw [simulateQ_bind, StateT.run_bind, QueryImpl.simulateQ_addLift_liftM_left]
      apply (mem_support_bind_iff _ _ _).mpr
      exact ⟨(recv, s''), hrecv, by simp⟩
    · obtain ⟨⟨⟨msg, st'⟩, s''⟩, hsend, hz⟩ := mem_support_bind_peel _ _ hz
      have hz' := eq_of_mem_support_pure _ hz
      subst z
      refine ⟨rfl, rfl, ?_⟩
      rw [MessagesUpTo.transcriptOfTable_concat messages hd, Prover.runToRound_succ,
        Prover.processRound_of_dir_eq_P_to_V _ hd, simulateQ_bind, StateT.run_bind]
      apply (mem_support_bind_iff _ _ _).mpr
      refine ⟨((messages.transcriptOfTable stmt f, st), s'), hOriginal, ?_⟩
      rw [simulateQ_bind, StateT.run_bind, QueryImpl.simulateQ_addLift_liftM_left]
      apply (mem_support_bind_iff _ _ _).mpr
      exact ⟨((msg, st'), s''), hsend, by simp⟩

/-- Fixed-table FS execution preserves the output pair and verdict of some interactive branch. -/
lemma Reduction.fiatShamir_run_support
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn)
    (s : σ) (f : QueryImpl (srChallengeOracle StmtIn pSpec) Id) :
    ∀ z ∈ support ((simulateQ
      ((impl.addLift fsChallengeQueryImpl' :
        QueryImpl (oSpec + srChallengeOracle StmtIn pSpec)
          (StateT (σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp)).addLift
          (n := ProbComp)
          (r := StateT (σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp)
          challengeQueryImpl :
        QueryImpl _ (StateT (σ × QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))
      (R.fiatShamir.run stmt wit).run).run (s, f)),
    ∃ y ∈ support ((simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl _ (StateT σ ProbComp)) (R.run stmt wit).run).run s),
      z.1.map (fun r => (r.1.2, r.2)) = y.1.map (fun r => (r.1.2, r.2)) := by
  intro z hz
  erw [Reduction.fiatShamir_run_option, liftComp_eq_liftM, QueryImpl.simulateQ_addLift_liftM_left,
    simulateQ_bind, StateT.run_bind] at hz
  obtain ⟨⟨⟨messages, stmt', st⟩, s', f'⟩, hp, hz⟩ := mem_support_bind_peel _ _ hz
  obtain ⟨hstmt, hf, hOriginal⟩ := R.prover.runToRoundFS_support impl stmt wit s f _ _ hp
  dsimp only at hstmt hf hOriginal hz
  subst stmt'
  subst f'
  erw [simulateQ_bind, StateT.run_bind, simulateQ_addLift_run_left] at hz
  simp only [bind_assoc, pure_bind] at hz
  obtain ⟨⟨ctx, s''⟩, hout, hz⟩ := mem_support_bind_peel _ _ hz
  erw [simulateQ_bind, StateT.run_bind, simulateQ_deriveTranscriptFS, pure_bind,
    simulateQ_bind, StateT.run_bind, simulateQ_addLift_run_left] at hz
  simp only [bind_assoc, pure_bind] at hz
  obtain ⟨⟨vr, sOut⟩, hv, hz⟩ := mem_support_bind_peel _ _ hz
  have hz' := eq_of_mem_support_pure _ hz
  subst z
  refine ⟨(vr.map (fun v =>
    ((Messages.transcriptOfTable messages.toMessages stmt f, ctx), v)), sOut),
    ?_, ?_⟩
  · rw [Reduction.run_run_eq_bind]
    simp only [Verifier.run, liftComp_eq_liftM, Prover.run, bind_assoc, pure_bind,
      simulateQ_bind, StateT.run_bind]
    apply (mem_support_bind_iff _ _ _).mpr
    refine ⟨((Messages.transcriptOfTable messages.toMessages stmt f, st), s'), hOriginal, ?_⟩
    rw [QueryImpl.simulateQ_addLift_liftM_left]
    apply (mem_support_bind_iff _ _ _).mpr
    refine ⟨(ctx, s''), hout, ?_⟩
    rw [QueryImpl.simulateQ_addLift_liftM_left]
    apply (mem_support_bind_iff _ _ _).mpr
    exact ⟨(vr, sOut), hv, by simp; rfl⟩
  · cases vr <;> rfl


section RandomOracle

omit [∀ i, SampleableType (pSpec.Challenge i)]

variable [DecidableEq (srChallengeOracle StmtIn pSpec).Domain]

/-- The random-oracle key used at a challenge round in a transcript. -/
abbrev ProtocolSpec.Transcript.challengeKey {k : Fin (n + 1)}
    (tr : pSpec.Transcript k) (stmt : StmtIn) (j : pSpec.ChallengeIdx)
    (h : j.1.val ≤ k.val) : (srChallengeOracle StmtIn pSpec).Domain :=
  ⟨j, stmt, tr.messagesBefore j.1 h⟩

/-- The shared cache containing exactly the challenge queries recorded in a transcript.
The decidable equality premise is needed for comparing statement and message-prefix keys. -/
def ProtocolSpec.Transcript.challengeCache {k : Fin (n + 1)}
    (tr : pSpec.Transcript k) (stmt : StmtIn) :
    (srChallengeOracle StmtIn pSpec).QueryCache :=
  QueryCache.ofFn fun q =>
    if h : q.1.1.val < k.val then
      if q = tr.challengeKey stmt q.1 (Nat.le_of_lt h) then
        some (tr ⟨q.1.1.val, h⟩)
      else none
    else none

/-- No future round has an entry in the transcript's cache. -/
lemma ProtocolSpec.Transcript.challengeCache_future {k : Fin (n + 1)}
    (tr : pSpec.Transcript k) (stmt : StmtIn)
    (q : (srChallengeOracle StmtIn pSpec).Domain) (h : k.val ≤ q.1.1.val) :
    tr.challengeCache stmt q = none := by
  simp [challengeCache, Nat.not_lt_of_ge h]

/-- Recorded challenge keys return their original answers. -/
lemma ProtocolSpec.Transcript.challengeCache_hit {k : Fin (n + 1)}
    (tr : pSpec.Transcript k) (stmt : StmtIn) (j : pSpec.ChallengeIdx)
    (h : j.1.val < k.val) :
    tr.challengeCache stmt (tr.challengeKey stmt j (Nat.le_of_lt h)) =
      some (tr ⟨j.1.val, h⟩) := by
  simp [challengeCache, challengeKey, h]
  rfl

/-- The empty transcript determines the empty cache. -/
lemma ProtocolSpec.Transcript.challengeCache_zero (tr : pSpec.Transcript 0)
    (stmt : StmtIn) : tr.challengeCache stmt = ∅ := by
  apply QueryCache.ext
  intro q
  exact tr.challengeCache_future stmt q (Nat.zero_le _)

/-- Adding a round leaves entries at every other round unchanged. -/
lemma ProtocolSpec.Transcript.challengeCache_concat_of_ne {j : Fin n}
    (tr : pSpec.Transcript j.castSucc) (x : pSpec.Type j) (stmt : StmtIn)
    (q : (srChallengeOracle StmtIn pSpec).Domain) (hne : q.1.1 ≠ j) :
    (tr.concat x).challengeCache stmt q = tr.challengeCache stmt q := by
  by_cases hlt : q.1.1.val < j.val
  · have hs : q.1.1.val < j.succ.val := Nat.lt_trans hlt (Nat.lt_succ_self _)
    have hk : (tr.concat x).challengeKey stmt q.1 (Nat.le_of_lt hs) =
        tr.challengeKey stmt q.1 (Nat.le_of_lt hlt) := by
      unfold challengeKey
      congr 2
      exact tr.messagesBefore_concat x q.1.1 (Nat.le_of_lt hlt)
    simp only [challengeCache, QueryCache.ofFn_apply, Fin.val_castSucc,
      dite_eq_left hlt, dite_eq_left hs, hk]
    split
    · congr 1
      change tr.concat x (Fin.castSucc (⟨q.1.1.val, hlt⟩ : Fin j)) = _
      rw [Transcript.concat_castSucc]
    · rfl
  · have hval : q.1.1.val ≠ j.val := fun h => hne (Fin.ext h)
    have hs : j.succ.val ≤ q.1.1.val := by
      change j.val + 1 ≤ q.1.1.val
      omega
    rw [challengeCache_future _ _ _ hs, challengeCache_future _ _ _ (by
      change j.val ≤ q.1.1.val
      omega)]

/-- Appending a prover message leaves the challenge cache unchanged. -/
lemma ProtocolSpec.Transcript.challengeCache_concat_message {j : Fin n}
    (tr : pSpec.Transcript j.castSucc) (stmt : StmtIn) (h : pSpec.dir j = .P_to_V)
    (x : pSpec.Message ⟨j, h⟩) :
    (tr.concat x).challengeCache stmt = tr.challengeCache stmt := by
  apply QueryCache.ext
  intro q
  apply tr.challengeCache_concat_of_ne x stmt q
  intro heq
  have hq := q.1.2
  rw [heq, h] at hq
  cases hq

/-- At the appended round, the canonical key records the appended challenge. -/
lemma ProtocolSpec.Transcript.challengeCache_concat_self {j : Fin n}
    (tr : pSpec.Transcript j.castSucc) (stmt : StmtIn) (h : pSpec.dir j = .V_to_P)
    (x : pSpec.Challenge ⟨j, h⟩) :
    (tr.concat x).challengeCache stmt (tr.challengeKey stmt ⟨j, h⟩ (Nat.le_refl _)) =
      some x := by
  have hh := (tr.concat x).challengeCache_hit stmt ⟨j, h⟩ (Nat.lt_succ_self _)
  simp only [challengeKey] at hh
  rw [messagesBefore_concat] at hh
  exact hh.trans (congrArg some (Transcript.concat_last x tr))

/-- Appending a challenge adds exactly its fresh key to the cache. -/
lemma ProtocolSpec.Transcript.challengeCache_concat_challenge {j : Fin n}
    (tr : pSpec.Transcript j.castSucc) (stmt : StmtIn) (h : pSpec.dir j = .V_to_P)
    (x : pSpec.Challenge ⟨j, h⟩) :
    (tr.concat x).challengeCache stmt =
      (tr.challengeCache stmt).cacheQuery
        (tr.challengeKey stmt ⟨j, h⟩ (Nat.le_refl _)) x := by
  apply QueryCache.ext
  intro q
  by_cases hq : q = tr.challengeKey stmt ⟨j, h⟩ (Nat.le_refl _)
  · subst q
    erw [QueryCache.cacheQuery_self, challengeCache_concat_self]
    rfl
  · erw [QueryCache.cacheQuery_of_ne _ _ hq]
    by_cases hi : q.1.1 = j
    · have hiv : q.1.1.val = j.val := congrArg Fin.val hi
      have hk : (tr.concat x).challengeKey stmt q.1 (by simp [hiv]) =
          tr.challengeKey stmt ⟨j, h⟩ (Nat.le_refl _) := by
        have hi' : q.1 = ⟨j, h⟩ := Subtype.ext hi
        rcases q with ⟨qi, args⟩
        dsimp only at hi'
        subst qi
        unfold challengeKey
        congr 2
        exact tr.messagesBefore_concat x j (Nat.le_refl _)
      rw [tr.challengeCache_future stmt q (by
        simpa only [Fin.val_castSucc, hiv] using Nat.le_refl j.val)]
      simp only [challengeCache, QueryCache.ofFn_apply]
      rw [dite_eq_left (show q.1.1.val < j.succ.val by
        simpa only [Fin.val_succ, hiv] using Nat.lt_succ_self j.val), hk, ite_eq_right hq]
    · exact tr.challengeCache_concat_of_ne x stmt q hi


include samples

local instance : ∀ q : (srChallengeOracle StmtIn pSpec).Domain,
    SampleableType ((srChallengeOracle StmtIn pSpec).Range q) :=
  fun q => inferInstanceAs (SampleableType (pSpec.Challenge q.1))

/-- Shared base state and lazy challenge cache for honest FS execution. -/
def FiatShamir.fsRandomOracleImpl : QueryImpl (oSpec + srChallengeOracle StmtIn pSpec)
    (StateT (σ × (srChallengeOracle StmtIn pSpec).QueryCache) ProbComp) :=
  impl.addLift (srChallengeOracle StmtIn pSpec).randomOracle

open FiatShamir

/-- Challenge queries operate on the shared cache and preserve the base state. -/
lemma simulateQ_fsRandom_query (q : (srChallengeOracle StmtIn pSpec).Domain) (s : σ)
    (c : (srChallengeOracle StmtIn pSpec).QueryCache) :
    (simulateQ (fsRandomOracleImpl impl)
      (liftM ((oSpec + srChallengeOracle StmtIn pSpec).query (.inr q)))).run (s, c) =
      (do let (a, c') ← ((srChallengeOracle StmtIn pSpec).randomOracle q).run c
          pure (a, s, c')) := by
  rw [simulateQ_spec_query, fsRandomOracleImpl, QueryImpl.addLift_def,
    QueryImpl.add_apply_inr]
  rfl

/-- The next round has not been queried, so its answer is a fresh uniform sample. -/
lemma simulateQ_fsRandom_fresh {j : Fin n} (tr : pSpec.Transcript j.castSucc)
    (stmt : StmtIn) (hd : pSpec.dir j = .V_to_P) (s : σ) :
    (simulateQ (fsRandomOracleImpl impl)
      (liftM ((oSpec + srChallengeOracle StmtIn pSpec).query
        (.inr ⟨⟨j, hd⟩, stmt, tr.toMessagesUpTo⟩)))).run
      (s, tr.challengeCache stmt) = (do
        let ch ← $ᵗ pSpec.Challenge ⟨j, hd⟩
        pure (ch, s, (tr.challengeCache stmt).cacheQuery
          ⟨⟨j, hd⟩, stmt, tr.toMessagesUpTo⟩ ch)) := by
  rw [simulateQ_fsRandom_query, randomOracle.run_eq,
    Transcript.challengeCache_future _ _ _ (Nat.le_refl _)]
  simp only [bind_assoc, pure_bind]
  rfl

/-- One honest FS round has the interactive distribution and records its challenge in the cache. -/
lemma Prover.processRoundFS_randomOracle
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (j : Fin n)
    (tr : pSpec.Transcript j.castSucc) (stmt : StmtIn)
    (st : P.PrvState j.castSucc) (s : σ) :
    (simulateQ (fsRandomOracleImpl impl)
      (P.processRoundFS j (pure (tr.toMessagesUpTo, stmt, st)))).run
        (s, tr.challengeCache stmt) =ᵈ (do
      let ((tr', st'), s') ← (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl _ (StateT σ ProbComp)) (P.processRound j (pure (tr, st)))).run s
      pure ((tr'.toMessagesUpTo, stmt, st'), s', tr'.challengeCache stmt)) := by
  unfold processRoundFS
  simp only [pure_bind]
  split <;> rename_i hd
  · erw [simulateQ_bind, StateT.run_bind, simulateQ_addLift_run_left]
    simp only [bind_assoc, pure_bind]
    rw [Prover.processRound_of_dir_eq_V_to_P _ hd]
    simp only [pure_bind, simulateQ_bind, StateT.run_bind]
    erw [simulateQ_addLift_challengeQueryImpl_getChallenge impl ⟨j, hd⟩]
    simp only [StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
    have hstep (recv : pSpec.Challenge ⟨j, hd⟩ → P.PrvState j.succ) (s' : σ) :
        (simulateQ (fsRandomOracleImpl impl) (do
          let ch : pSpec.Challenge ⟨j, hd⟩ ← liftM
            ((oSpec + srChallengeOracle StmtIn pSpec).query
              (.inr ⟨⟨j, hd⟩, stmt, tr.toMessagesUpTo⟩))
          pure (tr.toMessagesUpTo.extend hd, stmt, recv ch))).run
          (s', tr.challengeCache stmt) = (do
            let ch ← $ᵗ pSpec.Challenge ⟨j, hd⟩
            pure ((tr.toMessagesUpTo.extend hd, stmt, recv ch), s',
              (tr.challengeCache stmt).cacheQuery
                ⟨⟨j, hd⟩, stmt, tr.toMessagesUpTo⟩ ch)) := by
      have hb := congrArg (fun x => x.run (s', tr.challengeCache stmt))
        (simulateQ_bind (fsRandomOracleImpl impl)
          (liftM ((oSpec + srChallengeOracle StmtIn pSpec).query
            (.inr ⟨⟨j, hd⟩, stmt, tr.toMessagesUpTo⟩)) :
              OracleComp (oSpec + srChallengeOracle StmtIn pSpec) (pSpec.Challenge ⟨j, hd⟩))
          (fun ch => pure (tr.toMessagesUpTo.extend hd, stmt, recv ch)))
      refine hb.trans ?_
      erw [StateT.run_bind, simulateQ_fsRandom_fresh]
      simp only [simulateQ_pure, StateT.run_pure]
      refine (bind_assoc ($ᵗ pSpec.Challenge ⟨j, hd⟩)
        (fun ch => pure (ch, s',
          (tr.challengeCache stmt).cacheQuery ⟨⟨j, hd⟩, stmt, tr.toMessagesUpTo⟩ ch))
        (fun z => pure ((tr.toMessagesUpTo.extend hd, stmt, recv z.1), z.2))).trans ?_
      apply bind_congr
      intro ch
      exact pure_bind _ _
    apply (EvalDistEq.bind_right
      ((simulateQ impl (P.receiveChallenge ⟨j, hd⟩ st)).run s)
      (fun r => EvalDistEq.of_forall_prEvent_eq fun p =>
        congrArg (fun x => Pr{let z ← x}[p z]) (hstep r.1 r.2))).trans
    rw [QueryImpl.simulateQ_addLift_liftM_left]
    simp only [simulateQ_pure, StateT.run_pure, pure_bind,
      Transcript.toMessagesUpTo_concat_challenge,
      Transcript.challengeCache_concat_challenge]
    exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
  · erw [simulateQ_bind, StateT.run_bind, simulateQ_addLift_run_left]
    rw [Prover.processRound_of_dir_eq_P_to_V _ hd]
    simp only [pure_bind, simulateQ_bind, StateT.run_bind, bind_assoc]
    rw [QueryImpl.simulateQ_addLift_liftM_left]
    apply EvalDistEq.bind_right
    rintro ⟨⟨msg, st'⟩, s'⟩
    simp only [ChallengeIdx, Challenge, QueryImpl.addLift_def,
      PFunctor.Handler.liftTarget_self, simulateQ_pure, StateT.run_pure, bind_pure_comp,
      map_pure, Transcript.toMessagesUpTo_concat_message,
      Transcript.challengeCache_concat_message]
    exact EvalDistEq.rfl


/-- The entire FS prover has the interactive distribution, with its transcript recorded
in the shared cache and the arbitrary base-oracle state preserved. -/
lemma Prover.runToRoundFS_randomOracle
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn)
    (s : σ) (k : Fin (n + 1)) :
    (simulateQ (fsRandomOracleImpl impl)
      (P.runToRoundFS k stmt (P.input (stmt, wit)))).run (s, ∅) =ᵈ (do
        let ((tr, st), s') ← (simulateQ (impl.addLift challengeQueryImpl :
          QueryImpl _ (StateT σ ProbComp)) (P.runToRound k stmt wit)).run s
        pure ((tr.toMessagesUpTo, stmt, st), s', tr.challengeCache stmt)) := by
  induction k using Fin.induction with
  | zero =>
    simp only [runToRoundFS, Fin.induction_zero, Prover.runToRound_zero_of_prover_first,
      simulateQ_pure, StateT.run_pure, pure_bind, Transcript.challengeCache_zero]
    exact EvalDistEq.rfl
  | succ j ih =>
    erw [Prover.runToRoundFS_succ, Prover.processRoundFS_bind,
      simulateQ_bind, StateT.run_bind]
    apply (ih.bind_left _).trans
    simp only [bind_assoc, pure_bind]
    rw [Prover.runToRound_succ, Prover.processRound_bind,
      simulateQ_bind, StateT.run_bind]
    simp only [bind_assoc]
    apply EvalDistEq.bind_right
    rintro ⟨⟨tr, st⟩, s'⟩
    exact P.processRoundFS_randomOracle impl j tr stmt st s'


/-- A previously recorded challenge is replayed without sampling or changing either state. -/
lemma simulateQ_fsRandom_hit {k : Fin (n + 1)} (tr : pSpec.Transcript k)
    (stmt : StmtIn) (j : pSpec.ChallengeIdx) (h : j.1.val < k.val) (s : σ) :
    (simulateQ (fsRandomOracleImpl impl)
      (liftM ((oSpec + srChallengeOracle StmtIn pSpec).query
        (.inr (tr.challengeKey stmt j (Nat.le_of_lt h)))))).run
        (s, tr.challengeCache stmt) = pure (tr ⟨j.1.val, h⟩, s, tr.challengeCache stmt) := by
  rw [simulateQ_fsRandom_query, randomOracle.run_eq,
    Transcript.challengeCache_hit _ _ _ h, pure_bind]
  rfl

/-- The transformed verifier reconstructs precisely the interactive transcript from the cache. -/
lemma simulateQ_fsRandom_deriveTranscriptFS
    (tr : pSpec.Transcript (Fin.last n)) (stmt : StmtIn) (s : σ) :
    (simulateQ (fsRandomOracleImpl impl)
      (tr.toMessagesUpTo.toMessages.deriveTranscriptFS (oSpec := oSpec) stmt)).run
        (s, tr.challengeCache stmt) = pure (tr, s, tr.challengeCache stmt) := by
  apply simulateQ_deriveTranscriptSRAux
  intro i h
  have hh := simulateQ_fsRandom_hit impl tr stmt ⟨i, h⟩ i.isLt s
  simp only [simulateQ_spec_query] at hh
  exact hh



/-- Honest FS and interactive execution have the same optional outputs and final base state.
The shared cache is internal; the verifier replays every challenge from it. -/
lemma Reduction.fiatShamir_randomOracle_outputs
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn)
    (s : σ) :
    (fun z => (z.1.map (fun r => (r.1.2, r.2)), z.2.1)) <$>
      ((simulateQ ((fsRandomOracleImpl impl).addLift challengeQueryImpl :
        QueryImpl _ (StateT (σ × (srChallengeOracle StmtIn pSpec).QueryCache) ProbComp))
        (R.fiatShamir.run stmt wit).run).run (s, ∅)) =ᵈ
    (fun z => (z.1.map (fun r => (r.1.2, r.2)), z.2)) <$>
      ((simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (R.run stmt wit).run).run s) := by
  erw [Reduction.fiatShamir_run_option, liftComp_eq_liftM,
    QueryImpl.simulateQ_addLift_liftM_left, simulateQ_bind, StateT.run_bind]
  simp only [map_bind]
  apply ((R.prover.runToRoundFS_randomOracle impl stmt wit s (Fin.last n)).bind_left _).trans
  simp only [bind_assoc, pure_bind]
  rw [Reduction.run_run_eq_bind]
  simp only [Verifier.run, liftComp_eq_liftM, Prover.run, bind_assoc, pure_bind,
      simulateQ_bind, StateT.run_bind, map_bind]
  apply EvalDistEq.bind_right
  rintro ⟨⟨tr, st⟩, s'⟩
  dsimp only
  erw [simulateQ_bind, StateT.run_bind, simulateQ_addLift_run_left,
    QueryImpl.simulateQ_addLift_liftM_left]
  simp only [bind_assoc, pure_bind, map_bind]
  apply EvalDistEq.bind_right
  rintro ⟨ctx, s''⟩
  dsimp only
  erw [simulateQ_bind, StateT.run_bind]
  erw [simulateQ_fsRandom_deriveTranscriptFS, pure_bind,
    simulateQ_bind, StateT.run_bind, simulateQ_addLift_run_left,
    QueryImpl.simulateQ_addLift_liftM_left]
  simp only [bind_assoc, pure_bind, map_bind]
  apply EvalDistEq.bind_right
  rintro ⟨vr, sOut⟩
  cases vr <;> exact EvalDistEq.rfl

end RandomOracle

end Execution

open FiatShamir

section Security

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

noncomputable section

open scoped NNReal

variable [samples : ∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Perfect completeness is preserved for every fixed challenge table. Full support of each
uniform interactive challenge ensures that every transformed honest execution is an interactive
branch; verifier reconstruction replays exactly that branch. -/
theorem fiatShamir_perfectCompleteness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hR : R.perfectCompleteness init impl relIn relOut)
    (f : QueryImpl (srChallengeOracle StmtIn pSpec) Id) :
    R.fiatShamir.perfectCompleteness (do return (← init, f))
      (impl.addLift fsChallengeQueryImpl') relIn relOut := by
  erw [Reduction.perfectCompleteness_eq_prob_one] at hR ⊢
  intro stmt wit hin
  have hgood := (OracleComp.OptionT.prEvent_mk_eq_one_iff _ _).mp (hR stmt wit hin)
  apply (OracleComp.OptionT.prEvent_mk_eq_one_iff _ _).mpr
  intro result hresult
  simp only [bind_assoc, pure_bind] at hresult
  obtain ⟨s, hs, hresult⟩ := mem_support_bind_peel _ _ hresult
  rw [StateT.run'_eq] at hresult
  obtain ⟨z, hz, hresult⟩ := mem_support_map_peel _ _ hresult
  subst result
  obtain ⟨y, hy, heq⟩ := R.fiatShamir_run_support impl stmt wit s f z (by
    convert hz using 1
    congr 3
    funext q
    rcases q with q | q
    · rfl
    · exact isEmptyElim q.1)
  have hyInit : y.1 ∈ support (do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (R.run stmt wit).run).run' (← init)) := by
    apply (mem_support_bind_iff _ _ _).mpr
    refine ⟨s, hs, ?_⟩
    rw [StateT.run'_eq]
    rw [support_map]
    exact ⟨y, hy, rfl⟩
  obtain ⟨r, hr, hrel, hagree⟩ := hgood y.1 hyInit
  cases hzopt : z.1 with
  | none => simp [hzopt, hr] at heq
  | some zr =>
    refine ⟨zr, rfl, ?_⟩
    have hout : (zr.1.2, zr.2) = (r.1.2, r.2) := by
      simpa [hzopt, hr] using heq
    rcases zr with ⟨⟨_, _, _⟩, _⟩
    rcases r with ⟨⟨_, _, _⟩, _⟩
    simp only [Prod.mk.injEq] at hout
    rcases hout with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨hrel, hagree⟩

/-- Completeness error is preserved by a lazy random challenge oracle shared by the
transformed prover and verifier. The cache starts empty; distinct round indices make every
honest prover query fresh, and reconstruction replays the cached answers. Decidable equality
of query keys suffices, with no finite statement, message, or base-state assumption. -/
theorem fiatShamir_completeness_randomOracle
    [DecidableEq (srChallengeOracle StmtIn pSpec).Domain]
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (ε : ℝ≥0)
    (hR : R.completeness init impl relIn relOut ε) :
    R.fiatShamir.completeness
      (do return (← init, (∅ : (srChallengeOracle StmtIn pSpec).QueryCache)))
      (fsRandomOracleImpl impl) relIn relOut ε := by
  intro stmt wit hin
  have hd := EvalDistEq.bind_right init fun s =>
    R.fiatShamir_randomOracle_outputs impl stmt wit s
  have hp := hd.prEvent_eq (fun z => z.1.elim False (fun r =>
    (r.2, r.1.2) ∈ relOut ∧ r.1.1 = r.2))
  have h := hR stmt wit hin
  simp only [OptionT.prEvent_mk, StateT.run'_eq, bind_assoc, pure_bind,
    map_bind] at h ⊢
  simp only [map_bind, Functor.map_map, Option.elim_map, Function.comp_def] at hp h ⊢
  convert h.trans hp.ge using 1
  apply congrArg prEvent
  apply bind_congr
  intro s
  congr 3
  funext q
  rcases q with q | q
  · rfl
  · exact isEmptyElim q.1

-- TODO: state-restoration (knowledge) soundness implies (knowledge) soundness after Fiat-Shamir

end

end Security
