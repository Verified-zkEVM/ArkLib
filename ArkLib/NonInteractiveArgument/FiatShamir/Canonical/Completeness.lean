/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical
public import ArkLib.VCVioStaging.OracleComp.SimSemantics.OptionT
public import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# Perfect completeness of canonical Fiat–Shamir

A fixed verifier-message function reconstructs an honest interactive transcript supported by
uniform verifier messages. This transfers perfect completeness to the existing single-salt
reduction, including its original prover output, under a stateless ambient handler.

No uniformity is required of the salt sampler or the distribution of fixed functions.
`Canonical/RandomOracleCompleteness.lean` proves preservation of arbitrary completeness error
when prover and verifier share a lazy uniform random oracle.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut Salt : Type}

variable [VCVCompatible Salt]

namespace CanonicalFS

private abbrev fixedImpl (impl : QueryImpl oSpec ProbComp)
    (f : QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id) :
    QueryImpl (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) ProbComp :=
  impl + (fun q => pure (f q) : QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) ProbComp)

private def reconstruct
    (f : QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
    (stmt : StmtIn × Salt) (messages : pSpec.Messages) (i : Fin (n + 1)) :
    pSpec.Transcript i :=
  Fin.induction (fun j => j.elim0) (fun j prev =>
    match hd : pSpec.dir j with
    | .V_to_P => prev.concat (f ⟨⟨j, hd⟩, (stmt, messages.take j.castSucc)⟩)
    | .P_to_V => prev.concat (messages ⟨j, hd⟩)) i

set_option backward.isDefEq.respectTransparency false in
private theorem sim_round (impl : QueryImpl oSpec ProbComp)
    (f : QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (j : Fin n)
    (salt : Salt) (stmt : StmtIn) (state : P.PrvState 0) :
    simulateQ (fixedImpl impl f) (P.runToRoundFSSalted salt j.succ stmt state) = (do
      let ⟨messages, augStmt, state⟩ ←
        simulateQ (fixedImpl impl f) (P.runToRoundFSSalted salt j.castSucc stmt state)
      match hd : pSpec.dir j with
      | .V_to_P => do
        let recv ← simulateQ impl (P.receiveChallenge ⟨j, hd⟩ state)
        pure (messages.extend hd, augStmt, recv (f ⟨⟨j, hd⟩, (augStmt, messages)⟩))
      | .P_to_V => do
        let sent ← simulateQ impl (P.sendMessage ⟨j, hd⟩ state)
        pure (messages.concat hd sent.1, augStmt, sent.2)) := by
  simp only [Prover.runToRoundFSSalted, Prover.runToRoundFS, Fin.induction_succ,
    Prover.processRoundFS, contextProver, simulateQ_bind]
  apply bind_congr
  intro r
  split <;> split <;> try solve | exfalso; simp_all
  · simp only [simulateQ_bind, ← liftComp_eq_liftM, fixedImpl,
    QueryImpl.simulateQ_add_liftComp_left, simulateQ_pure]
    apply bind_congr
    intro recv
    change (simulateQ (fixedImpl impl f)
      (liftComp (query (spec := fsVerifierMessageOracle (StmtIn × Salt) pSpec)
        ⟨⟨j, by assumption⟩, (r.2.1, r.1)⟩ :
          OracleComp (fsVerifierMessageOracle (StmtIn × Salt) pSpec) _) _) >>= _) = _
    rw [QueryImpl.simulateQ_liftComp_right_eq_of_apply (fixedImpl impl f)
      (fun q => pure (f q)) (fun _ => rfl)]
    rw [simulateQ_HasQuery_query]
    rfl
  · simp only [simulateQ_bind, ← liftComp_eq_liftM, fixedImpl,
    QueryImpl.simulateQ_add_liftComp_left, simulateQ_pure]

omit [VCVCompatible Salt] in
set_option backward.isDefEq.respectTransparency false in
private theorem sim_derive_aux (impl : QueryImpl oSpec ProbComp)
    (f : QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
    (stmt : StmtIn × Salt) (messages : pSpec.Messages) (i : Fin (n + 1)) :
    simulateQ (fixedImpl impl f)
      (MessagesUpTo.deriveTranscriptSRAux stmt (Fin.last n) (Messages.asUpTo messages) i) =
      pure (reconstruct f stmt messages i) := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    simp only [MessagesUpTo.deriveTranscriptSRAux, Fin.induction_succ,
      simulateQ_bind] at ih ⊢
    rw [ih, pure_bind]
    unfold reconstruct
    rw [Fin.induction_succ]
    split <;> split <;> try solve | exfalso; simp_all
    · simp only [simulateQ_bind, simulateQ_pure]
      change (simulateQ (fixedImpl impl f)
        (liftComp (query (spec := fsVerifierMessageOracle (StmtIn × Salt) pSpec)
          ⟨⟨i, by assumption⟩, (stmt, messages.take i.castSucc)⟩ :
            OracleComp (fsVerifierMessageOracle (StmtIn × Salt) pSpec) _) _) >>= _) = _
      rw [QueryImpl.simulateQ_liftComp_right_eq_of_apply (fixedImpl impl f)
        (fun q => pure (f q)) (fun _ => rfl)]
      rw [simulateQ_HasQuery_query]
      rfl
    · rfl

omit [VCVCompatible Salt] in
private theorem sim_derive (impl : QueryImpl oSpec ProbComp)
    (f : QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
    (stmt : StmtIn × Salt) (messages : pSpec.Messages) :
    simulateQ (fixedImpl impl f) (messages.deriveTranscriptFS stmt) =
      pure (reconstruct f stmt messages (Fin.last n)) :=
  sim_derive_aux impl f stmt messages (Fin.last n)

variable [∀ i, SampleableType (pSpec.Challenge i)]

set_option backward.isDefEq.respectTransparency false in
private theorem reconstruct_supported (salt : Salt)
    (impl : QueryImpl oSpec ProbComp)
    (f : QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (i : Fin (n + 1)) (messages : pSpec.Messages)
    (z : pSpec.MessagesUpTo i × (StmtIn × Salt) × P.PrvState i)
    (hz : z ∈ support (simulateQ (fixedImpl impl f)
      (P.runToRoundFSSalted salt i stmt (P.input (stmt, wit)))))
    (hm : messages.take i = z.1) :
    z.2.1 = (stmt, salt) ∧
      (reconstruct f (stmt, salt) messages i, z.2.2) ∈ support
        (simulateQ (impl + challengeQueryImpl) (P.runToRound i stmt wit)) := by
  induction i using Fin.induction with
  | zero =>
    simp only [Prover.runToRoundFSSalted, Prover.runToRoundFS, Fin.induction_zero, simulateQ_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst z
    simp only [reconstruct, Fin.induction_zero, Prover.runToRound, simulateQ_pure,
      support_pure, Set.mem_singleton_iff, true_and, Prod.mk.injEq, and_true]
    rfl
  | succ i ih =>
    rw [sim_round] at hz
    split at hz
    · rename_i hd
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨r, hr, recv, hrecv, rfl⟩ := hz
      have hp := ih r hr (Messages.take_castSucc_of_take_succ_eq_extend _ hd messages hm)
      refine ⟨hp.1, ?_⟩
      rw [Prover.runToRound_succ, Prover.processRound_of_dir_eq_V_to_P i hd,
        simulateQ_bind, mem_support_bind_iff]
      refine ⟨_, hp.2, ?_⟩
      simp only [simulateQ_bind, mem_support_bind_iff]
      refine ⟨f ⟨⟨i, hd⟩, ((stmt, salt), messages.take i.castSucc)⟩, ?_, recv, ?_, ?_⟩
      · rw [← liftComp_eq_liftM,
          QueryImpl.simulateQ_liftComp_right_eq_of_apply _ challengeQueryImpl (fun _ => rfl)]
        have hq := simulateQ_HasQuery_query (challengeQueryImpl (pSpec := pSpec)) ⟨⟨i, hd⟩, ()⟩
        change simulateQ (challengeQueryImpl (pSpec := pSpec))
          (pSpec.getChallenge ⟨i, hd⟩) = _ at hq
        rw [hq]
        simp [challengeQueryImpl]
      · simpa only [← liftComp_eq_liftM,
          QueryImpl.simulateQ_liftComp_left_eq_of_apply (impl + challengeQueryImpl) impl
            (fun _ => rfl)] using hrecv
      · simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
        constructor
        · unfold reconstruct
          rw [Fin.induction_succ]
          split <;> first | rfl | (exfalso; simp_all)
        · rw [hp.1, Messages.take_castSucc_of_take_succ_eq_extend _ hd messages hm]
    · rename_i hd
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨r, hr, sent, hsent, rfl⟩ := hz
      have hp := ih r hr (Messages.take_castSucc_of_take_succ_eq_concat _ hd _ messages hm)
      have ha := Messages.get_of_take_succ_eq_concat _ hd _ messages hm
      refine ⟨hp.1, ?_⟩
      rw [Prover.runToRound_succ, Prover.processRound_of_dir_eq_P_to_V i hd,
        simulateQ_bind, mem_support_bind_iff]
      refine ⟨_, hp.2, ?_⟩
      simp only [simulateQ_bind, mem_support_bind_iff]
      refine ⟨sent, ?_, ?_⟩
      · simpa only [← liftComp_eq_liftM,
          QueryImpl.simulateQ_liftComp_left_eq_of_apply (impl + challengeQueryImpl) impl
            (fun _ => rfl)] using hsent
      · simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
          and_true]
        unfold reconstruct
        rw [Fin.induction_succ]
        split
        · exfalso; simp_all
        · rw [ha]

private def nargTranscript (salt : Salt) (messages : pSpec.Messages) :
    (⟨!v[.P_to_V], !v[FSSaltedNARGString pSpec Salt]⟩ : ProtocolSpec 1).FullTranscript :=
  fun i => match i with | ⟨0, _⟩ => (salt, messages)

omit [∀ i, SampleableType (pSpec.Challenge i)] in
set_option backward.isDefEq.respectTransparency false in
private theorem sim_run (impl : QueryImpl oSpec ProbComp)
    (f : QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) (stmt : StmtIn) (wit : WitIn) :
    simulateQ (fixedImpl impl f + challengeQueryImpl)
      ((R.compileFiatShamir sampleSalt).run stmt wit).run = (do
      let salt ← simulateQ impl sampleSalt
      let r ← simulateQ (fixedImpl impl f)
        (R.prover.runToRoundFSSalted salt (Fin.last n) stmt (R.prover.input (stmt, wit)))
      let out ← simulateQ impl (R.prover.output r.2.2)
      let v ← simulateQ impl
        (R.verifier.verify stmt (reconstruct f (stmt, salt) r.1 (Fin.last n))).run
      pure (v.map (fun stmtOut => ((nargTranscript salt r.1, out), stmtOut)))) := by
  have he : (challengeQueryImpl : QueryImpl
      ([(⟨!v[.P_to_V], !v[FSSaltedNARGString pSpec Salt]⟩ :
        ProtocolSpec 1).Challenge]ₒ'challengeOracleInterface)
      ProbComp) = (fun q => isEmptyElim q.1) := by
    funext q
    exact isEmptyElim q.1
  rw [he, Reduction.simulate_narg_run]
  simp only [Reduction.compileFiatShamir, Prover.compileFiatShamir,
    simulateQ_bind, simulateQ_pure, ← liftComp_eq_liftM, fixedImpl,
    QueryImpl.simulateQ_add_liftComp_left,
    bind_assoc, pure_bind]
  apply bind_congr
  intro salt
  apply bind_congr
  intro r
  apply bind_congr
  intro out
  simp only [Verifier.compileFiatShamir, OptionT.run_bind, Option.elimM,
    ← monadLift_liftM_OptionT, OptionT.run_monadLift, monadLift_self,
    ← liftComp_eq_liftM, simulateQ_bind, bind_map_left, Option.elim_some]
  simp only [sim_derive, pure_bind, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_getM_run, bind_pure]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem sim_ip_run (impl : QueryImpl oSpec ProbComp)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn) :
    simulateQ (impl + challengeQueryImpl) (R.run stmt wit).run = (do
      let t ← simulateQ (impl + challengeQueryImpl) (R.prover.runToRound (Fin.last n) stmt wit)
      let out ← simulateQ impl (R.prover.output t.2)
      let v ← simulateQ impl (R.verifier.verify stmt t.1).run
      pure (v.map (fun stmtOut => ((t.1, out), stmtOut)))) := by
  simp only [Reduction.run, Prover.run, Verifier.run, OptionT.run_bind, Option.elimM,
    ← monadLift_liftM_OptionT, OptionT.run_monadLift, monadLift_self,
    ← liftComp_eq_liftM, simulateQ_bind,
    bind_map_left, Option.elim_some, bind_assoc, pure_bind,
    QueryImpl.simulateQ_add_liftComp_left, simulateQ_getM_run]
  apply bind_congr
  intro t
  apply bind_congr
  intro out
  apply bind_congr
  intro v
  cases v <;> rfl

set_option backward.isDefEq.respectTransparency false in
private theorem fixed_perfectCompleteness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec ProbComp)
    (f : QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (h : R.perfectCompleteness init (impl.liftTarget (StateT σ ProbComp)) relIn relOut) :
    (R.compileFiatShamir sampleSalt).perfectCompleteness init
      ((fixedImpl impl f).liftTarget (StateT σ ProbComp)) relIn relOut := by
  rw [Reduction.perfectCompleteness_stateless_iff] at h ⊢
  intro stmt wit hIn x hx
  rw [sim_run] at hx
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hx
  obtain ⟨salt, _hsalt, r, hr, out, hout, v, hv, rfl⟩ := hx
  have ht := (reconstruct_supported salt impl f R.prover stmt wit (Fin.last n)
    r.1 r hr rfl).2
  let t := reconstruct f (stmt, salt) r.1 (Fin.last n)
  have hy : v.map (fun stmtOut => ((t, out), stmtOut)) ∈
      support (simulateQ (impl + challengeQueryImpl) (R.run stmt wit).run) := by
    rw [sim_ip_run]
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
    exact ⟨_, ht, out, hout, v, hv, rfl⟩
  obtain ⟨result, heq, hrel, hstmt⟩ := h stmt wit hIn _ hy
  cases v with
  | none => simp at heq
  | some b =>
    cases heq
    exact ⟨_, rfl, hrel, hstmt⟩

end CanonicalFS

open CanonicalFS

variable [∀ i, SampleableType (pSpec.Challenge i)]

set_option backward.isDefEq.respectTransparency false in
/-- **Perfect completeness of canonical Fiat–Shamir (CO25, Construction 3.17).**
A perfectly complete interactive reduction remains perfectly complete under a stateless ambient
handler and one fixed, consistently answered verifier-message function sampled at initialization.
The function distribution and the salt sampler need not be uniform. This is a probability-one
result; arbitrary completeness error is preserved under the random-oracle assumptions of
`canonicalFiatShamir_completeness_randomOracle`. -/
theorem canonicalFiatShamir_perfectCompleteness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec ProbComp)
    (fsInit : ProbComp (QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (h : R.perfectCompleteness init (impl.liftTarget (StateT σ ProbComp)) relIn relOut) :
    (R.compileFiatShamir sampleSalt).perfectCompleteness fsInit
      ((impl.liftTarget (StateT (QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
        ProbComp)).addLift fsChallengeQueryImpl') relIn relOut := by
  rw [Reduction.perfectCompleteness_eq_prob_one]
  intro stmt wit hIn
  rw [OptionT.prEvent_mk_eq_one_iff]
  intro x hx
  simp only [mem_support_bind_iff, StateT.run'_eq, support_map, Set.mem_image] at hx
  obtain ⟨f, _hf, z, hz, rfl⟩ := hx
  rw [simulateQ_readOnly_run (fixed := fun f => fixedImpl impl f + challengeQueryImpl)] at hz
  rotate_left
  · intro q f
    rcases q with q | q
    · rcases q with q | q
      · simp [fixedImpl, QueryImpl.addLift_def, QueryImpl.liftTarget]
      · simp [fixedImpl, QueryImpl.addLift_def, QueryImpl.liftTarget, fsChallengeQueryImpl',
          StateT.run]
    · exact isEmptyElim q.1
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨result, hresult, rfl⟩ := hz
  have hfixed := fixed_perfectCompleteness init impl f R sampleSalt relIn relOut h
  rw [Reduction.perfectCompleteness_stateless_iff] at hfixed
  exact hfixed stmt wit hIn result hresult

/-- Perfect completeness of canonical Fiat-Shamir for every configured salt length.
The private ambient sampler is invoked once per NARG string. -/
theorem fiatShamirSalted_perfectCompleteness {σ U : Type} [VCVCompatible U] (saltLength : ℕ)
    (init : ProbComp σ) (impl : QueryImpl oSpec ProbComp)
    (fsInit : ProbComp
      (QueryImpl (fsVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec) Id))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec (Vector U saltLength))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (h : R.perfectCompleteness init (impl.liftTarget (StateT σ ProbComp)) relIn relOut) :
    (R.fiatShamirSalted saltLength sampleSalt).perfectCompleteness fsInit
      ((impl.liftTarget (StateT
        (QueryImpl (fsVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec) Id)
        ProbComp)).addLift fsChallengeQueryImpl') relIn relOut := by
  exact canonicalFiatShamir_perfectCompleteness init impl fsInit R sampleSalt relIn relOut h
