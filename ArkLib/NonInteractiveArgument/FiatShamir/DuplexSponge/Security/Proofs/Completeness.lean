/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.DuplexSponge.InitialObject
public import ArkLib.NonInteractiveArgument.FiatShamir.DuplexSponge.Security.Proofs.Execution
public import ArkLib.NonInteractiveArgument.FiatShamir.DuplexSponge.Security.Proofs.MessageLaw
public import VCVio.OracleComp.SimSemantics.StateT.Measure
public import ArkLib.OracleReduction.Execution.Transcript
public import ArkLib.VCVioStaging.OracleComp.SimSemantics.OptionT

/-!
# Perfect completeness of duplex-sponge Fiat–Shamir

Fixed-realization transcript reconstruction establishes completeness of the full execution.
Equality of NARG-string distributions then transfers it to the canonical DSFS argument prover
under a stateless ambient handler, without executing terminal prover work.

## Supported public results

The canonical theorem statements are in `Security/Completeness.lean`, parameterized by salt length.
This module contains their supporting arguments.

- `duplex_sponge_fiat_shamir_perfect_completeness`: perfect completeness of the salted
  construction for any ambient-oracle salt sampler.

The conclusion concerns the canonical proof compiler with accept/reject output. The source
premise has its own initialization; the target samples one fixed public sponge realization.

## References

* [Chiesa, A. and Orrù, M., *A Fiat–Shamir Transformation From Duplex Sponges*][CO25]
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory DuplexSpongeFS

namespace DuplexSpongeFS

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut σ : Type} {δ : ℕ}
  {U : Type} [SpongeUnit U] [SpongeSize] [Codec pSpec U]

/-- One prover message containing the salt and all interactive prover messages. -/
private abbrev saltedNARGSpec (pSpec : ProtocolSpec n) (U : Type) (δ : ℕ) : ProtocolSpec 1 :=
  ⟨!v[.P_to_V], !v[DSFSTypedNARGString (pSpec := pSpec) (U := U) δ]⟩

/-! ### Transcript reconstruction for a fixed sponge realization -/

private theorem lift_forward_liftM {α : Type}
    (oa : OracleComp (forwardPermutationOracle (CanonicalSpongeState U)) α) :
    liftComp (liftM oa : OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) α)
        (oSpec + duplexSpongeOracle StmtIn U) =
      liftComp oa (oSpec + duplexSpongeOracle StmtIn U)
        (h := dsfsForwardPermutationLift) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [monadLift_bind, liftComp_bind, ih]
    rfl

private abbrev reconstruct
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (sponge : CanonicalDuplexSponge U) (messages : pSpec.Messages) (i : Fin (n + 1)) :=
  evalWithAnswerFn (fun q => f (.inr (.inl q))) (InitialObject.rounds sponge messages i)

private theorem reconstruct_verifierMessage
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (sponge : CanonicalDuplexSponge U) (messages : pSpec.Messages)
    (i : Fin n) (hd : pSpec.dir i = .V_to_P) :
    reconstruct f sponge messages i.succ =
      let t := reconstruct f sponge messages i.castSucc
      let sq := evalWithAnswerFn (fun q => f (.inr (.inl q)))
        (t.1.squeeze (verifierMessageSize ⟨i, hd⟩))
      (sq.2, t.2.concat ((Codec.instDeserializeChallenge ⟨i, hd⟩).deserialize sq.1)) := by
  simp only [reconstruct, InitialObject.rounds, Fin.induction_succ, evalWithAnswerFn_bind]
  split
  · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    rfl
  · rename_i he
    exact False.elim (by simp [hd] at he)

private theorem reconstruct_proverMessage
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (sponge : CanonicalDuplexSponge U) (messages : pSpec.Messages)
    (i : Fin n) (hd : pSpec.dir i = .P_to_V) :
    reconstruct f sponge messages i.succ =
      let t := reconstruct f sponge messages i.castSucc
      let sp := evalWithAnswerFn (fun q => f (.inr (.inl q)))
        (t.1.absorb ((Codec.instSerializeMessage ⟨i, hd⟩).serialize (messages ⟨i, hd⟩)).toList)
      (sp, t.2.concat (messages ⟨i, hd⟩)) := by
  simp only [reconstruct, InitialObject.rounds, Fin.induction_succ, evalWithAnswerFn_bind]
  split
  · rename_i he
    exact False.elim (by simp [hd] at he)
  · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    rfl

/-! ### Honest execution with a stateful ambient oracle -/

private theorem sim_forward {α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (oa : OracleComp (forwardPermutationOracle (CanonicalSpongeState U)) α) :
    simulateQ (ScheduledExecution.interp impl f)
      (liftComp oa (oSpec + duplexSpongeOracle StmtIn U)
        (h := dsfsForwardPermutationLift)) =
      pure (evalWithAnswerFn (fun q => f (.inr (.inl q))) oa) :=
  ScheduledExecution.interp_forward impl f oa

private theorem sim_reconstructedRun_verifierMessage
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (i : Fin n)
    (hd : pSpec.dir i = .V_to_P)
    (salt : Vector U δ) (stmt : StmtIn) (state : P.PrvState 0) :
    simulateQ (ScheduledExecution.interp impl f)
      (ScheduledExecution.reconstructedRun P salt i.succ stmt state) = (do
      let r ← simulateQ (ScheduledExecution.interp impl f)
        (ScheduledExecution.reconstructedRun P salt i.castSucc stmt state)
      let recv ← simulateQ impl (P.receiveChallenge ⟨i, hd⟩ r.2.2)
      let sq := evalWithAnswerFn (fun q => f (.inr (.inl q)))
        (r.2.1.squeeze (verifierMessageSize ⟨i, hd⟩))
      pure (r.1.extend hd, sq.2,
        recv ((Codec.instDeserializeChallenge ⟨i, hd⟩).deserialize sq.1))) := by
  rw [ScheduledExecution.reconstructedRun_succ]
  simp only [simulateQ_bind]
  apply bind_congr
  intro r
  split
  · simp only [simulateQ_bind, ← liftComp_eq_liftM,
    ScheduledExecution.interp_liftComp_left, sim_forward,
      pure_bind, simulateQ_pure]
  · rename_i he
    exact False.elim (by simp [hd] at he)

private theorem sim_reconstructedRun_proverMessage
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (i : Fin n)
    (hd : pSpec.dir i = .P_to_V)
    (salt : Vector U δ) (stmt : StmtIn) (state : P.PrvState 0) :
    simulateQ (ScheduledExecution.interp impl f)
      (ScheduledExecution.reconstructedRun P salt i.succ stmt state) = (do
      let r ← simulateQ (ScheduledExecution.interp impl f)
        (ScheduledExecution.reconstructedRun P salt i.castSucc stmt state)
      let sent ← simulateQ impl (P.sendMessage ⟨i, hd⟩ r.2.2)
      let sp := evalWithAnswerFn (fun q => f (.inr (.inl q)))
        (r.2.1.absorb ((Codec.instSerializeMessage ⟨i, hd⟩).serialize sent.1).toList)
      pure (r.1.concat hd sent.1, sp, sent.2)) := by
  rw [ScheduledExecution.reconstructedRun_succ]
  simp only [simulateQ_bind]
  apply bind_congr
  intro r
  split
  · rename_i he
    exact False.elim (by simp [hd] at he)
  · simp only [simulateQ_bind, ← liftComp_eq_liftM,
    ScheduledExecution.interp_liftComp_left, sim_forward,
      pure_bind, simulateQ_pure]

private theorem sim_initial
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (stmt : StmtIn) :
    simulateQ (ScheduledExecution.interp impl f)
      (liftM (DuplexSponge.start (U := U) (C := CanonicalSpongeState U) stmt) :
        OracleComp (oSpec + duplexSpongeOracle StmtIn U) _) =
      pure (evalWithAnswerFn (fun q => f (.inl q)) (DuplexSponge.start stmt)) := by
  simp only [DuplexSponge.start, monadLift_bind, monadLift_pure,
    simulateQ_bind, simulateQ_pure, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rfl

private abbrev saltedInitial
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (stmt : StmtIn) (salt : Vector U δ) : CanonicalDuplexSponge U :=
  let sponge := evalWithAnswerFn (fun q => f (.inl q)) (DuplexSponge.start stmt)
  evalWithAnswerFn (fun q => f (.inr (.inl q))) (sponge.absorb salt.toList)

variable [∀ i, SampleableType (pSpec.Challenge i)]

omit [SpongeSize] in
private theorem sim_ip_ambient {α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (oa : OracleComp oSpec α) :
    simulateQ (QueryImpl.addLift impl (challengeQueryImpl (pSpec := pSpec)) :
      QueryImpl (oSpec + [pSpec.Challenge]ₒ'challengeOracleInterface) (StateT σ ProbComp))
      (liftComp oa (oSpec + [pSpec.Challenge]ₒ'challengeOracleInterface)) = simulateQ impl oa := by
  exact QueryImpl.simulateQ_liftComp_left_eq_of_apply _ impl (fun _ => rfl) oa

private theorem reconstruct_runToRound_stateful (salt : Vector U δ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (i : Fin (n + 1)) (messages : pSpec.Messages)
    (s : σ) (z : (pSpec.MessagesUpTo i × CanonicalDuplexSponge U × P.PrvState i) × σ)
    (hz : z ∈ support ((simulateQ (ScheduledExecution.interp impl f)
      (ScheduledExecution.reconstructedRun (U := U) P salt i stmt (P.input (stmt, wit)))).run s))
    (hm : messages.take i = z.1.1) :
    let initial := saltedInitial f stmt salt
    let t := reconstruct f initial messages i
    t.1 = z.1.2.1 ∧ ((t.2, z.1.2.2), z.2) ∈ support
      ((simulateQ (QueryImpl.addLift impl (challengeQueryImpl (pSpec := pSpec)) :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ'challengeOracleInterface) (StateT σ ProbComp))
        (P.runToRound i stmt wit)).run s) := by
  induction i using Fin.induction with
  | zero =>
    simp only [ScheduledExecution.reconstructedRun_zero, simulateQ_bind,
      sim_initial, sim_forward, simulateQ_pure, pure_bind, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst z
    simp only [reconstruct, InitialObject.rounds,
      Fin.induction_zero, evalWithAnswerFn_pure, Prover.runToRound,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, true_and]
    congr 2
  | succ i ih =>
    by_cases hd : pSpec.dir i = .V_to_P
    · rw [sim_reconstructedRun_verifierMessage impl f P i hd salt stmt (P.input (stmt, wit))] at hz
      simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨r, hr, recv, hrecv, rfl⟩ := hz
      have hp := ih r hr (Messages.take_castSucc_of_take_succ_eq_extend _ hd messages hm)
      dsimp only
      rw [reconstruct_verifierMessage f _ messages i hd]
      dsimp only at hp ⊢
      rw [hp.1]
      refine ⟨rfl, ?_⟩
      rw [Prover.runToRound_succ, Prover.processRound_of_dir_eq_V_to_P i hd,
        simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
      refine ⟨_, hp.2, ?_⟩
      simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
      let c := (Codec.instDeserializeChallenge ⟨i, hd⟩).deserialize
        (evalWithAnswerFn (fun q => f (.inr (.inl q)))
          (r.1.2.1.squeeze (verifierMessageSize ⟨i, hd⟩))).1
      refine ⟨(c, r.2), ?_, ?_⟩
      · rw [← liftComp_eq_liftM]
        rw [QueryImpl.simulateQ_liftComp_right_eq_of_apply _
          ((challengeQueryImpl (pSpec := pSpec)).liftTarget (StateT σ ProbComp))
          (fun _ => rfl)]
        rw [simulateQ_liftTarget]
        simp only [StateT.run_liftM]
        have hq := simulateQ_HasQuery_query (challengeQueryImpl (pSpec := pSpec)) ⟨⟨i, hd⟩, ()⟩
        change simulateQ (challengeQueryImpl (pSpec := pSpec))
          (pSpec.getChallenge ⟨i, hd⟩) = _ at hq
        rw [hq]
        simp [challengeQueryImpl]
      · refine ⟨recv, ?_, ?_⟩
        · simpa only [← liftComp_eq_liftM, sim_ip_ambient] using hrecv
        · simp [c]
    · have hd : pSpec.dir i = .P_to_V := by cases he : pSpec.dir i <;> simp_all
      rw [sim_reconstructedRun_proverMessage impl f P i hd salt stmt (P.input (stmt, wit))] at hz
      simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨r, hr, sent, hsent, rfl⟩ := hz
      have hp := ih r hr (Messages.take_castSucc_of_take_succ_eq_concat _ hd _ messages hm)
      have ha := Messages.get_of_take_succ_eq_concat _ hd _ messages hm
      dsimp only
      rw [reconstruct_proverMessage f _ messages i hd]
      dsimp only at hp ⊢
      rw [hp.1, ha]
      refine ⟨rfl, ?_⟩
      rw [Prover.runToRound_succ, Prover.processRound_of_dir_eq_P_to_V i hd,
        simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
      refine ⟨_, hp.2, ?_⟩
      simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
      refine ⟨sent, ?_, ?_⟩
      · simpa only [← liftComp_eq_liftM, sim_ip_ambient] using hsent
      · simp

omit [∀ i, SampleableType (pSpec.Challenge i)] in
private theorem sim_reconstruct
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (sponge : CanonicalDuplexSponge U) (messages : pSpec.Messages) (i : Fin (n + 1)) :
    simulateQ (ScheduledExecution.interp impl f) (liftComp
      (messages.deriveTranscriptDSFSAux (oSpec := oSpec) (StmtIn := StmtIn) sponge i)
      (oSpec + duplexSpongeOracle StmtIn U)) =
      pure (reconstruct f sponge messages i) := by
  rw [← InitialObject.rounds_eq_existing, lift_forward_liftM]
  exact sim_forward impl f _

omit [∀ i, SampleableType (pSpec.Challenge i)] in
private theorem sim_derive (salt : Vector U δ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (stmt : StmtIn) (messages : pSpec.Messages) :
    simulateQ (ScheduledExecution.interp impl f) (liftComp
      (messages.deriveTranscriptDSFS (oSpec := oSpec) (U := U) stmt salt)
      (oSpec + duplexSpongeOracle StmtIn U)) =
      pure (reconstruct f (saltedInitial f stmt salt) messages (Fin.last n)) := by
  unfold ProtocolSpec.Messages.deriveTranscriptDSFS
  have hb := liftComp_bind (oSpec + duplexSpongeOracle StmtIn U)
    (liftM (DuplexSponge.start stmt) : OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U)
      (CanonicalDuplexSponge U))
    (fun sponge0 => do
      let sponge ← liftM (DuplexSponge.absorb sponge0 salt.toList)
      messages.deriveTranscriptDSFSAux (oSpec := oSpec) (StmtIn := StmtIn) sponge (Fin.last n))
  refine (congrArg (simulateQ (ScheduledExecution.interp impl f)) hb).trans ?_
  rw [simulateQ_bind]
  change (simulateQ (ScheduledExecution.interp impl f) (liftM (DuplexSponge.start stmt) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U) (CanonicalDuplexSponge U)) >>= _) = _
  rw [sim_initial, pure_bind]
  simp only [liftComp_bind, simulateQ_bind, lift_forward_liftM, sim_forward, pure_bind,
    sim_reconstruct, saltedInitial]


set_option backward.isDefEq.respectTransparency false in
/-- On an honest run, reconstruction recovers the transcript recorded in private prover state.
This quantitative-useful equality retains the execution law rather than just acceptance support.
-/
theorem deriveTranscript_withTranscript (salt : Vector U δ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (s : σ)
    (z : (pSpec.Messages × CanonicalDuplexSponge U ×
      (pSpec.FullTranscript × P.PrvState (Fin.last n))) × σ)
    (hz : z ∈ support ((simulateQ (ScheduledExecution.interp impl f)
      (ScheduledExecution.reconstructedRun (U := U) P.withTranscript salt (Fin.last n) stmt
        (P.withTranscript.input (stmt, wit)))).run s)) :
    simulateQ (ScheduledExecution.interp impl f) (liftComp
      (z.1.1.deriveTranscriptDSFS (oSpec := oSpec) (U := U) stmt salt)
      (oSpec + duplexSpongeOracle StmtIn U)) = pure (z.1.2.1, z.1.2.2.1) := by
  have hr := reconstruct_runToRound_stateful salt impl f P.withTranscript stmt wit
    (Fin.last n) z.1.1 s z hz (by rfl)
  obtain ⟨hsponge, hrun⟩ := hr
  rw [Prover.withTranscript_runToRound] at hrun
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hrun
  obtain ⟨y, _hy, heq⟩ := hrun
  have htranscript := (congrArg (fun x => x.1.1) heq).symm.trans
    (congrArg (fun x => x.1.2.1) heq)
  rw [sim_derive]
  exact congrArg pure (Prod.ext hsponge htranscript)

private def nargTranscript (salt : Vector U δ) (messages : pSpec.Messages) :
    (saltedNARGSpec pSpec U δ).FullTranscript :=
  fun i => match i with | ⟨0, _⟩ => (salt, messages)

/-- Observe the full execution for the completeness argument, including the original output.
This computation is a proof comparison, not a compiled prover or reduction. -/
private def fullExecution (salt : Vector U δ)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn) :
    OracleComp (oSpec + duplexSpongeOracle StmtIn U)
      (Option (((saltedNARGSpec pSpec U δ).FullTranscript × StmtOut × WitOut) × StmtOut)) := do
  let runResult ← R.prover.referenceRunDSFSSalted salt (Fin.last n) stmt
    (R.prover.input (stmt, wit))
  let proverOutput ← liftComp (R.prover.output runResult.2.2)
    (oSpec + duplexSpongeOracle StmtIn U)
  let verifierOutput ← (R.verifier.duplexSpongeFiatShamir δ).verify stmt
    (nargTranscript salt runResult.1) |>.run
  pure (verifierOutput.map (fun stmtOut =>
    ((nargTranscript (pSpec := pSpec) salt runResult.1, proverOutput), stmtOut)))

set_option backward.isDefEq.respectTransparency false in
omit [∀ i, SampleableType (pSpec.Challenge i)] in
private theorem sim_full_execution (salt : Vector U δ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn) :
    simulateQ (ScheduledExecution.interp impl f) (fullExecution salt R stmt wit) = (do
      let runResult ← simulateQ (ScheduledExecution.interp impl f)
        (ScheduledExecution.reconstructedRun (U := U) R.prover salt (Fin.last n) stmt
          (R.prover.input (stmt, wit)))
      let proverOutput ← simulateQ impl (R.prover.output runResult.2.2)
      let initialSponge := saltedInitial f stmt salt
      let reconstructedTranscript :=
        reconstruct (pSpec := pSpec) f initialSponge runResult.1 (Fin.last n)
      let verifierOutput ← simulateQ impl (R.verifier.verify stmt reconstructedTranscript.2).run
      pure (verifierOutput.map (fun stmtOut =>
        ((nargTranscript (pSpec := pSpec) salt runResult.1, proverOutput), stmtOut)))) := by
  simp only [ScheduledExecution.reconstructedRun, fullExecution, ← liftComp_eq_liftM,
    simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
  apply bind_congr
  intro runResult
  simp only [sim_forward, pure_bind, ScheduledExecution.interp_liftComp_left]
  apply bind_congr
  intro proverOutput
  simp only [Verifier.duplexSpongeFiatShamir, nargTranscript,
    OptionT.run_bind, Option.elimM, ← monadLift_liftM_OptionT,
    OptionT.run_monadLift, monadLift_self, ← liftComp_eq_liftM,
    simulateQ_bind, bind_map_left, Option.elim_some]
  simp only [sim_derive, pure_bind]
  simp only [ScheduledExecution.interp_liftComp_left, simulateQ_getM_run,
    bind_pure]

omit [SpongeSize] in
private theorem sim_ip_run
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn) :
    simulateQ (QueryImpl.addLift impl (challengeQueryImpl (pSpec := pSpec)) :
      QueryImpl (oSpec + [pSpec.Challenge]ₒ'challengeOracleInterface) (StateT σ ProbComp))
      (R.run stmt wit).run = (do
      let t ← simulateQ (QueryImpl.addLift impl (challengeQueryImpl (pSpec := pSpec)) :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ'challengeOracleInterface) (StateT σ ProbComp))
        (R.prover.runToRound (Fin.last n) stmt wit)
      let out ← simulateQ impl (R.prover.output t.2)
      let v ← simulateQ impl (R.verifier.verify stmt t.1).run
      pure (v.map (fun stmtOut => ((t.1, out), stmtOut)))) := by
  simp only [Reduction.run, Prover.run, OptionT.run_bind, Option.elimM,
    OptionT.run_monadLift, monadLift_self, simulateQ_bind, map_bind, map_pure,
    bind_assoc, pure_bind, Option.elim_some]
  apply bind_congr
  intro t
  simp only [← liftComp_eq_liftM, sim_ip_ambient]
  apply bind_congr
  intro out
  simp only [simulateQ_bind, ← monadLift_liftM_OptionT, OptionT.run_monadLift, simulateQ_map,
    ← liftComp_eq_liftM, monadLift_self, sim_ip_ambient, bind_map_left,
    Option.elim_some, simulateQ_getM_run, OptionT.run_pure]
  apply bind_congr
  intro v
  cases v <;> rfl

/-- Every transformed output is supported by an interactive run with the same ambient state. -/
private theorem stateful_output_supported (salt : Vector U δ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (s : σ)
    (x : Option (((saltedNARGSpec pSpec U δ).FullTranscript ×
      StmtOut × WitOut) × StmtOut) × σ)
    (hx : x ∈ support
      ((simulateQ (ScheduledExecution.interp impl f) (fullExecution salt R stmt wit)).run s)) :
    ∃ y ∈ support ((simulateQ (QueryImpl.addLift impl (challengeQueryImpl (pSpec := pSpec)) :
      QueryImpl (oSpec + [pSpec.Challenge]ₒ'challengeOracleInterface) (StateT σ ProbComp))
      (R.run stmt wit).run).run s),
      x.1.map (fun z => (z.1.2, z.2)) = y.1.map (fun z => (z.1.2, z.2)) := by
  rw [sim_full_execution salt] at hx
  simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hx
  obtain ⟨r, hr, out, hout, v, hv, rfl⟩ := hx
  have ht := reconstruct_runToRound_stateful salt impl f R.prover stmt wit (Fin.last n)
    (show pSpec.Messages from r.1.1) s r hr rfl
  dsimp only at ht ⊢
  let t := (reconstruct (pSpec := pSpec) f (saltedInitial f stmt salt) r.1.1 (Fin.last n)).2
  refine ⟨(v.1.map (fun stmtOut => ((t, out.1), stmtOut)), v.2), ?_, ?_⟩
  · rw [sim_ip_run]
    simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff]
    exact ⟨_, ht.2, out, hout, v, hv, rfl⟩
  · cases v.1 <;> rfl

private theorem stateful_perfectCompleteness (salt : Vector U δ)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (f : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (h : R.perfectCompleteness init impl relIn relOut) :
    ∀ stmt wit, (stmt, wit) ∈ relIn →
      Pr{let result ← OptionT.mk (do
        let s ← init
        (simulateQ (ScheduledExecution.interp impl f) (fullExecution salt R stmt wit)).run' s)}[
        (result.2, result.1.2.2) ∈ relOut ∧ result.1.2.1 = result.2] = 1 := by
  rw [Reduction.perfectCompleteness_eq_prob_one] at h
  intro stmt wit hIn
  have hc := h stmt wit hIn
  change (Pr{let result ← OptionT.mk (do
    let s ← init
    (simulateQ (QueryImpl.addLift impl (challengeQueryImpl (pSpec := pSpec)) :
      QueryImpl (oSpec + [pSpec.Challenge]ₒ'challengeOracleInterface) (StateT σ ProbComp))
      (R.run stmt wit).run).run' s)}[
    (result.2, result.1.2.2) ∈ relOut ∧ result.1.2.1 = result.2] = 1) at hc
  rw [OptionT.prEvent_mk_eq_one_iff] at hc ⊢
  intro x hx
  simp only [mem_support_bind_iff, StateT.run'_eq, support_map, Set.mem_image] at hx
  obtain ⟨s, hs, z, hz, rfl⟩ := hx
  obtain ⟨y, hy, heq⟩ := stateful_output_supported salt impl f R stmt wit s z hz
  have hy' : y.1 ∈ support (do
      let s ← init
      (simulateQ (QueryImpl.addLift impl (challengeQueryImpl (pSpec := pSpec)) :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ'challengeOracleInterface) (StateT σ ProbComp))
        (R.run stmt wit).run).run' s) := by
    simp only [mem_support_bind_iff, StateT.run'_eq, support_map, Set.mem_image]
    exact ⟨s, hs, y, hy, rfl⟩
  obtain ⟨result, hr, hrel, hstmt⟩ := hc _ hy'
  rw [hr] at heq
  cases hx : z.1 with
  | none => simp [hx] at heq
  | some result' =>
    simp only [hx, Option.map_some, Option.some.injEq, Prod.mk.injEq] at heq
    refine ⟨result', rfl, ?_, ?_⟩
    · simpa only [heq.1, heq.2] using hrel
    · simpa only [heq.1, heq.2] using hstmt

end DuplexSpongeFS

namespace DuplexSpongeFS.ProofExecution

local instance nonInteractiveProverOnly (Message : Type) :
    ProverOnly (⟨!v[.P_to_V], !v[Message]⟩ : ProtocolSpec 1) where
  prover_first' := rfl

/-! ## Shared acceptance transport -/

section AcceptanceTransport

set_option backward.isDefEq.respectTransparency false in
/-- Message-law equality transfers acceptance from an execution observation to the
canonical one-message proof. The observation does not define another compiled prover. -/
private theorem narg_acceptance_of_prover_message_law
    {ι : Type} {spec : OracleSpec ι} {Message Stmt Wit State : Type}
    (Q : NonInteractiveReduction Message spec Stmt Wit Bool Unit)
    (impl : QueryImpl spec ProbComp) (stmt : Stmt) (wit : Wit)
    (messages : ProbComp (Message × State)) (output : State → ProbComp (Bool × Unit))
    (hout : ∀ state, Q.prover.output state = pure (true, ()))
    (hmsg : ∀ event : Message → Prop,
      Pr{let sent ← (simulateQ impl
        (Q.prover.sendMessage ⟨0, rfl⟩ (Q.prover.input (stmt, wit))))}[event sent.1] =
      Pr{let sent ← messages}[event sent.1])
    (hP : ∀ x ∈ support (do
      let sent ← messages
      let out ← output sent.2
      let transcript : (⟨!v[.P_to_V], !v[Message]⟩ : ProtocolSpec 1).FullTranscript :=
        fun i => match i with | ⟨0, _⟩ => sent.1
      let accepted ← simulateQ impl (Q.verifier.verify stmt transcript).run
      pure (accepted.map (fun b => ((transcript, out), b)))),
      ∃ result, x = some result ∧ result.2 = true) :
    ∀ x ∈ support (simulateQ (impl + (fun q => isEmptyElim q.1 : QueryImpl
        ([(⟨!v[.P_to_V], !v[Message]⟩ : ProtocolSpec 1).Challenge]ₒ'challengeOracleInterface)
        ProbComp)) (Q.run stmt wit).run),
      ∃ result, x = some result ∧ result.2 = true ∧ result.1.2.1 = true := by
  intro x hx
  rw [Reduction.simulate_narg_run] at hx
  simp only [hout, simulateQ_pure, pure_bind, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hx
  obtain ⟨sent, hsent, accepted, haccepted, rfl⟩ := hx
  have hpos : 0 < Pr{let pair ← (simulateQ impl
      (Q.prover.sendMessage ⟨0, rfl⟩ (Q.prover.input (stmt, wit))))}[pair.1 = sent.1] :=
    OracleComp.prEvent_pos_iff _ _ |>.mpr ⟨sent, hsent, rfl⟩
  rw [hmsg (fun message => message = sent.1)] at hpos
  obtain ⟨oldSent, holdSent, heq⟩ := (OracleComp.prEvent_pos_iff _ _).mp hpos
  obtain ⟨oldOutput, holdOutput⟩ := support_nonempty (output oldSent.2)
  obtain ⟨result, hr, htrue⟩ := hP _ (by
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
    refine ⟨oldSent, holdSent, oldOutput, holdOutput, accepted, ?_, rfl⟩
    convert haccepted using 1
    congr 4
    funext i
    fin_cases i
    exact heq)
  cases accepted with
  | none => simp at hr
  | some b =>
    simp only [Option.map_some, Option.some.injEq] at hr
    subst result
    exact ⟨_, rfl, htrue, rfl⟩

end AcceptanceTransport

/-! ## Salted execution at a fixed oracle -/

section SaltedExecution

set_option backward.isDefEq.respectTransparency false in
/-- Perfect completeness of the terminal-erasing prover for every fixed salt and sponge.
The interactive premise uses only its own stateless ambient handler. -/
theorem perfectCompleteness_fixedOracle
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn U σ : Type} [SpongeUnit U] [SpongeSize] [Codec pSpec U]
    [∀ i, SampleableType (pSpec.Challenge i)]
    {δ : ℕ} (salt : Vector U δ) (P : Proof oSpec StmtIn WitIn pSpec)
    (init : ProbComp σ) (impl : QueryImpl oSpec ProbComp)
    (answer : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (relation : Set (StmtIn × WitIn))
    (h : P.perfectCompleteness init (impl.liftTarget (StateT σ ProbComp)) relation) :
    (P.duplexSpongeFiatShamir (U := U) δ (pure salt)).perfectCompleteness init
      ((ScheduledExecution.interp impl answer).liftTarget (StateT σ ProbComp))
      relation acceptRejectRel := by
  have hc := stateful_perfectCompleteness salt init
    (impl.liftTarget (StateT σ ProbComp)) answer P relation acceptRejectRel h
  have hi : ScheduledExecution.interp (impl.liftTarget (StateT σ ProbComp)) answer =
      (ScheduledExecution.interp impl answer).liftTarget (StateT σ ProbComp) := by
    funext q
    cases q <;> rfl
  simp only [hi, simulateQ_liftTarget, StateT.run'_eq, StateT.run_monadLift,
    map_bind, map_pure, monadLift_self, bind_pure, OptionT.prEvent_mk_eq_one_iff,
    mem_support_bind_iff] at hc
  apply (Proof.perfectCompleteness_stateless_iff _ init _ relation).mpr
  intro stmt wit hrel x hx
  have he : challengeQueryImpl (pSpec := (⟨!v[.P_to_V],
      !v[DSFSTypedNARGString (pSpec := pSpec) (U := U) δ]⟩ : ProtocolSpec 1)) =
      (fun q => isEmptyElim q.1) := by
    funext q
    exact isEmptyElim q.1
  simp only [he] at hx
  have hambient : ∀ {α : Type} (oa : OracleComp oSpec α),
      simulateQ (ScheduledExecution.interp impl answer)
        (liftComp oa (oSpec + duplexSpongeOracle StmtIn U)) = simulateQ impl oa :=
    fun oa => QueryImpl.simulateQ_liftComp_left_eq_of_apply _ impl (fun _ => rfl) oa
  let messages := do
    let r ← simulateQ (ScheduledExecution.interp impl answer)
      (P.prover.referenceRunDSFSSalted salt (Fin.last n) stmt (P.prover.input (stmt, wit)))
    pure ((salt, r.1), r.2.2)
  have hp := narg_acceptance_of_prover_message_law
    (P.duplexSpongeFiatShamir (U := U) δ (pure salt))
    (ScheduledExecution.interp impl answer) stmt wit messages
    (fun state => simulateQ impl (P.prover.output state)) (fun _ => rfl)
    (fun event => by
      simpa only [messages, Reduction.duplexSpongeFiatShamir,
        monadLift_pure, simulateQ_bind, simulateQ_pure, simulateQ_map, prEvent_norm] using
        proof_prover_messages P.prover impl answer δ (pure salt) stmt wit event)
    (fun y hy => by
      obtain ⟨s, hs⟩ := support_nonempty init
      have hy' : y ∈ support (simulateQ (ScheduledExecution.interp impl answer)
          (fullExecution salt P stmt wit)) := by
        simp only [fullExecution, messages, Reduction.duplexSpongeFiatShamir,
          simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind, hambient] at hy ⊢
        convert hy using 1
        congr 1
      obtain ⟨result, hr, hacc, _⟩ := hc stmt wit hrel y ⟨s, hs, hy'⟩
      exact ⟨result, hr, by simpa [acceptRejectRel] using hacc⟩) x hx
  obtain ⟨result, hr, hacc, hout⟩ := hp
  exact ⟨result, hr, by simpa [acceptRejectRel] using hacc, hout.trans hacc.symm⟩

/-- With the public sponge realization fixed, initialization commutes with salt sampling. -/
theorem proof_run_sample
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn U : Type} [SpongeUnit U] [SpongeSize] [Codec pSpec U]
    (δ : ℕ) (P : Proof oSpec StmtIn WitIn pSpec)
    (impl : QueryImpl oSpec ProbComp)
    (answer : QueryImpl (duplexSpongeOracle StmtIn U) Id)
    (sampleSalt : OracleComp oSpec (Vector U δ)) (stmt : StmtIn) (wit : WitIn) :
    let fixed := ScheduledExecution.interp impl answer +
      (fun q => isEmptyElim q.1 : QueryImpl
        ([(⟨!v[.P_to_V], !v[DSFSTypedNARGString (pSpec := pSpec) (U := U) δ]⟩ :
          ProtocolSpec 1).Challenge]ₒ'challengeOracleInterface) ProbComp)
    simulateQ fixed ((P.duplexSpongeFiatShamir (U := U) δ sampleSalt).run stmt wit).run =
      (do
        let salt ← simulateQ impl sampleSalt
        simulateQ fixed ((P.duplexSpongeFiatShamir (U := U) δ (pure salt)).run
          stmt wit).run) := by
  dsimp only
  simp only [Reduction.simulate_narg_run, Reduction.duplexSpongeFiatShamir,
    Prover.duplexSpongeFiatShamir, monadLift_pure, simulateQ_bind, simulateQ_pure,
    ScheduledExecution.interp_start, pure_bind, bind_assoc]
  have hsample : simulateQ (ScheduledExecution.interp impl answer)
      (liftComp sampleSalt (oSpec + duplexSpongeOracle StmtIn U)) =
      simulateQ impl sampleSalt :=
    QueryImpl.simulateQ_liftComp_left_eq_of_apply _ impl (fun _ => rfl) sampleSalt
  simp only [← liftComp_eq_liftM, hsample]


end SaltedExecution

/-! ## Shared oracle-sampling assembly -/

section OracleSampling

/-- Pointwise completeness for each fixed sponge realization lifts to its sampled execution. -/
theorem perfectCompleteness_of_fixedOracle
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn Message U σ : Type}
    [SpongeUnit U] [SpongeSize] [VCVCompatible StmtIn] [VCVCompatible U]
    (Q : NonInteractiveReduction Message (oSpec + duplexSpongeOracle StmtIn U)
      StmtIn WitIn Bool Unit)
    (init : ProbComp σ) (impl : QueryImpl oSpec ProbComp)
    (relation : Set (StmtIn × WitIn))
    (h : ∀ answer : QueryImpl (duplexSpongeOracle StmtIn U) Id,
      Q.perfectCompleteness init
        ((ScheduledExecution.interp impl answer).liftTarget (StateT σ ProbComp))
        relation acceptRejectRel) :
    Q.perfectCompleteness (D_𝔖.sample StmtIn U) (D_𝔖.withOracle impl)
      relation acceptRejectRel := by
  let answer : DuplexSpongeOracleFamily StmtIn U →
      QueryImpl (duplexSpongeOracle StmtIn U) Id := fun realization q =>
    match q with
    | .inl q => realization.1 q
    | .inr (.inl q) => realization.2 q
    | .inr (.inr q) => realization.2.symm q
  let fixed := fun realization => ScheduledExecution.interp impl (answer realization) +
    (fun q => isEmptyElim q.1 : QueryImpl
      ([(⟨!v[.P_to_V], !v[Message]⟩ : ProtocolSpec 1).Challenge]ₒ'challengeOracleInterface)
      ProbComp)
  rw [Reduction.perfectCompleteness_eq_prob_one]
  intro stmt wit hrel
  rw [OptionT.prEvent_mk_eq_one_iff]
  intro x hx
  simp only [mem_support_bind_iff, StateT.run'_eq, support_map, Set.mem_image] at hx
  obtain ⟨realization, _hrealization, z, hz, rfl⟩ := hx
  rw [OracleComp.simulateQ_readOnly_run (fixed := fixed)] at hz
  rotate_left
  · intro q realization
    rcases q with q | q
    · rcases q with q | q
      · simp [fixed, ScheduledExecution.interp, D_𝔖.withOracle, QueryImpl.addLift_def,
          QueryImpl.liftTarget]
      · rcases q with q | q | q <;>
          simp [fixed, answer, ScheduledExecution.interp, D_𝔖.withOracle, D_𝔖.answer,
            duplexSpongeOracleQueryImpl, QueryImpl.addLift_def, QueryImpl.liftTarget]
    · exact isEmptyElim q.1
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨result, hresult, rfl⟩ := hz
  have hold := (Proof.perfectCompleteness_stateless_iff _ init _ relation).mp
    (h (answer realization)) stmt wit hrel
  have he : challengeQueryImpl (pSpec :=
      (⟨!v[.P_to_V], !v[Message]⟩ : ProtocolSpec 1)) =
      (fun q => isEmptyElim q.1) := by
    funext q
    exact isEmptyElim q.1
  simp only [he] at hold
  exact hold result hresult

end OracleSampling

end DuplexSpongeFS.ProofExecution
