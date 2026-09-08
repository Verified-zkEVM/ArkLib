/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.FullFamily.Phase
import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness

/-!
# Exact execution of full-family packing

The verifier verdict is fixed by its checked slice message and challenge. The honest prover
issues only the specified challenge query. These contracts refer to the production interpreter,
including its oracle materialization and failure behavior.
-/

noncomputable section

namespace RingSwitching.Packing.FullFamily

open OracleSpec OracleComp ProtocolSpec MvPolynomial ProbabilityTheory

variable {B : Type} [CommRing B] (data : PackingData B) (m : ℕ)
  {C : Type} [CommRing C] [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C]
  (bat : BatchingStrategy C data.ιE) (pc : PackedCommitment data.P m)

/-- The honest slice message passes the verifier's public-family check. -/
theorem honest_check {stmt : Input data m} {oStmt : ∀ j, pc.OStmt j}
    {ps : data.ιP → B⦃≤ 1⦄[X Fin m]} (hIn : ((stmt, oStmt), ps) ∈ relIn data m pc) :
    data.claimConsistent stmt.1 (honestSlices data m stmt.2 (data.packedMLE ps)) :=
  data.claimConsistent_of_slices hIn.1 (honestSlices_mem_sliceRel data m _ _)

/-- Every challenge gives a valid honest output with the same packed commitment. -/
theorem honest_relOut {stmt : Input data m} {oStmt : ∀ j, pc.OStmt j}
    {ps : data.ιP → B⦃≤ 1⦄[X Fin m]} (hIn : ((stmt, oStmt), ps) ∈ relIn data m pc)
    (c : bat.Challenge) :
    ((nextStatement data m bat stmt (honestSlices data m stmt.2 (data.packedMLE ps)) c,
      oStmt), data.packedMLE ps) ∈ relOut data m bat pc :=
  ⟨data.sumcheckClaim_of_slices (honestSlices_mem_sliceRel data m _ _) _, hIn.2⟩

omit [IsScalarTower B data.P C] in
/-- A positive-probability related output pins the guard and the actual deterministic verdict. -/
theorem positive_output {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (stmt : Input data m) (oStmt : ∀ j, pc.OStmt j) (tr : FullTranscript (pSpec data bat))
    (p : data.P⦃≤ 1⦄[X Fin m])
    (h : Pr[ fun out => (out, p) ∈ relOut data m bat pc |
      OptionT.mk do (simulateQ impl
        ((verifier data m bat pc).toVerifier.run (stmt, oStmt) tr)).run' (← init)] > 0) :
    data.claimConsistent stmt.1 (tr.messages ⟨0, rfl⟩) ∧
      ((nextStatement data m bat stmt (tr.messages ⟨0, rfl⟩)
        (tr.challenges ⟨1, rfl⟩), oStmt), p) ∈ relOut data m bat pc := by
  classical
  rw [gt_iff_lt, probEvent_pos_iff] at h
  obtain ⟨out, hout, hrel⟩ := h
  rw [OptionT.mem_support_iff] at hout
  simp only [Verifier.run, verifier_verify] at hout
  by_cases hc : data.claimConsistent stmt.1 (tr.messages ⟨0, rfl⟩)
  · rw [if_pos hc] at hout
    change some out ∈ support (init >>= fun _ => pure (some
      (nextStatement data m bat stmt (tr.messages ⟨0, rfl⟩)
        (tr.challenges ⟨1, rfl⟩), oStmt))) at hout
    simp only [support_bind_const, support_pure, Set.mem_ofPred_eq] at hout
    obtain rfl := Option.some.inj hout.1
    exact ⟨hc, hrel⟩
  · rw [if_neg hc] at hout
    change some out ∈ support (init >>= fun _ => pure none) at hout
    simp at hout

omit [Algebra B C] [IsScalarTower B data.P C] in
/-- The honest prover executes exactly one challenge query and returns its canonical transcript. -/
theorem prover_run (stmt : Input data m) (oStmt : ∀ j, pc.OStmt j)
    (ps : data.ιP → B⦃≤ 1⦄[X Fin m]) :
    (prover data m bat pc).run (stmt, oStmt) ps = (do
      let c ← liftComp ((pSpec data bat).getChallenge ⟨1, rfl⟩)
        ([]ₒ + [(pSpec data bat).Challenge]ₒ'challengeOracleInterface)
      let p := data.packedMLE ps
      let s := honestSlices data m stmt.2 p
      pure (FullTranscript.mk2 s c, (nextStatement data m bat stmt s c, oStmt), p)) := by
  have h0 : (pSpec data bat).dir 0 = .P_to_V := rfl
  have h1 : (pSpec data bat).dir 1 = .V_to_P := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_two,
    Prover.processRound_of_dir_eq_P_to_V 0 h0,
    Prover.processRound_of_dir_eq_V_to_P 1 h1]
  simp only [prover, pure_bind, liftM_pure, bind_assoc]
  congr 1
  funext c
  exact congrArg (fun tr =>
    (pure (tr,
      (nextStatement data m bat stmt (honestSlices data m stmt.2 (data.packedMLE ps)) c,
        oStmt), data.packedMLE ps) :
      OracleComp ([]ₒ + [(pSpec data bat).Challenge]ₒ'challengeOracleInterface) _))
    (FullTranscript.mk2_eq_snoc_snoc _ _).symm

open scoped Classical in
omit [Algebra B C] [IsScalarTower B data.P C] in
/-- The complete production execution preserves rejection and the original commitment oracle. -/
theorem reduction_run (stmt : Input data m) (oStmt : ∀ j, pc.OStmt j)
    (ps : data.ιP → B⦃≤ 1⦄[X Fin m]) :
    ((reduction data m bat pc).toReduction.run (stmt, oStmt) ps).run = (do
      let c ← liftComp ((pSpec data bat).getChallenge ⟨1, rfl⟩)
        ([]ₒ + [(pSpec data bat).Challenge]ₒ'challengeOracleInterface)
      let p := data.packedMLE ps
      let s := honestSlices data m stmt.2 p
      let out := (nextStatement data m bat stmt s c, oStmt)
      pure (if data.claimConsistent stmt.1 s then
        some ((FullTranscript.mk2 s c, out, p), out) else none)) := by
  rw [Reduction.run_eq_of_guarded_verifier _ (guardedForm data m bat pc)]
  change ((prover data m bat pc).run (stmt, oStmt) ps >>= _) = _
  rw [prover_run]
  simp only [bind_assoc, pure_bind, guardedForm, FullTranscript.messages,
    FullTranscript.challenges, FullTranscript.mk2, decide_eq_true_eq]

end RingSwitching.Packing.FullFamily

end
