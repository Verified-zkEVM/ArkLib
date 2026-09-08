/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.BatchingPhase
import ArkLib.ProofSystem.RingSwitching.Packing.SumcheckPhase

/-!
# Execution contracts for the packing verifier

These equations describe the verifier on an arbitrary supplied transcript. They
prove rejection and the precise opening that is forwarded independently of the knowledge-soundness
proofs. Failure remains absorbing when another oracle verifier is appended.
-/

open OracleSpec OracleComp ProtocolSpec Sumcheck.Structured Polynomial

namespace RingSwitching
noncomputable section

variable (κ : ℕ) (L : Type) [CommRing L] [DecidableEq L]
  (K : Type) [CommRing K] [Algebra K L] (P : RingSwitchingProfile K L κ)
  (ℓ ℓ' : ℕ) (h_l : ℓ = ℓ' + κ) (O : AbstractOStmtIn L ℓ')

/-- The scalar check either aborts or retains the batching challenge and target. -/
theorem batching_verify
    (stmt : BatchingStmtIn L ℓ) (oStmt : ∀ j, O.OStmtIn j)
    (tr : FullTranscript (pSpecBatching κ L K P)) :
    (BatchingPhase.oracleVerifier κ L K P ℓ ℓ' h_l O).toVerifier.verify (stmt, oStmt) tr =
    (if (performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim
        stmt.t_eval_point (tr.messages ⟨0, rfl⟩)) then
      pure (⟨compute_s0 κ L K P (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩),
        Fin.elim0, ⟨⟨stmt.t_eval_point, stmt.original_claim⟩,
          tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩⟩⟩, oStmt)
    else failure) := by
  apply guardedScalarRoundOracleVerifier_verify

/-- The final check forwards the prover's value itself, including when the multiplier is zero. -/
theorem final_verify
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (oStmt : ∀ j, O.OStmtIn j) (tr : FullTranscript (pSpecFinalSumcheck L)) :
    let msg : L := tr.messages ⟨0, rfl⟩
    (SumcheckPhase.finalSumcheckVerifier κ L K P ℓ ℓ' h_l O).toVerifier.verify (stmt, oStmt) tr =
    (if (stmt.sumcheck_target = compute_final_eq_value κ L K P ℓ ℓ' h_l
        stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching * msg) then
      pure (⟨stmt.challenges, msg⟩, oStmt)
    else failure) := by
  apply guardedMessageRoundOracleVerifier_verify

set_option backward.isDefEq.respectTransparency false in
/-- A structured sumcheck round either aborts or keeps the sampled challenge and evaluation. -/
theorem round_verify [Nontrivial L] (i : Fin ℓ')
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (oStmt : ∀ j, O.OStmtIn j) (tr : FullTranscript (pSpecSumcheckRound L)) :
    let poly : L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    let challenge : L := tr.challenges ⟨1, rfl⟩
    (SumcheckPhase.iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' O i).toVerifier.verify
      (stmt, oStmt) tr =
    (if ((∑ b ∈ (boolDomain L ℓ').points i, poly.val.eval b) =
        stmt.sumcheck_target) then
      pure (⟨poly.val.eval challenge, Fin.snoc stmt.challenges challenge, stmt.ctx⟩, oStmt)
    else failure) := by
  classical
  apply OptionT.ext
  have hout : (SumcheckPhase.iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' O i).materializeOutput
      tr.challenges oStmt tr.messages = oStmt := by
    funext j
    rfl
  simp only [OracleVerifier.toVerifier, OptionT.run_mk]
  rw [hout]
  change (Option.map fun out => (out, oStmt)) <$>
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt tr.messages)
      (do
        let poly : L⦃≤ 2⦄[X] ← query (spec := [(pSpecSumcheckRound L).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
        if (∑ b ∈ (boolDomain L ℓ').points i, poly.val.eval b) = stmt.sumcheck_target then
          pure ⟨poly.val.eval (tr.challenges ⟨1, rfl⟩),
            Fin.snoc stmt.challenges (tr.challenges ⟨1, rfl⟩), stmt.ctx⟩
        else failure : OptionT (OracleComp ([]ₒ + ([O.OStmtIn]ₒ +
          [(pSpecSumcheckRound L).Message]ₒ)))
          (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ)).run = _
  have hquery : simulateQ (OracleInterface.simOracle2 []ₒ oStmt tr.messages)
      (query (spec := [(pSpecSumcheckRound L).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩ :
        OptionT (OracleComp ([]ₒ + ([O.OStmtIn]ₒ + [(pSpecSumcheckRound L).Message]ₒ)))
          L⦃≤ 2⦄[X]).run = pure (some (tr.messages ⟨0, rfl⟩)) := by
    change simulateQ (OracleInterface.simOracle2 []ₒ oStmt tr.messages)
      (some <$> (liftM (([(pSpecSumcheckRound L).Message]ₒ).query ⟨⟨0, rfl⟩, ()⟩) :
        OracleComp ([]ₒ + ([O.OStmtIn]ₒ + [(pSpecSumcheckRound L).Message]ₒ)) L⦃≤ 2⦄[X])) = _
    rw [simulateQ_map]
    have h := QueryImpl.simulateQ_addLift_add_liftM_right (target := OracleComp []ₒ)
      (QueryImpl.id []ₒ) (OracleInterface.simOracle0 O.OStmtIn oStmt)
      (OracleInterface.simOracle0 (pSpecSumcheckRound L).Message tr.messages)
      (([(pSpecSumcheckRound L).Message]ₒ).query ⟨⟨0, rfl⟩, ()⟩)
    exact (congrArg (fun x => some <$> x) h).trans rfl
  rw [simulateQ_optionT_bind_elimM, hquery]
  simp only [Option.elimM, pure_bind, Option.elim_some]
  split <;> simp_all [OptionT.run_pure, OptionT.run_failure]

/-- A rejected packing leaf remains rejected after oracle-verifier append. -/
theorem append_verify_failure {ι : Type} {oSpec : OracleSpec ι}
    {S T U : Type} {ι₁ ι₂ ι₃ : Type} {O₁ : ι₁ → Type} {O₂ : ι₂ → Type} {O₃ : ι₃ → Type}
    [∀ i, OracleInterface (O₁ i)] [∀ i, OracleInterface (O₂ i)]
    [∀ i, OracleInterface (O₃ i)] {m n : ℕ} {p : ProtocolSpec m} {q : ProtocolSpec n}
    [∀ i, OracleInterface (p.Message i)] [∀ i, OracleInterface (q.Message i)]
    (V : OracleVerifier oSpec S O₁ T O₂ p) (W : OracleVerifier oSpec T O₂ U O₃ q)
    (stmt : S × (∀ i, O₁ i)) (tr : FullTranscript (p ++ₚ q))
    (h : V.toVerifier.verify stmt tr.fst = failure) :
    (OracleVerifier.append V W).toVerifier.verify stmt tr = failure := by
  rw [OracleVerifier.append_toVerifier]
  change (V.toVerifier.verify stmt tr.fst >>= fun out =>
    W.toVerifier.verify out tr.snd) = failure
  rw [h]
  simp

end
end RingSwitching
