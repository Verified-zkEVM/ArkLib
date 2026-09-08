/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.Round

/-!
# Actual execution and completeness of a product-sumcheck round

The only query made by the prover samples the next scalar challenge. Every resulting honest
message satisfies the local check and advances the actual residual-sum relation on the same
packed witness and commitment oracle. Completeness is uniform in the initial oracle state.
-/

noncomputable section
namespace RingSwitching.Packing.Tail.Round
open OracleSpec OracleComp ProtocolSpec Polynomial MvPolynomial ProbabilityTheory
variable {P C Context : Type} [CommRing P] [CommRing C] [Algebra P C] {m : ℕ}
  (multiplier : Context → C⦃≤ 1⦄[X Fin m]) (pc : PackedCommitment P m) (i : Fin m)

/-- The actual honest prover queries one challenge and records the corresponding transcript. -/
theorem prover_run (stmt : Statement Context C i.castSucc) (ost : ∀ j, pc.OStmt j)
    (p : P⦃≤ 1⦄[X Fin m]) :
    (prover multiplier pc i).run (stmt, ost) p = (do
      let c ← liftComp ((pSpec C).getChallenge ⟨1, rfl⟩)
        ([]ₒ + [(pSpec C).Challenge]ₒ'challengeOracleInterface)
      let g := honestMessage multiplier i stmt p
      pure (FullTranscript.mk2 g c, (nextStatement i stmt g c, ost), p)) := by
  have h0 : (pSpec C).dir 0 = .P_to_V := rfl
  have h1 : (pSpec C).dir 1 = .V_to_P := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_two,
    Prover.processRound_of_dir_eq_P_to_V 0 h0,
    Prover.processRound_of_dir_eq_V_to_P 1 h1]
  simp only [prover, pure_bind, liftM_pure, bind_assoc]
  congr 1
  funext c
  exact congrArg (fun tr =>
    (pure (tr, (nextStatement i stmt (honestMessage multiplier i stmt p) c, ost), p) :
      OracleComp ([]ₒ + [(pSpec C).Challenge]ₒ'challengeOracleInterface) _))
    (FullTranscript.mk2_eq_snoc_snoc _ _).symm

open scoped Classical in
/-- The whole reduction preserves the checked verdict and the original oracle collection. -/
theorem reduction_run (stmt : Statement Context C i.castSucc) (ost : ∀ j, pc.OStmt j)
    (p : P⦃≤ 1⦄[X Fin m]) :
    ((reduction multiplier pc i).toReduction.run (stmt, ost) p).run = (do
      let c ← liftComp ((pSpec C).getChallenge ⟨1, rfl⟩)
        ([]ₒ + [(pSpec C).Challenge]ₒ'challengeOracleInterface)
      let g := honestMessage multiplier i stmt p
      let out := (nextStatement i stmt g c, ost)
      pure (if check i stmt g then some ((FullTranscript.mk2 g c, out, p), out) else none)) := by
  rw [Reduction.run_eq_of_guarded_verifier _ (guardedForm (C := C) (Context := Context) pc i)]
  change ((prover multiplier pc i).run (stmt, ost) p >>= _) = _
  rw [prover_run]
  simp only [bind_assoc, pure_bind, guardedForm, FullTranscript.messages,
    FullTranscript.challenges, FullTranscript.mk2, decide_eq_true_eq]

omit [Algebra P C] in
/-- Positive related output identifies the actual accepted guard and next residual relation. -/
theorem positive_output {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (stmt : Statement Context C i.castSucc) (ost : ∀ j, pc.OStmt j)
    (tr : FullTranscript (pSpec C)) (p : P⦃≤ 1⦄[X Fin m])
    (relOut : Set (((Statement Context C i.succ) × (∀ j, pc.OStmt j)) ×
      P⦃≤ 1⦄[X Fin m]))
    (h : Pr[ fun out => (out, p) ∈ relOut |
      OptionT.mk do (simulateQ impl
        ((verifier pc i).toVerifier.run (stmt, ost) tr)).run' (← init)] > 0) :
    check i stmt (tr.messages ⟨0, rfl⟩) ∧
      ((nextStatement i stmt (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩), ost), p) ∈
        relOut := by
  classical
  rw [gt_iff_lt, probEvent_pos_iff] at h
  obtain ⟨out, hout, hrel⟩ := h
  rw [OptionT.mem_support_iff] at hout
  simp only [Verifier.run, verifier_verify] at hout
  by_cases hc : check i stmt (tr.messages ⟨0, rfl⟩)
  · rw [if_pos hc] at hout
    change some out ∈ support (init >>= fun _ => pure (some
      (nextStatement i stmt (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩), ost))) at hout
    simp only [support_bind_const, support_pure, Set.mem_ofPred_eq] at hout
    obtain rfl := Option.some.inj hout.1
    exact ⟨hc, hrel⟩
  · rw [if_neg hc] at hout
    change some out ∈ support (init >>= fun _ => pure none) at hout
    simp at hout

/-- Every challenge preserves completeness over a finite commutative ring, at every oracle state. -/
theorem perfectCompleteness [Fintype C] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction multiplier pc i).perfectCompleteness init impl
      (rel multiplier pc i.castSucc) (rel multiplier pc i.succ) := by
  classical
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt p hIn x hx
  rw [Reduction.run_eq_of_guarded_verifier _
    (guardedForm (C := C) (Context := Context) pc i)] at hx
  change x ∈ support ((prover multiplier pc i).run stmt p >>= fun r =>
    pure (if (guardedForm (C := C) (Context := Context) pc i).check stmt r.1 then
      some (r, (guardedForm (C := C) (Context := Context) pc i).out stmt r.1) else none)) at hx
  rw [prover_run] at hx
  simp only [bind_assoc, pure_bind, mem_support_bind_iff] at hx
  obtain ⟨c, _, hx⟩ := hx
  have hc := honest_check multiplier pc i hIn
  simp only [guardedForm, FullTranscript.messages, FullTranscript.mk2,
    decide_eq_true_eq, hc, if_true, mem_support_pure_iff] at hx
  subst x
  exact ⟨_, rfl, honest_relOut multiplier pc i hIn c, rfl⟩

end RingSwitching.Packing.Tail.Round
