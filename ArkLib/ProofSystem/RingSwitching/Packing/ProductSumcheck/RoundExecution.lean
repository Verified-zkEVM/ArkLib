/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.ProductSumcheck.Round

public import ArkLib.OracleReduction.LogicStep

/-!
# Execution and completeness of a product-sumcheck round

The prover's only query samples the next scalar challenge. For related inputs, the honest
message satisfies the local check and advances the residual-sum relation on the same
packed witness and commitment oracle. Completeness is uniform in the initial oracle state.
-/

@[expose] public section

noncomputable section
namespace RingSwitching.Packing.ProductSumcheck.Round
open Probability OracleSpec OracleComp ProtocolSpec Polynomial MvPolynomial ProbabilityTheory
variable {P C Context : Type} [CommRing P] [CommRing C] [Algebra P C] {m : ℕ}
  (multiplier : Multiplier Context C m) (pc : PackedCommitment P m) (i : Fin m)

/-- The honest prover samples one challenge and records the round transcript. -/
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
  simp only [prover, proverForOracles, pure_bind, liftM_pure, bind_assoc]
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
  simp only [bind_assoc, pure_bind, guardedForm_check, guardedForm_out, FullTranscript.messages,
    FullTranscript.challenges, FullTranscript.mk2, decide_eq_true_eq]

omit [Algebra P C] in
/--
A positive-probability related output determines the accepted guard and next residual
relation.
-/
theorem check_and_mem_of_prEvent_pos {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (stmt : Statement Context C i.castSucc) (ost : ∀ j, pc.OStmt j)
    (tr : FullTranscript (pSpec C)) (p : P⦃≤ 1⦄[X Fin m])
    (relOut : Set (((Statement Context C i.succ) × (∀ j, pc.OStmt j)) ×
      P⦃≤ 1⦄[X Fin m]))
    (h : Pr{let out ← OptionT.mk do (simulateQ impl
        ((verifier pc i).toVerifier.run (stmt, ost) tr)).run' (← init)}[(out, p) ∈ relOut] > 0) :
    check i stmt (tr.messages ⟨0, rfl⟩) ∧
      ((nextStatement i stmt (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩), ost), p) ∈
        relOut := by
  classical
  obtain ⟨hc, hrel⟩ := (guardedForm (C := C) (Context := Context) pc i).check_and_of_prEvent_pos h
  exact ⟨of_decide_eq_true hc, hrel⟩

/-- Every challenge preserves completeness over a commutative ring, at every oracle state. -/
theorem perfectCompleteness [SampleableType C] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction multiplier pc i).perfectCompleteness init impl
      (rel multiplier pc i.castSucc) (rel multiplier pc i.succ) := by
  classical
  apply Reduction.perfectCompleteness_of_guarded_prover_support _
    (guardedForm (C := C) (Context := Context) pc i)
  intro ⟨stmt, ost⟩ p hIn q hq
  change q ∈ support ((prover multiplier pc i).run (stmt, ost) p) at hq
  rw [prover_run] at hq
  obtain ⟨c, _, hq⟩ := (mem_support_bind_iff _ _ _).mp hq
  have hq := OracleComp.eq_of_mem_support_pure _ hq
  subst q
  have hc := check_honestMessage_of_mem_rel multiplier pc i hIn
  simp only [guardedForm_check, guardedForm_out, FullTranscript.messages, FullTranscript.mk2,
    decide_eq_true_eq, hc]
  exact ⟨trivial, nextStatement_mem_rel multiplier pc i hIn c, trivial⟩

end RingSwitching.Packing.ProductSumcheck.Round
