/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
public import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness

/-!
# Binary Basefold: the fold step

The `i`-th fold step of the Binary Basefold sum-check. The prover sends the univariate round
polynomial `hᵢ(X)` of its current round polynomial `Hᵢ`; the verifier checks
`hᵢ(𝓑 0) + hᵢ(𝓑 1) = sᵢ`, sends a uniform challenge `r'ᵢ`, and sets `sᵢ₊₁ := hᵢ(r'ᵢ)`. The prover
folds its word along `r'ᵢ` and fixes the first variable of `Hᵢ` to `r'ᵢ`. No oracle is sent; the
oracle statements pass through unchanged.

## Main definitions and statements

* `foldOracleProver`, `foldOracleVerifier`, `foldOracleReduction`: the step, built from
  `foldStepLogic`.
* `foldOracleVerifierGuardedForm`: the verifier's guard and verdict as data, through the logic
  step's `ReductionLogicStep.queryGuardedForm`.
* `foldOracleReduction_perfectCompleteness`: perfect completeness from the strict round relation
  to the strict fold-step output relation.

The step's round-by-round knowledge soundness is in `Steps/Fold.lean`.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  The step is lines 1–4 of the loop of the evaluation IOP of Construction 4.12; its completeness
  is part of Theorem 4.13, with the fold of the prover's word as in Lemma 4.14.
-/

@[expose] public section

namespace Binius.BinaryBasefold.CoreInteraction
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open Binius.BinaryBasefold
open scoped NNReal ProbabilityTheory

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section FoldStep
variable {Context : Type} {multpoly : Context → MultilinearPoly L ℓ}

/-- The prover of the `i`-th fold step: it sends the round polynomial `foldProverComputeMsg`,
receives the challenge, and outputs `foldStepLogic`'s prover output on the transcript. -/
noncomputable def foldOracleProver (i : Fin ℓ) :
  OracleProver (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
    (pSpec := pSpecFold (L := L)) where
  PrvState := foldPrvState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage
  | ⟨0, _⟩ => fun ⟨stmt, oStmt, wit⟩ => do
    let h_i := foldProverComputeMsg (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i wit
    pure ⟨h_i, (stmt, oStmt, wit, h_i)⟩
  | ⟨1, _⟩ => by contradiction
  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, h_i⟩ => do
    pure (fun r_i' => (stmt, oStmt, wit, h_i, r_i'))
  output := fun finalPrvState =>
    let (stmt, oStmt, wit, h_i, r_i') := finalPrvState
    let t := FullTranscript.mk2 (pSpec := pSpecFold (L := L)) h_i r_i'
    pure ((foldStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multpoly) i).proverOut
        stmt wit oStmt t)

open Classical in
/-- The verifier of the `i`-th fold step: it queries the round polynomial, guards on
`foldStepLogic`'s check, and outputs its output statement. The oracle statements pass through. -/
def foldOracleVerifier (i : Fin ℓ) :
    OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (pSpec := pSpecFold (L := L)) where
  verify := fun stmtIn pSpecChallenges => do
    let h_i ← query (spec := [(pSpecFold (L := L)).Message]ₒ) ⟨⟨0, by rfl⟩, (by exact ())⟩
    let r_i' := pSpecChallenges ⟨1, rfl⟩
    let t := FullTranscript.mk2 h_i r_i'
    let logic := (foldStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multpoly) i)
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)
  outputOracle := .inl {
    embed := (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (multpoly := multpoly) i).embed
    hEq := by
      intro oracleIdx
      simp only [foldStepLogic, Fin.is_lt, ↓reduceDIte, Fin.eta,
        Function.Embedding.coeFn_mk]
    outputInterface_heq := by
      intro oracleIdx
      simp only [foldStepLogic, Fin.is_lt, ↓reduceDIte, Fin.eta,
        Function.Embedding.coeFn_mk]
      rfl }

/-- The oracle reduction of the `i`-th fold step. -/
noncomputable def foldOracleReduction (i : Fin ℓ) :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecFold (L := L)) where
  prover := foldOracleProver 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    (multpoly := multpoly) i
  verifier := foldOracleVerifier 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multpoly) i

open Classical in
/-- The fold verifier's guard and verdict as data: `foldStepLogic`'s check and output statement on
the sent round polynomial and the challenge, with the unchanged oracle statements. -/
def foldOracleVerifierGuardedForm (i : Fin ℓ) :
    (foldOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i).toVerifier.GuardedForm :=
  (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    (multpoly := multpoly) i).queryGuardedForm _ ⟨⟨0, rfl⟩, ()⟩
    (fun a chals => FullTranscript.mk2 a (chals ⟨1, rfl⟩)) (fun _ _ => rfl)

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
open Classical in
/-- The fold verifier's guard is the sum-check on the sent round polynomial. -/
@[simp]
theorem foldOracleVerifierGuardedForm_check (i : Fin ℓ)
    (s : Statement (L := L) Context i.castSucc × ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j)
    (tr : (pSpecFold (L := L)).FullTranscript) :
    (foldOracleVerifierGuardedForm 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i).check s tr =
      decide (foldVerifierCheck i s.1 (𝓑 := 𝓑) (tr.messages ⟨0, rfl⟩)) :=
  decide_eq_decide.mpr Iff.rfl

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
open Classical in
/-- The fold verifier's verdict is the folded statement at the sent round polynomial and the
challenge, with the unchanged oracle statements. -/
@[simp]
theorem foldOracleVerifierGuardedForm_out (i : Fin ℓ)
    (s : Statement (L := L) Context i.castSucc × ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j)
    (tr : (pSpecFold (L := L)).FullTranscript) :
    (foldOracleVerifierGuardedForm 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i).out s tr =
      (foldVerifierStmtOut i s.1 (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩),
        (foldOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
          (multpoly := multpoly) i).materializeOutput tr.challenges s.2 tr.messages) := rfl

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [SampleableType L] [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- The fold verifier passes its oracle statements through unchanged. -/
theorem foldOracleVerifier_materializeOutput (i : Fin ℓ)
    (chals : (pSpecFold (L := L)).Challenges)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j)
    (msgs : (pSpecFold (L := L)).Messages) :
    (foldOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i).materializeOutput chals oStmt msgs = oStmt := by
  funext j
  simp [OracleVerifier.materializeOutput, OracleVerifier.materializeOutputOracle,
    foldOracleVerifier, foldStepLogic]

omit [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- Perfect completeness of the `i`-th fold step, from the strict round relation at `i` to the
strict fold-step output relation. -/
theorem foldOracleReduction_perfectCompleteness (i : Fin ℓ) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecFold (L := L))
      (relIn := strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.castSucc (multpoly := multpoly))
      (relOut := strictFoldStepRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i (multpoly := multpoly))
      (oracleReduction := foldOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multpoly) i)
      (init := init)
      (impl := impl) := by
  classical
  let _ : ∀ j, OracleInterface ((pSpecFold (L := L)).Challenge j) :=
    ProtocolSpec.challengeOracleInterface
  apply Reduction.perfectCompleteness_of_run_support
  intro ⟨stmt, oStmt⟩ wit hIn x hx
  let step := foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    (multpoly := multpoly) i
  let msg : (pSpecFold (L := L)).«Type» 0 :=
    foldProverComputeMsg (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i wit
  let sample : OracleComp ([]ₒ + [(pSpecFold (L := L)).Challenge]ₒ) L :=
    liftM (query (spec := [(pSpecFold (L := L)).Challenge]ₒ) ⟨⟨1, rfl⟩, ()⟩ :
      OracleComp [(pSpecFold (L := L)).Challenge]ₒ L)
  have hp : (foldOracleProver 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i).run (stmt, oStmt) wit = (sample >>= fun c =>
      pure (FullTranscript.mk2 (pSpec := pSpecFold (L := L)) msg c,
        step.proverOut stmt wit oStmt (FullTranscript.mk2 msg c))) := by
    simp only [pSpecFold, ChallengeIdx, Challenge, Prover.run, Fin.reduceLast, foldOracleProver,
      Fin.isValue, MessageIdx, Message, Fin.castSucc_zero, Fin.succ_zero_eq_one,
      Fin.castSucc_one, Fin.succ_one_eq_two, Prover.runToRound, Nat.reduceAdd,
      Fin.induction_two', Prover.processRound, bind_pure_comp, pure_bind, liftM_pure,
      LawfulApplicative.map_pure, HasQuery.instOfMonadLift_query, sample, msg, step]
    change (sample >>= fun c => pure
      (((default : (pSpecFold (L := L)).Transcript 0).concat (m := 0) msg).concat (m := 1) c,
        step.proverOut stmt wit oStmt (FullTranscript.mk2 msg c))) = _
    conv_rhs => rw [map_eq_bind_pure_comp]
    apply bind_congr
    intro c
    congr 1
    exact congrArg (fun tr => (tr, step.proverOut stmt wit oStmt (FullTranscript.mk2 msg c)))
      (FullTranscript.mk2_eq_snoc_snoc (pSpec := pSpecFold (L := L)) msg c).symm
  let G := foldOracleVerifierGuardedForm 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) (multpoly := multpoly) i
  rw [Reduction.run_eq_of_guarded_verifier _ G] at hx
  change x ∈ MonadAttach.support ((foldOracleProver 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multpoly) i).run
      (stmt, oStmt) wit >>= fun r => pure
      (if G.check (stmt, oStmt) r.1 then some (r, G.out (stmt, oStmt) r.1) else none)) at hx
  rw [hp, bind_assoc] at hx
  simp only [pure_bind] at hx
  obtain ⟨c, _, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
  obtain ⟨hcheck, hrel, hstmt, horacle⟩ :=
    foldStepLogic_isStronglyComplete 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (multpoly := multpoly) i stmt wit oStmt
      (fun | ⟨0, h⟩ => nomatch h | ⟨1, _⟩ => c) hIn
  rw [show G.check (stmt, oStmt) (FullTranscript.mk2 msg c) = true from
    decide_eq_true hcheck] at hx
  simp only [↓reduceIte, mem_support_pure_iff] at hx
  subst x
  have hmat := foldOracleVerifier_materializeOutput 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := multpoly) i
    (FullTranscript.mk2 (pSpec := pSpecFold (L := L)) msg c).challenges oStmt
    (FullTranscript.mk2 (pSpec := pSpecFold (L := L)) msg c).messages
  rw [← horacle] at hrel
  refine ⟨_, rfl, ?_, ?_⟩
  · rw [foldOracleVerifierGuardedForm_out, hmat]
    exact hrel
  · rw [foldOracleVerifierGuardedForm_out, hmat]
    exact Prod.ext hstmt rfl

end FoldStep

end
end Binius.BinaryBasefold.CoreInteraction
