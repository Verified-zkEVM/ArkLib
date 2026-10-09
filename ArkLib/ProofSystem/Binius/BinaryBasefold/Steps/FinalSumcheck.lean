/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.FinalSumcheck.Extraction
public import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness
public import ArkLib.OracleReduction.Security.GuardedRoundByRound

/-!
# Binary Basefold: the final sum-check step

After the last fold, the prover sends the constant `c := f⁽ˡ⁾(0, …, 0)` of its fully folded word;
the verifier checks the closing sum-check equation `s_ℓ = eq̃(r, r') · c` and outputs the
statement extended by `c`. The step sends no challenge.

## Main definitions and statements

* `finalSumcheckProver`, `finalSumcheckVerifier`, `finalSumcheckOracleReduction`: the step.
* `finalSumcheckVerifierGuardedForm`: the verifier's guard (the closing equation) and verdict as
  data, through `ReductionLogicStep.queryGuardedForm`.
* `finalSumcheckOracleReduction_perfectCompleteness`: perfect completeness from the strict round
  relation at `ℓ` to the strict final sum-check output relation, through `finalSumcheckStepLogic`.
* `finalSumcheckKnowledgeStateFunction`: before the message, the round relation at `ℓ`; after it,
  the closing equation and the final folding state. Its backward step decodes the multilinear
  polynomial from the first oracle (`Steps/FinalSumcheck/Extraction.lean`).
* `finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith`: worst-case round-by-round
  knowledge soundness at `finalSumcheckRbrExtractor` and `finalSumcheckKnowledgeStateFunction`, with
  existential and averaged forms.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  The step is line 5 of the loop and step 3 of the evaluation IOP of Construction 4.12.
-/

@[expose] public section

namespace Binius.BinaryBasefold.CoreInteraction
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
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

section SingleIteratedSteps
variable {Context : Type} {multpoly : Context → MultilinearPoly L ℓ}

section FinalSumcheckStep

open Classical in
/-- The prover of the final sum-check step: it sends the constant of its fully folded word. -/
noncomputable def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  PrvState := fun
    | 0 => Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ) × (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
        × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)
    | _ => Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ) × (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
        × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    -- Compute the message using the honest transcript from logic
    let c : L := witIn.f ⟨0, by simp only [zero_mem]⟩ -- f^(ℓ)(0, ..., 0)
    pure ⟨c, (stmtIn, oStmtIn, witIn, c)⟩
  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- No challenges in this step
  output := fun ⟨stmtIn, oStmtIn, witIn, c⟩ => do
    -- Construct the transcript from the message and challenges (no challenges in this step)
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) c
    -- Delegate to the logic instance for prover output
    pure ((finalSumcheckStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).proverOut stmtIn witIn oStmtIn t)

open Classical in
/-- The verifier of the final sum-check step: it queries the sent constant, guards on the closing
sum-check equation of `finalSumcheckStepLogic`, and outputs the statement extended by the constant.
The oracle statements pass through. -/
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  verify := fun stmtIn _ => do
    -- Get the final constant `c` from the prover's message
    let c : L ← query (spec := [(pSpecFinalSumcheckStep (L := L)).Message]ₒ)
      ⟨⟨0, by rfl⟩, (by exact ())⟩
    -- Construct the transcript
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) c
    -- Get the logic instance
    let logic := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    -- Use guard for verifier check (fails if check doesn't pass)
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)
  outputOracle := .inl {
    embed := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)).embed
    hEq := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)).hEq
    outputInterface_heq := by
      intro _
      rfl }

/-- The oracle reduction of the final sum-check step. -/
noncomputable def finalSumcheckOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  prover := finalSumcheckProver 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  verifier := finalSumcheckVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)

open Classical in
/-- The final sum-check verifier's guard and verdict as data: `finalSumcheckStepLogic`'s check and
output statement on the sent constant, with the unchanged oracle statements. -/
def finalSumcheckVerifierGuardedForm :
    (finalSumcheckVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).toVerifier.GuardedForm :=
  (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑)).queryGuardedForm _ ⟨⟨0, rfl⟩, ()⟩
    (fun a _ => FullTranscript.mk1 a) (fun _ _ => rfl)

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
open Classical in
/-- The final sum-check verifier's guard is the closing sum-check equation
`s_ℓ = eq̃(r, r') · c` on the sent constant `c`. -/
@[simp]
theorem finalSumcheckVerifierGuardedForm_check
    (s : Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ) × ∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (tr : (pSpecFinalSumcheckStep (L := L)).FullTranscript) :
    (finalSumcheckVerifierGuardedForm 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).check s tr =
      decide (s.1.sumcheck_target =
        eqTilde s.1.ctx.t_eval_point s.1.challenges * (show L from tr.messages ⟨0, rfl⟩)) :=
  decide_eq_decide.mpr Iff.rfl

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
open Classical in
/-- The final sum-check verifier's verdict is the input statement extended by the sent constant,
with the unchanged oracle statements. -/
@[simp]
theorem finalSumcheckVerifierGuardedForm_out
    (s : Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ) × ∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (tr : (pSpecFinalSumcheckStep (L := L)).FullTranscript) :
    (finalSumcheckVerifierGuardedForm 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).out s tr =
      ({ ctx := s.1.ctx, sumcheck_target := s.1.sumcheck_target, challenges := s.1.challenges,
          final_constant := show L from tr.messages ⟨0, rfl⟩ }, s.2) := rfl

omit [DecidableEq 𝔽q] [CharP L 2] in
/-- Perfect completeness of the final sum-check step, from the strict round relation at `ℓ` to the
strict final sum-check output relation. -/
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecFinalSumcheckStep (L := L))
      (relIn := strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (multpoly := BBF_multiplier) (Fin.last ℓ))
      (relOut := strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (oracleReduction := finalSumcheckOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)) (init := init) (impl := impl) := by
  classical
  apply Reduction.perfectCompleteness_of_run_support
  intro ⟨stmt, oStmt⟩ wit hIn x hx
  let step := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  let c : L := wit.f ⟨0, by simp only [zero_mem]⟩
  have hp : (finalSumcheckProver 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).run (stmt, oStmt) wit =
      pure (((default : (pSpecFinalSumcheckStep (L := L)).Transcript 0).concat (m := 0) c),
        step.proverOut stmt wit oStmt (FullTranscript.mk1 c)) := rfl
  let G := finalSumcheckVerifierGuardedForm 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑)
  rw [Reduction.run_eq_of_guarded_verifier _ G] at hx
  change x ∈ MonadAttach.support ((finalSumcheckProver 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).run (stmt, oStmt) wit >>= fun r => pure
      (if G.check (stmt, oStmt) r.1 then some (r, G.out (stmt, oStmt) r.1) else none)) at hx
  obtain ⟨hcheck, hrel, hstmt, horacle⟩ := finalSumcheckStepLogic_isStronglyComplete (L := L)
    𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) stmt wit oStmt isEmptyElim hIn
  have hc : G.check (stmt, oStmt)
      ((default : (pSpecFinalSumcheckStep (L := L)).Transcript 0).concat (m := 0) c) = true :=
    (finalSumcheckVerifierGuardedForm_check 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) _ _).trans (decide_eq_true hcheck)
  rw [hp] at hx
  obtain ⟨r, hr, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
  replace hr := OracleComp.eq_of_mem_support_pure _ hr
  subst hr
  replace hx := OracleComp.eq_of_mem_support_pure _ hx
  subst x
  rw [← horacle] at hrel
  refine ⟨_, ite_eq_left_of_eq_true _ _ (eq_true hc), ?_, ?_⟩
  · rw [finalSumcheckVerifierGuardedForm_out 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)]
    exact hrel
  · rw [finalSumcheckVerifierGuardedForm_out 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)]
    exact Prod.ext hstmt rfl

/-- The final sum-check step sends no challenge, so its round-by-round knowledge error is the empty
family. -/
def finalSumcheckKnowledgeError (m : pSpecFinalSumcheckStep (L := L).ChallengeIdx) :
  ℝ≥0 :=
  match m with
  | ⟨0, h0⟩ => nomatch h0

/-- The intermediate witness types of the final sum-check step: the round-`ℓ` witness before the
message, nothing after it. -/
def FinalSumcheckWit := fun (m : Fin (1 + 1)) =>
 match m with
 | ⟨0, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)
 | ⟨1, _⟩ => Unit

/-- The round-by-round extractor of the final sum-check step. Across the message it decodes the
multilinear polynomial from the first oracle and rebuilds the round-`ℓ` witness from it, with the
constant round polynomial at the sum-check target; if decoding fails it returns the zero
polynomial. -/
noncomputable def finalSumcheckRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ)) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L))
    (WitMid := FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)) where
  eqIn := rfl
  extractMid := fun m ⟨stmtMid, oStmtMid⟩ trSucc witMidSucc => by
    have hm : m = 0 := by omega
    subst hm
    -- Decode t from the first oracle f^(0)
    let f0 := getFirstOracle 𝔽q β oStmtMid
    let polyOpt := extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨0, by exact Nat.pos_of_neZero ℓ⟩) (f := f0)
    have h_C_mem : MvPolynomial.C stmtMid.sumcheck_target ∈
        L⦃≤ 2⦄[X Fin (ℓ - ↑(Fin.last ℓ))] := by
      rw [mem_restrictDegree_iff_degreeOf_le]
      intro n
      exact le_trans (by rw [MvPolynomial.degreeOf_C]) (Nat.zero_le _)
    let H_constant : L⦃≤ 2⦄[X Fin (ℓ - ↑(Fin.last ℓ))] :=
      ⟨MvPolynomial.C stmtMid.sumcheck_target, h_C_mem⟩
    match polyOpt with
    | none =>
      -- Extraction failed - use constant H to satisfy sumcheckConsistencyProp trivially
      exact {
        t := ⟨0, by apply zero_mem⟩,
        H := H_constant,
        f := fun _ => 0
      }
    | some tpoly =>
      -- Build H_ℓ from t and challenges r'
      exact {
        t := tpoly,
        -- projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := tpoly)
          -- (m := BBF_multiplier stmtMid.ctx)
          -- (i := Fin.last ℓ) (challenges := stmtMid.challenges),
        H := H_constant,
        f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) tpoly stmtMid.challenges
      }
  extractOut := fun ⟨stmtIn, oStmtIn⟩ tr witOut => ()

/-- The knowledge state of the final sum-check step: before the message, the round relation at
`ℓ`; after it, the closing sum-check equation on the sent constant and the final folding state of
the output statement. -/
def finalSumcheckKStateProp {m : Fin (1 + 1)} (tr : Transcript m (pSpecFinalSumcheckStep (L := L)))
    (stmtIn : Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witMid : FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) m)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    masterKStateProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (multpoly := BBF_multiplier)
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (stmt := stmtIn) (wit := witMid) (oStmt := oStmtIn)
      (localChecks := sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) stmtIn.sumcheck_target
          witMid.H)
  | ⟨1, _⟩ => -- implied by relOut + local checks via extractOut proofs
    let c : L := tr.messages ⟨0, rfl⟩
    let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
      ctx := stmtIn.ctx,
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      final_constant := c
    }
    let sumcheckFinalCheck : Prop := stmtIn.sumcheck_target
      = eqTilde (stmtIn.ctx.t_eval_point) stmtIn.challenges * c
    let finalFoldingProp := finalSumcheckStepFoldingStateProp 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_le := by
        apply Nat.le_of_dvd;
        · exact Nat.pos_of_neZero ℓ
        · exact hdiv.out) (input := ⟨stmtOut, oStmtIn⟩)
    sumcheckFinalCheck ∧ finalFoldingProp -- local checks ∧ (oracleConsitency ∨ badEventExists)

/-- The knowledge-state function of the final sum-check step, `finalSumcheckKStateProp`, with its
obligations. -/
noncomputable def finalSumcheckKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).KnowledgeStateFunction init impl
    (relIn := roundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (multpoly := BBF_multiplier) (Fin.last ℓ) )
    (relOut := finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
    (extractor := finalSumcheckRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
  where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    finalSumcheckKStateProp 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (tr := tr) (stmtIn := stmtIn) (witMid := witMid) (oStmtIn := oStmtIn)
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witMid => by
    rfl
  toFun_next := fun m hDir (stmtIn, oStmtIn) tr msg witMid => by
    -- toFun_next is impacted by how we build extractMid
    -- For `pSpecFinalSumcheckStep`, the only P_to_V message is at index 0
    -- So m = 0, m.succ = 1, m.castSucc = 0
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => omega
    subst h_m_eq_0
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.castSucc_zero]
    -- declare c and stmtOut as in KState (m=1), as well as in honest verifier
    -- For the final sumcheck step, there is a single P→V message carrying the final constant,
    -- so we can read it directly from `msg` without reconstructing a truncated transcript.
    let c : L := msg
    let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
      ctx := stmtIn.ctx,
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      final_constant := c
    }
    intro h_kState_round1
    unfold finalSumcheckKStateProp finalSumcheckStepFoldingStateProp
      masterKStateProp at h_kState_round1 ⊢
    simp only [Fin.isValue, Nat.reduceAdd, Fin.mk_one,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod] at h_kState_round1
    -- At m=1 we have local final-check and (oracle-consistency ∨ block-bad-event).
    -- At m=0 the target is `masterKStateProp`:
    -- incremental-bad-event ∨ (local ∧ structural ∧ initial ∧ oracleFoldingConsistency).
    obtain ⟨h_V_check, h_core⟩ := h_kState_round1
    -- Case split on the m=1 final-folding state: consistency or block bad-event.
    cases h_core with
    | inl hConsistent =>
      -- When we have finalSumcheckStepOracleConsistencyProp, extractMLP must succeed.
      have ⟨tpoly, h_extractMLP⟩ :=
          exists_extractMLP_eq_some_of_finalSumcheckStepOracleConsistencyProp 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmtIn) (h_oracle_consistency := hConsistent)
      refine Or.inr ?_
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- local check at m=0
        unfold finalSumcheckRbrExtractor sumcheckConsistencyProp
        simp only [Fin.val_last, Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod]
        symm
        calc ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ℓ), (MvPolynomial.eval x)
                (MvPolynomial.C stmtIn.sumcheck_target)
            = ∑ _x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ℓ), stmtIn.sumcheck_target :=
              Finset.sum_congr rfl (fun x _ => MvPolynomial.eval_C (f := x) stmtIn.sumcheck_target)
          _ = stmtIn.sumcheck_target := by
              simp only [Finset.sum_const, Fintype.card_piFinset, Finset.card_map,
                Finset.card_univ, Fintype.card_fin, Finset.prod_const, tsub_self, pow_zero,
                one_smul]
      · -- witnessStructuralInvariant
        unfold finalSumcheckRbrExtractor witnessStructuralInvariant
        simp only [Fin.val_last, Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, and_true]
        refine SetLike.coe_eq_coe.mp ?_
        rw [Sumcheck.Structured.coe_projectToMidSumcheckPoly_last ℓ tpoly
          (BBF_multiplier stmtIn.ctx) stmtIn.challenges]
        have h_sumcheck_target_eq : stmtIn.sumcheck_target =
          (MvPolynomial.eval stmtIn.challenges
            (BBF_multiplier stmtIn.ctx).val) *
            (MvPolynomial.eval stmtIn.challenges tpoly.val) := by
          rw [h_V_check]
          congr 1
          change c = tpoly.val.eval stmtIn.challenges
          exact eval_eq_final_constant_of_extractMLP_eq_some 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmtOut := oStmtIn) (stmtOut := stmtOut)
            (tpoly := tpoly)
            (h_extractMLP := h_extractMLP) (h_finalSumcheckStepOracleConsistency := hConsistent)
        simp only
          [h_sumcheck_target_eq, Fin.val_last, Fin.coe_ofNat_eq_mod, MvPolynomial.C_mul]
      · -- firstOracleWitnessConsistencyProp
        dsimp only [finalSumcheckRbrExtractor, firstOracleWitnessConsistencyProp]
        simp only [Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, Fin.val_last,
          OracleFrontierIndex.val_mkFromStmtIdx]
        exact (extractMLP_eq_some_iff_pair_UDRClose 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (f := getFirstOracle 𝔽q β oStmtIn) (tpoly := tpoly)).mp h_extractMLP
      · exact hConsistent.1
    | inr hBad =>
      -- A block bad event at the last round is an incremental bad event there.
      exact Or.inl (
        (badEventExistsProp_iff_incrementalBadEventExistsProp_last 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
          (oStmt := oStmtIn) (challenges := stmtIn.challenges)).1 hBad
      )
  toFun_full := fun s tr witOut h => by
    obtain ⟨hcheck, hrel⟩ := (finalSumcheckVerifierGuardedForm 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).check_and_of_prEvent_pos h
    rw [finalSumcheckVerifierGuardedForm_check 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) s tr] at hcheck
    exact ⟨of_decide_eq_true hcheck, hrel⟩

omit [CharP L 2] in
/-- **Worst-case round-by-round knowledge soundness of the final sum-check step**, at the extractor
`finalSumcheckRbrExtractor`, the knowledge-state function `finalSumcheckKnowledgeStateFunction` and
the error `finalSumcheckKnowledgeError`. The step sends no challenge, so there is no
extraction-failure event to bound; the content is the knowledge-state function's obligations. -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (roundRelation 𝔽q β (ϑ := ϑ) (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (multpoly := BBF_multiplier) (Fin.last ℓ))
      (finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ))
      (finalSumcheckRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (finalSumcheckKnowledgeStateFunction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) init impl)
      finalSumcheckKnowledgeError :=
  Verifier.rbrKnowledgeSoundnessWorstCaseWith_of_isEmpty_challengeIdx _ _

omit [DecidableEq 𝔽q] [CharP L 2] in
/-- Worst-case round-by-round knowledge soundness of the final sum-check step: the existential
form of `finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith`. -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCase {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (roundRelation 𝔽q β (ϑ := ϑ) (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (multpoly := BBF_multiplier) (Fin.last ℓ))
      (finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      finalSumcheckKnowledgeError := by
  classical
  exact (Verifier.rbrKnowledgeSoundnessWorstCase_iff_exists_with init impl _ _ _ _).mpr
    ⟨_, _, _, finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith 𝔽q β init impl⟩

omit [DecidableEq 𝔽q] [CharP L 2] in
/-- Round-by-round knowledge soundness of the final sum-check step: the averaged form of
`finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCase`. -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
      (relIn := roundRelation 𝔽q β (ϑ := ϑ) (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (multpoly := BBF_multiplier) (Fin.last ℓ))
      (relOut := finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (rbrKnowledgeError := finalSumcheckKnowledgeError) :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCase 𝔽q β init impl)

end FinalSumcheckStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
