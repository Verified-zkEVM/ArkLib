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
  data, through `Verifier.GuardedForm.ofQueryGuard`.
* `finalSumcheckOracleReduction_perfectCompleteness`: perfect completeness from the strict round
  relation at `ℓ` to the strict final sum-check output relation, through `finalSumcheckStepLogic`.
* `finalSumcheckKnowledgeStateFunction`: before the message, the round relation at `ℓ`; after it,
  the closing equation and the final folding state. Its backward step decodes the multilinear
  polynomial from the first oracle (`Steps/FinalSumcheck/Extraction.lean`).
* `finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWith`: round-by-round
  knowledge soundness at `finalSumcheckRbrExtractor` and `finalSumcheckKnowledgeStateFunction`, with
  an existential form.

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
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]

omit [Fintype 𝔽q] in
local instance [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) := ⟨CharP.prime_ringChar 𝔽q⟩

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
    let : Decidable (logic.verifierCheck stmtIn t) := by
      dsimp only [logic, finalSumcheckStepLogic]
      infer_instance
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)
  outputOracle := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).outputOracle

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

/-- The final sum-check verifier's guard and verdict as data: `finalSumcheckStepLogic`'s check and
output statement on the sent constant, with the unchanged oracle statements. -/
def finalSumcheckVerifierGuardedForm :
    (finalSumcheckVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).toVerifier.GuardedForm :=
  Verifier.GuardedForm.ofQueryGuard _ ⟨⟨0, rfl⟩, ()⟩
    (fun s a _ => (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).verifierCheck s (FullTranscript.mk1 a))
    (hcheck := fun _ _ _ => by
      dsimp only [finalSumcheckStepLogic]
      infer_instance)
    (fun s a _ => (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).verifierOut s (FullTranscript.mk1 a))
    (fun _ _ => rfl)

omit [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
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

omit [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
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
          finalConstant := show L from tr.messages ⟨0, rfl⟩ }, s.2) := rfl

omit [DecidableEq 𝔽q] in
/-- Perfect completeness of the final sum-check step, from the strict round relation at `ℓ` to the
strict final sum-check output relation. -/
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecFinalSumcheckStep (L := L))
      (relIn := strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (multpoly := multiplier) (Fin.last ℓ))
      (relOut := strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (oracleReduction := finalSumcheckOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)) (init := init) (impl := impl) := by
  classical
  let step := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  apply step.perfectCompleteness_of_isStronglyComplete
    (finalSumcheckOracleReduction 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    (finalSumcheckVerifierGuardedForm 𝔽q β (𝓑 := 𝓑))
    (finalSumcheckStepLogic_isStronglyComplete 𝔽q β (𝓑 := 𝓑))
  · intro stmt wit oracles q hq
    let c : L := wit.f ⟨0, by simp only [zero_mem]⟩
    have hp : (finalSumcheckProver 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).run (stmt, oracles) wit =
        pure (((default : (pSpecFinalSumcheckStep (L := L)).Transcript 0).concat (m := 0) c),
          step.proverOut stmt wit oracles (FullTranscript.mk1 c)) := rfl
    dsimp only [finalSumcheckOracleReduction] at hq
    rw [hp] at hq
    replace hq := OracleComp.eq_of_mem_support_pure _ hq
    refine ⟨isEmptyElim, hq.trans ?_⟩
    apply Prod.ext
    · exact (FullTranscript.mk1_eq_snoc (pSpec := pSpecFinalSumcheckStep (L := L)) c).symm
    · rfl
  · intro stmt oracles tr
    exact decide_eq_decide.mpr Iff.rfl
  · intro stmt oracles tr
    rfl

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
  extractIn := fun _ w => w
  extractMid := fun m ⟨stmtMid, oStmtMid⟩ trSucc witMidSucc => by
    have hm : m = 0 := by omega
    subst hm
    -- Decode t from the first oracle f^(0)
    let f0 := getFirstOracle 𝔽q β oStmtMid
    let polyOpt := extractMlp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
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
        H := H_constant,
        f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) tpoly stmtMid.challenges
      }
  extractOut := fun ⟨stmtIn, oStmtIn⟩ tr witOut => ()

/-- The knowledge state of the final sum-check step: before the message, the round relation at
`ℓ`; after it, the closing sum-check equation on the sent constant and the final folding state of
the output statement. -/
def FinalSumcheckKnowledgeState {m : Fin (1 + 1)}
    (tr : Transcript m (pSpecFinalSumcheckStep (L := L)))
    (stmtIn : Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witMid : FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) m)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    KnowledgeInvariant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (multpoly := multiplier)
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
      finalConstant := c
    }
    let sumcheckFinalCheck : Prop := stmtIn.sumcheck_target
      = eqTilde (stmtIn.ctx.t_eval_point) stmtIn.challenges * c
    let finalFoldingProp := FinalSumcheckFoldingState 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)  (input := ⟨stmtOut, oStmtIn⟩)
    sumcheckFinalCheck ∧ finalFoldingProp -- local checks ∧ (oracleConsistency ∨ badEventExists)

/-- The knowledge-state function of the final sum-check step, `FinalSumcheckKnowledgeState`,
with its
obligations. -/
noncomputable def finalSumcheckKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).KnowledgeStateFunction init impl
    (relIn := roundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (multpoly := multiplier) (Fin.last ℓ) )
    (relOut := finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
    (extractor := finalSumcheckRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
  where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    FinalSumcheckKnowledgeState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (tr := tr) (stmtIn := stmtIn) (witMid := witMid) (oStmtIn := oStmtIn)
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witMid h => h
  toFun_next := fun m hDir (stmtIn, oStmtIn) tr msg witMid => by
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => omega
    subst h_m_eq_0
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.castSucc_zero]
    -- For the final sumcheck step, there is a single P→V message carrying the final constant,
    -- so we can read it directly from `msg` without reconstructing a truncated transcript.
    let c : L := msg
    let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
      ctx := stmtIn.ctx,
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      finalConstant := c
    }
    intro h_kState_round1
    unfold FinalSumcheckKnowledgeState FinalSumcheckFoldingState
      KnowledgeInvariant at h_kState_round1 ⊢
    simp only [Fin.isValue, Nat.reduceAdd, Fin.mk_one,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod] at h_kState_round1
    -- At m=1 we have local final-check and (oracle-consistency ∨ block-bad-event).
    -- At m=0 the target is `KnowledgeInvariant`:
    -- incremental-bad-event ∨ (local ∧ structural ∧ initial ∧ oracleFoldingConsistency).
    obtain ⟨h_V_check, h_core⟩ := h_kState_round1
    -- Case split on the m=1 final-folding state: consistency or block bad-event.
    cases h_core with
    | inl hConsistent =>
      -- When we have FinalSumcheckOracleConsistent, extractMlp must succeed.
      have ⟨tpoly, h_extractMLP⟩ :=
          exists_extractMlp_eq_some_of_finalSumcheckOracleConsistent 𝔽q β
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
      · -- WitnessStructuralInvariant
        unfold finalSumcheckRbrExtractor WitnessStructuralInvariant
        simp only [Fin.val_last, Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, and_true]
        refine SetLike.coe_eq_coe.mp ?_
        rw [Sumcheck.Structured.coe_fixPrefix_initial_last ℓ tpoly
          (multiplier stmtIn.ctx) stmtIn.challenges]
        have h_sumcheck_target_eq : stmtIn.sumcheck_target =
          (MvPolynomial.eval stmtIn.challenges
            (multiplier stmtIn.ctx).val) *
            (MvPolynomial.eval stmtIn.challenges tpoly.val) := by
          rw [h_V_check]
          congr 1
          change c = tpoly.val.eval stmtIn.challenges
          exact eval_eq_final_constant_of_extractMlp_eq_some 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmtOut := oStmtIn) (stmtOut := stmtOut)
            (tpoly := tpoly)
            (h_extractMLP := h_extractMLP) (h_finalSumcheckStepOracleConsistency := hConsistent)
        simp only
          [h_sumcheck_target_eq, Fin.val_last, Fin.coe_ofNat_eq_mod, MvPolynomial.C_mul]
      · -- FirstOracleWitnessConsistent
        dsimp only [finalSumcheckRbrExtractor, FirstOracleWitnessConsistent]
        simp only [Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, Fin.val_last,
          OracleFrontierIndex.val_mkFromStmtIdx]
        exact (extractMlp_eq_some_iff_pairUniqueDecodingClose 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (f := getFirstOracle 𝔽q β oStmtIn) (tpoly := tpoly)).mp h_extractMLP
      · exact hConsistent.1
    | inr hBad =>
      -- A block bad event at the last round is an incremental bad event there.
      exact Or.inl (
        (blockBadEventExists_iff_incrementalBadEventExists_last 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
          (oStmt := oStmtIn) (challenges := stmtIn.challenges)).1 hBad
      )
  toFun_full := fun s tr witOut h => by
    obtain ⟨hcheck, hrel⟩ := (finalSumcheckVerifierGuardedForm 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).check_and_of_prEvent_pos h
    rw [finalSumcheckVerifierGuardedForm_check 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) s tr] at hcheck
    exact ⟨of_decide_eq_true hcheck, hrel⟩

/-- Round-by-round knowledge soundness of the final sum-check step, at the extractor
`finalSumcheckRbrExtractor`, the knowledge-state function `finalSumcheckKnowledgeStateFunction` and
the error `finalSumcheckKnowledgeError`. The step sends no challenge, so there is no
extraction-failure event to bound; the content is the knowledge-state function's obligations. -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWith {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).toVerifier.rbrKnowledgeSoundnessWith init impl
      (roundRelation 𝔽q β (ϑ := ϑ) (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (multpoly := multiplier) (Fin.last ℓ))
      (finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ))
      (finalSumcheckRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (finalSumcheckKnowledgeStateFunction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) init impl)
      finalSumcheckKnowledgeError :=
  Verifier.rbrKnowledgeSoundnessWith_of_isEmpty_challengeIdx _ _

omit [DecidableEq 𝔽q] in
/-- Round-by-round knowledge soundness of the final sum-check step: the existential
form of `finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWith`. -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).toVerifier.rbrKnowledgeSoundness init impl
      (roundRelation 𝔽q β (ϑ := ϑ) (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (multpoly := multiplier) (Fin.last ℓ))
      (finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      finalSumcheckKnowledgeError := by
  classical
  exact (Verifier.rbrKnowledgeSoundness_iff_exists_with init impl _ _ _ _).mpr
    ⟨_, _, _, finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWith 𝔽q β init impl⟩

end FinalSumcheckStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
