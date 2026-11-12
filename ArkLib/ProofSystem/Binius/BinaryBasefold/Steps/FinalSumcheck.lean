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

After the last fold, the prover sends the constant `c := f⁽ˡ⁾(0, …, 0)` of its fully folded word.
For a public multiplier `A` with evaluator `Â`, the verifier checks the closing sum-check equation
`s_ℓ = Â(ctx, r') · c` and outputs the target, the challenges and `c`. The step sends no challenge.
The equation is a multiplication, not a division, so a zero multiplier value still constrains the
target. The evaluation-claim opening uses `openingMultiplier`, for which `Â(ctx, r') = eq̃(r, r')`;
the unrolled FRI-Binius protocol uses the ring-switching multiplier.

## Main definitions and statements

* `finalSumcheckProver`, `finalSumcheckVerifier`, `finalSumcheckOracleReduction`: the step.
* `finalSumcheckVerifierGuardedForm`: the verifier's guard (the closing equation) and verdict as
  data, through `Verifier.GuardedForm.ofQueryGuard`.
* `finalSumcheckOracleReduction_perfectCompleteness`: perfect completeness from the strict round
  relation at `ℓ` to the strict final sum-check output relation, through `finalSumcheckStepLogic`.
* `finalSumcheckKnowledgeStateFunction`: before the message, the round relation at `ℓ`; after it,
  the closing equation and the final folding state. Its backward step decodes the multilinear
  polynomial from the first oracle (`Steps/FinalSumcheck/Extraction.lean`) and recovers the product
  claim `s_ℓ = A(ctx)(r') · t(r')` without dividing by the multiplier.
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
variable {Context : Type} (multiplier : Multiplier Context L ℓ)

section FinalSumcheckStep

/-! ## Protocol definitions -/

open Classical in
/-- The prover of the final sum-check step: it sends the constant of its fully folded word. -/
noncomputable def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  PrvState := fun
    | 0 => Statement (L := L) Context (Fin.last ℓ) × (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
        × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)
    | _ => Statement (L := L) Context (Fin.last ℓ) × (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
        × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    let c : L := witIn.f ⟨0, by simp only [zero_mem]⟩ -- f^(ℓ)(0, ..., 0)
    pure ⟨c, (stmtIn, oStmtIn, witIn, c)⟩
  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- No challenges in this step
  output := fun ⟨stmtIn, oStmtIn, witIn, c⟩ => do
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) c
    pure ((finalSumcheckStepLogic 𝔽q β multiplier (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).proverOut stmtIn witIn oStmtIn t)

/-- The verifier of the final sum-check step: it queries the sent constant, guards on the closing
sum-check equation of `finalSumcheckStepLogic`, and outputs the target, the challenges and the
constant. The oracle statements pass through. -/
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  verify := fun stmtIn _ => do
    let c : L ← query (spec := [(pSpecFinalSumcheckStep (L := L)).Message]ₒ)
      ⟨⟨0, by rfl⟩, (by exact ())⟩
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) c
    let logic := (finalSumcheckStepLogic 𝔽q β multiplier (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    let : Decidable (logic.verifierCheck stmtIn t) := by
      dsimp only [logic, finalSumcheckStepLogic]
      infer_instance
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)
  outputOracle := (finalSumcheckStepLogic 𝔽q β multiplier (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).outputOracle

/-- The oracle reduction of the final sum-check step. -/
noncomputable def finalSumcheckOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  prover := finalSumcheckProver 𝔽q β multiplier (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  verifier := finalSumcheckVerifier 𝔽q β multiplier (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)

/-- The final sum-check verifier's guard and verdict as data: `finalSumcheckStepLogic`'s check and
output statement on the sent constant, with the unchanged oracle statements. -/
def finalSumcheckVerifierGuardedForm :
    (finalSumcheckVerifier 𝔽q β multiplier (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).toVerifier.GuardedForm :=
  Verifier.GuardedForm.ofQueryGuard _ ⟨⟨0, rfl⟩, ()⟩
    (fun s a _ => (finalSumcheckStepLogic 𝔽q β multiplier (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).verifierCheck s (FullTranscript.mk1 a))
    (hcheck := fun _ _ _ => by
      dsimp only [finalSumcheckStepLogic]
      infer_instance)
    (fun s a _ => (finalSumcheckStepLogic 𝔽q β multiplier (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).verifierOut s (FullTranscript.mk1 a))
    (fun _ _ => rfl)

omit [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
open Classical in
/-- The final sum-check verifier's guard is the closing sum-check equation
`s_ℓ = Â(ctx, r') · c` on the sent constant `c`. -/
@[simp]
theorem finalSumcheckVerifierGuardedForm_check
    (s : Statement (L := L) Context (Fin.last ℓ) × ∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (tr : (pSpecFinalSumcheckStep (L := L)).FullTranscript) :
    (finalSumcheckVerifierGuardedForm 𝔽q β multiplier (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).check s tr =
      decide (s.1.sumcheck_target =
        multiplier.evaluate s.1.ctx s.1.challenges * (show L from tr.messages ⟨0, rfl⟩)) :=
  decide_eq_decide.mpr Iff.rfl

omit [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
open Classical in
/-- The final sum-check verifier's verdict is the input target and challenges with the sent
constant, and the unchanged oracle statements. -/
@[simp]
theorem finalSumcheckVerifierGuardedForm_out
    (s : Statement (L := L) Context (Fin.last ℓ) × ∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (tr : (pSpecFinalSumcheckStep (L := L)).FullTranscript) :
    (finalSumcheckVerifierGuardedForm 𝔽q β multiplier (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).out s tr =
      ({ sumcheck_target := s.1.sumcheck_target, challenges := s.1.challenges,
          finalConstant := show L from tr.messages ⟨0, rfl⟩ }, s.2) := rfl

/-! ## Security

### Perfect completeness -/

omit [DecidableEq 𝔽q] in
/-- Perfect completeness of the final sum-check step, from the strict round relation at `ℓ` to the
strict final sum-check output relation. -/
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecFinalSumcheckStep (L := L))
      (relIn := strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (multpoly := multiplier.polynomial) (Fin.last ℓ))
      (relOut := strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (oracleReduction := finalSumcheckOracleReduction 𝔽q β multiplier (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)) (init := init) (impl := impl) := by
  classical
  let step := finalSumcheckStepLogic 𝔽q β multiplier (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  apply step.perfectCompleteness_of_isStronglyComplete
    (finalSumcheckOracleReduction 𝔽q β multiplier (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    (finalSumcheckVerifierGuardedForm 𝔽q β multiplier (𝓑 := 𝓑))
    (finalSumcheckStepLogic_isStronglyComplete 𝔽q β multiplier (𝓑 := 𝓑))
  · intro stmt wit oracles q hq
    let c : L := wit.f ⟨0, by simp only [zero_mem]⟩
    have hp : (finalSumcheckProver 𝔽q β multiplier (ϑ := ϑ)
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

/-! ### Round-by-round knowledge soundness -/

omit [SampleableType L] in
/-- A passing closing equation and consistent decoded folds recover the product claim
`s_ℓ = A(ctx)(r') · t(r')` for the decoded polynomial `t`, without dividing by the multiplier. -/
theorem sumcheck_target_eq_of_finalSumcheckOracleConsistent
    (stmtIn : Statement (L := L) Context (Fin.last ℓ)) (c : L)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (tpoly : MultilinearPoly L ℓ)
    (h_extract : extractMlp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (f := getFirstOracle 𝔽q β oStmtIn) = some tpoly)
    (h_consistent : FinalSumcheckOracleConsistent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtOut := ⟨stmtIn.sumcheck_target, stmtIn.challenges, c⟩) (oStmtOut := oStmtIn))
    (h_check : stmtIn.sumcheck_target = multiplier.evaluate stmtIn.ctx stmtIn.challenges * c) :
    stmtIn.sumcheck_target =
      (multiplier stmtIn.ctx).val.eval stmtIn.challenges * tpoly.val.eval stmtIn.challenges := by
  have hc := eval_eq_final_constant_of_extractMlp_eq_some 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨stmtIn.sumcheck_target, stmtIn.challenges, c⟩ oStmtIn
    tpoly h_extract h_consistent
  change c = tpoly.val.eval stmtIn.challenges at hc
  rw [multiplier.evaluate_eq, hc] at h_check
  exact h_check

/-- The round-`ℓ` witness rebuilt from a decoded polynomial `t`: the residual sum-check polynomial
is the constant target, and the folded word is the honest fold of `t`'s codeword. -/
noncomputable def finalSumcheckDecodedWitness
    (stmtIn : Statement (L := L) Context (Fin.last ℓ)) (tpoly : MultilinearPoly L ℓ) :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) where
  t := tpoly
  H := ⟨MvPolynomial.C stmtIn.sumcheck_target, by
    rw [mem_restrictDegree_iff_degreeOf_le]
    intro n
    rw [MvPolynomial.degreeOf_C]
    exact Nat.zero_le _⟩
  f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) tpoly stmtIn.challenges

omit [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] in
/-- The constant residual polynomial satisfies the local sum-check equation at round `ℓ`. -/
theorem finalSumcheckDecodedWitness_sumcheckConsistency
    (stmtIn : Statement (L := L) Context (Fin.last ℓ)) (tpoly : MultilinearPoly L ℓ) :
    sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) stmtIn.sumcheck_target
      (finalSumcheckDecodedWitness 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn tpoly).H := by
  unfold sumcheckConsistencyProp
  simp [finalSumcheckDecodedWitness]

omit [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] in
/-- The recovered product claim makes the rebuilt witness structurally honest. No nonzero
assumption on either factor is required. -/
theorem finalSumcheckDecodedWitness_structural
    (stmtIn : Statement (L := L) Context (Fin.last ℓ)) (tpoly : MultilinearPoly L ℓ)
    (h : stmtIn.sumcheck_target =
      (multiplier stmtIn.ctx).val.eval stmtIn.challenges * tpoly.val.eval stmtIn.challenges) :
    WitnessStructuralInvariant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (multpoly := multiplier.polynomial) stmtIn
      (finalSumcheckDecodedWitness 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn tpoly) := by
  refine ⟨?_, rfl⟩
  apply SetLike.coe_eq_coe.mp
  rw [Sumcheck.Structured.coe_fixPrefix_initial_last]
  simp only [finalSumcheckDecodedWitness, h, MvPolynomial.C_mul]

/-- Decode the first oracle and rebuild the round-`ℓ` witness; if decoding fails, rebuild it from
the zero polynomial. The fallback is never used under the final folding state's consistency
branch, and its bad-event branch needs no witness. -/
noncomputable def finalSumcheckExtractWitness
    (stmtIn : Statement (L := L) Context (Fin.last ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j) :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) :=
  match extractMlp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (f := getFirstOracle 𝔽q β oStmtIn) with
  | some tpoly => finalSumcheckDecodedWitness 𝔽q β stmtIn tpoly
  | none => finalSumcheckDecodedWitness 𝔽q β stmtIn 0

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

/-- The round-by-round extractor of the final sum-check step. Across the message it applies
`finalSumcheckExtractWitness`: it decodes the multilinear polynomial from the committed first
oracle, not from any prover-supplied witness. -/
noncomputable def finalSumcheckRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) Context (Fin.last ℓ)) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L))
    (WitMid := FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)) where
  extractIn := fun _ w => w
  extractMid := fun m ⟨stmtMid, oStmtMid⟩ _ _ => by
    have hm : m = 0 := by omega
    subst hm
    exact finalSumcheckExtractWitness 𝔽q β stmtMid oStmtMid
  extractOut := fun _ _ _ => ()

/-- The knowledge state of the final sum-check step: before the message, the round relation at
`ℓ`; after it, the closing sum-check equation on the sent constant and the final folding state of
the output statement. -/
def FinalSumcheckKnowledgeState {m : Fin (1 + 1)}
    (tr : Transcript m (pSpecFinalSumcheckStep (L := L)))
    (stmtIn : Statement (L := L) Context (Fin.last ℓ))
    (witMid : FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) m)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j) : Prop :=
  match m with
  | ⟨0, _⟩ =>
    KnowledgeInvariant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (multpoly := multiplier.polynomial)
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (stmt := stmtIn) (wit := witMid) (oStmt := oStmtIn)
      (localChecks := sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) stmtIn.sumcheck_target
          witMid.H)
  | ⟨1, _⟩ =>
    let c : L := tr.messages ⟨0, rfl⟩
    stmtIn.sumcheck_target = multiplier.evaluate stmtIn.ctx stmtIn.challenges * c ∧
      FinalSumcheckFoldingState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (input := ⟨⟨stmtIn.sumcheck_target, stmtIn.challenges, c⟩, oStmtIn⟩)

omit [SampleableType L] in
/-- Backward extraction across the final message: a passing closing equation and the final
folding state give the round-`ℓ` knowledge invariant for `finalSumcheckExtractWitness`. On the
consistency branch decoding succeeds and the product claim is recovered; the block bad event at
the last round is an incremental bad event there. -/
theorem finalSumcheckExtractWitness_knowledgeInvariant
    (stmtIn : Statement (L := L) Context (Fin.last ℓ)) (c : L)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (h_check : stmtIn.sumcheck_target = multiplier.evaluate stmtIn.ctx stmtIn.challenges * c)
    (h_state : FinalSumcheckFoldingState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (input := ⟨⟨stmtIn.sumcheck_target, stmtIn.challenges, c⟩, oStmtIn⟩)) :
    KnowledgeInvariant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (multpoly := multiplier.polynomial)
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (stmt := stmtIn) (wit := finalSumcheckExtractWitness 𝔽q β stmtIn oStmtIn) (oStmt := oStmtIn)
      (localChecks := sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) stmtIn.sumcheck_target
        (finalSumcheckExtractWitness 𝔽q β stmtIn oStmtIn).H) := by
  rcases h_state with h_consistent | h_bad
  · obtain ⟨tpoly, h_extract⟩ := exists_extractMlp_eq_some_of_finalSumcheckOracleConsistent 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmtIn)
      (h_oracle_consistency := h_consistent)
    simp only [finalSumcheckExtractWitness, h_extract]
    refine Or.inr ⟨finalSumcheckDecodedWitness_sumcheckConsistency 𝔽q β stmtIn tpoly, ?_, ?_,
      h_consistent.1⟩
    · exact finalSumcheckDecodedWitness_structural 𝔽q β multiplier stmtIn tpoly
        (sumcheck_target_eq_of_finalSumcheckOracleConsistent 𝔽q β multiplier stmtIn c oStmtIn
          tpoly h_extract h_consistent h_check)
    · exact (extractMlp_eq_some_iff_pairUniqueDecodingClose 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (f := getFirstOracle 𝔽q β oStmtIn)
        (tpoly := tpoly)).mp h_extract
  · exact Or.inl ((blockBadEventExists_iff_incrementalBadEventExists_last 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (oStmt := oStmtIn)
      (challenges := stmtIn.challenges)).mp h_bad)

/-- The knowledge-state function of the final sum-check step, `FinalSumcheckKnowledgeState`,
with its obligations. -/
noncomputable def finalSumcheckKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β multiplier (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).KnowledgeStateFunction init impl
    (relIn := roundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (multpoly := multiplier.polynomial) (Fin.last ℓ))
    (relOut := finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (extractor := finalSumcheckRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
  where
  toFun := fun _ ⟨stmtIn, oStmtIn⟩ tr witMid =>
    FinalSumcheckKnowledgeState 𝔽q β multiplier (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (tr := tr) (stmtIn := stmtIn) (witMid := witMid) (oStmtIn := oStmtIn)
  toFun_empty := fun _ _ h => h
  toFun_next := fun m _ ⟨stmtIn, oStmtIn⟩ _ msg _ => by
    have hm : m = 0 := by omega
    subst hm
    intro h
    exact finalSumcheckExtractWitness_knowledgeInvariant 𝔽q β multiplier stmtIn msg oStmtIn
      h.1 h.2
  toFun_full := fun s tr _ h => by
    obtain ⟨hcheck, hrel⟩ := (finalSumcheckVerifierGuardedForm 𝔽q β multiplier (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).check_and_of_prEvent_pos h
    rw [finalSumcheckVerifierGuardedForm_check 𝔽q β multiplier (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) s tr] at hcheck
    exact ⟨of_decide_eq_true hcheck, hrel⟩

/-- Round-by-round knowledge soundness of the final sum-check step, at the extractor
`finalSumcheckRbrExtractor`, the knowledge-state function `finalSumcheckKnowledgeStateFunction` and
the error `finalSumcheckKnowledgeError`. The step sends no challenge, so there is no
extraction-failure event to bound; the content is the knowledge-state function's obligations. -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWith {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β multiplier (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).toVerifier.rbrKnowledgeSoundnessWith init impl
      (roundRelation 𝔽q β (ϑ := ϑ) (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (multpoly := multiplier.polynomial) (Fin.last ℓ))
      (finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ))
      (finalSumcheckRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (finalSumcheckKnowledgeStateFunction 𝔽q β multiplier (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) init impl)
      finalSumcheckKnowledgeError :=
  Verifier.rbrKnowledgeSoundnessWith_of_isEmpty_challengeIdx _ _

omit [DecidableEq 𝔽q] in
/-- Round-by-round knowledge soundness of the final sum-check step: the existential
form of `finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWith`. -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β multiplier (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).toVerifier.rbrKnowledgeSoundness init impl
      (roundRelation 𝔽q β (ϑ := ϑ) (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (multpoly := multiplier.polynomial) (Fin.last ℓ))
      (finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      finalSumcheckKnowledgeError := by
  classical
  exact (Verifier.rbrKnowledgeSoundness_iff_exists_with init impl _ _ _ _).mpr
    ⟨_, _, _, finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWith 𝔽q β multiplier init impl⟩

end FinalSumcheckStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
