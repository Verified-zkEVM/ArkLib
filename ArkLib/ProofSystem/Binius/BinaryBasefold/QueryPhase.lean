/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import ArkLib.OracleReduction.Completeness
import ArkLib.OracleReduction.Basic
import ArkLib.Data.Misc.Basic

namespace Binius.BinaryBasefold.QueryPhase

/-!
## Query Phase (Final Query Round)
The final verification phase (proximity testing) as an oracle reduction.
(Note that here `B_k` means the boolean hypercube of dimension `k`)

- `V` executes the following querying procedure:
  for `γ` repetitions do
    `V` samples a challenge `v ← B_{ℓ+R}` randomly and sends it to P.
    for `i in {0, ϑ, ..., ℓ-ϑ}` (i.e., taking `ϑ`-sized steps) do
      for each `u` in `B_v`, => gather data for `c_{i+ϑ}`
        `V` sends (query, [f^(i)], (u_0, ..., u_{ϑ-1}, v_{i+ϑ}, ..., v_{ℓ+R-1})) to the oracle.
      if `i > 0` then `V` requires `c_i ?= f^(i)(v_i, ..., v_{ℓ+R-1})`.
      `V` defines `c_{i+ϑ} := fold(f^(i), r'_i, ..., r'_{i+ϑ-1})(v_{i+ϑ}, ..., v_{ℓ+R-1})`.
    `V` requires `c_ℓ ?= c`.
-/
noncomputable section
open OracleSpec OracleComp
open AdditiveNTT Polynomial MvPolynomial ProtocolSpec

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

section FinalQueryRoundIOR

/-!
### Oracle-Aware Reduction Logic for Query Phase

The query phase uses `OracleAwareReductionLogicStep` because its verifier check involves
oracle queries (querying committed codewords at fiber points).
-/

/-- The oracle-aware reduction logic step for the query phase.

This encapsulates the pure logic of the query phase:
- `verifierCheck`: Runs `verifyQueryPhase` which queries oracles for fiber evaluations
- `verifierOut`: Returns `true` (acceptance) or `false` (rejection)
- `honestProverTranscript`: The honest transcript just receives the challenges
- `proverOut`: The honest prover always outputs `(true, ())` -/
noncomputable def queryPhaseLogicStep :
    OracleAwareReductionLogicStep
      -- oSpec is the base/shared oracle (empty for query phase - no random oracles)
      -- The structure internally uses oSpec + ([OracleIn]ₒ + [pSpec.Message]ₒ)
      (oSpec := []ₒ)
      (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
      (WitIn := Unit)
      (OracleIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (OracleOut := fun _ : Empty => Unit)
      (StmtOut := Bool)
      (WitOut := Unit)
      (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  -- Relations
  completeness_relIn := strictFinalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  completeness_relOut := acceptRejectOracleRel
  -- Verifier (Oracle-Aware): verifierCheck queries oracles and returns StmtOut
  -- Iterates through all γ_repetitions and checks each one
  verifierCheck := fun stmtIn transcript => do
    let challenges := transcript.challenges
    let fold_challenges : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0 :=
      challenges ⟨0, by rfl⟩
    for rep in (List.finRange γ_repetitions) do
      let v := fold_challenges rep
      let _ ← checkSingleRepetition 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        v stmtIn stmtIn.final_constant
    return true  -- StmtOut = Bool for QueryPhase
  -- Pure output computation (deterministic)
  verifierOut := fun _stmtIn _transcript => true
  -- Oracle embedding (no output oracles for query phase)
  embed := ⟨Empty.elim, fun a _ => Empty.elim a⟩
  hEq := fun i => Empty.elim i
  -- Honest prover transcript: just receives the challenges
  honestProverTranscript := fun stmtIn _witIn _oStmtIn challenges =>
    FullTranscript.mk1 (challenges ⟨0, by rfl⟩)
  -- Prover output: always outputs (true, ())
  proverOut := fun _stmtIn _witIn _oStmtIn _transcript =>
    ((true, fun i => Empty.elim i), ())

def queryPhaseProverState : Fin (1 + 1) → Type := fun
  | 0 => FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ) ×
    (∀ i, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) i) × Unit
  | 1 => FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ) ×
    (∀ i, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) i) × Unit ×
    (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge ⟨0, by rfl⟩

/-- The oracle prover for the final query phase.

Uses components from `queryPhaseLogicStep` for consistency with the logic specification. -/
noncomputable def queryOracleProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (WitIn := Unit)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitOut := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  -- Prover state: tracks (stmtIn, oStmtIn, witIn) and optionally the challenges
  PrvState := queryPhaseProverState 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  input := fun ⟨⟨stmtIn, oStmtIn⟩, witIn⟩ => (stmtIn, oStmtIn, witIn)
  sendMessage
  | ⟨0, h⟩ => nomatch h
  receiveChallenge
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩  => do
    -- V sends all γ challenges v₁, ..., v_γ
    pure (fun challenges => (stmtIn, oStmtIn, witIn, challenges))
  output := fun ⟨stmtIn, oStmtIn, witIn, challenges⟩ => do
    -- Build the transcript using the logic step's honestProverTranscript
    let transcript := FullTranscript.mk1 (pSpec :=
      pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (challenges)
    -- Delegate to proverOut from the logic step
    pure ((queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).proverOut stmtIn witIn oStmtIn transcript)

/-- The oracle verifier for the final query phase.

Uses components from `queryPhaseLogicStep` for consistency with the logic specification:
- `verifierCheck`: monadic check via `verifyQueryPhase`
- `verifierOut`: pure output computation
- `embed` and `hEq`: oracle embedding from the logic step -/
noncomputable def queryOracleVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  verify := fun stmtIn challenges => do
    let transcript := FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (challenges ⟨0, by rfl⟩)
    let logic := queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    let _ ← (logic.verifierCheck stmtIn transcript)
    pure (logic.verifierOut stmtIn transcript)
  -- Use embed and hEq from the logic step
  embed := (queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).embed
  hEq := (queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).hEq

/-- The oracle reduction for the final query phase. -/
noncomputable def queryOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (WitIn := Unit)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitOut := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  prover := queryOracleProver 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  verifier := queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

/-- The final query round as an `OracleProof` (since it outputs Bool and no oracle statements). -/
noncomputable def queryOracleProof : OracleProof
    (oSpec := []ₒ)
    (Statement := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStatement := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (Witness := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  queryOracleReduction 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

lemma OracleComp.liftM_query_eq_liftM_liftM.{u, v, z}
    {ι : Type u} {spec : OracleSpec ι} {m : Type v → Type z}
    [MonadLift (OracleComp spec) m] {α : Type v}
    (q : OracleQuery spec α) :
    (liftM q : m α) = liftM (liftM q : OracleComp spec α) := rfl

omit [CharP L 2] [SampleableType L] in
lemma mem_support_queryFiberPoints
    -- The number of oracles in query phase is toCodewordsCount(ℓ) = ℓ/ϑ
    {oraclePositionIdx : Fin (ℓ / ϑ)} (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (f_i_on_fiber : Vector L (2 ^ ϑ))
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn :
      ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    -- Hypothesis: The fiber evaluations come from the simulated oracle query
    (h_fiber_mem :
      let step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      some (f_i_on_fiber) ∈
      (simulateQ.{0, 0, 0} so
        ((queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oraclePositionIdx v))).support) :
    let k_th_oracleIdx: Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
      ⟨oraclePositionIdx, by simp only [toOutCodewordsCount, Fin.val_last,
        lt_self_iff_false, ↓reduceIte, add_zero, Fin.is_lt];⟩
    ∀ (fiberIndex : Fin (2 ^ ϑ)),
      f_i_on_fiber.get fiberIndex =
      (oStmtIn k_th_oracleIdx (getFiberPoint 𝔽q β oraclePositionIdx v fiberIndex)) := by
  simp only [MessageIdx] at h_fiber_mem
  set step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) with h_step
  set transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges with h_transcript
  set so := OracleInterface.simOracle2 []ₒ oStmtIn transcript.messages with h_so
  -- rw [simulateQ_liftComp] at h_fiber_mem
  unfold queryFiberPoints at h_fiber_mem
  simp only [bind_pure] at h_fiber_mem
  unfold queryCodeword at h_fiber_mem
  -- Simplify the simulation through liftComp/liftM
  -- simp_rw [← simulateQ_liftComp] at h_fiber_mem
  -- simp only [liftComp_eq_liftM] at h_fiber_mem
  -- Step 1: Unpack Vector.mapM membership
  erw [OptionT.simulateQ_vector_mapM] at h_fiber_mem
  erw [OptionT.mem_support_vector_mapM] at h_fiber_mem
  -- simp only [liftM, monadLift, MonadLift.monadLift] at h_fiber_mem
  conv_rhs at h_fiber_mem =>
    erw [simulateQ_liftComp]
    simp only [MessageIdx, Message, Fin.getElem_fin, Vector.getElem_mk, OptionT.run_monadLift,
      simulateQ_map, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      OptionT.mem_support_iff, toPFunctor_emptySpec, OptionT.support_run_eq, support_map,
      Set.mem_image, Option.some.injEq, exists_eq_right]
    erw [simulateQ_query]
    erw [simulateQ_simOracle2_lift_liftComp_query_T1]
  simp only [monadLift_self, LawfulApplicative.map_pure, support_pure,
    Set.mem_singleton_iff] at h_fiber_mem
  simp only
  intro fiberIndex
  have h_res := h_fiber_mem fiberIndex
  convert h_res using 1
  congr 1
  simp only [Array.getElem_finRange, Fin.cast_mk, Fin.eta]

/-! Simulated `queryFiberPoints` has zero failure probability. -/
omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ in
lemma probFailure_simulateQ_queryFiberPoints_eq_zero
    (so : QueryImpl
      ([]ₒ + ([OracleStatement 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ +
        [(pSpecQuery 𝔽q β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))
      (OracleComp []ₒ))
    (k : Fin (List.finRange (ℓ / ϑ)).length)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    Pr[⊥ |
      OptionT.mk
        (simulateQ.{0, 0, 0} so
          (queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((List.finRange (ℓ / ϑ)).get k) v))] = 0 := by
  dsimp only [queryFiberPoints, queryCodeword, OptionT.mk]
  erw [simulateQ_bind]
  erw [OptionT.probFailure_mk_do_bind_eq_zero_iff.{0, 0}]
  constructor
  · erw [OptionT.simulateQ_vector_mapM]
    simp only [MessageIdx, Message, List.get_eq_getElem, HasEvalPMF.probFailure_eq_zero]
  · intro x hx_mem_support
    erw [OptionT.simulateQ_vector_mapM.{0}] at hx_mem_support
    cases x with
    | none =>
      exact absurd hx_mem_support
        (OptionT.not_mem_support_run_none_of_probFailure_eq_zero _ (by
          apply OptionT.probFailure_vector_mapM_eq_zero
          intro x _
          erw [OptionT.probFailure_eq (m := OracleComp []ₒ)]
          simp only [HasEvalPMF.probFailure_eq_zero, zero_add]
          rw [probOutput_eq_zero_iff]
          erw [simulateQ_map]
          simp))
    | some a =>
      simp only [OptionT.mk]
      erw [simulateQ_pure, probFailure_pure]

/-- Lemma 1 (Safety):
Proves that if `c_k` is the result of `iterated_fold` up to step `k`,
it must match the oracle evaluation at that step (provided by `h_relIn`).
-/
lemma query_phase_consistency_guard_safe
    {k : Fin (ℓ / ϑ)}
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (c_k : L)
    (f_i_on_fiber : Vector L (2 ^ ϑ))
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), witIn))
    -- Hypothesis: c_k is the correct iterated fold value up to this point
    (h_c_k_correct :
      let := k_mul_ϑ_lt_ℓ (k := k)
      let := k_succ_mul_ϑ_le_ℓ (k := k)
      c_k = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := k.val * ϑ)
        (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
        (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ)
          stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
        (y := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
          (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega))
        (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]))
    -- Hypothesis: We are at a step > 0 where a check actually happens
    (h_k_pos : k.val * ϑ > 0)
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    -- Hypothesis: The fiber evaluations come from the simulated oracle query
    (h_fiber_mem :
      let step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      some (f_i_on_fiber) ∈
      (simulateQ.{0, 0, 0} so
        ((queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v))).support) :
  let := k_mul_ϑ_lt_ℓ (k := k)
  c_k = f_i_on_fiber.get (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (v := v) (i := ⟨k.val * ϑ, by omega⟩) (steps := ϑ)) := by
  have h_fiber_val := mem_support_queryFiberPoints 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oraclePositionIdx := k) v f_i_on_fiber stmtIn
    oStmtIn witIn challenges (h_fiber_mem := h_fiber_mem)
  simp only at h_fiber_val
  rw [h_c_k_correct]
  simp only
  have h₁ : k.val * ϑ < ℓ := k_mul_ϑ_lt_ℓ (k := k)
  set destIdx : Fin r := ⟨k.val * ϑ, by omega⟩ with h_destIdx_eq
  conv_rhs => rw [h_fiber_val]
  dsimp only [strictFinalSumcheckRelOut, strictFinalSumcheckRelOutProp,
    strictfinalSumcheckStepFoldingStateProp] at h_relIn
  simp only [Fin.val_last, exists_and_right, Subtype.exists] at h_relIn
  rcases h_relIn with ⟨exists_t_MLP, _⟩
  rcases exists_t_MLP with ⟨t, h_t_mem_support, h_strictOracleFoldingConsistency⟩
  dsimp only [strictOracleFoldingConsistencyProp] at h_strictOracleFoldingConsistency
  -- Now extract the oStmtIn equality at position k
  have h_oStmtIn_k_eq := h_strictOracleFoldingConsistency ⟨k.val,
    by simp only [toOutCodewordsCount_last, Fin.is_lt]⟩
  conv_rhs => rw [h_oStmtIn_k_eq]
  simp only
  have h_point_eq : extractSuffixFromChallenge 𝔽q β v ⟨↑k * ϑ, by omega⟩ (by simp only; omega) =
      getFiberPoint 𝔽q β k v (extractMiddleFinMask 𝔽q β v ⟨↑k * ϑ, by omega⟩ ϑ) := by
    -- The key insight: getFiberPoint reconstructs a point in S^i by:
    -- 1. Taking the suffix at i+ϑ
    -- 2. Joining it with the fiber index u (the middle ϑ bits)
    -- 3. Converting back to sDomain
    -- When u = extractMiddleFinMask v i ϑ, this reconstructs exactly the suffix at i
    -- Unfold definitions
    dsimp only [getFiberPoint, getChallengeSuffix, challengeSuffixToFin, extractSuffixFromChallenge]
    -- Both sides use iteratedQuotientMap, so we need to show they're applied to the same element
    -- This requires showing that finToSDomain (joinBits u suffix_fin) = iteratedQuotientMap v
    -- where u = extractMiddleFinMask and suffix_fin comes from the suffix at i+ϑ
    -- This requires deep reasoning about the relationship between
      -- joinBits, sDomainToFin, finToSDomain, and iteratedQuotientMap
    sorry
  rw [h_point_eq]
  rw [polyToOracleFunc_eq_getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (t := ⟨t, h_t_mem_support⟩) (i := Fin.last ℓ)
    (challenges := stmtIn.challenges) (oStmt := oStmtIn)
    (h_consistency := h_strictOracleFoldingConsistency)]

/--
Lemma 2 (Preservation):
Proves that `checkSingleFoldingStep` computes the correct `iterated_fold` value at step `k+1`.

**Key insight**: This lemma does NOT require `c_k` to be the correct fold value as a hypothesis.
Why? Because `checkSingleFoldingStep` performs a **direct computation** from oracle queries:
  `c_{i+ϑ} := fold(f^(i), r'_i, ..., r'_{i+ϑ-1})(v_{i+ϑ}, ..., v_{ℓ+R-1})`

The output `s'` is computed via `single_point_localized_fold_matrix_form` using:
- Fresh oracle queries to `f^(i)` (the fiber evaluations)
- The folding challenges from position `i` to `i+ϑ`
- The suffix of the challenge `v` starting at `i+ϑ`

The input `c_k` is only used for the guard check (validating consistency when `i > 0`),
but it does NOT affect the computation of the output value `s'`.
-/
lemma query_phase_step_preserves_fold
    {k : Fin (ℓ / ϑ)}
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (c_k : L) (s' : L) -- The next state (c_next)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), ()))
    (h_c_k_correct_of_k_pos :
      let := k_mul_ϑ_lt_ℓ (k := k)
      let := k_succ_mul_ϑ_le_ℓ (k := k)
      if _ : k.val > 0 then
        c_k = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := k.val * ϑ)
          (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
          (f := getFirstOracle 𝔽q β oStmtIn)
          (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges
            0 (by simp only [zero_add, Fin.val_last]; omega))
          (y := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
            (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega))
          (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
      else True)
    -- Hypothesis: s' is a valid output of the simulated step function
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    (h_s'_mem :
      let step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      let witIn : Unit := ()
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      s' ∈
      (OptionT.mk
        (simulateQ.{0, 0, 0} so
          ((checkSingleFoldingStep 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k c_k v stmtIn))).support)) :
    let := k_succ_mul_ϑ_le_ℓ (k := k)
    s' = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := (k.val + 1) * ϑ)
        (destIdx := ⟨(k.val + 1) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
        (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0
          (by simp only [zero_add, Fin.val_last]; omega))
        (y := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
          (destIdx := ⟨(k.val + 1) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega))
          (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add];) := by
  let step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  let witIn : Unit := ()
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let so := OracleInterface.simOracle2 []ₒ oStmtIn transcript.messages
  -- This is basically due to definition of s'
  -- First, convert h_s'_mem to equality form
  dsimp only [checkSingleFoldingStep] at h_s'_mem
  -- 2. Handle the conditional guard (k > 0 vs k = 0)
  --    In both cases, the core computation (query + fold) is the same.
  have h₁ := k_succ_mul_ϑ_le_ℓ (k := k)
  have h₂ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  have h_ϑ_pos : ϑ > 0 := Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (by exact hdiv.out)
  let destIdx : Fin r := ⟨(k.val + 1) * ϑ, by omega⟩
  let midIdx : Fin r := ⟨k.val * ϑ, by omega⟩
  by_cases h_k_pos : k.val > 0
  · -- Case k > 0: The guard is present.
    -- **Simplify the monadic structure**
    -- fiber_vec is the vector of fiber evaluations at domain Sˆ{k * ϑ} of (y ∈ Sˆ{(k+1) * ϑ})
    -- Goal s'= fold (f^0)(r_0, ..., r_{(k+1)*ϑ-1})(y)
    simp only
    have h_mul_ϑ_gt_0 : k.val * ϑ > 0 := by
      simp only [gt_iff_lt, CanonicallyOrderedAdd.mul_pos]; omega
    simp only [MessageIdx, Message, gt_iff_lt, h_mul_ϑ_gt_0, ↓reduceDIte, guard_eq, Fin.val_last,
      bind_pure_comp, ReduceClaim.support_mk, Set.mem_setOf_eq] at h_s'_mem
    erw [simulateQ_bind, support_bind] at h_s'_mem
    simp only [Set.mem_iUnion, exists_prop] at h_s'_mem
    rcases h_s'_mem with ⟨fiber_vec_Opt, h_fiber_vec_Opt_mem_support, h_s'_mem_support_guard⟩
    let k_fin_list : Fin (List.finRange (ℓ / ϑ)).length := ⟨k.val, by
      simp only [List.length_finRange, Fin.is_lt]⟩
    have h_k_fin_list_eq : k = ((List.finRange (ℓ / ϑ)).get k_fin_list) := by
      apply Fin.eq_of_val_eq; simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta,
        Fin.val_cast]; rfl
    have h_probFailure_queryFiberPoints_eq_zero := by
      apply probFailure_simulateQ_queryFiberPoints_eq_zero (γ_repetitions := γ_repetitions)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝔽q := 𝔽q) (β := β)
        (so := so) (k := k_fin_list) (v := v)
    have h_probOutput_none_queryFiberPoints_eq_zero :=
      OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero
        (hfail := h_probFailure_queryFiberPoints_eq_zero)
    have h_fiber_vec_Opt_mem_support_eq := exists_eq_some_of_mem_support_of_probOutput_none_eq_zero
      (x := fiber_vec_Opt) (hx := h_fiber_vec_Opt_mem_support) (hnone := by
      simpa [so, transcript, h_k_fin_list_eq] using h_probOutput_none_queryFiberPoints_eq_zero)
    rcases h_fiber_vec_Opt_mem_support_eq with ⟨fiber_vec, h_fiber_vec_Opt_mem_support_eq⟩
    rw [h_fiber_vec_Opt_mem_support_eq] at h_s'_mem_support_guard h_fiber_vec_Opt_mem_support
    -- h_s'_eq : s' = the evaluation at y of the folded function from fiber_vec
    -- simp only [OptionT.simulateQ_map] at h_s'_mem_support_guard
    have h_fiber_val := mem_support_queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oraclePositionIdx := k) v fiber_vec stmtIn
      oStmtIn () challenges (by simpa using h_fiber_vec_Opt_mem_support)
    erw [simulateQ_bind, support_bind] at h_s'_mem_support_guard
    simp only [Function.comp_apply, Set.mem_iUnion, exists_prop] at h_s'_mem_support_guard
    have h₁ : k.val * ϑ < ℓ := k_mul_ϑ_lt_ℓ (k := k)
    -- 1. Simplify failure probability to just the guard condition
    -- simp only [h_i_pos, ↓reduceIte, OptionT.simulateQ_map]
    have h_guard_pass : c_k = fiber_vec.get (extractMiddleFinMask 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v) (i := ⟨k.val * ϑ, by omega⟩) (steps := ϑ)) := by
      have h_mul_gt_0 : k.val * ϑ > 0 := by
        simp only [gt_iff_lt, CanonicallyOrderedAdd.mul_pos]
        omega
      have h_k_eq_fin_cast : k = Fin.cast (by simp only [List.length_finRange]) k_fin_list := by
        apply Fin.eq_of_val_eq; simp only [Fin.val_cast]; rfl
      -- 4. Apply the lemma
      have res := query_phase_consistency_guard_safe 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (k := k) (v := v) (c_k := c_k) (f_i_on_fiber := fiber_vec) (stmtIn := stmtIn)
        (oStmtIn := oStmtIn) (witIn := witIn) (h_relIn := h_relIn) (h_c_k_correct := by
        simp only at h_c_k_correct_of_k_pos
        simp only [gt_iff_lt, h_k_pos] at h_c_k_correct_of_k_pos
        exact h_c_k_correct_of_k_pos
      ) (h_k_pos := h_mul_gt_0) (γ_repetitions := γ_repetitions) (challenges := challenges)
        (h_fiber_mem := by simp only [witIn]; exact h_fiber_vec_Opt_mem_support)
      exact res
    simp only [h_guard_pass, ↓reduceIte] at h_s'_mem_support_guard
    erw [simulateQ_pure] at h_s'_mem_support_guard
    simp only [support_pure, Set.mem_singleton_iff, exists_eq_left, OptionT.simulateQ_pure,
      OptionT.support_OptionT_pure_run, Option.some.injEq] at h_s'_mem_support_guard
    -- Step 1: Use symmetry of h_s'_eq
    rw [h_s'_mem_support_guard]
    dsimp only [getChallengeSuffix] -- extractSuffixFromChallenge  arise here
    have h_destIdx_eq : destIdx.val = k.val * ϑ + ϑ := by
      dsimp only [destIdx]; rw [Nat.add_mul, Nat.one_mul]
  --  iterated_fold 𝔽q β 0 ((↑k + 1) * ϑ) ⋯ ⋯ (getFirstOracle 𝔽q β oStmtIn)
  --   (getFoldingChallenges (Fin.last ℓ) stmtIn.challenges 0 ⋯) (extractSuffixFromChallenge
    -- 𝔽q β v ⟨(↑k + 1) * ϑ, ⋯⟩ ⋯)
    set challenges_full := getFoldingChallenges (𝓡 := 𝓡) (r := r) (ϑ := (k.val + 1) * ϑ)
      (i := Fin.last ℓ) stmtIn.challenges (k := 0)
      (h := by simp only [zero_add, Fin.val_last, k_succ_mul_ϑ_le_ℓ]) with h_challenges_full_defs
    set challenges_mid := getFoldingChallenges (𝓡 := 𝓡) (r := r) (ϑ := k.val * ϑ)
      (i := Fin.last ℓ) stmtIn.challenges (k := 0)
      (h := by simp only [zero_add, Fin.val_last]; omega) with h_challenges_mid_defs
    set challenges_last : Fin ϑ → L := (fun j ↦ stmtIn.challenges ⟨↑k * ϑ + ↑j, by
      simp only [Fin.val_last]; omega⟩) with h_challenges_last_defs
    set y_left := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
      (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩) (h_destIdx_le := by omega) with hy_left_defs
    set y_right := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
      (destIdx := ⟨(k.val + 1) * ϑ, by omega⟩) (h_destIdx_le := by omega) with hy_right_defs
    -- -- Step 2: Transform the RHS
    -- Define f_mid directly from oStmtIn k, which is simpler and aligns with fiber_vec.get
    let k_oracle_idx : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
      ⟨k, by simp only [toOutCodewordsCount_last, Fin.is_lt]⟩
    -- Prove that oraclePositionToDomainIndex matches midIdx
    have h_domain_idx_eq : (oraclePositionToDomainIndex ℓ ϑ (i := Fin.last ℓ)
      (positionIdx := k_oracle_idx)).val = midIdx.val := by
      dsimp only [oraclePositionToDomainIndex, midIdx]
    have h_sDomain_midIdx_eq : sDomain 𝔽q β h_ℓ_add_R_rate midIdx = sDomain 𝔽q β h_ℓ_add_R_rate
      ⟨(oraclePositionToDomainIndex ℓ ϑ (i := Fin.last ℓ)
        (positionIdx := k_oracle_idx)).val, by omega⟩ := by
      apply sDomain_eq_of_eq; apply Fin.eq_of_val_eq; rw [h_domain_idx_eq]
    let f_mid : ↥(sDomain 𝔽q β h_ℓ_add_R_rate midIdx) → L :=
      fun x => oStmtIn k_oracle_idx (cast (by rw [h_sDomain_midIdx_eq]) x)
    set fiber_vec_actual_def := fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx) (steps := ϑ) (destIdx := ⟨k * ϑ + ϑ, by omega⟩) (h_destIdx := by
        simp only [Nat.add_right_cancel_iff]; rfl)
      (h_destIdx_le := by omega) (f := f_mid)
      (y := y_left) with h_fiber_vec_actual_def
    have h_fiber_vec_get : fiber_vec.get = fiber_vec_actual_def := by
      dsimp only [fiber_vec_actual_def]; unfold fiberEvaluations
      funext x
      conv_lhs =>
        rw [h_fiber_val x]; dsimp only [getFiberPoint]
        dsimp only [getChallengeSuffix]
      conv_rhs =>
        dsimp only [getFirstOracle]
      dsimp only [f_mid]
      apply OracleStatement.oracle_eval_congr 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (oStmtIn := oStmtIn) (j' := k_oracle_idx) (j := ⟨k, by
          simp only [toOutCodewordsCount_last, Fin.is_lt]⟩) (h_j := by rfl)
      rfl
    rw [h_fiber_vec_get]; dsimp only [fiber_vec_actual_def]
    have h_eq := single_point_localized_fold_matrix_form_eq_iterated_fold 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (steps := ϑ)
      (destIdx := ⟨k * ϑ + ϑ, by omega⟩) (h_destIdx := by simp only [Nat.add_right_cancel_iff]; rfl)
      (h_destIdx_le := by omega) (f := f_mid) (y := y_left) (r_challenges :=
        fun j => stmtIn.challenges ⟨k.val * ϑ + j.val, by simp only [Fin.val_last]; omega⟩)
    conv_lhs => rw [h_eq]
    dsimp only [f_mid]
    -- Now rw the oStmtIn k_oracle_idx into the iterated_fold of f⁽⁰⁾ form
    -- Extract t and strictOracleFoldingConsistencyProp from h_relIn
    dsimp only [strictFinalSumcheckRelOut, strictFinalSumcheckRelOutProp,
      strictfinalSumcheckStepFoldingStateProp] at h_relIn
    simp only [Fin.val_last, exists_and_right, Subtype.exists] at h_relIn
    rcases h_relIn with ⟨exists_t_MLP, _⟩
    rcases exists_t_MLP with ⟨t, h_t_mem_support, h_strictOracleFoldingConsistency⟩
    dsimp only [strictOracleFoldingConsistencyProp] at h_strictOracleFoldingConsistency
    -- Get the equality for k_oracle_idx: oStmtIn k_oracle_idx = iterated_fold from 0 to k.val * ϑ
    have h_f_mid_eq_iterated_fold := h_strictOracleFoldingConsistency k_oracle_idx
    conv_lhs => rw [h_f_mid_eq_iterated_fold]
    let P₀: L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
      (fun ω => t.eval (bitsOfIndex ω))
    let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
    conv_lhs => dsimp only [midIdx]
    conv_lhs => simp only [cast_eq, Fin.val_last]; rw [←fun_eta_expansion]
    conv_lhs =>
      rw [iterated_fold_transitivity 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := by
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.add_right_cancel_iff,
          mul_eq_mul_right_iff]; left; rfl
      )]
    dsimp only [k_oracle_idx]
    -- Step 1: Align steps (k * ϑ + ϑ = (k + 1) * ϑ)
    have h_steps_eq : k.val * ϑ + ϑ = (k.val + 1) * ϑ := by rw [Nat.add_mul, Nat.one_mul]
    conv_lhs =>
      rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
        (steps := k.val * ϑ + ϑ) (steps' := (k.val + 1) * ϑ)
        (h_destIdx := by
          simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]) (h_destIdx_le := by omega)
        (h_steps_eq_steps' := h_steps_eq)
        (f := f₀) (r_challenges := Fin.append challenges_mid challenges_last)
        (y := y_left)]
    -- Step 2: Align destIdx (⟨k * ϑ + ϑ, ...⟩ = ⟨(k + 1) * ϑ, ...⟩)
    conv_lhs =>
      rw [iterated_fold_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
        (steps := (k.val + 1) * ϑ)
        (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩) (destIdx' := ⟨(k.val + 1) * ϑ, by omega⟩)
        (h_destIdx := by
          simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
        (h_destIdx_le := by omega) (h_destIdx_eq_destIdx' := by apply Fin.eq_of_val_eq; omega)
        (f := f₀)]
    -- Step 3: Align function (f₀ = getFirstOracle)
    have h_f₀_eq_getFirstOracle : f₀ = getFirstOracle 𝔽q β oStmtIn := by
      exact polyToOracleFunc_eq_getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (t := ⟨t, h_t_mem_support⟩) (i := Fin.last ℓ)
        (challenges := stmtIn.challenges) (oStmt := oStmtIn)
        (h_consistency := h_strictOracleFoldingConsistency)
    conv_lhs => rw [h_f₀_eq_getFirstOracle]
    -- Step 4: Align challenges
    have h_challenges_eq : (fun (cIdx : Fin ((↑k + 1) * ϑ)) => Fin.append challenges_mid
      challenges_last ⟨cIdx.val, by omega⟩) = challenges_full := by
      funext j
      dsimp only [Fin.append, Fin.addCases, challenges_full, challenges_mid, challenges_last]
      -- dsimp only [chalLeft, chalRight]
      by_cases h : j.val < k.val * ϑ
      · -- Case 1: cId < k_steps, so it's from the first part
        simp only [h, ↓reduceDIte, Fin.castLT_mk]; rfl
      · -- Case 2: cId >= k_steps, so it's from the second part
        dsimp only [getFoldingChallenges]
        simp only [h, ↓reduceDIte, Fin.cast_mk, Fin.subNat_mk, Fin.natAdd_mk, Fin.val_last,
          eq_rec_constant]
        congr 1; simp only [Fin.val_last, zero_add, Fin.mk.injEq]; omega
    conv_lhs => rw [h_challenges_eq]
    have h_sDomain_eq : sDomain 𝔽q β h_ℓ_add_R_rate ⟨k.val * ϑ + ϑ, by omega⟩
      = sDomain 𝔽q β h_ℓ_add_R_rate ⟨(↑k + 1) * ϑ, by omega⟩ := by
      apply sDomain_eq_of_eq; apply Fin.eq_of_val_eq; simp only; omega
    -- Step 5: Align points
    have h_y_eq : cast (by rw [h_sDomain_eq]) y_left = y_right := by
      dsimp only [y_left, y_right]
      rw [←extractSuffixFromChallenge_congr_destIdx 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (h_idx_eq := by apply Fin.eq_of_val_eq; omega)]
    conv_lhs => rw [h_y_eq]
  · -- Case k = 0: No guard.
    ---------------------------------------------------------------------
    -- First establish that k = 0
    simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at h_k_pos
    have h_mul_eq_0 : ↑k * ϑ = 0 := by
      rw [h_k_pos]; simp only [zero_mul]
    have h_k_eq_0 : k.val = 0 := by
      by_contra h_ne
      have : k.val > 0 := Nat.pos_of_ne_zero h_ne
      have : k.val * ϑ > 0 := Nat.mul_pos this (Nat.pos_of_neZero ϑ)
      omega
    simp only [h_k_eq_0, zero_mul, zero_add] at h_s'_mem ⊢
    simp only [MessageIdx, Message, gt_iff_lt, lt_self_iff_false, ↓reduceDIte, Fin.mk_zero',
      Fin.val_last, bind_pure_comp, ReduceClaim.support_mk,
      Set.mem_setOf_eq] at h_s'_mem
    erw [simulateQ_bind, support_bind] at h_s'_mem
    simp only [Set.mem_iUnion, exists_prop] at h_s'_mem
    rcases h_s'_mem with ⟨fiber_vec_Opt, h_fiber_vec_Opt_mem_support, h_s'_mem_support_guard⟩
    let k_fin_list : Fin (List.finRange (ℓ / ϑ)).length := ⟨k.val, by
      simp only [List.length_finRange, Fin.is_lt]⟩
    have h_k_fin_list_eq : k = ((List.finRange (ℓ / ϑ)).get k_fin_list) := by
      apply Fin.eq_of_val_eq; simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta,
        Fin.val_cast]; rfl
    have h_probFailure_queryFiberPoints_eq_zero := by
      apply probFailure_simulateQ_queryFiberPoints_eq_zero (γ_repetitions := γ_repetitions)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝔽q := 𝔽q) (β := β)
        (so := so) (k := k_fin_list) (v := v)
    have h_probOutput_none_queryFiberPoints_eq_zero :=
      OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero
        (hfail := h_probFailure_queryFiberPoints_eq_zero)
    have h_exists_some_fiber_vec_of_fiber_vec_Opt :=
      exists_eq_some_of_mem_support_of_probOutput_none_eq_zero
      (x := fiber_vec_Opt) (hx := h_fiber_vec_Opt_mem_support) (hnone := by
      simpa [so, transcript, h_k_fin_list_eq] using h_probOutput_none_queryFiberPoints_eq_zero)
    rcases h_exists_some_fiber_vec_of_fiber_vec_Opt with ⟨fiber_vec, h_fiber_vec_Opt_eq_some⟩
    rw [h_fiber_vec_Opt_eq_some] at h_s'_mem_support_guard h_fiber_vec_Opt_mem_support
    -- **Simplify the monadic structure**
    simp only [LawfulApplicative.map_pure] at h_s'_mem_support_guard
    erw [simulateQ_pure] at h_s'_mem_support_guard
    simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at h_s'_mem_support_guard
    -- h_s'_mem_support_guard : s' = single_point_localized_fold_matrix_form
    have h_fiber_val := mem_support_queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oraclePositionIdx := k) v fiber_vec stmtIn
      oStmtIn () challenges (by simpa using h_fiber_vec_Opt_mem_support)
    -- Step 1: Use symmetry of h_s'_eq
    rw [h_s'_mem_support_guard]
    -- ⊢ single_point_localized_fold_matrix_form ... = iterated_fold ...
    have h_destIdx_eq : destIdx.val = ϑ := by
      dsimp only [destIdx]; rw [h_k_eq_0, zero_add, one_mul]
  --  iterated_fold 𝔽q β 0 ((↑k + 1) * ϑ) ⋯ ⋯ (getFirstOracle 𝔽q β oStmtIn)
  --   (getFoldingChallenges (Fin.last ℓ) stmtIn.challenges 0 ⋯)
        -- (extractSuffixFromChallenge 𝔽q β v ⟨(↑k + 1) * ϑ, ⋯⟩ ⋯)
    let challenges_full := getFoldingChallenges (𝓡 := 𝓡) (r := r) (ϑ := (k.val + 1) * ϑ)
      (i := Fin.last ℓ) stmtIn.challenges
      (k := 0) (h := by simp only [zero_add, Fin.val_last]; omega)
    set y := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
      (destIdx := ⟨(k.val + 1) * ϑ, by omega⟩) (h_destIdx_le := by omega) with hy_def
    -- Step 2: Transform the RHS
    let rhs_to_mat_mul_form := iterated_fold_eq_matrix_form 𝔽q β (i := 0)
      (steps := (k.val + 1) * ϑ) (destIdx := destIdx) (h_destIdx := by
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; rfl)
      (h_destIdx_le := by omega) (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := challenges_full)
    conv_rhs =>
      rw [rhs_to_mat_mul_form]
      dsimp only [localized_fold_matrix_form]
    -- Step 3: Unfold localized form
    conv_rhs => unfold localized_fold_matrix_form
  -- 1. Simplify the index arithmetic for k=0
    --    (k+1)*ϑ becomes ϑ
    -- simp? [Fin.mk_zero', Fin.val_last]
    -- 2. Unfold your helper definition
    --    This reveals that LHS suffix is exactly the RHS suffix
    dsimp only [getChallengeSuffix]
    set fiber_vec_actual_def := fiberEvaluations 𝔽q β (i := 0) (steps := ϑ) (destIdx := destIdx)
      (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      (h_destIdx_le := by omega) (f := getFirstOracle 𝔽q β oStmtIn) (y := y) with hright_def
    have h_fiber_vec_get : fiber_vec.get = fiber_vec_actual_def := by
      dsimp only [fiber_vec_actual_def]; unfold fiberEvaluations
      funext x
      conv_lhs =>
        rw [h_fiber_val x]; dsimp only [getFiberPoint]
        dsimp only [getChallengeSuffix]
      conv_rhs =>
        dsimp only [getFirstOracle]
      simp only [Fin.mk_zero']
      -- symm
      apply OracleStatement.oracle_eval_congr 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (oStmtIn := oStmtIn) (j' := 0) (j := ⟨k, by
          simp only [toOutCodewordsCount_last, Fin.is_lt]⟩) (h_j := by
          apply Fin.eq_of_val_eq
          simpa using h_k_eq_0)
      have h_destIdx_eq : (⟨k.val * ϑ + ϑ, by omega⟩ : Fin r) = ⟨(k.val + 1) * ϑ, by omega⟩ := by
        apply Fin.eq_of_val_eq
        simp only [Nat.add_mul, one_mul]
      simp only [id_eq, Fin.coe_ofNat_eq_mod, cast_cast]
      have h_i_eq : (⟨k.val * ϑ, by omega⟩ : Fin r) = 0 := by
        apply Fin.eq_of_val_eq
        simp [h_mul_eq_0]
      have hsrc_fun := qMap_total_fiber_congr_source_apply 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (steps := ϑ) (destIdx := destIdx) (sourceIdx₁ := (⟨k.val * ϑ, by omega⟩ : Fin r))
        (sourceIdx₂ := 0) (h_sourceIdx_eq := h_i_eq)
        (h_destIdx := by dsimp only [destIdx]; rw [Nat.add_mul, Nat.one_mul])
        (h_destIdx_le := by omega) (y := y) (x := x)
      rw [←hsrc_fun]
      have hdest_congr := qMap_total_fiber_congr_dest 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (sourceIdx := ⟨k * ϑ, by omega⟩) (steps := ϑ) (destIdx₁ := ⟨k.val * ϑ + ϑ, by omega⟩)
        (destIdx₂ := destIdx) (h_destIdx_congr := by omega) (h_destIdx := by dsimp only)
        (h_destIdx_le := by omega)
      rw [hdest_congr]
      congr 1
      rw [←extractSuffixFromChallenge_congr_destIdx 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (v := v) (destIdx := destIdx) (destIdx' := ⟨k.val * ϑ + ϑ, by omega⟩)
        (h_idx_eq := by omega) (h_le := by omega) (h_le' := by omega)]
    rw [h_fiber_vec_get]
    -- Step 4: Apply the congruence lemma of single_point_localized_fold_matrix_form
      -- 1. Establish that the step counts are equal
    have h_steps_eq : ϑ = (↑k + 1) * ϑ := by
      simp only [h_k_eq_0, zero_add, one_mul]
    -- 2. Apply the Step Congruence Lemma to the RHS
    --    We rewrite the RHS to use 'ϑ' instead of '(k+1)*ϑ'
    conv_rhs => rw [single_point_localized_fold_matrix_form_congr_steps_index 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps' := ϑ) (h_steps_eq_steps' := h_steps_eq.symm)]
    have h_challenges_eq :
      (fun (j : Fin ϑ) => stmtIn.challenges ⟨j.val, by simp only [Fin.val_last]; omega⟩)
      = fun (j : Fin ϑ) => challenges_full ⟨j.val, by omega⟩ := by
        funext j
        dsimp only [challenges_full, getFoldingChallenges]
        simp only [Fin.val_last, zero_add]
    conv_lhs => rw [h_challenges_eq]
    have h_sDomain_eq : (sDomain 𝔽q β h_ℓ_add_R_rate ⟨↑k * ϑ + ϑ, by omega⟩)
      = (sDomain 𝔽q β h_ℓ_add_R_rate ⟨(↑k + 1) * ϑ, by omega⟩) := by
      apply sDomain_eq_of_eq; simp only [Fin.mk.injEq]; omega
    conv_lhs =>
      rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
      dsimp only [destIdx]; simp only [Nat.add_mul, Nat.one_mul])]
    have h_y_eq : y = cast (by rw [h_sDomain_eq]) (extractSuffixFromChallenge 𝔽q β (v := v)
      (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩)
      (h_destIdx_le := by simp only [k_succ_mul_ϑ_le_ℓ_₂])) := by
      rw [hy_def]
      rw [extractSuffixFromChallenge_congr_destIdx]
      simp only [Nat.add_mul, Nat.one_mul]
    rw [←h_y_eq]
    dsimp only [fiber_vec_actual_def, fiberEvaluations]
    rw [qMap_total_fiber_congr_steps 𝔽q β (i := 0) (steps := ϑ) (steps' := (↑k + 1) * ϑ)
      (h_steps_eq := h_steps_eq) (y := y)]

/-! Lemma 3 (Completeness):
Proves that the fully folded value (result of `iterated_fold` at `ℓ`)
equals the `final_constant` expected by the statement.
-/
omit [SampleableType L] [DecidableEq 𝔽q] in
lemma query_phase_final_fold_eq_constant
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (c : L)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), witIn))
    -- Hypothesis: x is the result of folding all the way to ℓ
    (h_c_correct :
      have h_mul_eq : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
      c = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := (ℓ / ϑ) * ϑ)
        (destIdx := ⟨(ℓ / ϑ) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
        (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0
          (by simp only [zero_add, Fin.val_last]; omega))
        (y := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
          (destIdx := ⟨(ℓ / ϑ) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega))
        (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add];)
    ) :
    c = stmtIn.final_constant := by
  classical
  dsimp only [strictFinalSumcheckRelOut, strictFinalSumcheckRelOutProp,
    strictfinalSumcheckStepFoldingStateProp] at h_relIn
  simp only [Fin.val_last, exists_and_right, Subtype.exists] at h_relIn
  -- 2. Extract the existential witnesses
  rw [h_c_correct]
  rcases h_relIn with ⟨exists_t_MLP, h_final_oracle_fold_to_constant⟩
  simp only at h_final_oracle_fold_to_constant
  have h_final_oracle_fold_to_const_at_0 := congr_fun h_final_oracle_fold_to_constant 0
  simp only at h_final_oracle_fold_to_const_at_0
  rw [h_final_oracle_fold_to_const_at_0.symm]
  rcases exists_t_MLP with ⟨t, h_t_mem_support, h_strictOracleFoldingConsistency⟩
  dsimp only [strictOracleFoldingConsistencyProp] at h_strictOracleFoldingConsistency
  let lastOraclePositionIndex := getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
  have h_last_oracle_eq_t_evals_folded := h_strictOracleFoldingConsistency lastOraclePositionIndex
  have h_ϑ_pos : ϑ > 0 := Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
  have h_ℓ_div_mul_eq_ℓ : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  have h_lastOraclePosIdx_mul_add :
    (getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)).val * ϑ + ϑ = ℓ := by
    conv_rhs => rw [←h_ℓ_div_mul_eq_ℓ]
    rw [getLastOraclePositionIndex_last]; simp only
    rw [Nat.sub_mul, Nat.one_mul]; rw [Nat.sub_add_cancel (by rw [h_ℓ_div_mul_eq_ℓ]; omega)]
  have h_first_oracle_eq_t_evals_folded := h_strictOracleFoldingConsistency ⟨0, by
    simp only [toOutCodewordsCount_last, Nat.div_pos_iff]; omega⟩
  dsimp only [getFirstOracle]
  have h_getLastOracle_eq : oStmtIn lastOraclePositionIndex =
    getLastOracle (h_destIdx := by rfl) (oracleFrontierIdx := Fin.last ℓ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmtIn) := by rfl
  rw [←h_getLastOracle_eq]
  rw [h_last_oracle_eq_t_evals_folded, h_first_oracle_eq_t_evals_folded]
  simp only [Fin.mk_zero', Fin.coe_ofNat_eq_mod]
  have h_zero_mod : 0 % toOutCodewordsCount ℓ ϑ (Fin.last ℓ) * ϑ = 0 := by
    rw [toOutCodewordsCount_last];
    simp only [Nat.zero_mod, zero_mul]
  rw [iterated_fold_transitivity 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := by
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.add_right_cancel_iff,
    mul_eq_mul_right_iff];
    rw [getLastOraclePositionIndex_last];
    dsimp only [lastOraclePositionIndex]
    rw [getLastOraclePositionIndex_last];
    simp only [true_or]
  )]
  set chalLeft := (getFoldingChallenges (i := Fin.last ℓ) (𝓡 := 𝓡) (r := r)
    (challenges := stmtIn.challenges) (k := 0) (ϑ := ℓ/ϑ * ϑ) (by
    simp only [zero_add, Fin.val_last]; omega)) with h_chalLeft
  -- have h_concat_challenges_eq :
  set chalRight := Fin.append (getFoldingChallenges (i := Fin.last ℓ) (𝓡 := 𝓡) (r := r)
    (challenges := stmtIn.challenges) (k := 0) (ϑ := lastOraclePositionIndex.val * ϑ)
      (by simp only [zero_add, Fin.val_last, oracle_index_le_ℓ]))
      (fun (cId : Fin ϑ) ↦
        stmtIn.challenges ⟨(getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)) * ϑ + cId.val, by
          simp only [Fin.val_last, getLastOraclePositionIndex_last];
          simp only [lastBlockIdx_mul_ϑ_add_fin_lt_ℓ]⟩) with h_chalLeft
  have h_chalLeft_eq_chalRight_cast : chalLeft = fun cIdx : Fin (ℓ / ϑ * ϑ) => chalRight ⟨cIdx, by
    dsimp only [lastOraclePositionIndex]
    simp only [getLastOraclePositionIndex_last];
    rw [Nat.sub_mul, Nat.one_mul]; omega
  ⟩ := by
    funext cIdx
    dsimp only [chalLeft, chalRight]
    by_cases h : cIdx.val < lastOraclePositionIndex.val * ϑ
    · -- Case 1: cId < k_steps, so it's from the first part
      simp only [Fin.val_last]
      dsimp only [Fin.append, Fin.addCases]
      simp only [h, ↓reduceDIte, getFoldingChallenges, Fin.val_last, Fin.val_castLT, zero_add]
    · -- Case 2: cId >= k_steps, so it's from the second part
      simp only [Fin.val_last]
      dsimp only [Fin.append, Fin.addCases]
      simp only [h, ↓reduceDIte, Fin.cast_mk, Fin.subNat_mk, Fin.natAdd_mk, eq_rec_constant]
      dsimp only [getFoldingChallenges]
      congr 1
      simp only [Fin.val_last, zero_add, Fin.mk.injEq]
      rw [add_comm];
      dsimp only [lastOraclePositionIndex, lastOraclePositionIndex] at ⊢ h
      rw [Nat.sub_add_cancel]
      rw [getLastOraclePositionIndex_last] at ⊢ h
      simp only [Nat.sub_mul, one_mul, not_lt, tsub_le_iff_right] at ⊢ h
      exact h
  rw [h_chalLeft_eq_chalRight_cast]
  conv_lhs =>
    -- 1. Locate the specific sub-term corresponding to the folding function
    --    This finds the lambda "fun y ↦ ..."
    pattern (fun y ↦ iterated_fold _ _ _ _ _ _ _ _ _)
    enter [y]
    rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
    (steps := 0 % toOutCodewordsCount ℓ ϑ (Fin.last ℓ) * ϑ) (steps' := 0) (h_destIdx := by
      simp only [toOutCodewordsCount_last, Nat.zero_mod, zero_mul, Fin.coe_ofNat_eq_mod, add_zero])
      (h_destIdx_le := by simp only [toOutCodewordsCount_last, Nat.zero_mod, zero_mul, zero_le])
      (h_steps_eq_steps' := by omega)]
    rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (h_destIdx := by simp only [toOutCodewordsCount_last,
      Nat.zero_mod, zero_mul, Fin.coe_ofNat_eq_mod])]
  conv_lhs => simp only [cast_cast, cast_eq]; simp only [←fun_eta_expansion]
  conv_lhs =>
    rw [←iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
    (steps := ↑lastOraclePositionIndex * ϑ + ϑ) (steps' := (ℓ / ϑ * ϑ)) (h_destIdx := by
      dsimp only [lastOraclePositionIndex];
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
    (h_destIdx_le := by simp only; omega) (h_steps_eq_steps' := by
      dsimp only [lastOraclePositionIndex]; omega)]
  let P₀: L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
    (fun ω => t.eval (bitsOfIndex ω))
  let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
  set destIdx' : Fin r := ⟨(getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)).val + ϑ, by
    rw [getLastOracleDomainIndex]; simp only; omega⟩ with h_destIdx'
  let point := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
    (destIdx := ⟨ℓ / ϑ * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
  conv_lhs =>
    rw [iterated_fold_congr_dest_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (steps := ↑lastOraclePositionIndex * ϑ + ϑ) (destIdx := ⟨ℓ / ϑ * ϑ, by omega⟩)
      (destIdx' := destIdx') (h_destIdx := by
        dsimp only [lastOraclePositionIndex];
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      (h_destIdx_le := by simp only; omega) (h_destIdx_eq_destIdx' := by
        dsimp only [destIdx']; simp only [Fin.mk.injEq]; omega) (f := f₀)
      (r_challenges := chalRight) (y := point)]
  rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
    (steps := ↑lastOraclePositionIndex * ϑ + ϑ) (steps' := ℓ) (h_destIdx := by
      dsimp only [destIdx'];
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.add_right_cancel_iff,
      mul_eq_mul_right_iff]; omega)
    (h_destIdx_le := by dsimp only [destIdx']; simp only [oracle_index_add_steps_le_ℓ])
    (h_steps_eq_steps' := by omega)]
  rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
    (steps := ↑lastOraclePositionIndex * ϑ + ϑ) (steps' := ℓ) (h_destIdx := by
    dsimp only [destIdx'];
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add,
      Nat.add_right_cancel_iff, mul_eq_mul_right_iff]; omega)
    (h_destIdx_le := by dsimp only [destIdx']; simp only [oracle_index_add_steps_le_ℓ])
    (h_steps_eq_steps' := by omega)]
  have h_sDomain_eq : (sDomain 𝔽q β h_ℓ_add_R_rate ⟨ℓ/ϑ * ϑ, by omega⟩)
    = (sDomain 𝔽q β h_ℓ_add_R_rate destIdx') := by
    apply sDomain_eq_of_eq; dsimp only [destIdx']; simp only [Fin.mk.injEq]; omega
  let res := iterated_fold_to_level_ℓ_is_constant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (t := ⟨t, h_t_mem_support⟩) (destIdx := destIdx') (h_destIdx := by omega)
    (challenges := fun (cIdx : Fin ℓ) =>
      chalRight ⟨cIdx, by dsimp only [lastOraclePositionIndex]; omega⟩)
    (x := cast (by rw [h_sDomain_eq]) point) (y := 0)
  rw [res]

/-- Relation used in the forIn loop of `checkSingleRepetition`: at index 0 the folded value is 0;
  at index `oraclePositionIdx > 0` it equals `iterated_fold` up to that position with challenges
    from `stmtIn` and suffix from `v`. -/
@[reducible]
def checkSingleRepetition_foldRel
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    Fin ((List.finRange (ℓ / ϑ)).length + 1) → L → Prop :=
  let f₀ := getFirstOracle 𝔽q β oStmtIn
  fun oraclePositionIdx val_folded_point =>
    if hk : oraclePositionIdx.val = 0 then
      val_folded_point = 0  -- Base case: initial value is 0
    else
      have h_toCodewordCount : toOutCodewordsCount ℓ ϑ (Fin.last ℓ) = ℓ / ϑ :=
        toOutCodewordsCount_last ℓ ϑ
      have h_le : oraclePositionIdx ≤ ℓ/ϑ := by
        have h := oraclePositionIdx.isLt
        simp only [List.length_finRange] at h
        exact Nat.le_of_lt_succ h
      have h_mul : (ℓ/ϑ) * ϑ = ℓ := by rw [Nat.div_mul_cancel (hdiv.out)]
      have h_mul_le : oraclePositionIdx * ϑ ≤ ℓ := by
        conv_rhs => rw [←h_mul]
        apply Nat.mul_le_mul_right; exact h_le
      let destIdx : Fin r := ⟨oraclePositionIdx * ϑ, by omega⟩
      let suffix_point_from_v : sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
        extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v:=v) (destIdx:=destIdx) (h_destIdx_le:=by omega)
      val_folded_point = iterated_fold
        (i := 0) (steps := oraclePositionIdx * ϑ) (destIdx := destIdx) (h_destIdx := by
          simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; rfl)
        (h_destIdx_le := by
          rw [←h_mul]
          dsimp only [destIdx];
          apply Nat.mul_le_mul_right; exact h_le
        ) (f := f₀)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0
          (by simp only [zero_add, Fin.val_last]; omega)) (y := suffix_point_from_v)

/-- Safety of the simulated inner `forIn` loop used by
`checkSingleRepetition_probFailure_eq_zero`. -/
lemma checkSingleRepetition_inner_forIn_probFailure_eq_zero
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((stmtIn, oStmtIn), witIn))
    (rep : Fin γ_repetitions)
    (challenges : (pSpecQuery 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges) :
      let step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      let v := (FullTranscript.mk1 (challenges ⟨0, by rfl⟩)).challenges ⟨0, by rfl⟩ rep
      let f : Fin (ℓ / ϑ) → L → OracleComp []ₒ (Option (ForInStep L)) :=
        fun (a : Fin (ℓ / ϑ)) (b : L) ↦
          ((ForInStep.yield <$>
            (simulateQ.{0, 0, 0} so
                (checkSingleFoldingStep 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) a b v stmtIn
              ).run
            )) : OptionT (OracleComp []ₒ) (ForInStep L))
      let inner_forIn_block : OptionT (OracleComp []ₒ) L :=
        forIn (List.finRange (ℓ / ϑ)) (0 : L) f
      Pr[⊥ | inner_forIn_block] = 0 := by
  intro step transcript so v f inner_forIn_block
  dsimp only [inner_forIn_block]
  let Rel : Fin ((List.finRange (ℓ / ϑ)).length + 1) → L → Prop :=
    checkSingleRepetition_foldRel 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (v := v)
  -- For this proof, we define a trivial relation since the real invariant
  -- is complex and involves the correctness of folding operations
  -- a. Push liftComp inside the forIn loop (twice, for the two layers)
  --    Goal: simulateQ so (liftComp (liftComp (forIn ...)))
  --    Becomes: simulateQ so (forIn ... (fun x s => liftComp ...))
  -- **Applying indutive relation inference**
  apply probFailure_forIn_of_relations_simplified (rel := Rel) (h_start := by rfl) (h_step := by
    -- Inductive step: any INNER repetition never fails
    intro (k : Fin (List.finRange (ℓ / ϑ)).length) (c_k : L) h_rel_k_c
    -- simp only [List.get_eq_getElem, List.getElem_finRange] at *
    -- Simplify k.succ ≠ 0 (always true)
    have h_succ_ne_zero : k.succ ≠ 0 := Fin.succ_ne_zero k
    constructor
    · -- Part 1: checkSingleFoldingStep is safe (never fails)
      -- where the forInStep.yield has spec
      -- `OracleComp [OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ (ForInStep L)`
      -- [⊥|simulateQ so
      --     ((ForInStep.yield <$> checkSingleFoldingStep 𝔽q β
      --       ((List.finRange (ℓ / ϑ)).get k) c_k v stmtIn).liftComp
      --       ([]ₒ ++ₒ
      --         ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ ++ₒ
      --           [fun i ↦ ![Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)] ↑i]ₒ)))] =
      -- 0
      dsimp only [f]
      -- rw [simulateQ_liftComp]
      rw [map_eq_bind_pure_comp]
      erw [probFailure_map] -- Pr[⊥ | f <$> mx] = Pr[⊥ | mx] **IMPORTANT**
      -- ⊢ Pr[⊥ | simulateQ so (checkSingleFoldingStep 𝔽q β γ_repetitions
      --   ((List.finRange (ℓ / ϑ)).get k) c_k v stmtIn).run] = 0
      dsimp only [checkSingleFoldingStep]
      erw [simulateQ_bind]
      erw [OptionT.probFailure_mk_do_bind_eq_zero_iff.{0, 0}]
      have h_probFailure_queryFiberPoints_eq_zero : Pr[⊥ |
        OptionT.mk
          (simulateQ so
            (queryFiberPoints 𝔽q β γ_repetitions ((List.finRange (ℓ / ϑ)).get k) v))] = 0 := by
        apply probFailure_simulateQ_queryFiberPoints_eq_zero
          (γ_repetitions := γ_repetitions) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝔽q := 𝔽q) (β := β)
          (so := so) (k := k) (v := v)
      have h_probOutput_none_queryFiberPoints_eq_zero :=
        OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero
          (hfail := h_probFailure_queryFiberPoints_eq_zero)
      constructor
      · -- queryFiberPoints never fails (oracle queries)
        simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta,
          HasEvalPMF.probFailure_eq_zero]
      · -- The guard and pure computation
        intro fiber_vec_opt h_fiber_vec_opt_mem_support
        have h_fiber_vec_eq_some :=
          exists_eq_some_of_mem_support_of_probOutput_none_eq_zero.{0, 0} (x := fiber_vec_opt)
            (hx := h_fiber_vec_opt_mem_support)
            (hnone := h_probOutput_none_queryFiberPoints_eq_zero)
        rcases h_fiber_vec_eq_some with ⟨fiber_vec, rfl⟩
        simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast,
          gt_iff_lt, CanonicallyOrderedAdd.mul_pos, Message, guard_eq, Fin.val_last, bind_pure_comp,
          dite_eq_ite]
        have h_ϑ_pos : ϑ > 0 := by exact Nat.pos_of_neZero ϑ
        simp only [h_ϑ_pos, and_true]
        by_cases h_i_pos : k.val > 0
        · -- Case k > 0: guard (c_k = f_i_val)
          let k_idx : Fin (ℓ / ϑ) := ⟨k.val, by
            have h := k.isLt
            simp only [List.length_finRange] at h
            exact h⟩
          have h₁ : k.val * ϑ < ℓ := k_mul_ϑ_lt_ℓ (k := k_idx)
          have h_k_idx_eq : k_idx = (List.finRange (ℓ / ϑ)).get k := by
            simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta]
            apply Fin.eq_of_val_eq
            simp only [Fin.val_cast]; rfl
          -- 1. Simplify failure probability to just the guard condition
          simp only [h_i_pos, ↓reduceIte, OptionT.simulateQ_map]
          have h_guard_pass :
              c_k = fiber_vec.get
                (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  (v := v) (i := ⟨k.val * ϑ, by omega⟩) (steps := ϑ)) := by
            -- ⊢ c_k = f_i_on_fiber.get (extractMiddleFinMask ...)
            -- 1. Construct the correct index type for the lemma
            -- 3. Unfold Rel to get the equality
            unfold Rel checkSingleRepetition_foldRel at h_rel_k_c
            have h_k_castSucc_ne_0 : ¬(k.castSucc.val = 0) := by
              simp only [Fin.val_castSucc]; omega
            rw [dif_neg h_k_castSucc_ne_0] at h_rel_k_c
            simp only [Fin.val_castSucc] at h_rel_k_c
            -- simp only [Fin.isValue, List.get_eq_getElem, List.getElem_finRange, Fin.eta,
            --   Fin.val_cast]
            have h_mul_gt_0 : k.val * ϑ > 0 := by
              simp only [gt_iff_lt, CanonicallyOrderedAdd.mul_pos]
              omega
            -- 4. Apply the lemma
            have res := query_phase_consistency_guard_safe 𝔽q β
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k_idx) (v := v) (c_k := c_k)
              (f_i_on_fiber := fiber_vec) (stmtIn := stmtIn) (oStmtIn := oStmtIn)
              (witIn := witIn) (h_relIn := h_relIn) (h_c_k_correct := h_rel_k_c)
              (h_k_pos := h_mul_gt_0) (γ_repetitions := γ_repetitions)
              (challenges := challenges) (h_fiber_mem := by
              rw [h_k_idx_eq]
              exact h_fiber_vec_opt_mem_support
            )
            exact res
          simp only [h_guard_pass, ↓reduceIte, OptionT.run_pure, simulateQ_pure]
          erw [probFailure_pure]
        · -- Case k = 0: no guard
          simp only [h_i_pos, ↓reduceIte]
          erw [simulateQ_pure, probFailure_pure]
    · -- Part 2: Results in support satisfy the next relation
      intro s' h_s'_support
      simp only [checkSingleRepetition_foldRel, dite_eq_ite, Fin.val_succ, Rel]
      simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta, support_map,
        Set.mem_image, OptionT.mem_support_iff, toPFunctor_emptySpec, OptionT.support_run,
        f] at h_s'_support
      -- Extract the actual value from ForInStep.yield
      rcases h_s'_support with ⟨x, h_x_support, h_s'_eq⟩
      rw [←h_s'_eq]
      dsimp only [ForInStep.state]
      -- Handle the index casting issue
      let k_idx : Fin (ℓ / ϑ) := ⟨k.val, by
        have h := k.isLt
        simp only [List.length_finRange] at h
        exact h
      ⟩
      -- Apply the preservation lemma
      let res := query_phase_step_preserves_fold 𝔽q β (γ_repetitions := γ_repetitions)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k_idx) (v := v) (c_k := c_k)
        (s' := x) (stmtIn := stmtIn) (oStmtIn := oStmtIn) (h_relIn := h_relIn)
        (challenges := challenges) (h_s'_mem := by
        dsimp only [so] at h_x_support
        dsimp only [pSpecQuery]
        exact h_x_support
      ) (h_c_k_correct_of_k_pos := by
        dsimp only [k_idx]
        dsimp only [Rel, checkSingleRepetition_foldRel] at h_rel_k_c
        simp only [Fin.val_castSucc, dite_eq_ite] at h_rel_k_c
        by_cases hk : k.val > 0
        · simp only [gt_iff_lt, hk, ↓reduceDIte]
          have h_ne_k_pos : ¬ (k.val = 0) := by omega
          simp only [h_ne_k_pos, ↓reduceIte] at h_rel_k_c
          exact h_rel_k_c
        · simp only [gt_iff_lt, hk, ↓reduceDIte]
      )
      exact res
  )

/--
Safety and Correctness of `checkSingleRepetition` under Honest Simulation.

This lemma proves that for any repetition `rep`, the check:
1. Never fails (safety).
2. Only returns if the accumulated value equals `final_constant`.
-/
lemma checkSingleRepetition_probFailure_eq_zero
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), witIn))
    (rep : Fin γ_repetitions)
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges) :
      let step := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      let v := (FullTranscript.mk1 (challenges ⟨0, by rfl⟩)).challenges ⟨0, by rfl⟩ rep
      Pr[⊥ | OptionT.mk.{0, 0} (simulateQ.{0, 0, 0} so
        (checkSingleRepetition 𝔽q β (γ_repetitions := γ_repetitions) (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v stmtIn stmtIn.final_constant).run)] = 0 := by
  intro step transcript so v
  let f₀ := getFirstOracle 𝔽q β oStmtIn
  let Rel : Fin ((List.finRange (ℓ / ϑ)).length + 1) → L → Prop :=
    checkSingleRepetition_foldRel 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (v := v)
  -- 1. Expand definition to expose the `forIn` and `guard`
  dsimp only [checkSingleRepetition]
  -- 2. Distribute simulateQ and liftM over the Bind (>>=)
  --    This splits `simulateQ (Loop >>= Guard)` into `simulateQ Loop >>= simulateQ Guard`
  simp only [bind_pure_comp]
  simp only [Fin.eta]
  -- erw [liftComp_bind]
  erw [simulateQ_bind]
  dsimp only [Function.comp_def]
  -- dsimp only [liftComp]
  simp only [OptionT.simulateQ_forIn.{0}] -- **universe 0 is important** here
  dsimp only [OptionT.mk]
  erw [OptionT.probFailure_mk_do_bind_eq_zero_iff.{0, 0}]
  dsimp only [OptionT.mk]
  -- rw [OptionT.liftComp_forIn]
  conv =>
    enter [1];
    simp only [MessageIdx, List.forIn_yield_eq_foldlM, id_map', List.foldlM_range, bind_pure_comp,
      HasEvalPMF.probFailure_eq_zero, zero_add, probOutput_eq_zero_iff', finSupport_map,
      Finset.mem_image, reduceCtorEq, and_false, exists_const, not_false_eq_true]
  rw [true_and]
  intro c h_c_support_inner_loop
  -- **if the inner for loop is passed, then the guard must be passed (given relIn)**
  simp only [MessageIdx, Message, LawfulApplicative.map_pure, bind_pure_comp,
    OptionT.simulateQ_map] at h_c_support_inner_loop
  set f : Fin (ℓ / ϑ) → L → OracleComp []ₒ (Option (ForInStep L)) :=
    fun (a :  Fin (ℓ / ϑ)) (b : L) ↦
    ((ForInStep.yield <$>
      (simulateQ.{0, 0, 0} so
        (checkSingleFoldingStep 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) a b v stmtIn
        ).run
      )) : OptionT (OracleComp []ₒ) (ForInStep L)) with h_f_def
  set inner_forIn_block := ((forIn (List.finRange (ℓ / ϑ)) (0 : L) f) :
    OptionT (OracleComp []ₒ) L) with h_inner_forIn_block
  have h_probFailure_loop_eq_zero : Pr[⊥ | inner_forIn_block] = 0 := by
    exact checkSingleRepetition_inner_forIn_probFailure_eq_zero 𝔽q β
      (γ_repetitions := γ_repetitions) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (rep := rep) (challenges := challenges)
  have h_probOutput_inner_forIn_block_eq_none :=
        OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero
          (hfail := h_probFailure_loop_eq_zero)
  have h_c_eq_some := exists_eq_some_of_mem_support_of_probOutput_none_eq_zero.{0, 0} (x := c)
      (hx := h_c_support_inner_loop) (hnone := h_probOutput_inner_forIn_block_eq_none)
  rcases h_c_eq_some with ⟨c_val, rfl⟩
  -- h_c_support_inner_loop : c ∈ forIn (List.finRange (ℓ / ϑ)) 0 f .support
  -- ⊢ x = stmtIn.final_constant
  -- We reuse the SAME relation `Rel` and the SAME logic we used for safety!
  have h_c_eq_final_constant : c_val = stmtIn.final_constant := by
    apply query_phase_final_fold_eq_constant 𝔽q β (v := v) (c := c_val)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (witIn := witIn)
      (h_relIn := h_relIn) (h_c_correct := by
        -- 1. Apply the helper lemma to transport the invariant to the end
      -- h_x_support : x ∈
      --   (forIn (List.finRange (ℓ / ϑ)) 0 fun a b ↦
      --       simulateQ (QueryImpl.lift so) (checkSingleFoldingStep 𝔽q β a b v stmtIn)
        -- >>= pure ∘ ForInStep.yield).support
      have h_rel_final : Rel ⟨ℓ/ϑ, by simp only [List.length_finRange,
        lt_add_iff_pos_right, zero_lt_one]⟩ c_val := by
        -- unfold OptionT at h_c_support_inner_loop
        -- Apply the yield-only helper
        let relation_correct_of_mem_support := support_forIn_subset_rel_yield_only.{0}
          (m := OptionT (OracleComp []ₒ)) (l := List.finRange (ℓ/ϑ)) (rel := Rel) (f := f)
          (init := 0) (h_start := by rfl) (h_step := by
          -- simp only [←simulateQ_liftComp]
          intro (k : Fin (List.finRange (ℓ / ϑ)).length) (c_k : L) h_rel_k_c iteration_output
            h_iteration_output_iteration
          -- 1. Unpack support (extract c_next)
          -- 1. Distribute simulateQ over >>= and pure
          --    This transforms: simulateQ (action >>= pure) -> (simulateQ action) >>= pure
          simp only [MessageIdx,  List.get_eq_getElem, List.getElem_finRange,
            Fin.eta, support_map, Set.mem_image, OptionT.mem_support_iff, toPFunctor_emptySpec,
            OptionT.support_run, f] at h_iteration_output_iteration
          -- 2. Now the hypothesis is exactly: ∃ c_next, c_next ∈ support ∧ output = yield c_next
          --    Extract it just like before!
          rcases h_iteration_output_iteration with ⟨c_next, h_c_next_mem, h_iteration_output_eq⟩
          rw [←h_iteration_output_eq]
          dsimp only [OptionT.run] at h_c_next_mem
          -- simp only [h_iteration_output_eq]
          constructor
          · rfl
          · -- Construct index (Same logic as Part 2)
            let k_idx : Fin (ℓ / ϑ) :=
              ⟨k.val, by
                have h_k_lt := k.isLt
                simp only [List.length_finRange] at h_k_lt
                exact h_k_lt⟩
            -- Apply preservation lemma (Exact same syntax as Part 2)
            let res := query_phase_step_preserves_fold 𝔽q β (γ_repetitions := γ_repetitions)
              (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k_idx) (v := v) (c_k := c_k)
              (s' := c_next) (stmtIn := stmtIn) (oStmtIn := oStmtIn) (h_relIn := h_relIn)
              (challenges := challenges) (h_s'_mem := h_c_next_mem)
              (h_c_k_correct_of_k_pos := by
                dsimp only [k_idx]
                dsimp only [Rel, checkSingleRepetition_foldRel] at h_rel_k_c
                simp only [Fin.val_castSucc, dite_eq_ite] at h_rel_k_c
                by_cases hk : k.val > 0
                · simp only [gt_iff_lt, hk, ↓reduceDIte]
                  have h_ne_k_pos : ¬ (k.val = 0) := by omega
                  simp only [h_ne_k_pos, ↓reduceIte] at h_rel_k_c
                  exact h_rel_k_c
                · simp only [gt_iff_lt, hk, ↓reduceDIte]
              )
            exact res
        )
        let res := relation_correct_of_mem_support c_val h_c_support_inner_loop
        simp only [List.length_finRange] at res
        exact res
      -- 2. Unpack the relation at the final index (ℓ/ϑ)
      unfold Rel at h_rel_final
      -- Prove that the final index is not 0
      have h_nonzero : (⟨ℓ/ϑ, by simp only [List.length_finRange,
        lt_add_iff_pos_right, zero_lt_one]⟩ :
          Fin (List.length (List.finRange (ℓ / ϑ)) + 1)) ≠ 0 := by
        simp only [ne_eq, Fin.mk_eq_zero, Nat.div_eq_zero_iff, not_or, not_lt]
        constructor
        · have h := Nat.pos_of_neZero (ϑ); omega
        · exact Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out
      -- Resolve the "if" statement to the "else" branch
      -- unfold Rel at h_rel_final
      dsimp only [checkSingleRepetition_foldRel] at h_rel_final
      simp only [ne_eq, Fin.mk_eq_zero] at h_nonzero
      rw [dif_neg h_nonzero] at h_rel_final
      -- Matches the goal exactly
      exact h_rel_final
    )
  rw [h_c_eq_final_constant]
  simp only [MessageIdx, guard_eq, ↓reduceIte]
  erw [simulateQ_pure.{0, 0, 0}]
  erw [probFailure_pure.{0, 0}]

/-- Pair-support projection wrapper of `support_simulateQ_run'_eq`.
`Prod.fst` of the stateful run support matches the spec support. -/
lemma support_run_simulateQ_run_fst_eq {ι : Type}
    {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited] {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec (Option α)) (s : σ)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    Prod.fst <$> support (m := ProbComp) (α := Option α × σ) ((simulateQ impl oa) s) =
      support (m := OracleComp oSpec) (α := Option α) oa := by
  simpa [StateT.run'_eq, support_map] using
    (support_simulateQ_run'_eq (impl := impl) (oa := oa) (s := s)
      (hImplSupp := hImplSupp))
/-! **Per-repetition support → logical** (extracted for reuse from completeness-style reasoning).
**Counterpart** of `checkSingleRepetition_probFailure_eq_zero` for the `OracleComp.support` case.
If `(ForInStep.yield PUnit.unit, state_post)` lies in the support of one iteration of the
  verifier's forIn body (for a given `rep`), then the logical proximity check holds for that
  repetition: `logical_checkSingleRepetition 𝔽q β oStmtIn (tr.challenges ⟨0, rfl⟩ rep) stmtIn
    stmtIn.final_constant`.
-/
omit [CharP L 2] [SampleableType L] in
lemma logical_checkSingleRepetition_of_mem_support_forIn_body {σ : Type}
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (tr : FullTranscript (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (stmtIn : FinalSumcheckStatementOut)
    (rep : Fin γ_repetitions)
    (state_pre : σ)
    (forIn_body : Fin γ_repetitions → PUnit → StateT σ ProbComp (Option (ForInStep PUnit)))
    (h_forIn_body_eq : forIn_body =
      fun (a : Fin γ_repetitions) (_ : PUnit.{1}) =>
      OptionT.mk (simulateQ impl ((((fun (_ : Unit) ↦ ForInStep.yield PUnit.unit) <$>
          ((simulateQ.{0, 0, 0} (impl := OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
            ((checkSingleRepetition 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              ((FullTranscript.mk1 (tr.challenges ⟨0, rfl⟩)).challenges ⟨0, rfl⟩ a)
              stmtIn stmtIn.final_constant) :
                OptionT (OracleComp
                  ([]ₒ + ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ +
                    [(pSpecQuery 𝔽q β γ_repetitions).Message]ₒ))) Unit).run) :
            OracleComp []ₒ (Option Unit))) :
          OptionT (OracleComp []ₒ) (ForInStep PUnit.{1})))))
    (h_mem : ∃ (res : ForInStep PUnit.{1} × σ), (some res.1, res.2) ∈
      ((forIn_body rep PUnit.unit).run state_pre).support) :
    logical_checkSingleRepetition 𝔽q β oStmtIn (tr.challenges ⟨0, rfl⟩ rep) stmtIn
      stmtIn.final_constant := by
  -- 1. Extract the witness res = (control_flow, state_post)
  rcases h_mem with ⟨⟨res_flow, state_post_single_outer_repetition⟩, h_support⟩
  -- 2. Unfold the body definition
  rw [h_forIn_body_eq] at h_support
  set v := tr.challenges ⟨0, rfl⟩ rep with h_v
  let Rel := checkSingleRepetition_foldRel 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (stmtIn := stmtIn) (oStmtIn := oStmtIn) (v := v)
  dsimp only [logical_checkSingleRepetition]
  conv at h_support =>
    -- 1. Expand definition to expose the `forIn` and `guard`
    dsimp only [checkSingleRepetition]
    -- 2. Distribute simulateQ and liftM over the Bind (>>=)
    --    This splits `simulateQ (Loop >>= Guard)` into `simulateQ Loop >>= simulateQ Guard`
    dsimp only [liftM, monadLift, MonadLift.monadLift]
    erw [simulateQ_bind, simulateQ_bind, simulateQ_bind]
    erw [support_bind]
    dsimp only [Function.comp_def]
    simp only [Fin.isValue, id_map',
      guard_eq, map_bind, simulateQ_bind, simulateQ_liftComp, StateT.run_bind, Function.comp_apply,
      simulateQ_map, simulateQ_ite, simulateQ_pure, OptionT.simulateQ_failure,
      StateT.run_map, support_bind,
      support_map, Set.mem_iUnion, Set.mem_image, Prod.mk.injEq, Prod.exists, exists_eq_right_right,
      exists_and_right, exists_and_left, exists_prop]
    erw [support_bind]
    simp only [Fin.isValue, id_map',
      guard_eq, map_bind, simulateQ_bind, simulateQ_liftComp, StateT.run_bind, Function.comp_apply,
      simulateQ_map, simulateQ_ite, simulateQ_pure, OptionT.simulateQ_failure,
      StateT.run_map, support_bind,
      support_map, Set.mem_iUnion, Set.mem_image, Prod.mk.injEq, Prod.exists, exists_eq_right_right,
      exists_and_right, exists_and_left, exists_prop]
  obtain ⟨output_final_guard, output_state_final_guard, exists_c_last,
    h_final_yield_support_mem⟩ := h_support
  -- c_last is the yielded folded value from the last inner iteration (i.e. γ_repetitions-1)
  rcases exists_c_last with ⟨c_last, output_state_inner_forIn, ⟨h_mem_forIn_support,
    h_mem_final_guard_support⟩⟩
  conv at h_mem_forIn_support =>
    simp only [Function.comp_def, simulateQ_pure, pure_bind]
    rw [OptionT.simulateQ_forIn]
    rw [OptionT.simulateQ_forIn_stateful_comp]
  -- Bridge to the `OptionT` path lemma: extract a successful `c_last` from support.
  obtain ⟨c_last_val, h_c_last_eq_some⟩ : ∃ c_last_val : L, c_last = some c_last_val := by
    cases h_c : c_last with
    | none =>
      exfalso
      simp only [MessageIdx, h_c, Message, simulateQ_pure] at h_mem_final_guard_support
      erw [support_pure] at h_mem_final_guard_support
      simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h_mem_final_guard_support
      obtain ⟨h_guard_none, _⟩ := h_mem_final_guard_support
      have h_final_mem := h_final_yield_support_mem
      simp only [h_guard_none, simulateQ_pure] at h_final_mem
      erw [support_pure] at h_final_mem
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at h_final_mem
    | some a =>
      exact ⟨a, rfl⟩
  have h_mem_forIn_support_some := by
    simpa [h_c_last_eq_some] using h_mem_forIn_support
  have h_ϑ_pos : ϑ > 0 := by exact Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
  have h_ℓ_div_ϑ_ge_1 : ℓ/ϑ ≥ 1 := by exact (Nat.one_le_div_iff h_ϑ_pos).mpr h_ϑ_le_ℓ
  have h_0_lt : 0 < (ℓ / ϑ) := by omega
  have h_ℓ_div_mul_eq_ℓ : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  have h_lastOraclePosIdx_mul_add :
    (getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)).val * ϑ + ϑ = ℓ := by
    conv_rhs => rw [←h_ℓ_div_mul_eq_ℓ]
    rw [getLastOraclePositionIndex_last]; simp only
    rw [Nat.sub_mul, Nat.one_mul]; rw [Nat.sub_add_cancel (by rw [h_ℓ_div_mul_eq_ℓ]; omega)]
  -- **Applying indutive relation inference** for the inner `forIn` only
  let Rel' := fun (i : Fin ((List.finRange (ℓ / ϑ)).length + 1)) (c_next : Option L) (_s : σ) =>
    -- state i => at the end of the inner repetition `i-1`
    -- which means at `i = 0`, value = True since nothing meaningful to check
    logical_stepCondition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmtIn)
      (k := ⟨i - 1, by
        have hi := i.isLt;
        simp only [List.length_finRange] at hi; omega
      ⟩) (v := v) (stmt := stmtIn) (final_constant := stmtIn.final_constant)
    ∧ (
      if hi : i > 0 then
        have hi_lt := i.isLt;
        have hi_lt₂ : i - 1 < ℓ / ϑ := by
          simp only [List.length_finRange] at hi_lt; omega
        let k : Fin (ℓ / ϑ) := ⟨i - 1, by omega⟩
        -- **NOTE**: At the end of repetition `k = i-1`, the value c_next which is
          -- the evaluation on `S^{(k+1)*ϑ}` of the folded oracle function must be computed
        -- let point := getChallengeSuffix 𝔽q β (List.finRange (ℓ / ϑ))[↑k] v; fiber_vec.get
        let point := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v) (k := k)
        let fiber_vec : Fin (2 ^ ϑ) → L := logical_queryFiberPoints 𝔽q β oStmtIn k v
        let output_of_iteration_k : L :=
          (single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨k.val * ϑ, by
            exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h := k_mul_ϑ_lt_ℓ (k := k))
          ⟩) (steps := ϑ) (destIdx := ⟨k.val * ϑ + ϑ, by
            apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            exact k_succ_mul_ϑ_le_ℓ_₂ (k := k)
          ⟩) (h_destIdx := by
            simp only [Nat.add_right_cancel_iff])
          (h_destIdx_le := k_succ_mul_ϑ_le_ℓ_₂ (k := k))
          (r_challenges := fun j ↦ stmtIn.challenges ⟨↑k * ϑ + ↑j, by
            simp only [Fin.val_last]
            have h_le : k.val * ϑ + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
            omega
          ⟩)
          (y := point) (fiber_eval_mapping := fiber_vec))
        some output_of_iteration_k = c_next
      else True)
  have h_ϑ_pos : ϑ > 0 := Nat.pos_of_neZero ϑ
  -- inductive relation inference for the intermediate folding steps
  have h_inductive_relations := _root_.OptionT.exists_rel_path_of_mem_support_forIn_stateful.{0}
    (spec := []ₒ) (l := List.finRange (ℓ / ϑ)) (init := 0) (σ := σ)
    (s := state_pre) (res := (c_last_val, output_state_inner_forIn))
    (h_mem := h_mem_forIn_support_some) (rel := Rel') (h_start := by
      simp only [logical_stepCondition, logical_checkSingleFoldingStep, gt_iff_lt,
        CanonicallyOrderedAdd.mul_pos, tsub_pos_iff_lt, dite_else_true, Fin.val_last,
        Fin.coe_ofNat_eq_mod, List.length_finRange, Nat.zero_mod, zero_tsub, h_0_lt, ↓reduceDIte,
        not_lt_zero', false_and, zero_mul, Fin.mk_zero', IsEmpty.forall_iff, lt_self_iff_false,
        zero_add, and_self, Rel'];
    )
    (h_step := by
      intro k (c_cur : L) (s_curr : σ) h_rel_k res_step h_res_step_mem
      -- c_cur is the yielded folded value from the previous inner iteration (i.e. k-1)
      have h_k := k.isLt
      simp only [List.length_finRange] at h_k
      have h_k_succ_sub_1_lt : k.succ.val - 1 < ℓ / ϑ := by
        simp only [Fin.val_succ, add_tsub_cancel_right]; omega
      have h_k_sub_1_lt : k.val - 1 < ℓ / ϑ := by
        omega
      have h_k_succ_gt_0 : k.succ > 0 := by simp only [gt_iff_lt, Fin.succ_pos]
      dsimp only [Rel', logical_stepCondition] at h_rel_k
      simp only [Fin.val_castSucc, h_k_sub_1_lt, ↓reduceDIte] at h_rel_k
      -- **Nested simulateQ structure** (do not simp the outer impl):
      -- • Outer: `simulateQ impl (...)` comes from RoundByRound's toFun_full: the reduction runs
      --   the verifier with a stateful oracle impl (black box). We do NOT unfold impl; we only
      --   use that its support equals the spec (support_simulateQ_run'_eq).
      -- • Inner: `simulateQ (simOracle2 []ₒ oStmtIn tr.messages) (...)` comes
      --   from OracleVerifier.toVerifier (Basic.lean): verifier checks are run with
      --   simOracle2 so oStmtIn and transcript answer the oracle queries. This inner layer
      --   can be simplified further (unfold checkSingleFoldingStep, use simOracle2 lemmas).
      set inner_base : OracleComp []ₒ (Option L) :=
        simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
          (checkSingleFoldingStep 𝔽q β γ_repetitions ((List.finRange (ℓ / ϑ)).get k)
            c_cur v stmtIn).run
      set inner_oa : OptionT (OracleComp []ₒ) (ForInStep L) :=
        ForInStep.yield <$> (OptionT.mk inner_base)
      have h_run'_supp_eq := OptionT.support_run_simulateQ_run'_eq (impl := impl)
        (oa := inner_oa)
        (s := s_curr)
        (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
      -- res_step ∈ (run s).support → res_step.1 ∈ (run' s).support = inner_oa.support
      have h_fst_mem :
          some res_step.1 ∈ ((simulateQ impl
            inner_oa).run' s_curr).support := by
        have h_run_mem :
            (some res_step.1, res_step.2) ∈
              ((simulateQ impl inner_oa).run s_curr).support := by
          simpa [inner_oa, inner_base, h_v] using h_res_step_mem
        simp only [StateT.run', support_map, Set.mem_image]
        exact ⟨(some res_step.1, res_step.2), h_run_mem, rfl⟩
      rw [h_run'_supp_eq] at h_fst_mem
      have h_fst_mem_opt : res_step.1 ∈ support (inner_oa) := by
        exact (OptionT.mem_support_iff (mx := inner_oa) (x := res_step.1)).2 h_fst_mem
      have h_inner_step_mem :
          ∃ c_next,
            (some c_next) ∈ support inner_base ∧ ForInStep.yield c_next = res_step.1 := by
        rcases (OptionT.mem_support_OptionT_map_some
            (ma := OptionT.mk inner_base) (f := ForInStep.yield) (y := res_step.1)).1
              h_fst_mem_opt with
          ⟨c_next, h_c_next_mem_mk, h_yield_eq⟩
        exact ⟨c_next, (OptionT.mem_support_mk (mx := inner_base) (x := c_next)).1
          h_c_next_mem_mk, h_yield_eq⟩
      rcases h_inner_step_mem with ⟨c_next, h_fst_mem, h_res_step1_eq⟩
      dsimp only [Rel', logical_stepCondition]
      dsimp only [inner_base] at h_fst_mem
      unfold checkSingleFoldingStep at h_fst_mem
      erw [simulateQ_bind] at h_fst_mem
      erw [simulateQ_bind, support_bind] at h_fst_mem
      dsimp only [OptionT.run] at h_fst_mem
      simp only [Set.mem_iUnion, exists_prop] at h_fst_mem
      rcases h_fst_mem with ⟨fiber_vec_opt, h_fiber_vec_opt_mem_support, h_c_k_mem_output⟩
      have h_probFailure_queryFiberPoints_eq_zero := probFailure_simulateQ_queryFiberPoints_eq_zero
          (𝔽q := 𝔽q) (β := β) (γ_repetitions := γ_repetitions) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (so := OracleInterface.simOracle2 []ₒ oStmtIn tr.messages) (k := k) (v := v)
      have h_probOutput_none_queryFiberPoints_eq_zero :=
        OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero
          (hfail := h_probFailure_queryFiberPoints_eq_zero)
      have h_fiber_vec_opt_mem_support_run :
          fiber_vec_opt ∈
            (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
              (queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((List.finRange (ℓ / ϑ)).get k)
                v)).support := by
        have h_fiber_vec_opt_mem_support' := h_fiber_vec_opt_mem_support
        simp only [queryFiberPoints, support_bind,
          Set.mem_iUnion, exists_prop] at h_fiber_vec_opt_mem_support' ⊢
        rcases h_fiber_vec_opt_mem_support' with ⟨i, h_i_mem, h_i_out⟩
        have h_eq : fiber_vec_opt = i := by
          cases i <;>
            simpa [simulateQ_pure, support_pure, Set.mem_singleton_iff] using h_i_out
        subst h_eq
        simpa [bind_pure_comp] using h_i_mem
      have h_fiber_vec_opt_eq_some := exists_eq_some_of_mem_support_of_probOutput_none_eq_zero
        (x := fiber_vec_opt) (hx := h_fiber_vec_opt_mem_support_run)
        (hnone := h_probOutput_none_queryFiberPoints_eq_zero)
      rcases h_fiber_vec_opt_eq_some with ⟨fiber_vec, h_fiber_vec_opt_eq_some⟩
      rw [h_fiber_vec_opt_eq_some] at h_fiber_vec_opt_mem_support_run h_c_k_mem_output
      have h_fiber_val := mem_support_queryFiberPoints 𝔽q β γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oraclePositionIdx := ⟨k, h_k⟩) (v := v)
          (f_i_on_fiber := fiber_vec) (stmtIn := stmtIn) (oStmtIn := oStmtIn)
            (witIn := ()) (challenges := tr.challenges)
        (h_fiber_mem := by
          dsimp only [queryPhaseLogicStep]
          have h_transcript : (FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (tr.challenges ⟨0, rfl⟩)).messages
              = tr.messages := by
            -- funext j
            simp only [MessageIdx, Fin.isValue, FullTranscript.mk1_eq_snoc]
            unfold FullTranscript.messages Transcript.concat
            funext x
            obtain ⟨i, hi⟩ := x; fin_cases i; simp at hi
          rw [h_transcript]
          have h_k_fin_eq : (List.finRange (ℓ / ϑ)).get k = ⟨k, h_k⟩ := by
            apply Fin.eq_of_val_eq
            simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast]
          simpa only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta] using
            h_fiber_vec_opt_mem_support_run
        )
      simp only at h_fiber_val
      have h_fiber_val_eq : fiber_vec.get = fun (fiberIndex : Fin (2 ^ ϑ)) => oStmtIn ⟨k.val, by
        simp only [toOutCodewordsCount_last]; omega⟩
        (getFiberPoint 𝔽q β ⟨↑k, h_k⟩ v fiberIndex) := by
        funext fiberIndex
        exact h_fiber_val fiberIndex
      simp only [h_fiber_val] at h_c_k_mem_output
      simp only [h_k_succ_sub_1_lt, h_k_succ_gt_0, ↓reduceDIte]
      -- ⊢ logical_checkSingleFoldingStep 𝔽q β oStmtIn ⟨↑k.succ - 1, ⋯⟩ v stmtIn
      dsimp only [logical_checkSingleFoldingStep]
      by_cases h_k_gt_0 : k.val > 0
      · have h_gt : (k.succ.val - 1) * ϑ > 0 := by
          have hk' : k.succ.val - 1 > 0 := by
            simpa [Fin.val_succ, add_tsub_cancel_right] using h_k_gt_0
          exact Nat.mul_pos hk' h_ϑ_pos
        simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast,
          gt_iff_lt, h_k_gt_0, mul_pos_iff_of_pos_left, h_ϑ_pos, ↓reduceDIte, Message, guard_eq,
          Fin.val_last, bind_pure_comp, OptionT.simulateQ_map] at h_c_k_mem_output
        erw [simulateQ_ite] at h_c_k_mem_output
        set V_check := (c_cur = oStmtIn ⟨k, by
          simp only [toOutCodewordsCount_last]; omega⟩ (
            (getFiberPoint 𝔽q β ⟨↑k, h_k⟩ v (extractMiddleFinMask 𝔽q β v ⟨k.val * ϑ, by
              have h := oracle_index_le_ℓ (i := Fin.last ℓ)
                (j := ⟨k, by simpa only [toOutCodewordsCount_last] using h_k⟩)
              simp only at h; omega⟩ ϑ))
          )) with h_V_check_def
        have h_V_check_passed : V_check := by
          by_contra h_V_check_false
          rw [h_V_check_def] at h_V_check_false
          simp only [h_V_check_false, ↓reduceIte, OptionT.simulateQ_failure, OptionT.map_failure,
            OptionT.support_failure_run, Set.mem_singleton_iff, reduceCtorEq] at h_c_k_mem_output
        rw [h_V_check_def] at h_V_check_passed
        simp only [h_V_check_passed, ↓reduceIte] at h_c_k_mem_output
        erw [simulateQ_pure, support_bind] at h_c_k_mem_output
        simp only [support_pure, Set.mem_singleton_iff, Function.comp_apply,
          Set.iUnion_iUnion_eq_left, OptionT.support_OptionT_pure_run,
          Option.some.injEq] at h_c_k_mem_output
        -- dsimp only [Functor.map] at h_c_k_mem_output
        have h_k_cast_gt_0 : 0 < k.castSucc := by
          simpa [gt_iff_lt, Fin.val_castSucc] using h_k_gt_0
        simp only [gt_iff_lt, h_k_cast_gt_0, ↓reduceDIte, Fin.val_last,
          Option.some.injEq] at h_rel_k
        simp only [h_gt, ↓reduceDIte]
        simp only [Fin.val_succ, add_tsub_cancel_right]
        -- Goal: LHS = RHS. We have h_c_k_mem_output.1 : b = (RHS as oStmtIn ... getFiberPoint ...).
        conv_rhs => dsimp only [logical_queryFiberPoints];
        dsimp only [logical_queryFiberPoints]
        -- ⊢ logical_computeFoldedValue 𝔽q β ⟨↑k - 1, ⋯⟩ v stmtIn (logical_queryFiberPoints 𝔽q β
          -- oStmtIn ⟨↑k - 1, ⋯⟩ v) = oStmtIn ⟨↑k, ⋯⟩ (getFiberPoint 𝔽q β ⟨↑k, ⋯⟩ v
            -- (extractMiddleFinMask 𝔽q β v ⟨↑k * ϑ, ⋯⟩ ϑ))
        dsimp only [logical_computeFoldedValue, logical_queryFiberPoints]
        constructor
        · -- V check in the current iteration passes
          rw [←h_V_check_passed]
          -- rw previous computation of c_cur (in previous iteration)
          simp only [Fin.val_last, h_rel_k.2.symm]
          rfl
        · -- prove equality relation for the output of the current iteration (i.e. c_next)
          simp only [ForInStep.state]
          rw [h_c_k_mem_output] at h_res_step1_eq
          rw [h_res_step1_eq.symm]
          dsimp only [ForInStep.state]
          rw [h_fiber_val_eq]
          simp only [Nat.add_one_sub_one, Fin.val_last]
          have h_k_fin_eq : (List.finRange (ℓ / ϑ)).get k = ⟨k, by omega⟩ := by
            apply Fin.eq_of_val_eq;
            simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast]
          let destIdx : Fin r := ⟨k.val * ϑ + ϑ, by
            apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            have h_le : k.val * ϑ + ϑ ≤ ℓ := by
              exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ)
                (j := ⟨k.val, by simpa [toOutCodewordsCount_last] using h_k⟩)
            exact h_le
          ⟩
          conv_lhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
            simp only [add_tsub_cancel_right]; dsimp only [destIdx])]
          conv_rhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
            simp only [List.getElem_finRange, Fin.eta, Fin.val_cast]; dsimp only [destIdx])]
          congr 1; congr 1;
          -- only challenges equality left
          simp only [Nat.add_one_sub_one, cast_eq]
          dsimp only [getChallengeSuffix]
          apply extractSuffixFromChallenge_congr_destIdx 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (h_idx_eq := by
              simp only [List.getElem_finRange, Fin.eta, Fin.val_cast]) (h_le := by
              have h_main : k.val * ϑ + ϑ ≤ ℓ := by
                exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ)
                  (j := ⟨k.val, by simpa [toOutCodewordsCount_last] using h_k⟩)
              simpa [Fin.val_succ, add_tsub_cancel_right] using h_main
            ) (h_le' := by
            have h_main : k.val * ϑ + ϑ ≤ ℓ := by
              exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ)
                (j := ⟨k.val, by simpa [toOutCodewordsCount_last] using h_k⟩)
            simpa [List.getElem_finRange, Fin.eta, Fin.val_cast] using h_main
          )
      · have h_ne_gt : ¬ ((k.succ.val - 1) * ϑ > 0) := by
          intro h_gt
          have h_mul_pos : k.val * ϑ > 0 := by
            simpa [Fin.val_succ, add_tsub_cancel_right] using h_gt
          have hk_pos : k.val > 0 := by
            exact Nat.pos_of_mul_pos_right h_mul_pos
          exact h_k_gt_0 hk_pos
        simp only [h_ne_gt, ↓reduceDIte, true_and]
        simp only [Fin.val_succ, add_tsub_cancel_right, Nat.add_one_sub_one, Fin.val_last,
          Option.some.injEq]
        -- ⊢ single_point_localized_fold_matrix_form 𝔽q β ⟨(↑k.succ - 1) * ϑ, ⋯⟩ ϑ ⋯ ⋯
        --     (fun j ↦ stmtIn.challenges ⟨(↑k.succ - 1) * ϑ + ↑j, ⋯⟩)
          -- (getChallengeSuffix 𝔽q β ⟨↑k.succ - 1, ⋯⟩ v)
        --     (logical_queryFiberPoints 𝔽q β oStmtIn ⟨↑k.succ - 1, ⋯⟩ v) =
        --   res_step.1.state
        simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast,
          gt_iff_lt, CanonicallyOrderedAdd.mul_pos, h_k_gt_0, false_and, ↓reduceDIte, Message,
          Fin.val_last, bind_pure_comp, LawfulApplicative.map_pure] at h_c_k_mem_output
        erw [simulateQ_pure, support_pure] at h_c_k_mem_output
        simp only [Set.mem_singleton_iff, Option.some.injEq] at h_c_k_mem_output
        rw [h_c_k_mem_output] at h_res_step1_eq
        rw [h_res_step1_eq.symm]
        dsimp only [ForInStep.state]
        dsimp only [logical_queryFiberPoints]
        rw [h_fiber_val_eq]
        have h_k_fin_eq : (List.finRange (ℓ / ϑ)).get k = ⟨k, by omega⟩ := by
          apply Fin.eq_of_val_eq;
          simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast]
        let destIdx : Fin r := ⟨k.val * ϑ + ϑ, by
          apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          have h_le : k.val * ϑ + ϑ ≤ ℓ := by
            exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ)
              (j := ⟨k.val, by simpa [toOutCodewordsCount_last] using h_k⟩)
          exact h_le
        ⟩
        conv_lhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
          apply Fin.eq_of_val_eq;
          simp only; dsimp only [destIdx])]
        conv_rhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
          simp only [List.getElem_finRange, Fin.eta, Fin.val_cast]; dsimp only [destIdx])]
        congr 1;
        -- only challenges equality left
        simp only [cast_eq]
        dsimp only [getChallengeSuffix]
        apply extractSuffixFromChallenge_congr_destIdx 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (h_idx_eq := by
            simp only [List.getElem_finRange, Fin.eta, Fin.val_cast]) (h_le := by
            have h_main : k.val * ϑ + ϑ ≤ ℓ := by
              exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ)
                (j := ⟨k.val, by simpa [toOutCodewordsCount_last] using h_k⟩)
            simpa [Fin.val_succ, add_tsub_cancel_right] using h_main
          ) (h_le' := by
            have h_main : k.val * ϑ + ϑ ≤ ℓ := by
              exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ)
                (j := ⟨k.val, by simpa [toOutCodewordsCount_last] using h_k⟩)
            simpa [List.getElem_finRange, Fin.eta, Fin.val_cast] using h_main
          )
    )
    (h_yield := by
      intro k c_cur s_curr res_step h_res_step_mem
      -- erw [OptionT.support_run] at h_res_step_mem
      erw [simulateQ_bind] at h_res_step_mem
      erw [simulateQ_bind, support_bind] at h_res_step_mem
      dsimp only [OptionT.run] at h_res_step_mem
      simp only [MessageIdx, Fin.isValue, Message,
        Set.mem_iUnion, exists_prop, Prod.exists] at h_res_step_mem
      rcases h_res_step_mem with
        ⟨c_next_opt, output_state_next, _h_mem_support_cur_folding_step, h_res_step_mem_yield⟩
      cases h_c : c_next_opt with
      | none =>
        have h_res_step1_mem :
            some res_step.1 ∈ support (m := OracleComp []ₒ) (α := Option (ForInStep L))
              (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
                (pure (none : Option (ForInStep L)))) := by
          have h_proj_mem :
              some res_step.1 ∈ Prod.fst <$> support (m := ProbComp)
                (α := Option (ForInStep L) × σ)
                  ((simulateQ impl
                    (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
                      (pure (none : Option (ForInStep L))))) output_state_next) := by
            refine ⟨(some res_step.1, res_step.2), ?_, rfl⟩
            simpa only [MessageIdx, simulateQ_pure, h_c] using h_res_step_mem_yield
          have h_proj_eq := support_run_simulateQ_run_fst_eq (impl := impl)
            (oa := simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
              (pure (none : Option (ForInStep L))))
            (s := output_state_next)
            (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
          rw [h_proj_eq] at h_proj_mem
          exact h_proj_mem
        simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at h_res_step1_mem
        cases h_res_step1_mem
      | some next =>
        have h_res_step1_mem :
            some res_step.1 ∈ support (m := OracleComp []ₒ) (α := Option (ForInStep L))
              (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
                (pure (some (ForInStep.yield next)))) := by
          have h_proj_mem :
              some res_step.1 ∈ Prod.fst <$> support (m := ProbComp)
                (α := Option (ForInStep L) × σ)
                  ((simulateQ impl
                    (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
                      (pure (some (ForInStep.yield next))))) output_state_next) := by
            refine ⟨(some res_step.1, res_step.2), ?_, rfl⟩
            simpa [h_c] using h_res_step_mem_yield
          have h_proj_eq := support_run_simulateQ_run_fst_eq (impl := impl)
            (oa := simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
              (pure (some (ForInStep.yield next))))
            (s := output_state_next)
            (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
          rw [h_proj_eq] at h_proj_mem
          exact h_proj_mem
        simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at h_res_step1_mem
        exact ⟨next, by simpa using h_res_step1_mem⟩
    )
  -- extract the final guard relation from h_c_last_mem
  set v_challenge := (FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (tr.challenges ⟨0, rfl⟩)).challenges ⟨0, rfl⟩
      with h_v_challenge
  intro (k : Fin (ℓ / ϑ + 1))
  dsimp only [logical_stepCondition]
  by_cases h_k_lt : ↑k < ℓ / ϑ
  · simp only [h_k_lt, ↓reduceDIte]
    have h_pred_lt : k.val + 1 - 1 < ℓ / ϑ := by omega
    have res := h_inductive_relations.2
    -- 1. Unpack the existence proof
    rcases res with ⟨bs, ss, h_init, h_s_init, h_final_b, h_final_s, h_steps, h_rel_all⟩
    -- 2. Specialize the relation for the 'input' to the k-th iteration
    -- Since k : Fin (ℓ / ϑ), it can be cast into Fin (ℓ / ϑ + 1)
    have h_rel_for_k_th_level_guard := h_rel_all ⟨k + 1, by simp only [List.length_finRange]; omega⟩
    dsimp only [Rel', checkSingleRepetition_foldRel] at h_rel_for_k_th_level_guard
    have h_res := h_rel_for_k_th_level_guard
    simp only [logical_stepCondition, h_pred_lt, ↓reduceDIte, gt_iff_lt, Fin.val_last,
      dite_else_true] at h_res
    -- rw [h_v] at h_res
    exact h_res.1
  · simp only [h_k_lt, ↓reduceDIte]
    --   ⊢ logical_computeFoldedValue 𝔽q β ⟨ℓ / ϑ - 1, ⋯⟩ v stmtIn
      -- (logical_queryFiberPoints 𝔽q β oStmtIn ⟨ℓ / ϑ - 1, ⋯⟩ v) = stmtIn.final_constant
    have h_last_guard_relation := h_inductive_relations.1.2
    dsimp only [Rel', Rel, checkSingleRepetition_foldRel] at h_last_guard_relation
    simp only [List.length_finRange, gt_iff_lt, Fin.val_last,
      dite_else_true] at h_last_guard_relation
    have h_lt : 0 < (⟨ℓ/ϑ, by simp only [List.length_finRange, lt_add_iff_pos_right,
      zero_lt_one]⟩ : Fin ((List.finRange (ℓ / ϑ)).length + 1)) := by
      change (0 : ℕ) < (ℓ / ϑ)
      exact h_0_lt
    dsimp only [logical_computeFoldedValue]
    simp only [h_lt, forall_true_left] at h_last_guard_relation
    obtain ⟨rfl⟩ := h_c_last_eq_some
    simp only [Option.some.injEq] at h_last_guard_relation
    simp only [MessageIdx, h_last_guard_relation.symm, Message] at h_mem_final_guard_support
    erw [simulateQ_ite, simulateQ_ite, simulateQ_pure, simulateQ_pure] at h_mem_final_guard_support
    have h_dest_le_final : (ℓ / ϑ - 1) * ϑ + ϑ ≤ ℓ := by
      have h_dest_eq_final : (ℓ / ϑ - 1) * ϑ + ϑ = ℓ := by
        calc
          (ℓ / ϑ - 1) * ϑ + ϑ = ((ℓ / ϑ - 1) + 1) * ϑ := by
            rw [Nat.add_mul, Nat.one_mul]
          _ = (ℓ / ϑ) * ϑ := by
            rw [Nat.sub_add_cancel (Nat.succ_le_of_lt h_0_lt)]
          _ = ℓ := h_ℓ_div_mul_eq_ℓ
      exact le_of_eq h_dest_eq_final
    let destIdx : Fin r := ⟨(ℓ / ϑ - 1) * ϑ + ϑ, by
      apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      exact h_dest_le_final
    ⟩
    set fiber_vec := logical_queryFiberPoints 𝔽q β oStmtIn ⟨ℓ / ϑ - 1, by omega⟩ v
      with h_fiber_vec_def
    set single_point_localized_fold_matrix_form_val :=
      single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        _ _ _ _ _ _ _ with h_single_point_localized_fold_matrix_form_val_def
    conv at h_mem_final_guard_support =>
      rw [support_StateT_ite_apply]
      erw [support_pure, support_pure]
      enter [1]
      -- dsimp only [getChallengeSuffix]
      rw [h_last_guard_relation]
      -- h_final_yield_support_mem
      -- erw [extractSuffixFromChallenge_congr_destIdx 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      --   (h_idx_eq := by simp only [List.length_finRange]) (h_le := by exact h_dest_le_final)
      --   (h_le' := by simpa [List.length_finRange] using h_dest_le_final)]
      -- change single_point_localized_fold_matrix_form_val
    have h_final_check_passed : c_last_val = stmtIn.final_constant := by
      by_contra h_neq
      simp only [h_neq, ↓reduceIte, Set.mem_singleton_iff,
        Prod.mk.injEq] at h_mem_final_guard_support
      -- h_mem_final_guard_support :
      -- output_final_guard = none ∧ output_state_final_guard = output_state_inner_forIn
      simp only [h_mem_final_guard_support, simulateQ_pure] at h_final_yield_support_mem
      erw [support_pure] at h_final_yield_support_mem
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq,
        false_and] at h_final_yield_support_mem
    simp only [h_final_check_passed, ↓reduceIte, Set.mem_singleton_iff,
      Prod.mk.injEq] at h_mem_final_guard_support -- pure equalities now
    -- h_mem_final_guard_support :
    -- output_final_guard = some () ∧ output_state_final_guard = output_state_inner_forIn
    rw [←h_final_check_passed]
    rw [←h_last_guard_relation]
    dsimp only [single_point_localized_fold_matrix_form_val]
    conv_lhs =>
      rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx)
        (h_destIdx_eq_destIdx' := by dsimp only [destIdx]) (fiber_eval_mapping := fiber_vec)]
    conv_rhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
        simp only [List.length_finRange]; dsimp only [destIdx]) (fiber_eval_mapping := fiber_vec)]
    congr 1
    -- only challenges equality left
    simp only [cast_eq]
    dsimp only [getChallengeSuffix]
    apply extractSuffixFromChallenge_congr_destIdx 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_idx_eq := by
        simp only [List.length_finRange]) (h_le := by
        exact h_dest_le_final) (h_le' := by
        simpa [List.length_finRange] using h_dest_le_final)

/-! Main lemma connecting verifier support to logical proximity checks.
    This is the key lemma used in toFun_full of queryKnowledgeStateFunction.
    The left side matches the hypothesis from StateT.run characterization:
      (stmtOut, oStmtOut) ∈ support ((fun x ↦ x.1) <$> simulateQ impl (Verifier.run ...) s)
    The right side gives us:
      1. stmtOut = true
      2. oStmtOut = mkVerifierOStmtOut ...
      3. ∀ rep, logical_checkSingleRepetition ... (the proximity checks spec)
-/
omit [CharP L 2] [SampleableType L] in
lemma logical_consistency_checks_passed_of_mem_support_V_run {σ : Type}
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (stmtIn : FinalSumcheckStatementOut)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (tr : FullTranscript (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (s : σ) (stmtOut : Bool) (oStmtOut : Empty → Unit)
    (h_mem_V_run_support :
      (stmtOut, oStmtOut) ∈
        OptionT.mk (Prod.fst <$> ((simulateQ.{0, 0, 0} impl
            (Verifier.run (stmtIn, oStmtIn) tr
              (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).toVerifier)) :
              StateT σ ProbComp (Option (Bool × (Empty → Unit)))).run s).support) :
    (stmtOut = true ∧
      oStmtOut = OracleVerifier.mkVerifierOStmtOut
        (embed := (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).embed)
        (hEq := (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).hEq) oStmtIn tr ∧
     ∀ (rep : Fin γ_repetitions),
       logical_checkSingleRepetition 𝔽q β oStmtIn
         (tr.challenges ⟨0, rfl⟩ rep) stmtIn stmtIn.final_constant) := by
  -- dsimp only [OptionT.mk] at h_mem_V_run_support
  conv at h_mem_V_run_support =>
    dsimp only [Verifier.run, OracleVerifier.toVerifier, queryOracleVerifier]
    dsimp only [queryPhaseLogicStep]
    -- Simplify the `(fun x ↦ x.1) <$> ...` part
    -- Group the last two `bind`
    rw [pure_bind]; rw [bind_assoc]; rw [pure_bind]
    -- Distribute `simulateQ` over the `bind`
    erw [simulateQ_bind, simulateQ_bind, simulateQ_bind]
    -- Resolve the constant mappings
    simp only [Function.comp_def, simulateQ_pure, pure_bind]
    rw [OptionT.simulateQ_forIn]
    rw [OptionT.simulateQ_forIn_stateful_comp]
  conv at h_mem_V_run_support =>
    -- rw [simulateQ_forIn_stateful_comp (impl := impl)
      -- (l := List.finRange γ_repetitions) (init := PUnit.unit)]
    erw [OptionT.support_mk]
    erw [support_map]
    erw [Set.mem_image]
    erw [support_bind]
    enter [1, x]
    simp only [MessageIdx, Message, Fin.isValue, FullTranscript.mk1_eq_snoc, bind_pure_comp,
      OptionT.simulateQ_map, id_map', Set.mem_iUnion,
      exists_prop, Prod.exists]
  obtain ⟨x, hx_mem, hx_1_eq_stmtOut_oStmtOut⟩ := h_mem_V_run_support
  -- Note: hx_mem now refers to the exact simulateQ (forIn ...) block
  -- after the conv with OptionT.simulateQ_forIn
  -- The structure is: hx_mem : ∃ a b, (a, b) ∈ (simulateQ impl (forIn ...)).support
  -- where the forIn is exactly: forIn (List.finRange γ_repetitions) PUnit.unit (fun a b => ...)
  let forIn_body : Fin γ_repetitions → PUnit.{1} →
      StateT σ ProbComp (Option (ForInStep PUnit.{1})) := fun (a : Fin γ_repetitions)
      (b : PUnit.{1}) =>
    simulateQ impl (
      (((fun (_ : Unit) ↦ ForInStep.yield PUnit.unit) <$>
        ((simulateQ.{0, 0, 0} (impl := OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
          ((checkSingleRepetition 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            ((FullTranscript.mk1 (tr.challenges ⟨0, rfl⟩)).challenges ⟨0, rfl⟩ a)
            stmtIn stmtIn.final_constant) :
              OptionT (OracleComp
                ([]ₒ + ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ +
                  [(pSpecQuery 𝔽q β γ_repetitions).Message]ₒ))) Unit).run) :
            OracleComp []ₒ (Option Unit))) :
        OptionT (OracleComp []ₒ) (ForInStep PUnit.{1}))
    )
  let forIn_block : OptionT (StateT σ ProbComp) PUnit.{1} :=
    forIn (xs := List.finRange γ_repetitions) (b := PUnit.unit.{1}) (f := forIn_body)
  -- let simulateQ_forIn_block := simulateQ impl forIn_block
  -- Verify that hx_mem is about the exact simulateQ (forIn ...) block
  conv at hx_mem =>
    enter [1, x, 1, b, 1, 1, 1, 1]
    -- Unfold the set definitions to expose the structure
    change (forIn_block)
  conv at hx_mem =>
    enter [1, x_1, 1, b, 1]
    change ((x_1, b) ∈ (((forIn_block >>=
      (fun (u : Option PUnit.{1}) => (_ : StateT σ ProbComp (Option Bool))))
        : StateT σ ProbComp (Option Bool)).run s).support)
    rw [OptionT.mem_support_StateT_bind_run (ma := forIn_block) (x := (x_1, b))]
  rcases hx_mem with ⟨y, s', h_y_s'_mem_support_forIn_block, h_x_eq⟩
  -- simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h_x_eq -- TODO
  have h_y_ne_none : y ≠ none := by
    intro h_y_eq_none
    simp only [h_y_eq_none, simulateQ_pure] at h_x_eq
    erw [support_pure] at h_x_eq
    simp only [Set.mem_singleton_iff] at h_x_eq
    rw [Prod.mk_inj] at h_x_eq
    rw [hx_1_eq_stmtOut_oStmtOut] at h_x_eq
    simp only [reduceCtorEq, false_and] at h_x_eq
  obtain ⟨y_val, h_y_eq⟩ := Option.ne_none_iff_exists.mp h_y_ne_none
  obtain ⟨rfl⟩ := h_y_eq
  simp only at h_x_eq
  erw [simulateQ_pure, support_pure] at h_x_eq
  rw [Set.mem_singleton_iff, Prod.mk_inj] at h_x_eq
  -- **Now we have pure equalities of x.1 and x.2**
  rcases h_y_s'_mem_support_forIn_block with ⟨z, s'', h_forIn_run_mem, h_pure⟩
  have h_z_ne_none : z ≠ none := by
    intro h_z_eq_none
    simp only [h_z_eq_none, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, reduceCtorEq, false_and] at h_pure
  obtain ⟨z_val, h_z_eq⟩ := Option.ne_none_iff_exists.mp h_z_ne_none
  obtain ⟨rfl⟩ := h_z_eq
  erw [simulateQ_pure, support_pure] at h_pure
  simp only [Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at h_pure
  -- **h_pure : y_val = true ∧ s' = s''**
  dsimp only [forIn_block] at h_forIn_run_mem
  -- 1. Apply the extraction lemma
  have h_independent_support_mem_exists := OptionT.exists_path_of_mem_support_forIn_unit.{0}
    (spec := []ₒ) (l := List.finRange γ_repetitions) (f := forIn_body) (s_init := s)
    (s_final := s'') (u := z_val)
    (h_yield := by
      intro rep s_pre res_step h_res_step_mem
      dsimp only [forIn_body] at h_res_step_mem
      set oa : OracleComp []ₒ (Option Unit) :=
       ((simulateQ.{0, 0, 0} (impl := OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
          ((checkSingleRepetition 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            ((FullTranscript.mk1 (tr.challenges ⟨0, rfl⟩)).challenges ⟨0, rfl⟩ rep)
            stmtIn stmtIn.final_constant) :
              OptionT (OracleComp
                ([]ₒ + ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ +
                  [(pSpecQuery 𝔽q β γ_repetitions).Message]ₒ))) Unit).run) :
            OracleComp []ₒ (Option Unit))
      have h_fst_mem : some res_step.1 ∈ ((simulateQ impl
          ((((fun (_ : Unit) ↦ ForInStep.yield PUnit.unit) <$> oa) :
            OptionT (OracleComp []ₒ) (ForInStep PUnit)))).run' s_pre).support := by
        rw [StateT.run', support_map]
        exact Set.mem_image_of_mem Prod.fst h_res_step_mem
      have h_run'_supp_eq := support_simulateQ_run'_eq (impl := impl)
        (oa := ((((fun (_ : Unit) ↦ ForInStep.yield PUnit.unit) <$> oa) :
          OptionT (OracleComp []ₒ) (ForInStep PUnit))))
        (s := s_pre)
        (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
      rw [h_run'_supp_eq] at h_fst_mem
      erw [OptionT.mem_support_OptionT_run_map_some] at h_fst_mem
      obtain ⟨u, _h_u_mem, h_eq⟩ := h_fst_mem
      exact h_eq.symm
    )
    (h_mem := h_forIn_run_mem)
  set γ_challenges : Fin γ_repetitions →
    sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩ := tr.challenges ⟨0, rfl⟩ with h_γ_challenges_def
  rw [h_pure.1] at h_x_eq
  rw [h_x_eq.1] at hx_1_eq_stmtOut_oStmtOut
  simp only [Option.some.injEq, Prod.mk.injEq, Bool.true_eq] at hx_1_eq_stmtOut_oStmtOut
  constructor
  · exact hx_1_eq_stmtOut_oStmtOut.1
  · constructor
    · exact hx_1_eq_stmtOut_oStmtOut.2.symm
    · -- 2. Quantify over an arbitrary repetition
      intro rep
      -- ⊢ logical_checkSingleRepetition 𝔽q β oStmtIn (γ_challenges rep)
        -- stmtIn stmtIn.final_constant
      have h_rep_th_support_mem := h_independent_support_mem_exists rep
        (by simp only [List.mem_finRange])
      rcases h_rep_th_support_mem with ⟨state_pre_repetition, state_post_repetition,
        h_support_rep_ith_iteration⟩
      exact logical_checkSingleRepetition_of_mem_support_forIn_body 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (γ_repetitions := γ_repetitions) (σ := σ) (impl := impl)
        (oStmtIn := oStmtIn) (tr := tr) (stmtIn := stmtIn) (rep := rep)
        (state_pre := state_pre_repetition) (forIn_body := forIn_body) (h_forIn_body_eq := rfl)
        (h_mem := by
          use (ForInStep.yield PUnit.unit, state_post_repetition)
          exact h_support_rep_ith_iteration
        )

/-- Strong completeness for the query phase logic step.

This proves that for any valid input satisfying `strictFinalSumcheckRelOut`,
the verifier check succeeds with probability 1, and the output satisfies
`acceptRejectOracleRel` (i.e., the statement is `true`). -/
theorem queryPhaseLogicStep_isStronglyComplete :
    (queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).IsStronglyCompleteUnderSimulation := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let f₀ := getFirstOracle 𝔽q β oStmtIn
  have h_ϑ_pos : ϑ > 0 := by exact Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
  let step := queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  -- 1. Generate the Honest Transcript (Deterministic given challenges)
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  -- 2. Define the honest oracle simulator
  -- simOracle2 oSpec t₁ t₂ : SimOracle.Stateless (oSpec + ([T₁]ₒ + [T₂]ₒ)) oSpec
  -- This answers queries to OracleIn using oStmtIn and queries to Messages using transcript
  let so := OracleInterface.simOracle2 []ₒ oStmtIn transcript.messages
  -- We need to prove:
  -- 1. [⊥ | verifierCheck ...] = 0  (never fails)
  -- 2. [fun b => b = true | verifierCheck ...] = 1  (always returns true)
  -- 3. completeness_relOut holds
  -- 4-5. Prover and verifier agree
  -- Prove safety: verifier check never fails
  have h_guards_pass : Pr[⊥ | OptionT.mk
    (simulateQ so (step.verifierCheck stmtIn transcript))] = 0 := by
    -- Unfold the definitions
    dsimp only [step, queryPhaseLogicStep]
    rw [OptionT.probFailure_mk]
    conv_lhs => -- first summand is 0
      enter [1]; simp only [MessageIdx, Message, Fin.isValue, liftM_OptionT_eq, bind_pure_comp,
        map_pure, id_map', List.foldlM_range, OptionT.simulateQ_map,
        HasEvalPMF.probFailure_eq_zero]
    rw [zero_add]
    -- 2. Push simulation inside the 'bind' structure
    -- simulateQ (do a <- x; b) = do a <- simulateQ x; simulateQ b
    erw [simulateQ_bind]
    -- simp only [Function.comp_apply, probOutput_eq_zero_iff]
    -- rw [OptionT.support_run_eq]
    -- simp only [←probOutput_eq_zero_iff]
    -- erw [probOutput_none_OptionT_pure_eq_zero]
    apply OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero
    -- rw [probFailure_bind_eq_zero_iff]
    erw [OptionT.probFailure_mk_bind_eq_zero_iff]
    -- [⊥|simulateQ so (forIn ...)] = 0 ∧ (∀ x ∈ (simulateQ so (forIn ...)).support, ...))
    -- conv => -- Simp away the second term (which is simulateQ of pure)
      -- enter [2]
      -- simp only [liftM_OptionT_eq, bind_pure_comp]
    set simulateQ_forIn_block :  OracleComp []ₒ (Option PUnit.{1}) :=
      simulateQ so _ with h_simulateQ_forIn_block
    have h_probFailure_simulateQ_forIn_eq_0 : Pr[⊥ | OptionT.mk simulateQ_forIn_block] = 0 := by
      dsimp only [simulateQ_forIn_block]
      rw [OptionT.simulateQ_forIn]
      dsimp only [OptionT.mk]
      -- rw [OptionT.probFailure_mk]
      -- conv_lhs =>
      --   enter [1]; simp only [MessageIdx, Message, Fin.isValue, liftM_OptionT_eq, bind_pure_comp,
      --     map_pure, List.forIn_yield_eq_foldlM, id_map', List.foldlM_range,
      --     HasEvalPMF.probFailure_eq_zero]
      -- rw [zero_add]
      -- -- ⊢ Pr[=none | simulateQ_forIn_block] = 0
      -- change (Pr[=none | simulateQ_forIn_block] = 0)
      -- 3. Now we are at the outer loop (forIn γ_repetitions).
      -- Push simulateQ inside the loop using the lemma that `simulateQ distributes over the loop`
      -- NOW apply the safety lemma
      -- The goal is: [⊥ | forIn ... (fun ... ↦ simulateQ so ...)] = 0
      apply _root_.probFailure_forIn_eq_zero_of_body_safe
      intro rep h_rep_mem s_rep
      -- 4. Push simulation inside the inner logic
      erw [simulateQ_bind]
      -- rw [probFailure_bind_eq_zero_iff]
      conv =>
        enter [2]
        simp only [bind_pure_comp, map_pure, Function.comp_apply, simulateQ_pure, probFailure_pure,
          implies_true]
      erw [OptionT.probFailure_mk]
      conv_lhs =>
        enter [1];
        simp only [MessageIdx, Message, Fin.isValue, liftM_OptionT_eq, bind_pure_comp, map_pure,
          HasEvalPMF.probFailure_eq_zero]
      rw [zero_add]
      apply OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero
      erw [OptionT.probFailure_mk_bind_eq_zero_iff]
      set simulateQ_singleRepetition_block :  OracleComp []ₒ (Option PUnit.{1}) :=
      simulateQ so _ with h_simulateQ_singleRepetition_block
      have h_probFailure_simulateQ_singleRepetition_eq_0 :
        Pr[⊥ | OptionT.mk simulateQ_singleRepetition_block] = 0 := by
        apply checkSingleRepetition_probFailure_eq_zero (h_relIn := h_relIn)
      have h_probOutput_simulateQ_singleRepetition_eq_none :=
        OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero
          (hfail := h_probFailure_simulateQ_singleRepetition_eq_0)
      constructor
      · simp only [HasEvalPMF.probFailure_eq_zero]
      · intro x hx -- output from the single repetition
        have h_x_eq : ∃ val, x = some (val) := by
          have h_exists_some := exists_eq_some_of_mem_support_of_probOutput_none_eq_zero (x := x)
            (hx := hx) (hnone := h_probOutput_simulateQ_singleRepetition_eq_none)
          exact h_exists_some
        rcases h_x_eq with ⟨val, h_x_eq⟩
        rw [h_x_eq]
        rw [OptionT.probFailure_mk]
        simp only [MessageIdx, Message, bind_pure_comp, HasEvalPMF.probFailure_eq_zero, zero_add]
        erw [simulateQ_pure]
        simp only [probOutput_eq_zero_iff, support_pure, Set.mem_singleton_iff, reduceCtorEq,
          not_false_eq_true]
    have h_probOutput_simulateQ_forIn_eq_none :=
      OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero
        (hfail := h_probFailure_simulateQ_forIn_eq_0)
    constructor
    · simp only [HasEvalPMF.probFailure_eq_zero]
    · intro x hx -- output from the forIn loop
      have h_x_eq : ∃ val, x = some (val) := by
        have h_exists_some := exists_eq_some_of_mem_support_of_probOutput_none_eq_zero (x := x)
          (hx := hx) (hnone := h_probOutput_simulateQ_forIn_eq_none)
        exact h_exists_some
      rcases h_x_eq with ⟨val, h_x_eq⟩
      rw [h_x_eq]
      rw [OptionT.probFailure_mk]
      simp only [HasEvalPMF.probFailure_eq_zero, zero_add]
      erw [simulateQ_pure]
      simp only [probOutput_pure, reduceCtorEq, ↓reduceIte]
  exact ⟨h_guards_pass, rfl, rfl, rfl⟩

/-- Perfect completeness for the final query round (using the oracle queryProof). -/
theorem queryOracleProof_perfectCompleteness {σ : Type}
  (init : ProbComp σ) (hInit : NeverFail init)
  (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  OracleProof.perfectCompleteness
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (relation := strictFinalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (oracleProof := queryOracleProof 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (init := init)
    (impl := impl) := by
  unfold OracleProof.perfectCompleteness
 -- Step 1: Unroll the 2-message reduction to convert from probability to logic
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_V_to_P (hInit := hInit)
    (hDir0 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- Step 2: Convert probability 1 to universal quantification over support
  rw [probEvent_eq_one_iff]
  -- Step 3: Unfold protocol definitions
  -- dsimp only [queryOracleProof, queryOracleProver, queryOracleVerifier,
  dsimp only [OracleVerifier.toVerifier, FullTranscript.mk1]
  let step := (queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
  let strongly_complete : step.IsStronglyCompleteUnderSimulation :=
    queryPhaseLogicStep_isStronglyComplete (L := L)
      𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  constructor
  -- GOAL 1: SAFETY - Prove the verifier never crashes ([⊥|...] = 0)
  · -- Peel off monadic layers to reach the core verifier logic
    -- ⊢ [⊥| do
    --   let challenge ← getChallenge          -- (A) V samples v ← B_{ℓ+R}
    --   let receiveChallengeFn ← pure (...)               -- (B) P receives challenge
      -- (pure, never fails)
    --   let __discr ← proverOut ...           -- (C) P computes output (pure, never fails)
    --   let verifierStmtOut ← simulateQ ...   -- (D) V runs verifierCheck ← THIS IS THE KEY
    --       do
    --         let _ ← liftM verifierCheck     -- The guards live here!
    --         pure verifierOut
    --   pure (...)
    -- ] = 0
    -- Step 1: Peel off the safe layers
    -- For each layer:
    --   A: neverFails_getChallenge or neverFails_query
    --   B: neverFails_pure
    --   C: neverFails_pure (after liftComp)
    simp only [probFailure_bind_eq_zero_iff]
    conv_lhs =>
      simp only [liftComp_eq_liftM, liftM_pure, probFailure_eq_zero]
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [OptionT.probFailure_lift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_zero, liftComp_eq_liftM,
        liftComp_id, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]
    intro chal h_chal_support
    -- 1.B Handle the `let receiveChallengeFn ← pure (...)`
    conv =>
      enter [1]; simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_zero,
        Fin.succ_zero_eq_one, liftComp_eq_liftM]
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [OptionT.probFailure_lift]
      simp only [Fin.isValue, liftComp_eq_liftM, liftComp_id, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]
    intro h_receiveChallengeFn h_receiveChallengeFn_support
    -- 1.B Handle the `(queryOracleReduction 𝔽q β γ_repetitions).prover.output
      -- (h_receiveChallengeFn chal)) ...`
    conv =>
      enter [1];
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_zero,
        Fin.succ_zero_eq_one, liftComp_eq_liftM]
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [OptionT.probFailure_lift]
      simp only [Fin.isValue, liftComp_eq_liftM, liftComp_id, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]
    intro prover_final_output h_prover_final_output_support
    conv at h_prover_final_output_support =>
      erw [OptionT.support_mk]
      dsimp only [ChallengeIdx, Challenge, liftComp_eq_liftM, monadLift, MonadLift.monadLift,
        Set.mem_setOf_eq]
      rw [liftComp_id]
      simp only [Fin.reduceLast, Fin.isValue]
      dsimp only [OptionT.lift];
      erw [support_bind]; dsimp only [liftM, monadLift, MonadLift.monadLift];
      rw [support_liftComp]; erw [support_pure]
      simp only [Fin.isValue, Challenge, Matrix.cons_val_zero, Set.mem_singleton_iff, support_pure,
        Set.iUnion_iUnion_eq_left, Option.some.injEq]
      -- pure equalities now
    -- 1.C Handle the `let __discr ← proverOut ...`
    -- Note: Use simp instead of rw to avoid typeclass diamond issues with Fintype instances
    -- erw [probFailure_liftComp]
    -- split;
    simp only [ChallengeIdx, Challenge, MessageIdx, bind_pure_comp, liftComp_eq_liftM,
      OptionT.mem_support_iff, toPFunctor_add, toPFunctor_emptySpec, OptionT.support_run,
      Prod.mk.eta, probFailure_eq_zero, implies_true, and_true]
    -- erw [OptionT.probFailure_mk]
    erw [OptionT.probFailure_liftComp_of_OracleComp_Option]
    conv_lhs =>
      enter [1]
      simp only [MessageIdx, Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one,
        id_eq, bind_pure_comp, OptionT.run_map, HasEvalPMF.probFailure_eq_zero]
    rw [zero_add]
    simp only [probOutput_eq_zero_iff]
    rw [OptionT.support_run_eq]
    simp only [←probOutput_eq_zero_iff]
    change Pr[= none | OptionT.run (m := (OracleComp []ₒ)) (x := (OptionT.bind _ _)) ] = 0
    rw [OptionT.probOutput_none_bind_eq_zero_iff]
    conv =>
      enter [x]
      rw [OptionT.support_run]
    intro vStmtOut h_vStmtOut_mem_support
    -- Apply the simulateQ safety lemma
    -- Can't apply probFailure_simulateQ_simOracle2_eq_zero here
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete
      (stmtIn := stmtIn) (witIn := witIn) (h_relIn := h_relIn)
      (challenges := fun ⟨j, hj⟩ => by
        match j with
        | 0 => exact chal
      )
    have h_transcript_eq : FullTranscript.mk1 ((FullTranscript.mk1 chal).challenges ⟨0, by rfl⟩) =
      FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions) chal := by
      rfl
    rw [h_transcript_eq]
    have h_probOutput_none_V_check_eq_0 :=
      OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero (hfail := h_V_check)
    have h_vStmtOut_eq : ∃ val, vStmtOut = some (val) := by
      have h_exists_some := exists_eq_some_of_mem_support_of_probOutput_none_eq_zero (x := vStmtOut)
        (hx := h_vStmtOut_mem_support) (hnone := by
          dsimp only [step] at h_probOutput_none_V_check_eq_0
          dsimp only [queryOracleProof, queryOracleReduction, queryPhaseLogicStep,
            queryOracleVerifier, OracleVerifier.toVerifier] at h_probOutput_none_V_check_eq_0 ⊢
          rw [h_transcript_eq] at h_probOutput_none_V_check_eq_0 ⊢
          simp only [MessageIdx, Message, Fin.isValue, bind_pure_comp, Functor.map_map,
            OptionT.simulateQ_map]
          simp only [MessageIdx, Message, Fin.isValue, bind_pure_comp,
            OptionT.simulateQ_map] at h_probOutput_none_V_check_eq_0
          exact h_probOutput_none_V_check_eq_0
        )
      exact h_exists_some
    rcases h_vStmtOut_eq with ⟨val, h_vStmtOut_eq⟩
    rw [h_vStmtOut_eq]
    simp only [Function.comp_apply, probOutput_eq_zero_iff]
    rw [OptionT.support_run_eq]
    simp only [←probOutput_eq_zero_iff]
    erw [probOutput_none_pure_some_eq_zero]
  · -- GOAL 2: CORRECTNESS - Prove all outputs in support satisfy the relation
    intro x hx_mem_support
    rcases x with ⟨⟨prvStmtOut, prvOStmtOut⟩, ⟨verStmtOut, verOStmtOut⟩, witOut⟩
    simp only
    -- Step 2a: Simplify the support membership to extract the challenge
    simp only [ support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, Prod.exists
    ] at hx_mem_support
    conv at hx_mem_support =>
      erw [OptionT.support_mk, support_pure]
      simp only [
        Set.mem_singleton_iff, Option.some.injEq, Set.setOf_eq_eq_singleton, Prod.mk.injEq,
        OptionT.mem_support_iff,
        OptionT.run_monadLift, support_map, Set.mem_image, exists_eq_right, Fin.succ_one_eq_two,
        id_eq, guard_eq, bind_pure_comp,
        toPFunctor_add, toPFunctor_emptySpec, OptionT.support_run, ↓existsAndEq, and_true, true_and,
        exists_eq_right_right', liftM_pure, support_pure, exists_eq_left]
      dsimp only [monadLift, MonadLift.monadLift]
    simp only [Fin.isValue, Challenge, Matrix.cons_val_zero, ChallengeIdx,
      liftComp_eq_liftM, Fin.reduceLast, MessageIdx] at hx_mem_support
    -- Step 2b: Extract the challenge r1 and the trace equations
    obtain ⟨r1, ⟨_h_r1_mem_challenge_support, h_trace_support⟩⟩ := hx_mem_support
    rcases h_trace_support with ⟨prvWitOut, h_prvOut_mem_support, h_verOut_mem_support⟩
    conv at h_prvOut_mem_support => -- similar simplification as in commit step
      dsimp only [queryOracleProof, queryOracleReduction, queryPhaseLogicStep, queryOracleProver,
        queryOracleVerifier, OracleVerifier.toVerifier, FullTranscript.mk1]
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [liftComp_id]
      rw [support_liftComp]
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, and_true]
    -- Step 2c: Simplify the verifier computation
    conv at h_verOut_mem_support =>
      erw [simulateQ_bind]
      -- rw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      -- erw [_root_.bind_pure_simulateQ_comp]
      simp only
      -- simp only [show OptionT.pure (m := (OracleComp ([]ₒ
        -- + ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ + [pSpecFold.Message]ₒ)))) = pure by rfl]
      change some (verStmtOut, verOStmtOut) ∈ (liftComp _ _).support
      rw [support_liftComp]
      dsimp only [Functor.map]
      erw [support_bind]
      simp only [Fin.isValue, MessageIdx, Message, support_bind, Set.mem_iUnion, exists_prop,
        Function.comp_apply, Set.iUnion_exists, Set.biUnion_and']
      -- erw [support_pure]
      -- simp only [Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq]
    rcases h_verOut_mem_support with ⟨VCheck_boolean, h_VCheck_boolean_mem_support,
      VOut_boolean, h_VOut_boolean_mem_support, h_VOut_mem_support⟩
    set V_check := step.verifierCheck stmtIn (FullTranscript.mk1
      (msg0 := _)) with h_V_check_def
    -- Apply the simulateQ safety lemma
    -- Can't apply probFailure_simulateQ_simOracle2_eq_zero here
    obtain ⟨h_V_check_not_fail, h_rel, h_agree⟩ := strongly_complete
      (stmtIn := stmtIn) (witIn := witIn) (h_relIn := h_relIn)
      (challenges := fun ⟨j, hj⟩ => by
        match j with
        | 0 => exact r1
      )
    have h_VOut_boolean_eq_true : VOut_boolean = true := by
      match VCheck_boolean with -- VOut_boolean depends on VCheck_boolean
      | some a =>
        simp only [Fin.isValue] at h_VOut_boolean_mem_support
        erw [simulateQ_pure] at h_VOut_boolean_mem_support
        simp only [Fin.isValue, support_pure, Set.mem_singleton_iff] at h_VOut_boolean_mem_support
        dsimp only [queryPhaseLogicStep] at h_VOut_boolean_mem_support
        exact h_VOut_boolean_mem_support
      | none =>
        simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff]
          at h_VOut_boolean_mem_support
        simp only [h_VOut_boolean_mem_support, support_pure, Set.mem_singleton_iff,
          reduceCtorEq] at h_VOut_mem_support ⊢
    simp only [h_VOut_boolean_eq_true, OptionT.support_OptionT_pure_run, Set.mem_singleton_iff,
      Option.some.injEq, Prod.mk.injEq] at h_VOut_mem_support -- pure equalities now
    have prvStmtOut_eq := h_prvOut_mem_support
    obtain ⟨verStmtOut_eq, verOStmtOut_eq⟩ := h_VOut_mem_support
    constructor
    · rw [verStmtOut_eq, verOStmtOut_eq];
      exact h_rel
    · constructor
      · rw [verStmtOut_eq, prvStmtOut_eq];
      · rw [verOStmtOut_eq];
        exact h_agree.2

open scoped NNReal

/-- The round-by-round extractor for the query phase.
Since f^(0) is always available, we can invoke the extractMLP function directly. -/
noncomputable def queryRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := (FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
      × (∀ j, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j))
    (WitIn := Unit)
    Unit
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (fun _ => Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun _ _ _ => ()

def queryKStateProp (m : Fin (1 + 1))
  (tr : ProtocolSpec.Transcript m
    (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
  (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
  (witMid : Unit)
  (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- Same as last KState of finalSumcheck reduction (= relIn)
    Binius.BinaryBasefold.finalSumcheckRelOutProp 𝔽q β
      (input := ⟨⟨stmtIn, oStmtIn⟩, witMid⟩)
  | ⟨1, _⟩ => -- After V sends γ challenges: proximity tests must pass
    let γ_challenges : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩ :=
      tr.challenges ⟨0, rfl⟩
    let fold_challenges := stmtIn.challenges
    logical_proximityChecksSpec 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) (γ_repetitions := γ_repetitions) (γ_challenges := γ_challenges)
      (final_constant := stmtIn.final_constant) (oStmt := oStmtIn) (stmt := stmtIn)

/-- The knowledge state function for the query phase -/
noncomputable def queryKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  (queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions).KnowledgeStateFunction init impl
  (relIn := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
  (relOut := acceptRejectOracleRel)
  (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ)
    γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    queryKStateProp 𝔽q β (ϑ:=ϑ) (γ_repetitions:=γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (m:=m) (tr:=tr) (stmtIn:=stmtIn) (witMid:=witMid) (oStmtIn:=oStmtIn)
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witMid => by rfl
  toFun_next := fun m hDir ⟨stmtMid, oStmtMid⟩ tr msg witMid => by
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, Matrix.cons_val_fin_one,
      Direction.not_V_to_P_eq_P_to_V] at hDir
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
    -- h_relOut: ∃ stmtOut oStmtOut, verifier outputs (stmtOut, oStmtOut) with prob > 0
    --   and ((stmtOut, oStmtOut), witOut) ∈ foldStepRelOut
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, Prod.exists] at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩
    have h_output_mem_V_run_support' :
        some (stmtOut, oStmtOut) ∈
          (do
              let s ← init
              Prod.fst <$>
                (simulateQ impl
                  (Verifier.run (stmtIn, oStmtIn) tr
                    (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
                      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).toVerifier)).run s).support := by
      exact (OptionT.mem_support_iff
        (mx := OptionT.mk (do
          let s ← init
          Prod.fst <$>
            (simulateQ impl
              (Verifier.run (stmtIn, oStmtIn) tr
                (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).toVerifier)).run s))
        (x := (stmtOut, oStmtOut))).1 h_output_mem_V_run_support
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output_mem_V_run_support'
    rcases h_output_mem_V_run_support' with ⟨s, hs_init, h_output_mem_V_run_support_with_s⟩
    -- Apply the main lemma connecting verifier support to logical proximity checks
    have h_res := logical_consistency_checks_passed_of_mem_support_V_run
      (impl := impl) (stmtIn := stmtIn) (oStmtIn := oStmtIn) (tr := tr)
      (s := s) (stmtOut := stmtOut) (oStmtOut := oStmtOut)
      (h_mem_V_run_support := by
        rw [OptionT.mem_support_iff]
        dsimp only [OptionT.mk, OptionT.run]
        exact h_output_mem_V_run_support_with_s
      )
    -- The lemma gives us:
    exact h_res.2.2

/-- **Single Repetition Proximity Check Bound (Proposition 4.23)**

For a single repetition of the proximity check, the probability that a non-compliant
oracle (not close to RS codeword) passes the fold consistency check is bounded by:
  `(1/2) + 1/(2 * 2^𝓡)`

**Preconditions (from Proposition 4.23 in DG25):**
- `h_not_oracleFoldingConsistent`: At least one oracle is non-compliant
- `h_no_bad_event`: No bad folding events occurred (Definition 4.19)

This is the fundamental proximity testing bound used in the soundness proof. -/
theorem prop_4_23_singleRepetition_proximityCheck_bound
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_not_oracleFoldingConsistent : ¬ finalSumcheckStepOracleConsistencyProp 𝔽q β
      (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
      (stmtOut := stmtIn) (oStmtOut := oStmtIn))
    (h_no_bad_event : ¬ blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges)) :
    Pr_{ let v ← $ᵖ ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
      logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn v stmtIn stmtIn.final_constant ] ≤
    queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡) := by
  -- Delegates to Soundness Prop 4.23 (Lemma 4.25 supplies the query-rejection property).
  have h_res :=
    (Binius.BinaryBasefold.prop_4_23_singleRepetition_proximityCheck_bound
      (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (h_not_consistent := h_not_oracleFoldingConsistent)
      (h_no_bad := h_no_bad_event)
      (h_le := by
        apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)))
  dsimp only [queryRbrKnowledgeError_singleRepetition]
  simp only [one_div, mul_inv_rev, ENNReal.coe_add, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_ofNat, ENNReal.coe_mul, pow_eq_zero_iff',
    false_and, ENNReal.coe_pow, ge_iff_le]
  simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_inv,
    ENNReal.coe_ofNat, ENNReal.coe_one] at h_res
  rw [ENNReal.mul_inv (ha := by
    left; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true])
    (hb := by
      left; simp only [ne_eq, ENNReal.ofNat_ne_top, not_false_eq_true]) , mul_comm] at h_res
  exact h_res

theorem singleRepetition_proximityCheck_bound
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_not_oracleFoldingConsistent : ¬ finalSumcheckStepOracleConsistencyProp 𝔽q β
      (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
      (stmtOut := stmtIn) (oStmtOut := oStmtIn))
    (h_no_bad_event : ¬ blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges)) :
    Pr_{ let v ← $ᵖ ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
      logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn v stmtIn stmtIn.final_constant ] ≤
    queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡) := by
  -- This is Proposition 4.23 (DG25) specialized to a single repetition.
  simpa using
    (prop_4_23_singleRepetition_proximityCheck_bound (𝔽q := 𝔽q) (β := β)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (h_not_oracleFoldingConsistent := h_not_oracleFoldingConsistent)
      (h_no_bad_event := h_no_bad_event))

open Classical in
/-! Round-by-round knowledge soundness for the oracle verifier (query phase).

**Proof Strategy (RBR Extraction Failure Event):**

The RBR extraction failure event is: `¬ KState(0) ∧ KState(1)`, i.e.,
  - `¬ finalSumcheckRelOutProp` (KState 0 = FALSE), AND
  - `proximityChecksSpec` (KState 1 = TRUE)

By De Morgan's law:
  `¬ finalSumcheckRelOutProp = ¬ (oracleFoldingConsistency ∨ badEvent)`
                             `= ¬ oracleFoldingConsistency ∧ ¬ badEvent`

This means:
  - `¬ oracleFoldingConsistency`: Some oracle is NOT compliant (not close to correct folding)
  - `¬ badEvent`: No bad events detected

**Proposition 4.23 (DG25 - Assuming no bad events):**
If any of the adversary's oracles is not compliant (not close to RS codeword),
then the verifier accepts with at most negligible probability:
  `Pr[V accepts] ≤ ((1/2) + 1/(2 * 2^𝓡))^γ_repetitions`

This is exactly `queryRbrKnowledgeError`. -/
theorem queryOracleVerifier_rbrKnowledgeSoundness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions).rbrKnowledgeSoundness init impl
    (relIn := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
    (relOut := acceptRejectOracleRel)
    (rbrKnowledgeError := queryRbrKnowledgeError 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  classical
  apply OracleReduction.unroll_rbrKnowledgeSoundness
    (kSF := queryKnowledgeStateFunction 𝔽q β (ϑ:=ϑ) γ_repetitions init impl)
  intro stmtIn_oStmtIn witIn prover j initState
  let P := rbrExtractionFailureEvent
    (kSF := queryKnowledgeStateFunction 𝔽q β (ϑ:=ϑ) γ_repetitions init impl)
    (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (i := j) (stmtIn := stmtIn_oStmtIn)
  rw [OracleReduction.probEvent_soundness_goal_unroll_log' (pSpec := pSpecQuery 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (P := P) (impl := impl) (prover := prover) (i := j)
    (stmt := stmtIn_oStmtIn) (wit := witIn) (s := initState)]
  have h_j_eq_1 : j = ⟨0, rfl⟩ :=
    match j with
    | ⟨0, h0⟩ => rfl
  subst h_j_eq_1
  conv_lhs => simp only [Fin.isValue, Fin.castSucc_zero];
  rw [OracleReduction.soundness_unroll_runToRound_0_pSpec_1_V_to_P
    (prover := prover) (stmtIn := stmtIn_oStmtIn) (witIn := witIn)]
  simp only [Fin.isValue, Challenge,  Matrix.cons_val_zero, ChallengeIdx,
    QueryImpl.addLift_def, QueryImpl.liftTarget_self,  bind_pure_comp,
    liftComp_eq_liftM, simulateQ_bind, simulateQ_map, StateT.run'_eq,
    StateT.run_bind, StateT.run_map, map_bind, Functor.map_map]
  rw [probEvent_bind_eq_tsum]
  -- erw [simulateQ_simOracle2_lift_liftComp_query_T1]
  -- conv =>
  --   enter [1]
  --   erw [probEvent_map]
  --   rw [OracleQuery.cont_apply]
  -- erw [probEvent_bind_eq_tsum]
  apply OracleReduction.ENNReal.tsum_mul_le_of_le_of_sum_le_one
  · -- Bound the conditional probability for each transcript
    intro x
    -- rw [OracleComp.probEvent_map]
    simp only [Fin.isValue, probEvent_map]
    let q : OracleQuery
        [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge]ₒ
        _ := query ⟨⟨0, by rfl⟩, ()⟩
    erw [OracleReduction.probEvent_StateT_run_ignore_state
      (comp := simulateQ (impl.addLift challengeQueryImpl) (liftM (query q.input)))
      (s := x.2)
      (P := fun a => P (x.1.1) (q.cont a))]
    rw [probEvent_eq_tsum_ite]
    erw [simulateQ_query]
    simp only [ChallengeIdx, Challenge, Fin.isValue, monadLift_self,
      QueryImpl.addLift_def, QueryImpl.liftTarget_self, StateT.run'_eq, StateT.run_map,
      Functor.map_map, ge_iff_le]
    have h_L_inhabited : Inhabited L := ⟨0⟩
    conv_lhs =>
      enter [1, x_1, 2, 1, 2]
      rw [addLift_challengeQueryImpl_input_run_eq_liftM_run (impl := impl) (q := q) (s := x.2)]
    erw [StateT.run_monadLift, monadLift_self, liftComp_id]
    rw [bind_pure_comp]
    conv =>
      enter [1, 1, x_1, 2]
      rw [Functor.map_map]
      rw [← probEvent_eq_eq_probOutput]
      rw [probEvent_map]
      rw [OracleQuery.cont_apply]
      dsimp only [MonadLift.monadLift]
      rw [OracleQuery.cont_apply]
      dsimp only [q]
    simp_rw [OracleQuery.input_query, OracleQuery.snd_query]
    conv_lhs => change (∑' (x_1 : (Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0))), _)
    simp only [Function.comp_id]
    conv =>
      enter [1, 1, x_1, 2]
      rw [probEvent_eq_eq_probOutput]
      change Pr[=x_1 | $ᵗ (Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0))]
      rw [OracleReduction.probOutput_uniformOfFintype_eq_Pr (L := _) (x := x_1)]
    rw [OracleReduction.tsum_uniform_Pr_eq_Pr
      (L := (Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)))
      (P := fun x_1 => P x.1.1 (q.2 x_1))]
      -- Now the goal is in do-notation form, which is exactly what Pr_ notation expands to
    -- Make this explicit using change
    conv_lhs => change (∑' (x_1 : (Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0))), _)
    -- Now the goal is in do-notation form, which is exactly what Pr_ notation expands to
    -- Make this explicit using change
    change Pr_{ let y ← $ᵖ (Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)) }[(P x.1.1) y] ≤
      queryRbrKnowledgeError 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, rfl⟩
    -- Factor over independent repetitions using the structure of rbrExtractionFailureEvent
    --
    -- Key observations:
    -- 1. P = rbrExtractionFailureEvent = ∃ witMid : Unit, ¬kSF 0 ... ∧ kSF 1 ...
    -- 2. Since witMid : Unit, the existential is trivial (there's only ())
    -- 3. kSF 1 = logical_proximityChecksSpec = ∀ rep, single_check (challenges rep)
    -- 4. The bound follows from: P y → ∀ rep, single_check (y rep)
    --    So Pr[P y] ≤ Pr[∀ rep, single_check (y rep)] = Pr[single_check c]^γ
    --
    -- Strategy: Use monotonicity of probability, then factor the forall
    obtain ⟨stmtIn, oStmtIn⟩ := stmtIn_oStmtIn
    -- Step 1: Define the single-repetition predicate
    let single_P : ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0) → Prop := fun v =>
      logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtIn v stmtIn
        stmtIn.final_constant
    -- Case split FIRST: if P is empty, handle directly; otherwise extract preconditions
    by_cases h_P_nonempty : ∃ y, P x.1.1 y
    case neg =>
      -- If no y satisfies P x.1.1 y, then Pr[P x.1.1 _] = 0 ≤ bound trivially
      push_neg at h_P_nonempty
      -- Show Pr[P x.1.1 _] = 0 using that P is never true
      calc Pr_{ let y ← $ᵖ (Fin γ_repetitions →
            ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)) }[ P x.1.1 y ]
        _ = Pr_{ let y ← $ᵖ (Fin γ_repetitions →
            ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)) }[ False ] := by
          congr 1; ext y;
          simp only [Fin.isValue, h_P_nonempty, PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind,
            PMF.bind_const, PMF.pure_apply, eq_iff_iff, iff_false, ite_not]
        _ = 0 := by
          simp only [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.bind_const, PMF.pure_apply,
            eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte]
        _ ≤ _ := zero_le _
    case pos =>
      -- P is non-empty: extract preconditions from a witness
      obtain ⟨y₀, h_P_y₀⟩ := h_P_nonempty
      -- Step 2: Show P implies the forall form
      have h_P_implies_forall : ∀ y, P x.1.1 y → (∀ rep : Fin γ_repetitions, single_P (y rep)) := by
        intro y h_P
        unfold rbrExtractionFailureEvent at h_P
        rcases h_P with ⟨witMid, h_kSF_false_before, h_kSF_true_after⟩
        unfold queryKnowledgeStateFunction queryKStateProp logical_proximityChecksSpec
          at h_kSF_true_after
        exact h_kSF_true_after
      -- Step 2b: Extract the preconditions from h_kSF_false_before via De Morgan
      have h_preconditions :
          (¬ finalSumcheckStepOracleConsistencyProp 𝔽q β
            (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
            (stmtOut := stmtIn) (oStmtOut := oStmtIn)) ∧
          (¬ blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
            (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
            (oStmt := oStmtIn) (challenges := stmtIn.challenges)) := by
        -- Use h_P_y₀ to extract preconditions
        -- First substitute P with its definition
        simp only [P] at h_P_y₀
        unfold rbrExtractionFailureEvent at h_P_y₀
        rcases h_P_y₀ with ⟨witMid, h_kSF_false_before, h_kSF_true_after⟩
        unfold queryKnowledgeStateFunction at h_kSF_false_before
        simp only [Fin.castSucc_zero, queryRbrExtractor] at h_kSF_false_before
        unfold queryKStateProp at h_kSF_false_before
        simp only [Prod.mk.injEq] at h_kSF_false_before
        unfold finalSumcheckRelOutProp finalSumcheckStepFoldingStateProp at h_kSF_false_before
        simp only [Prod.fst, Prod.snd] at h_kSF_false_before
        push_neg at h_kSF_false_before
        exact h_kSF_false_before
      obtain ⟨h_not_consistent, h_no_bad⟩ := h_preconditions
      -- Step 3: Apply monotonicity
      apply le_trans (prob_mono (D := $ᵖ (Fin γ_repetitions →
        ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0))) (P x.1.1)
        (fun y => ∀ rep : Fin γ_repetitions, single_P (y rep)) h_P_implies_forall)
      -- Step 4: Factor independent repetitions
      rw [prob_pow_of_forall_finFun (n := γ_repetitions) (P := single_P)]
      -- Step 5: Bound single repetition using singleRepetition_proximityCheck_bound
      have h_single_repetition_bound :
          Pr_{ let v ← $ᵖ ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0) }[ single_P v ] ≤
          queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡) :=
        singleRepetition_proximityCheck_bound 𝔽q β stmtIn oStmtIn h_not_consistent h_no_bad
      -- Step 6: Finalize exponential bound
      unfold queryRbrKnowledgeError
      exact ENNReal.pow_le_pow_left h_single_repetition_bound
  · -- Prove: ∑' x, [=x|transcript computation] ≤ 1
    apply tsum_probOutput_le_one

end FinalQueryRoundIOR
end
end Binius.BinaryBasefold.QueryPhase
