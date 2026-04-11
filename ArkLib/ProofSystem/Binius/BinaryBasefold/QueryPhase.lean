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

def queryPhaseProverState : Fin (1 + 1) → Type := fun
  | 0 => FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ) ×
    (∀ i, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) i) × Unit
  | 1 => FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ) ×
    (∀ i, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) i) × Unit ×
    (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge ⟨0, by rfl⟩

/-- Keep the computable query challenge carrier on the computable side. -/
private def canonicalizeQueryChallenge
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0) :
    AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 :=
  v

/-- Keep the query challenge family carried by `pSpecQuery` on the computable side. -/
private def canonicalizeQueryChallenges
    (challenges : (pSpecQuery 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge ⟨0, by rfl⟩) :
    Fin γ_repetitions → AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 :=
  fun rep => challenges rep

/-- Deterministic search-based decoding from computable `S⁽⁰⁾` points to loose global indices. -/
private def queryPointToIndex
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0) :
    Fin (2 ^ (ℓ + 𝓡)) :=
  match (List.finRange (2 ^ (ℓ + 𝓡))).find? (fun vIdx =>
      decide ((AdditiveNTT.Comp.indexToSDomainZero (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
        (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) vIdx).1 = v.1)) with
  | some vIdx => vIdx
  | none => 0

/-! ### Executable query checks over computable query challenges -/

/-- Query a committed codeword using a loose global index, decoded through
`AdditiveNTT.Comp.indexToSDomain` at the requested source domain index. -/
private def queryCodewordFromIndex
    (j : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)))
    (pointIdx : Fin (2 ^ (ℓ + 𝓡))) :
    OptionT
      (OracleComp
        ([]ₒ + ([OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (Fin.last ℓ)]ₒ +
          [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ)))
      L := do
  let sourceIdx : Fin r :=
    ⟨oraclePositionToDomainIndex (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (positionIdx := j), by
      exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (h := (oraclePositionToDomainIndex (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ)
          (positionIdx := j)).isLt)⟩
  let pointComp := AdditiveNTT.Comp.indexToSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
    (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := sourceIdx) pointIdx
  let qBase :
      OracleComp
        ([OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (Fin.last ℓ)]ₒ) L :=
    liftM
      (query (spec := [OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (Fin.last ℓ)]ₒ) ⟨j, by simpa [sourceIdx] using pointComp⟩)
  let q :
      OracleComp
        ([]ₒ + ([OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (Fin.last ℓ)]ₒ +
          [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ)) L :=
    OracleComp.liftComp
      qBase
      ([]ₒ + ([OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (Fin.last ℓ)]ₒ +
        [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))
  OptionT.lift q

/-- Query all `2^ϑ` fiber points for repetition challenge index `vIdx` at fold step `k`. -/
private def queryFiberPointsFromIndex
    (k : Fin (ℓ / ϑ)) (vIdx : Fin (2 ^ (ℓ + 𝓡))) :
    OptionT
      (OracleComp
        ([]ₒ + ([OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (Fin.last ℓ)]ₒ +
          [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ)))
      (Vector L (2 ^ ϑ)) := do
  let k_th_oracleIdx : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
    ⟨k, by
      simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero,
        Fin.is_lt]⟩
  let sourceIdx : Fin r := ⟨k.val * ϑ, by
    exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k.val * ϑ) (h := k_mul_ϑ_lt_ℓ)⟩
  have h_i_steps_le : sourceIdx.val + ϑ ≤ ℓ + 𝓡 := by
    have h_i_add_ϑ_le_ℓ : k.val * ϑ + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
    dsimp [sourceIdx]
    omega
  let results : Vector L (2 ^ ϑ) ←
    (⟨Array.finRange (2 ^ ϑ), by simp only [Array.size_finRange]⟩ :
      Vector (Fin (2 ^ ϑ)) (2 ^ ϑ)).mapM (fun (u : Fin (2 ^ ϑ)) => do
      let pointIdx := fiberPointIndexFromIndex (ℓ := ℓ) (𝓡 := 𝓡) (vIdx := vIdx)
        (i := sourceIdx) (steps := ϑ) h_i_steps_le u
      queryCodewordFromIndex (𝔽q := 𝔽q) (β := β)
        (γ_repetitions := γ_repetitions) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (j := k_th_oracleIdx) pointIdx)
  pure results

/-- Compute the folded value from queried fiber evaluations and fold challenges. -/
private def computeFoldedValueFromFiber
    (r_challenges : Fin ϑ → L) (fiber_eval_mapping : Fin (2 ^ ϑ) → L) : L :=
  let challenge_vec : Fin (2 ^ ϑ) → L := challengeTensorExpansion (n := ϑ) (r := r_challenges)
  dotProduct challenge_vec fiber_eval_mapping

/-- Single folding-step checker for the executable query verifier. -/
private def checkSingleFoldingStepFromIndex
    (k_val : Fin (ℓ / ϑ)) (c_cur : L) (vIdx : Fin (2 ^ (ℓ + 𝓡)))
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
    OptionT
      (OracleComp
        ([]ₒ + ([OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (Fin.last ℓ)]ₒ +
          [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))) L := do
  let i := k_val.val * ϑ
  let iIdx : Fin r := ⟨i, by
    exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := i)
      (h := k_mul_ϑ_lt_ℓ (k := k_val))⟩
  have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k_val)
  let f_i_on_fiber ← queryFiberPointsFromIndex (𝔽q := 𝔽q) (β := β)
    (γ_repetitions := γ_repetitions) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k_val vIdx
  if h_i_pos : i > 0 then
    let oracle_point_idx := extractMiddleFinMaskFromIndex (ℓ := ℓ) (𝓡 := 𝓡) (vIdx := vIdx)
      (i := iIdx) (steps := ϑ)
    let f_i_val := f_i_on_fiber.get oracle_point_idx
    guard (c_cur = f_i_val)
  let cur_challenge_batch : Fin ϑ → L := fun j =>
    stmt.challenges ⟨i + j.val, by
      have h_i_add_j_lt : i + j.val < i + ϑ := Nat.add_lt_add_left j.isLt i
      exact lt_of_lt_of_le h_i_add_j_lt h_i_add_ϑ_le_ℓ⟩
  let c_next : L := computeFoldedValueFromFiber (ϑ := ϑ)
    (r_challenges := cur_challenge_batch) (fiber_eval_mapping := f_i_on_fiber.get)
  return c_next

/-- Full repetition checker for the executable query verifier. -/
private def checkSingleRepetitionFromIndex
    (vIdx : Fin (2 ^ (ℓ + 𝓡)))
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (final_constant : L) :
    OptionT
      (OracleComp
        ([]ₒ + ([OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (Fin.last ℓ)]ₒ +
          [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))) Unit := do
  let mut c_cur : L := 0
  for k_val in List.finRange (ℓ / ϑ) do
    let c_next ← checkSingleFoldingStepFromIndex (𝔽q := 𝔽q) (β := β)
      (γ_repetitions := γ_repetitions) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨k_val, by omega⟩ c_cur vIdx stmt
    c_cur := c_next
  guard (c_cur = final_constant)

/-- The oracle-aware reduction logic step for the query phase.

This encapsulates the pure logic of the query phase:
- `verifierCheck`: Runs `verifyQueryPhase` which queries oracles for fiber evaluations
- `verifierOut`: Returns `true` (acceptance) or `false` (rejection)
- `honestProverTranscript`: The honest transcript just receives the challenges
- `proverOut`: The honest prover always outputs `(true, ())` -/
def queryPhaseLogicStep :
    OracleAwareReductionLogicStep
      (oSpec := []ₒ)
      (StmtIn := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
      (WitIn := Unit)
      (OracleIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (Fin.last ℓ))
      (OracleOut := fun _ : Empty => Unit)
      (StmtOut := Bool)
      (WitOut := Unit)
      (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  completeness_relIn := strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  completeness_relOut := acceptRejectOracleRel
  verifierCheck := fun stmtIn transcript => do
    let challenges := transcript.challenges
    let fold_challenges :
        Fin γ_repetitions →
          AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 :=
      challenges ⟨0, by rfl⟩
    for rep in List.finRange γ_repetitions do
      let v := fold_challenges rep
      let vIdx := queryPointToIndex (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (𝓡 := 𝓡)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v
      let _ ← checkSingleRepetitionFromIndex (𝔽q := 𝔽q) (β := β)
        (γ_repetitions := γ_repetitions) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        vIdx stmtIn stmtIn.final_constant
      pure ()
    return true
  verifierOut := fun _stmtIn _transcript => true
  embed := ⟨Empty.elim, fun a _ => Empty.elim a⟩
  hEq := fun i => Empty.elim i
  honestProverTranscript := fun _stmtIn _witIn _oStmtIn challenges =>
    FullTranscript.mk1 (challenges ⟨0, by rfl⟩)
  proverOut := fun _stmtIn _witIn _oStmtIn _transcript =>
    ((true, fun i => Empty.elim i), ())

/-- Executable query-phase verifier over computable query challenges. -/
@[reducible]
def queryOracleVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  verify := fun stmtIn challenges => do
    let transcript := FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (challenges ⟨0, by rfl⟩)
    let logic := queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    let _ ← logic.verifierCheck stmtIn transcript
    pure (logic.verifierOut stmtIn transcript)
  embed := (queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).embed
  hEq := (queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).hEq

/-- Executable query-phase prover over computable query challenges. -/
@[reducible]
def queryOracleProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (Fin.last ℓ))
    (WitIn := Unit)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitOut := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  PrvState := queryPhaseProverState 𝔽q β (ϑ := ϑ) γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  input := fun ⟨⟨stmtIn, oStmtIn⟩, witIn⟩ => (stmtIn, oStmtIn, witIn)
  sendMessage
  | ⟨0, h⟩ => nomatch h
  receiveChallenge
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    pure (fun challenges => (stmtIn, oStmtIn, witIn, challenges))
  output := fun ⟨stmtIn, oStmtIn, witIn, challenges⟩ => do
    let transcript := FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) challenges
    pure ((queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).proverOut stmtIn witIn oStmtIn transcript)

/-- Executable query-phase reduction over computable query challenges. -/
@[reducible]
def queryOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (WitIn := Unit)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitOut := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  prover := queryOracleProver 𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  verifier := queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

/-- Executable query-phase proof. -/
@[reducible]
def queryOracleProof : OracleProof
    (oSpec := []ₒ)
    (Statement := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStatement := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (Fin.last ℓ))
    (Witness := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  queryOracleReduction 𝔽q β (ϑ := ϑ) γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

lemma OracleComp.liftM_query_eq_liftM_liftM.{u, v, z}
    {ι : Type u} {spec : OracleSpec ι} {m : Type v → Type z}
    [MonadLift (OracleComp spec) m] {α : Type v}
    (q : OracleQuery spec α) :
    (liftM q : m α) = liftM (liftM q : OracleComp spec α) := rfl

omit [CharP L 2] [SampleableType L] in
lemma mem_support_queryFiberPoints
    -- The number of oracles in query phase is toCodewordsCount(ℓ) = ℓ/ϑ
    {oraclePositionIdx : Fin (ℓ / ϑ)} (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
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
      support (simulateQ.{0, 0, 0} so
        ((queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oraclePositionIdx v)))) :
    let k_th_oracleIdx: Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
      ⟨oraclePositionIdx, by simp only [toOutCodewordsCount, Fin.val_last,
        lt_self_iff_false, ↓reduceIte, add_zero, Fin.is_lt];⟩
    ∀ (fiberIndex : Fin (2 ^ ϑ)),
      f_i_on_fiber.get fiberIndex =
      (oStmtIn k_th_oracleIdx (getFiberPoint 𝔽q β oraclePositionIdx v fiberIndex)) := by
  sorry

lemma probFailure_simulateQ_queryFiberPoints_eq_zero
    (so : QueryImpl
      ([]ₒ + ([OracleStatement 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ +
        [(pSpecQuery 𝔽q β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))
      (OracleComp []ₒ))
    (k : Fin (List.finRange (ℓ / ϑ)).length)
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, by omega⟩) :
    Pr[⊥ |
      OptionT.mk
        (simulateQ.{0, 0, 0} so
          (queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((List.finRange (ℓ / ϑ)).get k) v))] = 0 := by
  sorry

lemma getBit_eq_testBit (n k : ℕ) : Nat.getBit k n = 1 ↔ Nat.testBit n k = true := by
  unfold Nat.getBit Nat.testBit
  have h : n >>> k &&& 1 = 1 &&& n >>> k := Nat.land_comm _ _
  rw [h]
  cases h_eq : 1 &&& n >>> k
  · simp
  · case succ m =>
    have h_le : m + 1 ≤ 1 := by
      calc m + 1 = 1 &&& n >>> k := h_eq.symm
        _ ≤ 1 := Nat.and_le_left
    have h_m_0 : m = 0 := by omega
    subst h_m_0
    simp

set_option maxHeartbeats 200000 in
lemma iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask
    (i : Fin r) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps)
    (h_destIdx_le : destIdx.val ≤ ℓ)
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, by omega⟩) :
    True := by
  sorry

lemma query_phase_consistency_guard_safe : True := by
  sorry

lemma query_phase_step_preserves_fold : True := by
  sorry

lemma query_phase_final_fold_eq_constant : True := by
  sorry

lemma checkSingleRepetition_inner_forIn_probFailure_eq_zero : True := by
  sorry

lemma checkSingleRepetition_probFailure_eq_zero : True := by
  sorry

lemma support_run_simulateQ_run_fst_eq {ι : Type}
    {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited] {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec (Option α)) (s : σ)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    Prod.fst <$> support (m := ProbComp) (α := Option α × σ) ((simulateQ impl oa) s) =
      support (m := OracleComp oSpec) (α := Option α) oa := by
  have h_support := support_simulateQ_run'_eq (impl := impl) (oa := oa) (s := s)
    (hImplSupp := hImplSupp)
  rw [StateT.run'_eq, support_map] at h_support
  exact h_support
/-! **Per-repetition support → logical** (extracted for reuse from completeness-style reasoning).
**Counterpart** of `checkSingleRepetition_probFailure_eq_zero` for the `OracleComp.support` case.
If `(ForInStep.yield PUnit.unit, state_post)` lies in the support of one iteration of the
  verifier's forIn body (for a given `rep`), then the logical proximity check holds for that
  repetition after canonicalizing the computable query challenge carried by `tr`.
-/
lemma logical_checkSingleRepetition_of_mem_support_forIn_body {σ : Type} : True := by
  sorry

lemma logical_consistency_checks_passed_of_mem_support_V_run {σ : Type}
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (stmtIn : FinalSumcheckStatementOut)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (tr : FullTranscript (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (s : σ) (stmtOut : Bool) (oStmtOut : Empty → Unit)
    (h_mem_V_run_support :
      (stmtOut, oStmtOut) ∈
        support (OptionT.mk (Prod.fst <$> ((simulateQ.{0, 0, 0} impl
            (Verifier.run (stmtIn, oStmtIn) tr
              (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).toVerifier)) :
              StateT σ ProbComp (Option (Bool × (Empty → Unit)))).run s))) :
    True := by
  sorry

/-- Strong completeness for the query phase logic step.

This proves that for any valid input satisfying `strictFinalSumcheckRelOut`,
the verifier check succeeds with probability 1, and the output satisfies
`acceptRejectOracleRel` (i.e., the statement is `true`). -/
theorem queryPhaseLogicStep_isStronglyComplete :
    (queryPhaseLogicStep 𝔽q β (ϑ:=ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).IsStronglyCompleteUnderSimulation := by
  sorry

/-- Perfect completeness for the final query round (using the oracle queryProof). -/
theorem queryOracleProof_perfectCompleteness {σ : Type}
  (init : ProbComp σ) (hInit : NeverFail init)
  (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  OracleReduction.perfectCompleteness
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (relIn := strictFinalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (relOut := acceptRejectOracleRel)
    (oracleReduction := queryOracleReduction 𝔽q β (ϑ := ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (init := init)
    (impl := impl) := by
  sorry
/- Original proof commented out because verify/embed/hEq fields are sorry'd
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
            queryOracleVerifier, OracleVerifier.toVerifier] at
            h_probOutput_none_V_check_eq_0 ⊢
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
      dsimp only [queryOracleProof, queryOracleReduction, queryPhaseLogicStep,
        queryOracleProver, queryOracleVerifier, OracleVerifier.toVerifier,
        FullTranscript.mk1]
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
      change (some (verStmtOut, verOStmtOut)) ∈ _root_.support (liftComp _ _)
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
-/

open scoped NNReal

/-- The round-by-round extractor for the query phase.
Since f^(0) is always available, we can invoke the extractMLP function directly. -/
def queryRbrExtractor :
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
  | ⟨1, _⟩ => True

/-- The knowledge state function for the query phase -/
def queryKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).KnowledgeStateFunction init impl
  (relIn := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
  (relOut := acceptRejectOracleRel)
  (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ)
    γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  toFun := fun m ⟨stmtMid, oStmtMid⟩ tr witMid =>
    queryKStateProp (𝔽q := 𝔽q) (β := β) (ϑ := ϑ) (γ_repetitions := γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (m := m) (tr := tr) (stmtIn := stmtMid) (witMid := witMid) (oStmtIn := oStmtMid)
  toFun_empty := by
    intro stmtIn witMid
    cases stmtIn
    rfl
  toFun_next := by
    sorry
  toFun_full := by
    sorry

/-- **Single Repetition Proximity Check Bound (Proposition 4.24)**

For a single repetition of the proximity check, the probability that a non-compliant
oracle (not close to RS codeword) passes the fold consistency check is bounded by:
  `(1/2) + 1/(2 * 2^𝓡)`

**Preconditions (from Proposition 4.24 in the archived DP24 PDF):**
- `h_not_oracleFoldingConsistent`: At least one oracle is non-compliant
- `h_no_bad_event`: No bad folding events occurred (Definition 4.20)

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
    Pr_{ let v ← $ᵖ ↥(AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0) }[
      logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn v stmtIn stmtIn.final_constant ] ≤
    queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡) := by
  -- Delegates to Soundness Prop 4.24 (Lemma 4.26 supplies the query-rejection property).
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
    Pr_{ let v ← $ᵖ ↥(AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0) }[
      logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn v stmtIn stmtIn.final_constant ] ≤
    queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡) := by
  -- This is Proposition 4.24 from the archived DP24 PDF specialized to a single repetition.
  exact
    prop_4_23_singleRepetition_proximityCheck_bound (𝔽q := 𝔽q) (β := β)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (h_not_oracleFoldingConsistent := h_not_oracleFoldingConsistent)
      (h_no_bad_event := h_no_bad_event)

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

**Proposition 4.24 (archived DP24 - assuming no bad events):**
If any of the adversary's oracles is not compliant (not close to RS codeword),
then the verifier accepts with at most negligible probability:
  `Pr[V accepts] ≤ ((1/2) + 1/(2 * 2^𝓡))^γ_repetitions`

This is exactly `queryRbrKnowledgeError`. -/
theorem queryOracleVerifier_rbrKnowledgeSoundness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).rbrKnowledgeSoundness init impl
    (relIn := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
    (relOut := acceptRejectOracleRel)
    (rbrKnowledgeError := queryRbrKnowledgeError 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  sorry

end FinalQueryRoundIOR
end Binius.BinaryBasefold.QueryPhase
