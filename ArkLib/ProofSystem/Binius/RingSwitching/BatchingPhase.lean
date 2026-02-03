/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.RingSwitching.Prelude
import ArkLib.ProofSystem.Binius.RingSwitching.Spec
import ArkLib.OracleReduction.Basic
import ArkLib.OracleReduction.Completeness
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import CompPoly.Fields.Binary.Tower.TensorAlgebra
import ArkLib.Data.Probability.Instances

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Module Binius.BinaryBasefold TensorProduct Nat Matrix ProbabilityTheory
open scoped NNReal

/-!
# Ring-Switching IOP Batching Phase

This module implements the Batching Phase of the ring-switching IOP: steps 1-5.
This phase is the initial phase of the Interactive Oracle Proof and consists of:

## Construction 3.1 - Steps 1-5 (Batching Phase)

We define `(P, V)` as the following IOP, in which both parties have the common
input `[f]`, `s ∈ L`, and `(r_0, ..., r_{ℓ-1}) ∈ L^ℓ`, and `P` has the further
input `t(X_0, ..., X_{ℓ-1}) ∈ K[X_0, ..., X_{ℓ-1}]^⪯1`.

1. `P` computes `ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1}))` and sends `V` the A-element `ŝ`.
2. `V` decomposes `ŝ =: Σ_{v ∈ {0,1}^κ} ŝ_v ⊗ β_v`.
  `V` requires `s ?= Σ_{v ∈ {0,1}^κ} eq̃(v_0, ..., v_{κ-1}, r_0, ..., r_{κ-1}) ⋅ ŝ_v`.
3. `V` samples batching scalars `(r''_0, ..., r''_{κ-1}) ← L^κ` and sends them to `P`.
4. For each `w ∈ {0,1}^{ℓ'}`,
  `P` decomposes `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})`
    `=: Σ_{u ∈ {0,1}^κ} A_{w, u} ⋅ β_u`.
  `P` defines the function
    `A: w ↦ Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ A_{w, u}`
    on `{0,1}^{ℓ'}` and writes `A(X_0, ..., X_{ℓ'-1})` for its multilinear extension.
  `P` defines `h(X_0, ..., X_{ℓ'-1}) := A(X_0, ..., X_{ℓ'-1}) ⋅ t'(X_0, ..., X_{ℓ'-1})`.c
5. `V` decomposes `ŝ =: Σ_{u ∈ {0,1}^κ} β_u ⊗ ŝ_u`, and
  sets `s_0 := Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ ŝ_u`.

Input: `witIn =  BatchingWitIn, stmtIn = BatchingStmtIn, oStmt = aOStmtIn.OStmtIn`

Output: `witOut = (Statement (L := L) (ℓ := ℓ')`
  `(RingSwitchingBaseContext κ L K ℓ) 0) × (SumcheckWitness L ℓ' 0), oStmt = aOStmtIn.OStmtIn`
-/

noncomputable section
namespace Binius.RingSwitching.BatchingPhase

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (β : Basis (Fin κ → Fin 2) K L)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable {𝓑 : Fin 2 ↪ L}
variable (aOStmtIn : AbstractOStmtIn L ℓ')

/-! ## Formalized Helper Functions
These functions provide concrete implementations for tensor algebra operations
and other logic required by the protocol.
-/

/-- A dummy state returned by the verifier upon failure of Check 1. -/
def failureState (stmt : BatchingStmtIn L ℓ) (s_hat : TensorAlgebra K L) :
  Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0 := {
    ctx := {
      t_eval_point := stmt.t_eval_point,
      original_claim := stmt.original_claim
      s_hat := s_hat,
      r_batching := 0, -- Dummy value
    },
    sumcheck_target := 0,
    challenges := Fin.elim0
  }

/-! ## Relations -/

def batchingInputRelationProp (stmt : BatchingStmtIn L ℓ)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) (wit : BatchingWitIn L K ℓ ℓ') : Prop :=
  wit.t' = packMLE κ L K ℓ ℓ' h_l β wit.t ∧ stmt.original_claim = wit.t.val.aeval stmt.t_eval_point
  ∧ aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩

def strictBatchingInputRelationProp (stmt : BatchingStmtIn L ℓ)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) (wit : BatchingWitIn L K ℓ ℓ') : Prop :=
  wit.t' = packMLE κ L K ℓ ℓ' h_l β wit.t ∧ stmt.original_claim = wit.t.val.aeval stmt.t_eval_point
  ∧ aOStmtIn.strictInitialCompatibility ⟨wit.t', oStmt⟩

/-- Input relation: the witness `t` and `t'` are consistent,
and `t` satisfies the original claim. -/
def batchingInputRelation :
  Set ((BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)) × BatchingWitIn L K ℓ ℓ') :=
  {⟨⟨stmt, oStmt⟩, wit⟩ | batchingInputRelationProp κ L K β ℓ ℓ' h_l aOStmtIn stmt oStmt wit }

/-- Strict input relation for completeness proofs. -/
def strictBatchingInputRelation :
  Set ((BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)) × BatchingWitIn L K ℓ ℓ') :=
  {⟨⟨stmt, oStmt⟩, wit⟩ |
    strictBatchingInputRelationProp κ L K β ℓ ℓ' h_l aOStmtIn stmt oStmt wit }

omit [NeZero κ] [Fintype L] [DecidableEq L] [CharP L 2] [SelectableType L] [Fintype K]
  [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
lemma strictBatchingInputRelation_subset_batchingInputRelation :
    strictBatchingInputRelation κ L K β ℓ ℓ' h_l aOStmtIn ⊆
      batchingInputRelation κ L K β ℓ ℓ' h_l aOStmtIn := by
  intro input h_input
  rcases input with ⟨⟨stmt, oStmt⟩, wit⟩
  rcases h_input with ⟨h_pack, h_claim, h_strict_compat⟩
  exact ⟨h_pack, h_claim,
    aOStmtIn.strictInitialCompatibility_implies_initialCompatibility oStmt wit.t' h_strict_compat⟩

/-! ## Pure Logic Functions (ReductionLogicStep Infrastructure) -/

/-- Pure verifier check: validates that the prover's ŝ satisfies Check 1.
This is extracted from the monadic verifier for use in ReductionLogicStep. -/
@[reducible]
def batchingVerifierCheck (stmtIn : BatchingStmtIn L ℓ) (msg0 : TensorAlgebra K L) : Prop :=
  performCheckOriginalEvaluation κ L K β ℓ ℓ' h_l
    stmtIn.original_claim stmtIn.t_eval_point msg0 = true

/-- Pure verifier output: computes the output statement given the transcript.
This is extracted from the monadic verifier for use in ReductionLogicStep. -/
@[reducible]
def batchingVerifierStmtOut (stmtIn : BatchingStmtIn L ℓ)
    (msg0 : TensorAlgebra K L) (r_batching : Fin κ → L) :
    Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0 :=
  let s₀ := compute_s0 κ L K β msg0 r_batching
  let ctx : RingSwitchingBaseContext κ L K ℓ := {
    t_eval_point := stmtIn.t_eval_point,
    original_claim := stmtIn.original_claim,
    s_hat := msg0,
    r_batching := r_batching
  }
  {
    ctx := ctx,
    sumcheck_target := s₀,
    challenges := Fin.elim0
  }

/-- Pure prover message computation: computes ŝ from the witness.
This is extracted from the monadic prover for use in ReductionLogicStep. -/
@[reducible]
def batchingProverComputeMsg (stmtIn : BatchingStmtIn L ℓ) (witIn : BatchingWitIn L K ℓ ℓ') :
    TensorAlgebra K L :=
  embedded_MLP_eval κ L K ℓ ℓ' h_l witIn.t' stmtIn.t_eval_point

/-- Pure prover output: computes the output witness given the transcript.
This is extracted from the monadic prover for use in ReductionLogicStep. -/
@[reducible]
def batchingProverWitOut (stmtIn : BatchingStmtIn L ℓ) (witIn : BatchingWitIn L K ℓ ℓ')
    (msg0 : TensorAlgebra K L) (r_batching : Fin κ → L) :
    SumcheckWitness L ℓ' 0 :=
  let ctx : RingSwitchingBaseContext κ L K ℓ := {
    t_eval_point := stmtIn.t_eval_point,
    original_claim := stmtIn.original_claim,
    s_hat := msg0,
    r_batching := r_batching
  }
  let h_poly : ↥L⦃≤ 2⦄[X Fin ℓ'] :=
    projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witIn.t')
      (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly (ctx := ctx))
      (i := 0) (challenges := Fin.elim0)
  {
    t' := witIn.t',
    H := h_poly
  }

/-! ## ReductionLogicStep Instance -/

/-- The Logic Instance for the Batching Phase.
This encapsulates the pure logic of the batching phase, separating it from
the monadic oracle operations. -/
def batchingStepLogic :
    Binius.BinaryBasefold.ReductionLogicStep
      -- In/Out Types
      (BatchingStmtIn L ℓ)
      (BatchingWitIn L K ℓ ℓ')
      (aOStmtIn.OStmtIn)
      (aOStmtIn.OStmtIn)
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
      (SumcheckWitness L ℓ' 0)
      -- Protocol Spec
      (pSpecBatching (κ:=κ) (L:=L) (K:=K))
      where

  -- 1. Relations (using strict relations for completeness)
  completeness_relIn := fun ((s, o), w) =>
    ((s, o), w) ∈ strictBatchingInputRelation κ L K β ℓ ℓ' h_l aOStmtIn
  completeness_relOut := fun ((s, o), w) =>
    ((s, o), w) ∈ strictSumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn 0

  -- 2. Verifier Logic (Using extracted kernels)
  verifierCheck := fun stmtIn transcript =>
    batchingVerifierCheck (κ:=κ) (L:=L) (K:=K) (β:=β) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l) (stmtIn := stmtIn) (transcript.messages ⟨0, rfl⟩)

  verifierOut := fun stmtIn transcript =>
    batchingVerifierStmtOut (κ:=κ) (L:=L) (K:=K) (β:=β) (ℓ:=ℓ) (ℓ':=ℓ') (stmtIn := stmtIn) (msg0 := transcript.messages ⟨0, rfl⟩) (r_batching := transcript.challenges ⟨1, rfl⟩)

  -- 2b. Oracle Embedding (must match oracleVerifier)
  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun i => rfl

  -- 3. Honest Prover Logic (Constructing the transcript)
  honestProverTranscript := fun stmtIn witIn _oStmtIn chal =>
    let msg : TensorAlgebra K L := batchingProverComputeMsg (κ := κ) (L := L) (K := K) (ℓ := ℓ)
      (ℓ' := ℓ') (h_l := h_l) stmtIn witIn
    FullTranscript.mk2 msg (chal ⟨1, rfl⟩)

  -- 4. Prover Output (State Update)
  proverOut := fun stmtIn witIn oStmtIn transcript =>
    let msg0 : TensorAlgebra K L := transcript.messages ⟨0, rfl⟩
    let r_batching : Fin κ → L := transcript.challenges ⟨1, rfl⟩
    let stmtOut := batchingVerifierStmtOut (κ:=κ) (L:=L) (K:=K) (β:=β) (ℓ:=ℓ) (ℓ':=ℓ')
      (stmtIn := stmtIn) (msg0 := msg0) (r_batching := r_batching)
    let witOut := batchingProverWitOut (κ:=κ) (L:=L) (K:=K) (β:=β) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l)
      (stmtIn := stmtIn) (witIn := witIn) (msg0 := msg0) (r_batching := r_batching)
    ((stmtOut, oStmtIn), witOut)

/-! ## Strong Completeness Theorem -/

/-- The Main Lemma: Batching Phase satisfies Strong Completeness.

This proves that for any valid input satisfying `batchingInputRelation`, the honest
prover-verifier interaction correctly computes ŝ, performs Check 1, and produces
a valid output satisfying `sumcheckRoundRelation 0`.

**Proof Structure:**
- Verifier check: Uses the definition of `performCheckOriginalEvaluation` and properties
  of `embedded_MLP_eval` and `packMLE`.
- Output relation: Uses properties of `compute_s0`, `projectToMidSumcheckPoly`, and the
  witness structural invariant.
- Agreement: Prover and verifier agree on output statements and oracles by construction.
-/
lemma batchingStep_is_logic_complete :
    (batchingStepLogic (κ := κ) (L := L) (K := K) (β := β) (𝓑 := 𝓑) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (aOStmtIn := aOStmtIn)).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := (batchingStepLogic (κ := κ) (L := L) (K := K) (β := β) (𝓑 := 𝓑) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (aOStmtIn := aOStmtIn))
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
    oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2

  -- Extract properties from h_relIn (strictBatchingInputRelation)
  simp only [batchingStepLogic, strictBatchingInputRelation, strictBatchingInputRelationProp,
    Set.mem_setOf_eq] at h_relIn
  obtain ⟨h_t'_eq_t_packed, h_original_evaluation_claim, h_compat⟩ := h_relIn

  -- The message computed by the honest prover
  let msg0 := batchingProverComputeMsg κ L K ℓ ℓ' h_l stmtIn witIn
  let r_batching := challenges ⟨1, rfl⟩

  have h_s_hat_eq : transcript.messages ⟨0, rfl⟩ = embedded_MLP_eval κ L K ℓ ℓ' h_l
    (packMLE κ L K ℓ ℓ' h_l β witIn.t) stmtIn.t_eval_point := by
    dsimp only [transcript, step, batchingStepLogic]
    unfold FullTranscript.mk2
    dsimp only [batchingProverComputeMsg]
    rw [h_t'_eq_t_packed]

  -- Fact 1: Verifier check passes
  let hVCheck_passed : step.verifierCheck stmtIn transcript := by
    simp only [step, batchingStepLogic, batchingVerifierCheck]
    let res := batching_check_correctness (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
      (ℓ' := ℓ') (h_l := h_l) (t := witIn.t) (eval_point := stmtIn.t_eval_point)
    rw [←h_s_hat_eq] at res
    rw [h_original_evaluation_claim]
    exact res

  -- Fact 2: Output relation holds (strictSumcheckRoundRelation 0)
  let hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    simp only [step, batchingStepLogic, strictSumcheckRoundRelation, strictSumcheckRoundRelationProp,
      Set.mem_setOf_eq]
    -- batching_target_consistency
    dsimp only [masterStrictKStateProp, Fin.coe_ofNat_eq_mod];
    constructor
    · -- ⊢ sumcheckConsistencyProp verifierStmtOut.sumcheck_target proverWitOut.H
        exact batching_target_consistency κ L K β ℓ ℓ' h_l (𝓑:=𝓑) witIn.t'
          (transcript.messages ⟨0, rfl⟩) r_batching verifierStmtOut.ctx
    · constructor
      · -- ⊢ witnessStructuralInvariant κ L K β ℓ ℓ' h_l verifierStmtOut proverWitOut
        rfl
      · -- ⊢ aOStmtIn.initialCompatibility (proverWitOut.t', verifierOStmtOut)
        exact h_compat

  -- Fact 3: Prover and verifier statements agree
  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    simp only [step, batchingStepLogic, proverStmtOut, verifierStmtOut]
    rfl

  -- Fact 4: Prover and verifier oracle statements agree
  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by
    simp only [step, batchingStepLogic, proverOStmtOut, verifierOStmtOut]
    funext j
    simp only [OracleVerifier.mkVerifierOStmtOut]
    -- Oracle statements are unchanged (all map via Sum.inl)
    rfl

  -- Combine all facts
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hVCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

/-! ## Prover and Verifier Implementation -/

/-- The state maintained by the prover throughout the batching phase. -/
def PrvState : Fin (2 + 1) → Type
  | ⟨0, _⟩ => BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j) × BatchingWitIn L K ℓ ℓ'
  | ⟨1, _⟩ => BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)
    × BatchingWitIn L K ℓ ℓ' × TensorAlgebra K L
  | _      => BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)
    × BatchingWitIn L K ℓ ℓ' × TensorAlgebra K L × (Fin κ → L)

noncomputable def batchingOracleProver :
  OracleProver (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn L ℓ) (OStmtIn := aOStmtIn.OStmtIn) (WitIn := BatchingWitIn L K ℓ ℓ')
    (StmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ) 0) (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' 0)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K)) where
  PrvState := PrvState κ L K ℓ ℓ' aOStmtIn

  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)

  sendMessage
    | ⟨0, _⟩ => fun (stmt, oStmt, wit) => do
      -- USE THE SHARED KERNEL (Guarantees match with batchingStepLogic)
      let s_hat := batchingProverComputeMsg (κ:=κ) (L:=L) (K:=K) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l) stmt wit
      return ⟨s_hat, (stmt, oStmt, wit, s_hat)⟩
    | ⟨1, h⟩ => fun _ => do nomatch h -- V to P round

  receiveChallenge
    | ⟨0, h⟩ => nomatch h -- i.e. contradiction
    | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, s_hat⟩ => do
      return fun r_batching => (stmt, oStmt, wit, s_hat, r_batching)

  output := fun ⟨stmt, oStmt, wit, (s_hat : TensorAlgebra K L), (r_batching : Fin κ → L)⟩ => do
    -- Construct the transcript that the honest prover produces
    -- This matches logic.honestProverTranscript exactly
    let logic := (batchingStepLogic (κ := κ) (L := L) (K := K) (β := β) (𝓑 := 𝓑) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (aOStmtIn := aOStmtIn))
    let challenges : (pSpecBatching (κ:=κ) (L:=L) (K:=K)).Challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 => exact False.elim (by simp only [ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue,
          cons_val_zero, Direction.not_P_to_V_eq_V_to_P] at hj)  -- No challenge at index 0
        | 1 => exact r_batching
    let t := logic.honestProverTranscript stmt wit oStmt challenges
    -- Delegate to Logic Instance (ensures consistency with batchingStepLogic)
    pure (logic.proverOut stmt wit oStmt t)

open Classical in
noncomputable def batchingOracleVerifier :
  OracleVerifier (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn L ℓ) (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K)) where
  verify | stmtIn, pSpec_batching_challenges => do
     -- Query ŝ from Message 0.
    let s_hat : TensorAlgebra K L ← query (spec := [pSpecBatching (κ:=κ)
      (L:=L) (K:=K).Message]ₒ) ⟨⟨0, by rfl⟩, (by simpa using ())⟩
    let r_batching : Fin κ → L := pSpec_batching_challenges ⟨1, by rfl⟩
    -- Reconstruct the transcript (matches what honestProverTranscript produces)
    let logic := (batchingStepLogic (κ := κ) (L := L) (K := K) (β := β) (𝓑 := 𝓑) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (aOStmtIn := aOStmtIn))
    -- Note: We can't call honestProverTranscript directly because we don't have the witness
    -- But we know the transcript structure must match it
    let t := FullTranscript.mk2 s_hat r_batching
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)

  -- Reuse embed and hEq from batchingStepLogic to ensure consistency
  embed := (batchingStepLogic (κ := κ) (L := L) (K := K) (β := β) (𝓑 := 𝓑) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (aOStmtIn := aOStmtIn)).embed
  hEq := (batchingStepLogic (κ := κ) (L := L) (K := K) (β := β) (𝓑 := 𝓑) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (aOStmtIn := aOStmtIn)).hEq

/-- The Oracle Reduction for the Batching Phase. -/
noncomputable def batchingOracleReduction : OracleReduction (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn L ℓ) (OStmtIn := aOStmtIn.OStmtIn) (WitIn := BatchingWitIn L K ℓ ℓ')
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' 0)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K)) where
  prover := batchingOracleProver κ L K β ℓ ℓ' h_l (𝓑:=𝓑) (aOStmtIn:=aOStmtIn)
  verifier := batchingOracleVerifier κ L K β ℓ ℓ' h_l (𝓑:=𝓑) (aOStmtIn:=aOStmtIn)

/-! ## RBR Knowledge Soundness Components -/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Intermediate witness types for RBR knowledge soundness. -/
def batchingWitMid : Fin (2 + 1) → Type
  | ⟨0, _⟩ => BatchingWitIn L K ℓ ℓ'       -- Before any messages
  | ⟨1, _⟩ => BatchingWitIn L K ℓ ℓ'       -- After P sends ŝ
  | ⟨2, _⟩ => SumcheckWitness L ℓ' 0          -- After V sends r'' and all computations are done

/-- RBR extractor for the batching phase. -/
noncomputable def batchingRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := BatchingWitIn L K ℓ ℓ')
    (WitOut := SumcheckWitness L ℓ' 0)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K))
    (WitMid := batchingWitMid L K ℓ ℓ') where
  eqIn := rfl
  extractMid m _ _ witSucc :=
    match m with
    | ⟨0, _⟩ => witSucc -- Extracting `WitIn` from a future `WitIn`
    | ⟨1, _⟩ => by
      exact { t := unpackMLE κ L K ℓ ℓ' h_l β witSucc.t', t' := witSucc.t' }
  extractOut _ _ witOut := witOut

/-- RBR knowledge soundness error for the batching phase.
The only verifier randomness is `r''`. A collision has probability related to `κ/|L|`.
For simplicity, we can set a placeholder value. -/
def batchingRBRKnowledgeError : ℝ≥0 := (κ : ℝ≥0) / (Fintype.card L : ℝ≥0) -- Schwartz-Zippel error

def batchingKStateProp {m : Fin (2 + 1)}
    (tr : Transcript m (pSpecBatching (κ := κ) (L := L) (K := K)))
    (stmt : BatchingStmtIn L ℓ) (witMid : batchingWitMid L K ℓ ℓ' m)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) :
    Prop :=
  match m with
  | ⟨0, _⟩ => -- equiv s relIn
    batchingInputRelationProp κ L K β ℓ ℓ' h_l aOStmtIn stmt oStmt witMid
  | ⟨1, _⟩ => by -- P sends ŝ
    let s_hat : TensorAlgebra K L := tr.messages ⟨0, rfl⟩
    exact
      witMid.t' = packMLE κ L K ℓ ℓ' h_l β witMid.t -- implied by `extractMid`
      -- `P's computation: ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1}))`
      ∧ embedded_MLP_eval κ L K ℓ ℓ' h_l witMid.t' stmt.t_eval_point = s_hat
      -- The last two constraints are equivalent to `t(r) = s`
      -- `V's check: s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v.`
      ∧ performCheckOriginalEvaluation κ L K β ℓ ℓ' h_l stmt.original_claim
        stmt.t_eval_point s_hat -- local V check
      -- The passed-through oracle compatibility condition of `t'`, i.e. carried through the whole ring-switching protocol
      ∧ aOStmtIn.initialCompatibility ⟨witMid.t', oStmt⟩
  | ⟨2, _⟩ => by -- implied by relOut
    simp only [batchingWitMid] at witMid
    let s_hat : TensorAlgebra K L := tr.messages ⟨0, rfl⟩
    let batching_challenges : Fin κ → L := tr.challenges ⟨1, rfl⟩
    let ctx : RingSwitchingBaseContext κ L K ℓ := {
      t_eval_point := stmt.t_eval_point,
      original_claim := stmt.original_claim,
      s_hat := s_hat,
      r_batching := batching_challenges
    }
    let stmtOut : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0 := {
      ctx := ctx,
      sumcheck_target := compute_s0 κ L K β s_hat batching_challenges,
      challenges := Fin.elim0
    }
    let witOut : SumcheckWitness L ℓ' 0 := {
      t' := witMid.t',
      H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witMid.t')
        (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly (ctx := ctx))
        (i := 0) (challenges := Fin.elim0)
    }
    exact
      sumcheckRoundRelationProp κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn (i:=0) stmtOut oStmt witOut
      ∧ performCheckOriginalEvaluation κ L K β ℓ ℓ' h_l stmt.original_claim
        stmt.t_eval_point s_hat -- local V check (kept in m=2 for doom proof; see batching_doom_escape_probability_bound)
      ∧ aOStmtIn.initialCompatibility ⟨witMid.t', oStmt⟩

/-- Knowledge state function for the batching phase. -/
noncomputable def batchingKnowledgeStateFunction :
  (batchingOracleVerifier κ L K β ℓ ℓ' h_l (𝓑:=𝓑) (aOStmtIn:=aOStmtIn)).KnowledgeStateFunction init impl
    (relIn := batchingInputRelation κ L K β ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn 0)
    (batchingRbrExtractor κ L K β ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)) where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    batchingKStateProp κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn tr stmt witMid oStmt
  toFun_empty _ _ := by rfl
  toFun_next := fun m hDir stmtIn tr msg witMid => by
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => simp only [ne_eq, reduceCtorEq, not_false_eq_true, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Direction.not_V_to_P_eq_P_to_V] at hDir
    subst h_m_eq_0
    intro hSuccTrue
    unfold batchingKStateProp at hSuccTrue ⊢
    simp only [Fin.zero_eta, Fin.isValue, Fin.succ_zero_eq_one, Fin.castSucc_zero,
      batchingRbrExtractor, Fin.mk_one, Fin.succ_one_eq_two] at hSuccTrue ⊢
    obtain ⟨h_t'_eq, h_embed_eq, h_check_true, h_compat⟩ := hSuccTrue
    simp only [batchingInputRelationProp]
    constructor
    · exact h_t'_eq
    · constructor
      · -- stmt.original_claim = witMid.t.val.aeval stmt.t_eval_point from check + s_hat = φ(t')(r)
        have h_check_stmt :
            performCheckOriginalEvaluation κ L K β ℓ ℓ' h_l
              stmtIn.1.original_claim stmtIn.1.t_eval_point
              (embedded_MLP_eval κ L K ℓ ℓ' h_l witMid.t' stmtIn.1.t_eval_point) = true := by
          simpa [h_embed_eq] using h_check_true
        have h_check_wit :
            performCheckOriginalEvaluation κ L K β ℓ ℓ' h_l
              (witMid.t.val.aeval stmtIn.1.t_eval_point) stmtIn.1.t_eval_point
              (embedded_MLP_eval κ L K ℓ ℓ' h_l witMid.t' stmtIn.1.t_eval_point) = true := by
          have h_honest :=
            batching_check_correctness (κ := κ) (L := L) (K := K) (β := β)
              (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (t := witMid.t)
              (eval_point := stmtIn.1.t_eval_point)
          simpa [h_t'_eq] using h_honest
        have hs₁ := (decide_eq_true_eq.mp h_check_stmt)
        have hs₂ := (decide_eq_true_eq.mp h_check_wit)
        exact hs₁.trans hs₂.symm
      · -- aOStmtIn.initialCompatibility
        exact h_compat
  toFun_full := fun ⟨stmtLast, oStmtLast⟩ tr witOut h_relOut => by
    -- Same pattern as fold step: from relOut get verifier output, then prove KState 2
    simp at h_relOut
    rcases h_relOut with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩
    conv at h_output_mem_V_run_support =>
      simp only [Verifier.run, OracleVerifier.toVerifier]
      simp only [oracleVerifier]
      simp only [support_bind, Set.mem_iUnion]
      dsimp only [StateT.run]
      rw [simulateQ_bind, simulateQ_bind, simulateQ_bind]
      erw [simulateQ_simOracle2_liftM (oSpec := []ₒ) (t₁ := oStmtLast)]
      erw [simOracle2_impl_inr_inr]
      unfold OracleInterface.answer
      dsimp only [instOracleInterfaceMessagePSpecBatching]
      simp only [MessageIdx, Fin.isValue, Matrix.cons_val_zero, simulateQ_pure, Message, guard_eq,
        pure_bind, Function.comp_apply, simulateQ_map, simulateQ_ite,
        simulateQ_failure, bind_map_left]
      simp only [MessageIdx, Message, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        bind_pure_comp, simulateQ_map, simulateQ_ite, simulateQ_pure, simulateQ_failure,
        bind_map_left, Function.comp_apply]
      unfold Functor.map
      dsimp only [StateT.instMonad]
      simp only [StateT.map_ite]
      simp only [support_ite, StateT.support_map_const_pure, StateT.support_map_failure]
      simp only [Fin.isValue, Set.mem_ite_empty_right, Set.mem_singleton_iff, Prod.mk.injEq,
        exists_and_left, exists_eq', exists_eq_right, exists_and_right]
    rcases h_output_mem_V_run_support with ⟨init_value, h_init_value_mem_support,
      h_V_check_passed, ⟨h_stmtOut_eq, h_oStmtOut_eq⟩, h_initValue_trivial⟩
    simp only [Fin.reduceLast, Fin.isValue]
    dsimp only [sumcheckRoundRelation, sumcheckRoundRelationProp, Set.mem_setOf_eq] at h_relOut
    unfold batchingKStateProp
    simp only [Fin.isValue, batchingWitMid]
    set s_hat := tr.messages ⟨0, rfl⟩ with _h_s_hat
    set batching_challenges := tr.challenges ⟨1, rfl⟩ with _h_chal
    set ctx : RingSwitchingBaseContext κ L K ℓ :=
      { t_eval_point := stmtLast.t_eval_point, original_claim := stmtLast.original_claim,
        s_hat := s_hat, r_batching := batching_challenges } with h_ctx_def
    set stmtOut_computed := batchingVerifierStmtOut (κ:=κ) (L:=L) (K:=K) (β:=β) (ℓ:=ℓ) (ℓ':=ℓ')
      stmtLast s_hat batching_challenges with _h_stmtOut
    have h_stmtOut_eq_computed : stmtOut = stmtOut_computed := by
      rw [h_stmtOut_eq]; rfl
    rw [h_stmtOut_eq_computed] at h_relOut
    constructor
    · -- masterKStateProp with oStmtOut/witOut → sumcheckRoundRelationProp with oStmtLast/extractOut; extractOut = id; need embed compatibility
      have h_oStmtOut_eq_oStmtLast : oStmtOut = oStmtLast := by
        rw [h_oStmtOut_eq]
        funext j
        simp [OracleVerifier.mkVerifierOStmtOut, batchingStepLogic]
      rw [h_oStmtOut_eq_oStmtLast] at h_relOut
      have h_stmt_goal_eq :
          ({ sumcheck_target := compute_s0 κ L K β s_hat batching_challenges,
             challenges := Fin.elim0, ctx := ctx } :
            Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ) 0)
          = stmtOut_computed := by
        subst ctx
        simp [stmtOut_computed, batchingVerifierStmtOut]
      rw [h_stmt_goal_eq]
      unfold sumcheckRoundRelationProp masterKStateProp
      have h_cons :
          sumcheckConsistencyProp (𝓑 := 𝓑) stmtOut_computed.sumcheck_target witOut.H := h_relOut.1
      have h_wit_struct :
          witOut.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witOut.t')
            (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmtOut_computed.ctx)
            (i := 0) (challenges := stmtOut_computed.challenges) := h_relOut.2.1
      have h_h_goal_eq :
          projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witOut.t')
            (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly ctx)
            (i := 0) (challenges := Fin.elim0) =
          projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witOut.t')
            (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmtOut_computed.ctx)
            (i := 0) (challenges := stmtOut_computed.challenges) := by
        subst ctx
        simp only [Fin.coe_ofNat_eq_mod, stmtOut_computed]
      have h_wit_H_eq_goal :
          witOut.H =
            projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witOut.t')
              (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly ctx)
              (i := 0) (challenges := Fin.elim0) := by
        calc
          witOut.H
              = projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witOut.t')
                  (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmtOut_computed.ctx)
                  (i := 0) (challenges := stmtOut_computed.challenges) := h_wit_struct
          _ = projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witOut.t')
                (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly ctx)
                (i := 0) (challenges := Fin.elim0) := by
              simpa using h_h_goal_eq.symm
      constructor
      · simpa [batchingRbrExtractor, h_wit_H_eq_goal] using h_cons
      · constructor
        · unfold witnessStructuralInvariant
          simp [batchingRbrExtractor]
          exact h_h_goal_eq
        · simpa [batchingRbrExtractor] using h_relOut.2.2
    · constructor
      · exact h_V_check_passed  -- verifierCheck is performCheckOriginalEvaluation ... = true
      · have h_oStmtOut_eq_oStmtLast : oStmtOut = oStmtLast := by
          rw [h_oStmtOut_eq]
          funext j
          simp [OracleVerifier.mkVerifierOStmtOut, batchingStepLogic]
        rw [h_oStmtOut_eq_oStmtLast] at h_relOut
        simpa [batchingRbrExtractor] using h_relOut.2.2

/-! ## Security Properties -/

/-- Perfect completeness for the batching phase oracle reduction.

This theorem proves that the honest prover-verifier interaction for the batching phase
always succeeds (with probability 1) and produces valid outputs.

**Proof Strategy:**
1. Unroll the 2-message reduction to convert probabilistic statement to logical statement
2. Split into safety (no failures) and correctness (valid outputs)
3. For safety: prove the verifier never crashes on honest prover messages
4. For correctness: apply the logic completeness lemma (batchingStep_is_logic_complete)

**Key Technique:**
- Use `batchingStep_is_logic_complete` to get the pure logic properties
- Convert the challenge function by proving the only valid challenge index is 1
- Rewrite all intermediate variables to their concrete values
- Apply the logic properties to complete the proof
-/
theorem batchingReduction_perfectCompleteness (hInit : NeverFail init) :
  OracleReduction.perfectCompleteness
    (oracleReduction := batchingOracleReduction κ L K β ℓ ℓ' h_l (𝓑:=𝓑) (aOStmtIn:=aOStmtIn))
    (relIn := strictBatchingInputRelation κ L K β ℓ ℓ' h_l aOStmtIn)
    (relOut := strictSumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn 0)
    (init := init) (impl := impl) := by
  -- Step 1: Unroll the 2-message reduction to convert from probability to logic
  -- **NOTE**: this requires `ProtocolSpec.challengeOracleInterface` to avoid conflict
  rw [OracleReduction.unroll_2_message_reduction_perfectCompleteness (oSpec := []ₒ)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K)) (init := init) (impl := impl)
    (hInit := hInit) (hDir0 := by rfl) (hDir1 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image,
      IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- Step 2: Convert probability 1 to universal quantification over support
  rw [probEvent_eq_one_iff]
  -- Step 3: Unfold protocol definitions
  dsimp only [batchingOracleReduction, batchingOracleProver, batchingOracleVerifier, OracleVerifier.toVerifier,
    FullTranscript.mk2]
  let step := (batchingStepLogic (κ := κ) (L := L) (K := K) (β := β) (𝓑 := 𝓑) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (aOStmtIn := aOStmtIn))
  let strongly_complete : step.IsStronglyComplete := batchingStep_is_logic_complete (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn)

  -- Step 4: Split into safety and correctness goals
  refine ⟨?_, ?_⟩
  -- GOAL 1: SAFETY - Prove the verifier never crashes ([⊥|...] = 0)
  · -- Peel off monadic layers to reach the core verifier logic
    simp only [probFailure_bind_eq_zero_iff]
    conv_lhs =>
      simp only [liftComp_eq_liftM, liftM_pure, probFailure_eq_zero]
    rw [true_and]
    intro inputState hInputState_mem_support
    simp only [Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one, ChallengeIdx,
      Challenge, liftComp_eq_liftM, liftM_pure, support_pure,
      Set.mem_singleton_iff] at hInputState_mem_support
    conv_lhs =>
      simp only [liftM, monadLift, MonadLift.monadLift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        liftComp_eq_liftM, OptionT.probFailure_lift, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]

    intro r_i' h_r_i'_mem_query_1_support
    conv =>
      enter [1];
      simp only [probFailure_eq_zero_iff]
      simp only [liftM, monadLift, MonadLift.monadLift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        Fin.succ_one_eq_two, Message, Fin.succ_zero_eq_one, Fin.castSucc_one, liftComp_eq_liftM,
        OptionT.probFailure_lift, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]

    intro h_receive_challenge_fn h_receive_challenge_fn_mem_support
    conv =>
      enter [1];
      simp only [probFailure_eq_zero_iff]
      simp only [liftM, monadLift, MonadLift.monadLift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        Fin.succ_one_eq_two, Message, Fin.succ_zero_eq_one, Fin.castSucc_one, liftComp_eq_liftM,
        OptionT.probFailure_lift, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]
    -- ⊢ ∀ x ∈ .. support, ... ∧ ... ∧ ...
    intro h_prover_final_output h_prover_final_output_support
    conv =>
      simp only [guard_eq] -- simplify the `guard`
      enter [2];
      simp only [bind_pure_comp, NeverFail.probFailure_eq_zero, implies_true]
    rw [and_true]
    rw [OptionT.probFailure_liftComp_of_OracleComp_Option]
    conv_lhs =>
      enter [1]
      simp only [MessageIdx, Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one,
        id_eq, bind_pure_comp, OptionT.run_map, HasEvalPMF.probFailure_eq_zero]
    rw [zero_add]
    simp only [probOutput_eq_zero_iff]
    rw [OptionT.support_run_eq]
    simp only [←probOutput_eq_zero_iff]
    simp_all only
    change Pr[= none | OptionT.run (m := (OracleComp []ₒ)) (x := (OptionT.bind _ _)) ] = 0
    rw [OptionT.probOutput_none_bind_eq_zero_iff]
    conv =>
      enter [x]
      rw [OptionT.support_run]
    intro vStmtOut h_vStmtOut_mem_support
    conv at h_vStmtOut_mem_support =>
      erw [simulateQ_bind]
      -- turn the simulated oracle query into OracleInterface.answer form
      rw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      change vStmtOut ∈ (Bind.bind (m := (OracleComp []ₒ)) _ _).support
      erw [_root_.bind_pure_simulateQ_comp]
      simp only [Matrix.cons_val_zero, guard_eq]
      -- simp  [bind_pure_comp,
      -- OptionT.simulateQ_map, OptionT.simulateQ_ite, OptionT.simulateQ_pure,
      -- OptionT.support_map_run, OptionT.support_ite_run, support_pure,
      -- OptionT.support_failure_run, Set.mem_image, Set.mem_ite_empty_right,
      -- Set.mem_singleton_iff, and_true, exists_const, Prod.mk.injEq, existsAndEq]
      rw [bind_pure_comp]
      dsimp only [Functor.map]
      rw [OptionT.simulateQ_bind]
      erw [support_bind]
      rw [simulateQ_ite]
      simp only [Fin.isValue, Message, Matrix.cons_val_zero, id_eq, MessageIdx, support_ite,
        toPFunctor_emptySpec, Function.comp_apply, OptionT.simulateQ_pure, Set.mem_iUnion,
        exists_prop]
      simp only [OptionT.simulateQ_failure']
      erw [_root_.simulateQ_pure]
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk2
        (msg0 := _)
        (msg1 := (FullTranscript.mk2 (batchingProverComputeMsg κ L K ℓ ℓ' h_l stmtIn witIn) r_i').challenges ⟨1, rfl⟩))
      with h_V_check_def
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecFold (L := L)).dir 0 ≠ Direction.V_to_P := by
            simp only [ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue, Matrix.cons_val_zero,
              Direction.not_P_to_V_eq_V_to_P]
          exfalso
          exact hj_ne hj
        | 1 => exact r_i'
      )
    have h_V_check_is_true : V_check := h_V_check
    simp only [h_V_check_is_true, ↓reduceIte, support_pure, Set.mem_singleton_iff, Fin.isValue,
      exists_eq_left, OptionT.support_OptionT_pure_run] at h_vStmtOut_mem_support
    rw [h_vStmtOut_mem_support]
    simp only [Fin.isValue, OptionT.run_pure, probOutput_none_pure_some_eq_zero]
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
    simp only [Fin.isValue, Challenge, Matrix.cons_val_one, Matrix.cons_val_zero, ChallengeIdx,
      liftComp_eq_liftM, liftM_pure, liftComp_pure, support_pure, Set.mem_singleton_iff,
      Fin.reduceLast, MessageIdx, Message, exists_eq_left] at hx_mem_support
    -- Step 2b: Extract the challenge r1 and the trace equations
    obtain ⟨r1, ⟨_h_r1_mem_challenge_support, h_trace_support⟩⟩ := hx_mem_support

    rcases h_trace_support with ⟨prvOut_eq, h_verOut_mem_support⟩

    -- Step 2c: Simplify the verifier computation
    conv at h_verOut_mem_support =>
      erw [simulateQ_bind]
      rw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      erw [_root_.bind_pure_simulateQ_comp]
      simp only [Matrix.cons_val_zero, guard_eq]
      erw [simulateQ_bind]
      simp only [show OptionT.pure (m := (OracleComp ([]ₒ + ([OracleStatement 𝔽q β ϑ i.castSucc]ₒ +
        [pSpecFold.Message]ₒ)))) = pure by rfl]
      rw [simulateQ_ite]
      simp only [Fin.isValue, Message, Matrix.cons_val_zero, id_eq, MessageIdx, support_ite,
        toPFunctor_emptySpec, Function.comp_apply, simulateQ_pure, Set.mem_iUnion,
        exists_prop]
      simp only [OptionT.simulateQ_failure']
      erw [_root_.simulateQ_pure]
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk2
        (msg0 := _)
        (msg1 := (FullTranscript.mk2 (batchingProverComputeMsg κ L K ℓ ℓ' h_l stmtIn witIn) r1).challenges ⟨1, rfl⟩))
      with h_V_check_def
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecFold (L := L)).dir 0 ≠ Direction.V_to_P := by
            simp only [ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue, Matrix.cons_val_zero,
              Direction.not_P_to_V_eq_V_to_P]
          exfalso
          exact hj_ne hj
        | 1 => exact r1
      )

    have h_V_check_is_true : V_check := h_V_check
    simp only [h_V_check_is_true, ↓reduceIte, Fin.isValue, pure_bind] at h_verOut_mem_support
    erw [simulateQ_pure, liftM_pure] at h_verOut_mem_support
    simp only [Fin.isValue, support_pure, Set.mem_singleton_iff, Option.some.injEq,
      Prod.mk.injEq] at h_verOut_mem_support
    rcases h_verOut_mem_support with ⟨verStmtOut_eq, verOStmtOut_eq⟩
    dsimp only [batchingStepLogic, batchingProverComputeMsg, step] at prvOut_eq
    rw [Prod.mk.injEq, Prod.mk.injEq] at prvOut_eq

    obtain ⟨⟨prvStmtOut_eq, prvOStmtOut_eq⟩, prvWitOut_eq⟩ := prvOut_eq

    constructor
    · rw [prvWitOut_eq, verStmtOut_eq, verOStmtOut_eq];
      exact h_rel
    · constructor
      · rw [verStmtOut_eq, prvStmtOut_eq]; rfl
      · rw [verOStmtOut_eq, prvOStmtOut_eq];
        exact h_agree.2

#check ProtocolSpec.challengeOracleInterface

/-- Repacking the unpacked polynomial is identity for multilinear `t'`. -/
lemma batching_pack_unpack_id (t' : MultilinearPoly L ℓ') :
    packMLE κ L K ℓ ℓ' h_l β (unpackMLE κ L K ℓ ℓ' h_l β t') = t' := by
  apply Subtype.ext
  simp [packMLE, unpackMLE]
  simpa [MvPolynomial.toEvalsZeroOne] using
    (MvPolynomial.is_multilinear_iff_eq_evals_zeroOne (p := t'.val)).mp t'.property

/-- `compute_s0` is evaluation of the row-MLE at the batching challenge. -/
lemma batching_compute_s0_eq_eval_MLE
    (s_hat : TensorAlgebra K L) (y : Fin κ → L) :
    compute_s0 κ L K β s_hat y =
      MvPolynomial.eval y
        (MvPolynomial.MLE (fun u : Fin κ → Fin 2 =>
          decompose_tensor_algebra_rows (L := L) (K := K) (β := β) s_hat u)) := by
  classical
  rw [compute_s0, MvPolynomial.MLE]
  simp_rw [Binius.BinaryBasefold.eqTilde]
  simp [MvPolynomial.eval_mul, MvPolynomial.eval_C]
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  by_cases hux : u x = 1
  · simp [hux]
  · have hux0 : u x = 0 := by
      have hix : ((u x : Fin 2) : ℕ) = 0 ∨ ((u x : Fin 2) : ℕ) = 1 := by omega
      rcases hix with h0 | h1
      · exact Fin.ext h0
      · exfalso
        exact hux (Fin.ext h1)
    simp only [hux0, Fin.isValue, zero_ne_one, ↓reduceIte, sub_zero, one_mul, map_zero, add_zero,
      Fin.coe_ofNat_eq_mod, zero_mod, cast_zero, zero_mul]

/-- Mismatch polynomial from row-decomposition difference `msg0 - s_bar`. -/
def batchingMismatchPoly (msg0 s_bar : TensorAlgebra K L) : MvPolynomial (Fin κ) L :=
  MvPolynomial.MLE (fun u : Fin κ → Fin 2 =>
    decompose_tensor_algebra_rows (L := L) (K := K) (β := β) msg0 u -
    decompose_tensor_algebra_rows (L := L) (K := K) (β := β) s_bar u)

/-- The mismatch polynomial evaluates to the `compute_s0` difference. -/
lemma batching_compute_s0_sub_eq_eval_mismatch
    (msg0 s_bar : TensorAlgebra K L) (y : Fin κ → L) :
    compute_s0 κ L K β msg0 y - compute_s0 κ L K β s_bar y =
      MvPolynomial.eval y (batchingMismatchPoly (κ := κ) (L := L) (K := K) (β := β) msg0 s_bar) := by
  rw [batching_compute_s0_eq_eval_MLE (κ := κ) (L := L) (K := K) (β := β)
    (s_hat := msg0) (y := y)]
  rw [batching_compute_s0_eq_eval_MLE (κ := κ) (L := L) (K := K) (β := β)
    (s_hat := s_bar) (y := y)]
  unfold batchingMismatchPoly
  simp [MvPolynomial.MLE, MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    sub_eq_add_neg]
  rw [← Finset.sum_neg_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Degree bound for mismatch polynomial: multilinear in `κ` vars, so total degree ≤ `κ`. -/
lemma batchingMismatchPoly_totalDegree_le
    (msg0 s_bar : TensorAlgebra K L) :
    (batchingMismatchPoly (κ := κ) (L := L) (K := K) (β := β) msg0 s_bar).totalDegree ≤ κ := by
  let P := batchingMismatchPoly (κ := κ) (L := L) (K := K) (β := β) msg0 s_bar
  have h_mem : P ∈ MvPolynomial.restrictDegree (Fin κ) L 1 := by
    dsimp [P, batchingMismatchPoly]
    exact (MvPolynomial.MLE_mem_restrictDegree (σ := Fin κ) (R := L)
      (evals := fun u : Fin κ → Fin 2 =>
        decompose_tensor_algebra_rows (L := L) (K := K) (β := β) msg0 u -
        decompose_tensor_algebra_rows (L := L) (K := K) (β := β) s_bar u))
  have h_degOf : ∀ i : Fin κ, MvPolynomial.degreeOf i P ≤ 1 := by
    intro i
    exact (MvPolynomial.mem_restrictDegree_iff_degreeOf_le (p := P) (n := 1)).1 h_mem i
  rw [MvPolynomial.totalDegree_eq]
  apply Finset.sup_le
  intro m hm
  rw [Finsupp.card_toMultiset]
  have hm_le_one : ∀ i ∈ m.support, m i ≤ 1 := by
    intro i hi
    exact le_trans (MvPolynomial.monomial_le_degreeOf i hm) (h_degOf i)
  calc
    m.sum (fun _ e => e) ≤ m.sum (fun _ _ => (1 : ℕ)) := by
      exact Finsupp.sum_le_sum hm_le_one
    _ = m.support.card := by
      rw [Finsupp.sum]
      simp
    _ ≤ κ := by
      simpa using (Finset.card_le_univ (s := m.support))

/-- If embedded evaluation mismatches `msg0`, the mismatch polynomial is nonzero. -/
lemma batchingMismatchPoly_nonzero_of_embed_ne
    (stmt : BatchingStmtIn L ℓ)
    (msg0 : TensorAlgebra K L)
    (t' : MultilinearPoly L ℓ')
    (h_embed_ne : embedded_MLP_eval κ L K ℓ ℓ' h_l t' stmt.t_eval_point ≠ msg0) :
    batchingMismatchPoly (κ := κ) (L := L) (K := K) (β := β) msg0
      (embedded_MLP_eval κ L K ℓ ℓ' h_l t' stmt.t_eval_point) ≠ 0 := by
  let s_bar := embedded_MLP_eval κ L K ℓ ℓ' h_l t' stmt.t_eval_point
  have h_rows_ne :
      (decompose_tensor_algebra_rows (L := L) (K := K) (β := β) msg0) ≠
      (decompose_tensor_algebra_rows (L := L) (K := K) (β := β) s_bar) := by
    intro h_eq
    have h_repr_eq : (β.baseChange L).repr msg0 = (β.baseChange L).repr s_bar := by
      ext u
      exact congrFun h_eq u
    have hs : msg0 = s_bar := (β.baseChange L).repr.injective h_repr_eq
    exact h_embed_ne (by simpa [s_bar] using hs.symm)
  have h_diff_ne :
      (fun u : Fin κ → Fin 2 =>
        decompose_tensor_algebra_rows (L := L) (K := K) (β := β) msg0 u -
        decompose_tensor_algebra_rows (L := L) (K := K) (β := β) s_bar u) ≠ 0 := by
    intro h_zero
    apply h_rows_ne
    funext u
    exact sub_eq_zero.mp (congrFun h_zero u)
  intro h_poly_zero
  have h_poly_zero' :
      batchingMismatchPoly (κ := κ) (L := L) (K := K) (β := β) msg0 s_bar = 0 := by
    simpa [s_bar] using h_poly_zero
  apply h_diff_ne
  funext u
  have hu_eval_zero :
      MvPolynomial.eval (fun i => ((u i : Fin 2) : L))
        (batchingMismatchPoly (κ := κ) (L := L) (K := K) (β := β) msg0 s_bar) = 0 := by
    rw [h_poly_zero']
    simp
  have hu_eval_mle :
      MvPolynomial.eval (fun i => ((u i : Fin 2) : L))
        (batchingMismatchPoly (κ := κ) (L := L) (K := K) (β := β) msg0 s_bar) =
      decompose_tensor_algebra_rows (L := L) (K := K) (β := β) msg0 u -
        decompose_tensor_algebra_rows (L := L) (K := K) (β := β) s_bar u := by
    simp [batchingMismatchPoly, MvPolynomial.MLE_eval_zeroOne]
  rw [hu_eval_mle] at hu_eval_zero
  exact hu_eval_zero

omit [NeZero κ] [Fintype L] [DecidableEq L] [CharP L 2] [SelectableType L]
  [Fintype K] [DecidableEq K] in
/-- If `msg0 ≠ s_bar` in the tensor algebra, the mismatch polynomial is nonzero.
  Generalization of `batchingMismatchPoly_nonzero_of_embed_ne`. -/
lemma batchingMismatchPoly_nonzero_of_ne
    (msg0 s_bar : TensorAlgebra K L)
    (h_ne : msg0 ≠ s_bar) :
    batchingMismatchPoly (κ := κ) (L := L) (K := K) (β := β) msg0 s_bar ≠ 0 := by
  have h_rows_ne :
      (decompose_tensor_algebra_rows (L := L) (K := K) (β := β) msg0) ≠
      (decompose_tensor_algebra_rows (L := L) (K := K) (β := β) s_bar) := by
    intro h_eq
    have h_repr_eq : (β.baseChange L).repr msg0 = (β.baseChange L).repr s_bar := by
      ext u; exact congrFun h_eq u
    exact h_ne ((β.baseChange L).repr.injective h_repr_eq)
  have h_diff_ne :
      (fun u : Fin κ → Fin 2 =>
        decompose_tensor_algebra_rows (L := L) (K := K) (β := β) msg0 u -
        decompose_tensor_algebra_rows (L := L) (K := K) (β := β) s_bar u) ≠ 0 := by
    intro h_zero
    apply h_rows_ne
    funext u
    exact sub_eq_zero.mp (congrFun h_zero u)
  intro h_poly_zero
  apply h_diff_ne
  funext u
  have hu_eval_zero :
      MvPolynomial.eval (fun i => ((u i : Fin 2) : L))
        (batchingMismatchPoly (κ := κ) (L := L) (K := K) (β := β) msg0 s_bar) = 0 := by
    rw [h_poly_zero]; simp
  have hu_eval_mle :
      MvPolynomial.eval (fun i => ((u i : Fin 2) : L))
        (batchingMismatchPoly (κ := κ) (L := L) (K := K) (β := β) msg0 s_bar) =
      decompose_tensor_algebra_rows (L := L) (K := K) (β := β) msg0 u -
        decompose_tensor_algebra_rows (L := L) (K := K) (β := β) s_bar u := by
    simp [batchingMismatchPoly, MvPolynomial.MLE_eval_zeroOne]
  rw [hu_eval_mle] at hu_eval_zero
  exact hu_eval_zero

/-- From `KState 2` truth, derive equality of the two `compute_s0` forms. -/
lemma batching_compute_eq_from_hafter
    (stmtOStmtIn : (BatchingStmtIn L ℓ) × (∀ j, aOStmtIn.OStmtIn j))
    (msg0 : (pSpecBatching (κ := κ) (L := L) (K := K)).Message ⟨0, rfl⟩)
    (y : Fin κ → L)
    (witMid : batchingWitMid L K ℓ ℓ' 2)
    (h_after : batchingKStateProp (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (tr := FullTranscript.mk2 msg0 y) stmtOStmtIn.1
      witMid stmtOStmtIn.2) :
    compute_s0 κ L K β msg0 y =
      compute_s0 κ L K β
        (embedded_MLP_eval κ L K ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point) y := by
  dsimp [batchingKStateProp] at h_after
  have h_sumcheck_msg0 := h_after.1
  dsimp [sumcheckRoundRelationProp] at h_sumcheck_msg0
  dsimp [Binius.RingSwitching.masterKStateProp] at h_sumcheck_msg0
  have h_msg :
      sumcheckConsistencyProp (𝓑 := 𝓑)
        (compute_s0 κ L K β msg0 y)
        (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witMid.t')
          (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly
            { t_eval_point := stmtOStmtIn.1.t_eval_point,
              original_claim := stmtOStmtIn.1.original_claim,
              s_hat := msg0,
              r_batching := y })
          (i := 0) (challenges := Fin.elim0)) := h_sumcheck_msg0.1
  have h_bar :
      sumcheckConsistencyProp (𝓑 := 𝓑)
        (compute_s0 κ L K β
          (embedded_MLP_eval κ L K ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point) y)
        (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witMid.t')
          (m := (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly
            { t_eval_point := stmtOStmtIn.1.t_eval_point,
              original_claim := stmtOStmtIn.1.original_claim,
              s_hat := msg0,
              r_batching := y })
          (i := 0) (challenges := Fin.elim0)) := by
    simpa using
      (batching_target_consistency (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
        (ℓ' := ℓ') (h_l := h_l) (𝓑 := 𝓑) (t' := witMid.t')
        (msg0 := embedded_MLP_eval κ L K ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point)
        (r_batching := y)
        (ctx := { t_eval_point := stmtOStmtIn.1.t_eval_point,
                  original_claim := stmtOStmtIn.1.original_claim,
                  s_hat := msg0,
                  r_batching := y }))
  unfold sumcheckConsistencyProp at h_msg h_bar
  exact h_msg.trans h_bar.symm

/-- The "bad batching event": the prover's ŝ (`msg0`) disagrees with the honest ŝ (`s_bar`),
  but their `compute_s0` values agree at the batching challenges `y`.
  Corresponds to $S(r''_0, \ldots, r''_{\kappa-1}) = 0$ in Theorem 3.5 of the spec, where
  $S(X) := \sum_{u \in \mathcal{B}_\kappa} (\hat{s}_u - \bar{s}_u) \cdot \widetilde{eq}(u, X)$. -/
def badBatchingEventProp (y : Fin κ → L) (msg0 s_bar : TensorAlgebra K L) : Prop :=
  msg0 ≠ s_bar ∧ compute_s0 κ L K β msg0 y = compute_s0 κ L K β s_bar y

/-- **Schwartz-Zippel bound for the bad batching event.**
  When `msg0 = s_bar`, the event never holds (first conjunct is `False`).
  When `msg0 ≠ s_bar`, the mismatch polynomial $S$ is nonzero with `totalDegree ≤ κ`,
  so Schwartz-Zippel gives `Pr[S(y) = 0] ≤ κ / |L|`. -/
lemma probability_bound_badBatchingEventProp
    (msg0 s_bar : TensorAlgebra K L) :
    Pr_{ let y ← $ᵖ (Fin κ → L) }[
      badBatchingEventProp (κ := κ) (L := L) (K := K) (β := β) y msg0 s_bar ] ≤
      batchingRBRKnowledgeError (κ := κ) (L := L) := by
  classical
  unfold badBatchingEventProp
  by_cases h_ne : msg0 ≠ s_bar
  · -- msg0 ≠ s_bar: reduce to S.eval(y) = 0, apply Schwartz-Zippel
    simp only [ne_eq, h_ne, not_false_eq_true, true_and]
    -- Rewrite compute_s0 equality as mismatch polynomial root
    have h_mono := prob_mono (D := $ᵖ (Fin κ → L))
      (f := fun y => compute_s0 κ L K β msg0 y = compute_s0 κ L K β s_bar y)
      (g := fun y => MvPolynomial.eval y
        (batchingMismatchPoly (κ := κ) (L := L) (K := K) (β := β) msg0 s_bar) = 0)
      (h_imp := by
        intro y h_eq
        rw [← batching_compute_s0_sub_eq_eval_mismatch (κ := κ) (L := L) (K := K) (β := β)
          (msg0 := msg0) (s_bar := s_bar) (y := y)]
        exact sub_eq_zero.mpr h_eq)
    apply le_trans h_mono
    have h_nonzero : batchingMismatchPoly (κ := κ) (L := L) (K := K) (β := β) msg0 s_bar ≠ 0 :=
      batchingMismatchPoly_nonzero_of_ne (κ := κ) (L := L) (K := K) (β := β) msg0 s_bar h_ne
    have h_sz := prob_schwartz_zippel_mv_polynomial
      (P := batchingMismatchPoly (κ := κ) (L := L) (K := K) (β := β) msg0 s_bar) h_nonzero
      (batchingMismatchPoly_totalDegree_le (κ := κ) (L := L) (K := K) (β := β)
        (msg0 := msg0) (s_bar := s_bar))
    conv_rhs =>
      dsimp only [batchingRBRKnowledgeError]
      rw [ENNReal.coe_div (hr := by simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero,
        not_false_eq_true])]
      simp only [ENNReal.coe_ofNat, ENNReal.coe_natCast]
    exact h_sz
  · -- msg0 = s_bar: event is False ∧ _, which never holds
    simp only [h_ne, false_and]
    simp only [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.bind_const, PMF.pure_apply,
      eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte, _root_.zero_le]

/-- Extraction failure implies a witness-dependent bad batching event.
  The extracted `witMid` also carries oracle compatibility at the same `oStmt`. -/
lemma batching_rbrExtractionFailureEvent_imply_badBatchingEvent
    (stmtOStmtIn : (BatchingStmtIn L ℓ) × (∀ j, aOStmtIn.OStmtIn j))
    (msg0 : (pSpecBatching (κ := κ) (L := L) (K := K)).Message ⟨0, rfl⟩)
    (y : Fin κ → L)
    (doomEscape : rbrExtractionFailureEvent
      (kSF := batchingKnowledgeStateFunction (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
        (ℓ' := ℓ') (h_l := h_l) (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (init := init) (impl := impl))
      (extractor := batchingRbrExtractor (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
        (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
      ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 msg0) y) :
    ∃ witMid : batchingWitMid L K ℓ ℓ' 2,
      aOStmtIn.initialCompatibility ⟨witMid.t', stmtOStmtIn.2⟩ ∧
      let s_bar := embedded_MLP_eval κ L K ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point
      badBatchingEventProp (κ := κ) (L := L) (K := K) (β := β) y msg0 s_bar := by
  classical
  unfold rbrExtractionFailureEvent at doomEscape
  rcases doomEscape with ⟨witMid, h_kState_before_false, h_kState_after_true⟩
  have h_after :
      batchingKStateProp (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
        (h_l := h_l) (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (tr := FullTranscript.mk2 msg0 y)
        stmtOStmtIn.1 witMid stmtOStmtIn.2 := by
    simpa [batchingKnowledgeStateFunction] using h_kState_after_true
  have h_before_false := by
    simpa [batchingKnowledgeStateFunction] using h_kState_before_false
  have h_compute_eq :=
    batching_compute_eq_from_hafter (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (stmtOStmtIn := stmtOStmtIn) (msg0 := msg0)
      (y := y) (witMid := witMid) (h_after := h_after)
  dsimp [batchingKStateProp] at h_after
  have h_check_true :
      performCheckOriginalEvaluation κ L K β ℓ ℓ' h_l stmtOStmtIn.1.original_claim
        stmtOStmtIn.1.t_eval_point msg0 = true := h_after.2.1
  have h_compat_mid : aOStmtIn.initialCompatibility ⟨witMid.t', stmtOStmtIn.2⟩ := h_after.2.2
  have h_embed_ne :
      embedded_MLP_eval κ L K ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point ≠ msg0 := by
    intro h_embed_eq
    apply h_before_false
    dsimp [batchingKStateProp]
    refine ⟨?_, ?_, h_check_true, h_compat_mid⟩
    · simp [batchingRbrExtractor, batching_pack_unpack_id]
    · simpa using h_embed_eq
  have h_msg0_ne :
      msg0 ≠ embedded_MLP_eval κ L K ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point := by
    intro h_eq
    exact h_embed_ne h_eq.symm
  have h_bad :
      badBatchingEventProp (κ := κ) (L := L) (K := K) (β := β) y msg0
        (embedded_MLP_eval κ L K ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point) := by
    exact ⟨h_msg0_ne, h_compute_eq⟩
  refine ⟨witMid, h_compat_mid, ?_⟩
  exact h_bad

/-- Per-transcript batching bound: for a fixed prover message `msg0`, the probability
  (over batching challenges `y : Fin κ → L`) that extraction fails is bounded by
  `batchingRBRKnowledgeError`.

  **Proof strategy** (follows `foldStep_doom_escape_probability_bound`):
  1. **Implication**: Show that extraction failure implies the
     `badBatchingEventProp` (Theorem 3.5, $S(r'') = 0$).
  2. **Monotonicity**: Conclude `Pr[doom] ≤ Pr[badBatchingEvent]` via `prob_mono`.
  3. **Schwartz–Zippel**: Bound `Pr[badBatchingEvent]` by `κ/|L|`. -/
lemma batching_doom_escape_probability_bound
    (stmtOStmtIn : (BatchingStmtIn L ℓ) × (∀ j, aOStmtIn.OStmtIn j))
    (msg0 : (pSpecBatching (κ := κ) (L := L) (K := K)).Message ⟨0, rfl⟩) :
    Pr_{ let y ← $ᵖ (Fin κ → L) }[
      rbrExtractionFailureEvent
        (kSF := batchingKnowledgeStateFunction (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (init := init) (impl := impl))
        (extractor := batchingRbrExtractor (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 msg0) y ] ≤
      batchingRBRKnowledgeError (κ := κ) (L := L) := by
  classical
  let compatPred : MultilinearPoly L ℓ' → Prop := fun t =>
    aOStmtIn.initialCompatibility ⟨t, stmtOStmtIn.2⟩
  by_cases hCompat : ∃ t : MultilinearPoly L ℓ', compatPred t
  · rcases hCompat with ⟨t_fixed, h_t_fixed_compat⟩
    let s_bar_fixed :=
      embedded_MLP_eval κ L K ℓ ℓ' h_l t_fixed stmtOStmtIn.1.t_eval_point
    have h_prob_mono := prob_mono (D := $ᵖ (Fin κ → L))
      (f := fun y => rbrExtractionFailureEvent
        (kSF := batchingKnowledgeStateFunction (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (init := init)
          (impl := impl))
        (extractor := batchingRbrExtractor (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 msg0) y)
      (g := fun y =>
        badBatchingEventProp (κ := κ) (L := L) (K := K) (β := β) y msg0 s_bar_fixed)
      (h_imp := by
        -- Uniqueness proof of `witMid` and `s_bar_fixed`
        intro y h_doomEscape
        obtain ⟨witMid, h_mid_compat, h_bad_extracted⟩ :=
          batching_rbrExtractionFailureEvent_imply_badBatchingEvent
            (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
            (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (init := init) (impl := impl)
            (stmtOStmtIn := stmtOStmtIn) (msg0 := msg0) (y := y)
            (doomEscape := h_doomEscape)
        have h_t_eq : witMid.t' = t_fixed :=
          aOStmtIn.initialCompatibility_unique stmtOStmtIn.2 witMid.t' t_fixed
            h_mid_compat h_t_fixed_compat
        simpa [s_bar_fixed, h_t_eq] using h_bad_extracted)
    apply le_trans h_prob_mono
    exact probability_bound_badBatchingEventProp (κ := κ) (L := L) (K := K) (β := β)
      (msg0 := msg0) (s_bar := s_bar_fixed)
  · have h_prob_mono_false := prob_mono (D := $ᵖ (Fin κ → L))
      (f := fun y => rbrExtractionFailureEvent
        (kSF := batchingKnowledgeStateFunction (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (init := init)
          (impl := impl))
        (extractor := batchingRbrExtractor (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 msg0) y)
      (g := fun _ => False)
      (h_imp := by
        intro y h_doomEscape
        obtain ⟨witMid, h_mid_compat, _h_bad_extracted⟩ :=
          batching_rbrExtractionFailureEvent_imply_badBatchingEvent
            (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
            (𝓑 := 𝓑) (aOStmtIn := aOStmtIn) (init := init) (impl := impl)
            (stmtOStmtIn := stmtOStmtIn) (msg0 := msg0) (y := y)
            (doomEscape := h_doomEscape)
        exact (hCompat ⟨witMid.t', h_mid_compat⟩).elim)
    refine le_trans h_prob_mono_false ?_
    simp only [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.bind_const, PMF.pure_apply,
      eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte, _root_.zero_le]

/-- RBR knowledge soundness for the batching phase oracle verifier. -/
theorem batchingOracleVerifier_rbrKnowledgeSoundness :
  OracleVerifier.rbrKnowledgeSoundness
    (verifier := batchingOracleVerifier κ L K β ℓ ℓ' h_l (𝓑:=𝓑) (aOStmtIn:=aOStmtIn))
    (init := init) (impl := impl)
    (relIn := batchingInputRelation κ L K β ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn 0)
    (rbrKnowledgeError := fun _ => batchingRBRKnowledgeError (κ:=κ) (L:=L)) := by
  classical
  -- -- Proof follows by constructing the extractor and knowledge state function.
  -- use batchingWitMid L K ℓ ℓ'
  -- use batchingRbrExtractor κ L K β ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)
  -- use batchingKnowledgeStateFunction κ L K β ℓ ℓ' h_l (aOStmtIn:=aOStmtIn) (init:=init) (impl:=impl)
  -- intro stmtIn witIn prover iChal
  -- -- `KState 1 = (t' = packMLE t) ∧ (ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1})))`
  --   -- `∧ (s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v.`
  -- -- `KState 2 = (s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v) ∧`
  --   -- `h = projectSumcheckPoly t' 0 r r' ∧ s_0 = Σ_{w ∈ {0,1}^{ℓ'}} h(w)`
  -- -- ⊢ `Pr[KState(2, witMidSucc) ∧ ¬KState(1, extractMid(iChal, witMidSucc))] ≤ (κ/|L|)`

  apply OracleReduction.unroll_rbrKnowledgeSoundness (kSF := batchingKnowledgeStateFunction κ L K β ℓ ℓ' h_l (aOStmtIn:=aOStmtIn) (init:=init) (impl:=impl))
  intro stmtOStmtIn witIn prover j initState
  let P := rbrExtractionFailureEvent
    (kSF := batchingKnowledgeStateFunction κ L K β (𝓑 := 𝓑) ℓ ℓ' h_l (aOStmtIn:=aOStmtIn) (init:=init) (impl:=impl))
    (extractor := batchingRbrExtractor κ L K β ℓ ℓ' h_l (aOStmtIn:=aOStmtIn))
    (i := j) (stmtIn := stmtOStmtIn)
  rw [OracleReduction.probEvent_soundness_goal_unroll_log'
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K))
    (P := P) (impl := impl) (prover := prover) (i := j) (stmt := stmtOStmtIn)
    (wit := witIn) (s := initState)]
  have h_j_eq_1 : j = ⟨1, rfl⟩ := by
    match j with
    | ⟨0, h0⟩ => nomatch h0
    | ⟨1, _⟩ => rfl
  subst h_j_eq_1
  conv_lhs => simp only [Fin.isValue, Fin.castSucc_one];
  rw [OracleReduction.soundness_unroll_runToRound_1_P_to_V_pSpec_2
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K)) (prover := prover) (hDir0 := by rfl)]
  simp only [
    bind_pure_comp, liftComp_query, SubSpec.liftM_query_eq_liftM_liftM, liftM_append_right_eq,
    bind_map_left, simulateQ_bind, simulateQ_liftComp, StateT.run'_eq, StateT.run_bind,
    Function.comp_apply, simulateQ_map, simulateQ_query,
    StateT.run_map, map_bind, Functor.map_map]
  rw [probEvent_bind_eq_tsum]
  apply OracleReduction.ENNReal.tsum_mul_le_of_le_of_sum_le_one
  · -- Bound the conditional probability for each transcript
    intro x
    -- rw [OracleComp.probEvent_map]
    simp only [Fin.isValue, Nat.reduceAdd, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
      Fin.succ_zero_eq_one, probEvent_map]
    dsimp only [Fin.isValue, StateT.run]
    rw [OracleReduction.QueryImpl_append_impl_inr_stateful]
    dsimp only [challengeQueryImpl]
    simp only [ChallengeIdx, Fin.isValue, Challenge, Matrix.cons_val_one, Matrix.cons_val_zero,
      StateT.run_monadLift, monadLift_self, bind_pure_comp, probEvent_map]
    rw [OracleComp.probEvent_eq_tsum_ite]
    have h_L_eq : [(pSpecFold (L := L)).Challenge]ₒ.range ⟨1, by rfl⟩ = L := by rfl
    have h_L_inhabited : Inhabited L := ⟨0⟩
    conv_lhs =>
      enter [1, x_1, 2]
      rw [OracleReduction.probOutput_uniformOfFintype_eq_Pr (L := (Fin κ → L)) (x := x_1)]
    dsimp only [Function.comp_apply]
    -- Convert the sum domain from [pSpecFold.Challenge]ₒ.range to L using h_L_eq
    conv_lhs => change (∑' (x_1 : (Fin κ → L)), _)
    rw [OracleReduction.tsum_uniform_Pr_eq_Pr (L := (Fin κ → L))
      (P := P (FullTranscript.mk1 x.1.1))]
    -- Apply the per-transcript bound
    exact batching_doom_escape_probability_bound (κ := κ) (L := L) (K := K)
      (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (𝓑 := 𝓑) (aOStmtIn := aOStmtIn)
      (stmtOStmtIn := stmtOStmtIn) (msg0 := x.1.1)
      (impl := impl) (init := init)
  · -- Prove: ∑' x, [=x|transcript computation] ≤ 1
    apply OracleComp.tsum_probOutput_le_one

end BatchingPhase
end Binius.RingSwitching
