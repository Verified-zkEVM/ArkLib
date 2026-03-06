/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.RingSwitching.Prelude
import ArkLib.ProofSystem.Binius.RingSwitching.Spec
import ArkLib.OracleReduction.Basic
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import CompPoly.Fields.Binary.Tower.TensorAlgebra

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Module Binius.BinaryBasefold TensorProduct Nat Matrix
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

/-- Input relation: the witness `t` and `t'` are consistent,
and `t` satisfies the original claim. -/
def batchingInputRelation :
  Set ((BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)) × BatchingWitIn L K ℓ ℓ') :=
  {⟨⟨stmt, oStmt⟩, wit⟩ | batchingInputRelationProp κ L K β ℓ ℓ' h_l aOStmtIn stmt oStmt wit }

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
    Binius.BinaryBasefold.CoreInteraction.ReductionLogicStep
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
    ((s, o), w) ∈ batchingInputRelation κ L K β ℓ ℓ' h_l aOStmtIn
  completeness_relOut := fun ((s, o), w) =>
    ((s, o), w) ∈ sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) aOStmtIn 0

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

  -- Extract properties from h_relIn (batchingInputRelation)
  simp only [batchingStepLogic, batchingInputRelation, batchingInputRelationProp,
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

  -- Fact 2: Output relation holds (sumcheckRoundRelation 0)
  let hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    simp only [step, batchingStepLogic, sumcheckRoundRelation, sumcheckRoundRelationProp,
      Set.mem_setOf_eq]
    -- batching_target_consistency
    dsimp only [masterKStateProp, Fin.coe_ofNat_eq_mod]; rw [true_and]
    constructor
    · -- ⊢ witnessStructuralInvariant κ L K β ℓ ℓ' h_l verifierStmtOut proverWitOut
      rfl
    · constructor
      · -- ⊢ sumcheckConsistencyProp verifierStmtOut.sumcheck_target proverWitOut.H
        exact batching_target_consistency κ L K β ℓ ℓ' h_l (𝓑:=𝓑) witIn.t'
          (transcript.messages ⟨0, rfl⟩) r_batching verifierStmtOut.ctx
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
def batchingRBRKnowledgeError (i : (pSpecBatching (κ := κ) (L := L) (K := K)).ChallengeIdx) : ℝ≥0 :=
  match i with
  | ⟨1, _⟩ => (κ : ℝ≥0) / (Fintype.card L : ℝ≥0) -- Schwartz-Zippel error
  | _ => 0 -- No other challenges

def batchingKStateProp {m : Fin (2 + 1)}
    (tr : Transcript m (pSpecBatching (κ := κ) (L := L) (K := K)))
    (stmt : BatchingStmtIn L ℓ) (witMid : batchingWitMid L K ℓ ℓ' m)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) :
    Prop :=
  match m with
  | ⟨0, _⟩ => -- equiv s relIn
    batchingInputRelationProp κ L K β ℓ ℓ' h_l aOStmtIn stmt oStmt witMid
  | ⟨1, _⟩ => by -- P sends hᵢ(X)
    let ⟨msgsUpTo, _⟩ := Transcript.equivMessagesChallenges (k := 1)
      (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K)) tr
    let i_msg1 : ((pSpecBatching (κ:=κ) (L:=L) (K:=K)).take 1 (by omega)).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le (by omega)⟩, by simp [pSpecBatching]; rfl⟩
    let s_hat: TensorAlgebra K L := msgsUpTo i_msg1
    exact
      witMid.t' = packMLE κ L K ℓ ℓ' h_l β witMid.t -- implied by `extractMid`
      -- The last two constraints are equivalent to `t(r) = s`
      ∧ embedded_MLP_eval κ L K ℓ ℓ' h_l witMid.t' stmt.t_eval_point = s_hat
      ∧ performCheckOriginalEvaluation κ L K β ℓ ℓ' h_l stmt.original_claim
        stmt.t_eval_point s_hat -- local V check
  | ⟨2, _⟩ => by -- implied by relOut
    simp only [batchingWitMid] at witMid
    let ⟨msgsUpTo, chalsUpTo⟩ := Transcript.equivMessagesChallenges (k := 2)
      (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K)) tr
    let i_msg1 : ((pSpecBatching (κ:=κ) (L:=L) (K:=K)).take 2 (by omega)).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le (by omega)⟩, by simp [pSpecBatching]; rfl⟩
    let s_hat: TensorAlgebra K L := msgsUpTo i_msg1
    let i_msg2 : ((pSpecBatching (κ:=κ) (L:=L) (K:=K)).take 2 (by omega)).ChallengeIdx :=
      ⟨⟨1, Nat.lt_of_succ_le (by omega)⟩, by simp [pSpecBatching]; rfl⟩
    let batching_challenges: Fin κ → L := chalsUpTo i_msg2

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
        stmt.t_eval_point s_hat -- local V check
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
  toFun_next := fun m hDir stmtIn tr msg witMid =>
    match m with
    | ⟨0, _⟩ => by -- from accumulative KState
      intro hSuccTrue
      simp only [batchingKStateProp, Fin.zero_eta, Fin.isValue, Fin.succ_zero_eq_one,
        Equiv.toFun_as_coe, Transcript.equivMessagesChallenges_apply, Fin.castSucc_zero,
        batchingRbrExtractor, Fin.mk_one, Fin.succ_one_eq_two,
        batchingInputRelationProp] at ⊢ hSuccTrue
      rw [hSuccTrue.1]
      simp only [true_and]
      set s_hat := (Transcript.concat msg tr).toMessagesChallenges.1 ⟨(0 : Fin (0 + 1)), by rfl⟩
      -- ⊢ stmtIn.1.original_claim = (MvPolynomial.aeval stmtIn.1.t_eval_point) ↑witMid.t
      sorry
    | ⟨1, h⟩ => nomatch h
  toFun_full := fun ⟨stmtLast, oStmtLast⟩ tr witOut => by sorry

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
    (relIn := batchingInputRelation κ L K β ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn 0)
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

/-- RBR knowledge soundness for the batching phase oracle verifier. -/
theorem batchingOracleVerifier_rbrKnowledgeSoundness :
  OracleVerifier.rbrKnowledgeSoundness
    (verifier := batchingOracleVerifier κ L K β ℓ ℓ' h_l (𝓑:=𝓑) (aOStmtIn:=aOStmtIn))
    (init := init) (impl := impl)
    (relIn := batchingInputRelation κ L K β ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn 0)
    (rbrKnowledgeError := batchingRBRKnowledgeError (κ:=κ) (L:=L) (K:=K)) := by
  -- Proof follows by constructing the extractor and knowledge state function.
  use batchingWitMid L K ℓ ℓ'
  use batchingRbrExtractor κ L K β ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)
  use batchingKnowledgeStateFunction κ L K β ℓ ℓ' h_l (aOStmtIn:=aOStmtIn) (init:=init) (impl:=impl)
  intro stmtIn witIn prover iChal
  -- `KState 1 = (t' = packMLE t) ∧ (ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1})))`
    -- `∧ (s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v.`
  -- `KState 2 = (s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v) ∧`
    -- `h = projectSumcheckPoly t' 0 r r' ∧ s_0 = Σ_{w ∈ {0,1}^{ℓ'}} h(w)`
  -- ⊢ `Pr[KState(2, witMidSucc) ∧ ¬KState(1, extractMid(iChal, witMidSucc))] ≤ (κ/|L|)`
  sorry

end BatchingPhase
end Binius.RingSwitching
