/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
import ArkLib.ProofSystem.RingSwitching.Packing.Spec
import ArkLib.OracleReduction.Basic
import ArkLib.OracleReduction.Completeness
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import CompPoly.Fields.Binary.Tower.TensorAlgebra

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix Binius.BinaryBasefold ProbabilityTheory
open scoped NNReal
open Sumcheck.Structured

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

Input: `witIn = BatchingWitIn, stmtIn = BatchingStmtIn, oStmt = aOStmtIn.OStmtIn`

Output: `witOut = (Statement (L := L) (ℓ := ℓ')`
  `(RingSwitchingBaseContext κ L K ℓ P) 0) × (SumcheckWitness L ℓ' 0), oStmt = aOStmtIn.OStmtIn`
-/

noncomputable section
namespace RingSwitching.BatchingPhase

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (aOStmtIn : AbstractOStmtIn L ℓ')

/-! ## Formalized Helper Functions
These functions provide concrete implementations for tensor algebra operations
and other logic required by the protocol.
-/

/-- A dummy state returned by the verifier upon failure of Check 1. -/
def failureState (stmt : BatchingStmtIn L ℓ) (s_hat : P.A) :
  Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0 := {
    ctx := {
      t_eval_point := stmt.t_eval_point,
      original_claim := stmt.original_claim
      s_hat := s_hat,
      r_batching := 0, -- Dummy value
    },
    sumcheck_target := 0,
    challenges := Fin.elim0
  }

/-! ## Prover and Verifier Implementation -/

/-- The state maintained by the prover throughout the batching phase. -/
def PrvState : Fin (2 + 1) → Type
  | ⟨0, _⟩ => BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j) × BatchingWitIn L K ℓ ℓ'
  | ⟨1, _⟩ => BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)
    × BatchingWitIn L K ℓ ℓ' × P.A
  | _ => BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)
    × BatchingWitIn L K ℓ ℓ' × P.A × (Fin κ → L)

/-! ## Logic Infrastructure (relations + `ReductionLogicStep`), needed by prover/verifier. -/

def batchingInputRelationProp (stmt : BatchingStmtIn L ℓ)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) (wit : BatchingWitIn L K ℓ ℓ') : Prop :=
  wit.t' = packMLE κ L K ℓ ℓ' h_l P.basis wit.t ∧ stmt.original_claim = wit.t.val.aeval stmt.t_eval_point
  ∧ aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩

/-- Input relation: the witness `t` and `t'` are consistent,
and `t` satisfies the original claim. -/
def batchingInputRelation :
  Set ((BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)) × BatchingWitIn L K ℓ ℓ') :=
  {⟨⟨stmt, oStmt⟩, wit⟩ | batchingInputRelationProp κ L K P ℓ ℓ' h_l aOStmtIn stmt oStmt wit }

/-- Strict input relation for completeness proofs (carries `strictInitialCompatibility`). -/
def strictBatchingInputRelationProp (stmt : BatchingStmtIn L ℓ)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) (wit : BatchingWitIn L K ℓ ℓ') : Prop :=
  wit.t' = packMLE κ L K ℓ ℓ' h_l P.basis wit.t
  ∧ stmt.original_claim = wit.t.val.aeval stmt.t_eval_point
  ∧ aOStmtIn.strictInitialCompatibility ⟨wit.t', oStmt⟩

def strictBatchingInputRelation :
  Set ((BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)) × BatchingWitIn L K ℓ ℓ') :=
  {⟨⟨stmt, oStmt⟩, wit⟩ |
    strictBatchingInputRelationProp κ L K P ℓ ℓ' h_l aOStmtIn stmt oStmt wit }

lemma strictBatchingInputRelation_subset_batchingInputRelation :
    strictBatchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn ⊆
      batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn := by
  intro input h_input
  rcases input with ⟨⟨stmt, oStmt⟩, wit⟩
  rcases h_input with ⟨h_pack, h_claim, h_strict_compat⟩
  exact ⟨h_pack, h_claim,
    aOStmtIn.strictInitialCompatibility_implies_initialCompatibility oStmt wit.t' h_strict_compat⟩

/-! ## Pure Logic Functions (ReductionLogicStep Infrastructure)
Ported from our HEAD ring-switching architecture, Profile-parameterized (`β/𝓑 → P`, message
type `TensorAlgebra K L → P.A`). Uses our `ReductionLogicStep` (from `BinaryBasefold`) + strict
relations for completeness (relaxed stays for soundness). -/

/-- Pure verifier check: validates that the prover's ŝ satisfies Check 1. -/
@[reducible]
def batchingVerifierCheck (stmtIn : BatchingStmtIn L ℓ) (msg0 : P.A) : Prop :=
  performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l
    stmtIn.original_claim stmtIn.t_eval_point msg0 = true

/-- Pure verifier output: computes the output statement given the transcript. -/
@[reducible]
def batchingVerifierStmtOut (stmtIn : BatchingStmtIn L ℓ)
    (msg0 : P.A) (r_batching : Fin κ → L) :
    Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0 :=
  let s₀ := compute_s0 κ L K P msg0 r_batching
  let ctx : RingSwitchingBaseContext κ L K ℓ P := {
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

/-- Pure prover message computation: computes ŝ from the witness. -/
@[reducible]
def batchingProverComputeMsg (stmtIn : BatchingStmtIn L ℓ) (witIn : BatchingWitIn L K ℓ ℓ') :
    P.A :=
  embedded_MLP_eval κ L K P ℓ ℓ' h_l witIn.t' stmtIn.t_eval_point

/-- Pure prover output: computes the output witness given the transcript. -/
@[reducible]
def batchingProverWitOut (stmtIn : BatchingStmtIn L ℓ) (witIn : BatchingWitIn L K ℓ ℓ')
    (msg0 : P.A) (r_batching : Fin κ → L) :
    SumcheckWitness L ℓ' 0 :=
  let ctx : RingSwitchingBaseContext κ L K ℓ P := {
    t_eval_point := stmtIn.t_eval_point,
    original_claim := stmtIn.original_claim,
    s_hat := msg0,
    r_batching := r_batching
  }
  let h_poly : ↥L⦃≤ 2⦄[X Fin ℓ'] :=
    projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
      (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
      (ctx := ctx) (t := witIn.t') (i := 0) (challenges := Fin.elim0)
  {
    t' := witIn.t',
    H := h_poly
  }

/-- The Logic Instance for the Batching Phase (our `ReductionLogicStep` architecture). -/
def batchingStepLogic :
    Binius.BinaryBasefold.ReductionLogicStep
      (BatchingStmtIn L ℓ)
      (BatchingWitIn L K ℓ ℓ')
      (aOStmtIn.OStmtIn)
      (aOStmtIn.OStmtIn)
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
      (SumcheckWitness L ℓ' 0)
      (pSpecBatching κ L K P)
      where
  completeness_relIn := fun ((s, o), w) =>
    ((s, o), w) ∈ strictBatchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn
  completeness_relOut := fun ((s, o), w) =>
    ((s, o), w) ∈ strictSumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0
  verifierCheck := fun stmtIn transcript =>
    batchingVerifierCheck (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (stmtIn := stmtIn) (msg0 := transcript.messages ⟨0, rfl⟩)
  verifierOut := fun stmtIn transcript =>
    batchingVerifierStmtOut (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
      (stmtIn := stmtIn)
      (msg0 := transcript.messages ⟨0, rfl⟩) (r_batching := transcript.challenges ⟨1, rfl⟩)
  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun i => rfl
  honestProverTranscript := fun stmtIn witIn _oStmtIn chal =>
    let msg : P.A := batchingProverComputeMsg (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
      (ℓ' := ℓ') (h_l := h_l) (stmtIn := stmtIn) (witIn := witIn)
    FullTranscript.mk2 msg (chal ⟨1, rfl⟩)
  proverOut := fun stmtIn witIn oStmtIn transcript =>
    let msg0 : P.A := transcript.messages ⟨0, rfl⟩
    let r_batching : Fin κ → L := transcript.challenges ⟨1, rfl⟩
    let stmtOut := batchingVerifierStmtOut (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
      (stmtIn := stmtIn) (msg0 := msg0) (r_batching := r_batching)
    let witOut := batchingProverWitOut (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (stmtIn := stmtIn) (witIn := witIn) (msg0 := msg0) (r_batching := r_batching)
    ((stmtOut, oStmtIn), witOut)

noncomputable def oracleProver :
  OracleProver (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn L ℓ) (OStmtIn := aOStmtIn.OStmtIn) (WitIn := BatchingWitIn L K ℓ ℓ')
    (StmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ P) 0) (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' 0)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) where
  PrvState := PrvState κ L K P ℓ ℓ' aOStmtIn

  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)

  sendMessage
    | ⟨0, _⟩ => fun (stmt, oStmt, wit) => do
      -- USE THE SHARED KERNEL (Guarantees match with batchingStepLogic)
      let s_hat := batchingProverComputeMsg (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
        (ℓ' := ℓ') (h_l := h_l) stmt wit
      return ⟨s_hat, (stmt, oStmt, wit, s_hat)⟩
    | ⟨1, h⟩ => fun _ => do nomatch h -- V to P round

  receiveChallenge
    | ⟨0, h⟩ => nomatch h -- i.e. contradiction
    | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, s_hat⟩ => do
      return fun r_batching => (stmt, oStmt, wit, s_hat, r_batching)

  output := fun ⟨stmt, oStmt, wit, s_hat, r_batching⟩ => do
    -- Construct the transcript that the honest prover produces
    -- This matches logic.honestProverTranscript exactly
    let logic := (batchingStepLogic (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
      (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
    let challenges : (pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)).Challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 => exact False.elim (by simp only [ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue,
          cons_val_zero, Direction.not_P_to_V_eq_V_to_P] at hj)  -- No challenge at index 0
        | 1 => exact r_batching
    let t := logic.honestProverTranscript stmt wit oStmt challenges
    -- Delegate to Logic Instance (ensures consistency with batchingStepLogic)
    pure (logic.proverOut stmt wit oStmt t)

open Classical in
include h_l in
noncomputable def oracleVerifier :
  OracleVerifier (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn L ℓ) (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) where
  verify | stmtIn, pSpec_batching_challenges => do
     -- Query ŝ from Message 0.
    let s_hat : P.A ← query (spec := [pSpecBatching (κ:=κ)
      (L:=L) (K:=K) (P:=P).Message]ₒ) ⟨⟨0, by rfl⟩, (by exact ())⟩
    let r_batching : Fin κ → L := pSpec_batching_challenges ⟨1, by rfl⟩
    -- Reconstruct the transcript (matches what honestProverTranscript produces)
    let logic := (batchingStepLogic (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
      (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
    -- Note: We can't call honestProverTranscript directly because we don't have the witness
    -- But we know the transcript structure must match it
    let t := FullTranscript.mk2 s_hat r_batching
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)
  -- Reuse embed and hEq from batchingStepLogic to ensure consistency
  embed := (batchingStepLogic (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (aOStmtIn := aOStmtIn)).embed
  hEq := (batchingStepLogic (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (aOStmtIn := aOStmtIn)).hEq

/-- The Oracle Reduction for the Batching Phase. -/
noncomputable def batchingOracleReduction : OracleReduction (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn L ℓ) (OStmtIn := aOStmtIn.OStmtIn) (WitIn := BatchingWitIn L K ℓ ℓ')
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' 0)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) where
  prover := oracleProver κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)
  verifier := oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)

/-! ## RBR Knowledge Soundness Components -/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Intermediate witness types for RBR knowledge soundness. -/
def batchingWitMid : Fin (2 + 1) → Type
  | ⟨0, _⟩ => BatchingWitIn L K ℓ ℓ' -- Before any messages
  | ⟨1, _⟩ => BatchingWitIn L K ℓ ℓ' -- After P sends ŝ
  | ⟨2, _⟩ => SumcheckWitness L ℓ' 0 -- After V sends r'' and all computations are done

/-- RBR extractor for the batching phase. -/
noncomputable def batchingRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := BatchingWitIn L K ℓ ℓ')
    (WitOut := SumcheckWitness L ℓ' 0)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P))
    (WitMid := batchingWitMid L K ℓ ℓ') where
  eqIn := rfl
  extractMid m _ _ witSucc :=
    match m with
    | ⟨0, _⟩ => witSucc -- Extracting `WitIn` from a future `WitIn`
    | ⟨1, _⟩ => by
      exact { t := unpackMLE κ L K ℓ ℓ' h_l P.basis witSucc.t', t' := witSucc.t' }
  extractOut _ _ witOut := witOut

/-- RBR knowledge soundness error for the batching phase.
The only verifier randomness is `r''`; DP24's batching check is a nonzero `κ`-variate multilinear
identity test, giving the Schwartz-Zippel bound `κ/|L|`. -/
def batchingRBRKnowledgeError
    (i : (pSpecBatching (κ := κ) (L := L) (K := K) (P := P)).ChallengeIdx) : ℝ≥0 :=
  match i with
  | ⟨1, _⟩ => (κ : ℝ≥0) / (Fintype.card L : ℝ≥0) -- Schwartz-Zippel error
  | _ => 0 -- No other challenges

def batchingKStateProp {m : Fin (2 + 1)}
    (tr : Transcript m (pSpecBatching (κ := κ) (L := L) (K := K) (P := P)))
    (stmt : BatchingStmtIn L ℓ) (witMid : batchingWitMid L K ℓ ℓ' m)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) :
    Prop :=
  match m with
  | ⟨0, _⟩ => -- equiv s relIn
    batchingInputRelationProp κ L K P ℓ ℓ' h_l aOStmtIn stmt oStmt witMid
  | ⟨1, _⟩ => by -- P sends hᵢ(X)
    let ⟨msgsUpTo, _⟩ := Transcript.equivMessagesChallenges (k := 1)
      (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) tr
    let i_msg1 : ((pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)).take 1 (by omega)).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le (by omega)⟩, by simp [pSpecBatching]; rfl⟩
    let s_hat: P.A := msgsUpTo i_msg1
    exact
      witMid.t' = packMLE κ L K ℓ ℓ' h_l P.basis witMid.t -- implied by `extractMid`
      -- The last two constraints are equivalent to `t(r) = s`
      ∧ embedded_MLP_eval κ L K P ℓ ℓ' h_l witMid.t' stmt.t_eval_point = s_hat
      ∧ performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim
        stmt.t_eval_point s_hat -- local V check
      ∧ aOStmtIn.initialCompatibility ⟨witMid.t', oStmt⟩
  | ⟨2, _⟩ => by -- implied by relOut
    simp only [batchingWitMid] at witMid
    let ⟨msgsUpTo, chalsUpTo⟩ := Transcript.equivMessagesChallenges (k := 2)
      (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) tr
    let i_msg1 : ((pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)).take 2 (by omega)).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le (by omega)⟩, by simp [pSpecBatching]; rfl⟩
    let s_hat: P.A := msgsUpTo i_msg1
    let i_msg2 : ((pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)).take 2 (by omega)).ChallengeIdx :=
      ⟨⟨1, Nat.lt_of_succ_le (by omega)⟩, by simp [pSpecBatching]; rfl⟩
    let batching_challenges: Fin κ → L := chalsUpTo i_msg2

    let ctx : RingSwitchingBaseContext κ L K ℓ P := {
      t_eval_point := stmt.t_eval_point,
      original_claim := stmt.original_claim,
      s_hat := s_hat,
      r_batching := batching_challenges
    }
    let stmtOut : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0 := {
      ctx := ctx,
      sumcheck_target := compute_s0 κ L K P s_hat batching_challenges,
      challenges := Fin.elim0
    }
    let witOut : SumcheckWitness L ℓ' 0 := {
      t' := witMid.t',
      H := projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
        (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
        (ctx := ctx) (t := witMid.t') (i := 0) (challenges := Fin.elim0)
    }
    exact
      sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l aOStmtIn (i:=0) stmtOut oStmt witOut
      ∧ performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim
        stmt.t_eval_point s_hat -- local V check
      ∧ aOStmtIn.initialCompatibility ⟨witMid.t', oStmt⟩

/-- Knowledge state function for the batching phase. -/
noncomputable def batchingKnowledgeStateFunction [IsDomain K] [IsDomain L] :
  (oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)).KnowledgeStateFunction init impl
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (batchingRbrExtractor κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)) where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    batchingKStateProp κ L K P ℓ ℓ' h_l aOStmtIn tr stmt witMid oStmt
  toFun_empty _ _ := by rfl
  toFun_next := fun m hDir stmtIn tr msg witMid =>
    match m with
    | ⟨0, _⟩ => by -- from accumulative KState
      intro hSuccTrue
      simp only [batchingKStateProp, Fin.zero_eta, Fin.isValue, Fin.succ_zero_eq_one,
        Equiv.toFun_as_coe, Transcript.equivMessagesChallenges_apply, Fin.castSucc_zero,
        batchingRbrExtractor, Fin.mk_one, Fin.succ_one_eq_two,
        batchingInputRelationProp] at ⊢ hSuccTrue
      obtain ⟨h_t'_eq, h_embed_eq, h_check_true, h_compat⟩ := hSuccTrue
      refine ⟨h_t'_eq, ?_, ?_⟩
      · -- stmt.original_claim = witMid.t.val.aeval stmt.t_eval_point
        -- from `performCheck(original_claim, s_hat) = true` and
        -- `performCheck(t(r), s_hat) = true` (batching_check_correctness), by injectivity of check.
        have h_check_stmt :
            performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l
              stmtIn.1.original_claim stmtIn.1.t_eval_point
              (embedded_MLP_eval κ L K P ℓ ℓ' h_l witMid.t' stmtIn.1.t_eval_point) = true := by
          rw [h_embed_eq]; exact h_check_true
        have h_check_wit :
            performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l
              (witMid.t.val.aeval stmtIn.1.t_eval_point) stmtIn.1.t_eval_point
              (embedded_MLP_eval κ L K P ℓ ℓ' h_l witMid.t' stmtIn.1.t_eval_point) = true := by
          have h_honest :=
            batching_check_correctness (κ := κ) (L := L) (K := K) (P := P)
              (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (t := witMid.t)
              (eval_point := stmtIn.1.t_eval_point)
          rw [h_t'_eq]; exact h_honest
        have hs₁ := (decide_eq_true_eq.mp h_check_stmt)
        have hs₂ := (decide_eq_true_eq.mp h_check_wit)
        exact hs₁.trans hs₂.symm
      · -- aOStmtIn.initialCompatibility (witMid.t', stmtIn.2)
        exact h_compat
    | ⟨1, h⟩ => nomatch h
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut h_relOut => by
    -- h_relOut: ∃ stmtOut oStmtOut, verifier outputs (stmtOut, oStmtOut) with prob > 0
    --   and ((stmtOut, oStmtOut), witOut) ∈ relOut
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, Prod.exists] at h_relOut
    rcases h_relOut with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩
    have h_output_mem_V_run_support' :
        some (stmtOut, oStmtOut) ∈
          support (do
            let s ← init
            Prod.fst <$>
              (simulateQ impl
                (Verifier.run (stmtIn, oStmtIn) tr
                  (oracleVerifier κ L K P ℓ ℓ' h_l
                    (aOStmtIn := aOStmtIn)).toVerifier)).run s) := by
      exact (OptionT.mem_support_iff
        (mx := OptionT.mk (do
          let s ← init
          Prod.fst <$>
            (simulateQ impl
              (Verifier.run (stmtIn, oStmtIn) tr
                (oracleVerifier κ L K P ℓ ℓ' h_l
                  (aOStmtIn := aOStmtIn)).toVerifier)).run s))
        (x := (stmtOut, oStmtOut))).1 h_output_mem_V_run_support
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output_mem_V_run_support'
    rcases h_output_mem_V_run_support' with ⟨s, hs_init, h_output_mem_V_run_support⟩
    conv at h_output_mem_V_run_support =>
      simp only [Verifier.run, OracleVerifier.toVerifier]
      -- Now unfold the oracleVerifier's `verify()` method
      simp only [oracleVerifier]
      -- oracle query unfolding
      simp only [support_bind, Set.mem_iUnion]
      dsimp only [StateT.run]
      simp only [simulateQ_bind]
      unfold OracleInterface.answer
      ---------------------------------------
      -- Now simplify the `guard` and `ite` of StateT.map generated from it
      simp only [MessageIdx, Fin.isValue, Matrix.cons_val_zero, simulateQ_pure, Message, guard_eq,
        pure_bind, Function.comp_apply, simulateQ_map, simulateQ_ite,
        OptionT.simulateQ_failure, bind_map_left]
      simp only [MessageIdx, Message, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        bind_pure_comp, simulateQ_map, simulateQ_ite, simulateQ_pure, OptionT.simulateQ_failure,
        bind_map_left, Function.comp_apply]
      simp only [support_ite]
      simp only [Fin.isValue, Set.mem_ite_empty_right, Set.mem_singleton_iff, Prod.mk.injEq,
        exists_and_left, exists_eq', exists_eq_right, exists_and_right]
      erw [simulateQ_bind]
      enter [1, x, 1, 2, 1, 2];
      erw [simulateQ_bind]
      erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      simp only [Fin.isValue, FullTranscript.mk1_eq_snoc, pure_bind, OptionT.simulateQ_map]
    conv at h_output_mem_V_run_support =>
      simp only [Fin.isValue, cons_val_zero, id_eq, Function.comp_apply, support_map, Set.mem_image,
        Prod.exists, exists_and_right, exists_eq_right]
    simp only [show OptionT.pure (m := (OracleComp ([]ₒ))) = pure by rfl]
      at h_output_mem_V_run_support
    erw [support_bind] at h_output_mem_V_run_support
    set V_check := (batchingStepLogic κ L K P ℓ ℓ' h_l aOStmtIn).verifierCheck stmtIn
      (FullTranscript.mk2 (msg0 :=
        (OracleInterface.answer (Message := P.A)
          (FullTranscript.messages tr ⟨(0 : Fin 2), rfl⟩) ())
      ) (msg1 := FullTranscript.challenges tr ⟨(1 : Fin 2), rfl⟩)) with h_V_check_def
    by_cases h_V_check : V_check
    · simp only [Fin.isValue, h_V_check, ↓reduceIte, OptionT.run_pure, simulateQ_pure,
      Set.mem_iUnion, exists_prop, Prod.exists] at h_output_mem_V_run_support
      erw [simulateQ_bind] at h_output_mem_V_run_support
      erw [simulateQ_pure] at h_output_mem_V_run_support
      simp only [Fin.isValue, Function.comp_apply,
        pure_bind] at h_output_mem_V_run_support
      rw [if_pos (h_V_check_def ▸ h_V_check)] at h_output_mem_V_run_support
      erw [_root_.map_pure] at h_output_mem_V_run_support
      erw [simulateQ_pure] at h_output_mem_V_run_support
      (try erw [simulateQ_pure] at h_output_mem_V_run_support)
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Fin.isValue, Set.mem_singleton_iff, Prod.mk.injEq, ↓existsAndEq, and_true,
        exists_eq_left] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Fin.isValue, Set.mem_singleton_iff, Option.some.injEq,
        Prod.mk.injEq] at h_output_mem_V_run_support
      rcases h_output_mem_V_run_support with ⟨init_value, ⟨h_stmtOut_eq, h_oStmtOut_eq⟩,
        h_initValue_eq⟩
      simp only [Fin.reduceLast, Fin.isValue]
      dsimp only [sumcheckRoundRelation, sumcheckRoundRelationProp, masterKStateProp,
        Set.mem_setOf_eq] at h_relOut
      unfold batchingKStateProp
      simp only [Fin.isValue, batchingWitMid]
      dsimp only [Transcript.equivMessagesChallenges, Equiv.coe_fn_mk,
        Transcript.toMessagesChallenges, Transcript.toMessagesUpTo, Transcript.toChallengesUpTo]
      set s_hat := tr.messages ⟨(0 : Fin 2), rfl⟩ with _h_s_hat
      set batching_challenges := tr.challenges ⟨(1 : Fin 2), rfl⟩ with _h_chal
      set ctx : RingSwitchingBaseContext κ L K ℓ P :=
        { t_eval_point := stmtIn.t_eval_point, original_claim := stmtIn.original_claim,
          s_hat := s_hat, r_batching := batching_challenges } with h_ctx_def
      set stmtOut_computed : Statement (RingSwitchingBaseContext κ L K ℓ P) 0 :=
        batchingVerifierStmtOut (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
        stmtIn s_hat batching_challenges with _h_stmtOut
      have h_stmtOut_eq_computed : stmtOut = stmtOut_computed := by
        rw [h_stmtOut_eq]; rfl
      rw [h_stmtOut_eq_computed] at h_relOut
      constructor
      · -- masterKStateProp with oStmtOut/witOut → sumcheckRoundRelationProp with
        -- oStmtLast/extractOut; extractOut = id; need embed compatibility
        have h_oStmtOut_eq_oStmtIn : oStmtOut = oStmtIn := by
          rw [h_oStmtOut_eq]
          funext j
          simp [OracleVerifier.mkVerifierOStmtOut, batchingStepLogic]
        rw [h_oStmtOut_eq_oStmtIn] at h_relOut
        show sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l aOStmtIn 0 stmtOut_computed oStmtIn _
        unfold sumcheckRoundRelationProp masterKStateProp
        have h_cons :
            sumcheckConsistencyProp (boolDomain L _)
              stmtOut_computed.sumcheck_target witOut.H := h_relOut.2.2.1
        have h_wit_struct :
            witOut.H.val = (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
              (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
              (ctx := stmtOut_computed.ctx) (t := witOut.t')
              (i := 0) (challenges := stmtOut_computed.challenges)).val := h_relOut.2.1
        have h_h_goal_eq :
            (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
              (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
              (ctx := ctx) (t := witOut.t')
              (i := 0) (challenges := Fin.elim0)).val =
            (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
              (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
              (ctx := stmtOut_computed.ctx) (t := witOut.t')
              (i := 0) (challenges := stmtOut_computed.challenges)).val := by
          subst ctx
          simp only [Fin.coe_ofNat_eq_mod, stmtOut_computed]
        have h_wit_H_eq_goal :
            witOut.H.val =
              (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
                (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
                (ctx := ctx) (t := witOut.t')
                (i := 0) (challenges := Fin.elim0)).val := by
          rw [h_wit_struct, ← h_h_goal_eq]
        refine ⟨trivial, ?_, ?_, ?_⟩
        · -- witnessStructuralInvariant: goal's H is the reconstructed poly, RHS is the same up to
          -- defeq (`ctx` vs the inlined ctx record, `Fin.elim0` vs `stmtOut_computed.challenges`).
          unfold witnessStructuralInvariant
          rfl
        · -- sumcheckConsistencyProp: transport `h_cons` (stated for `witOut.H`) across the
          -- `.val`-equality `h_wit_H_eq_goal` to the goal's reconstructed `H`.
          convert h_cons using 3
          · rfl
          · exact Subtype.ext h_wit_H_eq_goal.symm
        · -- initialCompatibility
          dsimp [batchingRbrExtractor]
          exact h_relOut.2.2.2
      · constructor
        · exact h_V_check  -- verifierCheck is performCheckOriginalEvaluation ... = true
        · rw [h_oStmtOut_eq] at h_relOut
          dsimp [batchingRbrExtractor]
          exact h_relOut.2.2.2
    · simp only [Fin.isValue, h_V_check, ↓reduceIte, OptionT.run_failure, simulateQ_pure,
        Set.mem_iUnion, exists_prop, Prod.exists] at h_output_mem_V_run_support
      erw [simulateQ_bind] at h_output_mem_V_run_support
      erw [simulateQ_pure] at h_output_mem_V_run_support
      simp only [Fin.isValue, Function.comp_apply,
        pure_bind] at h_output_mem_V_run_support
      rw [if_neg (h_V_check_def ▸ h_V_check)] at h_output_mem_V_run_support
      erw [map_failure] at h_output_mem_V_run_support
      erw [OptionT.simulateQ_failure] at h_output_mem_V_run_support
      obtain ⟨x, a, b, hab, hsome⟩ := h_output_mem_V_run_support
      rw [OracleComp.failure_def] at hab
      unfold OptionT.fail at hab
      erw [simulateQ_pure] at hab
      rw [show ((pure none : StateT σ ProbComp (Option (Statement
        (RingSwitchingBaseContext κ L K ℓ P) 0))) s) = pure (none, s) from rfl] at hab
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hab
      obtain ⟨ha, hb⟩ := hab
      subst ha
      dsimp only at hsome
      erw [simulateQ_pure] at hsome
      change (some (stmtOut, oStmtOut), x) ∈ _root_.support (pure (none, b)) at hsome
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq,
        false_and] at hsome

/-- The batching logic step is strongly complete: on any input in the strict input relation, the
honest transcript passes the verifier check and the outputs satisfy the strict round relation.
Ported from HEAD `batchingStep_is_logic_complete` (`β/𝓑 → P`); uses `batching_check_correctness`
(Check 1 correctness) and `batching_target_consistency` (sumcheck-target consistency). -/
lemma batchingStep_is_logic_complete [IsDomain K] [IsDomain L] :
    (batchingStepLogic (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (aOStmtIn := aOStmtIn)).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := (batchingStepLogic (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
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
  let r_batching := challenges ⟨1, rfl⟩
  have h_s_hat_eq : transcript.messages ⟨0, rfl⟩ = embedded_MLP_eval κ L K P ℓ ℓ' h_l
    (packMLE κ L K ℓ ℓ' h_l P.basis witIn.t) stmtIn.t_eval_point := by
    dsimp only [transcript, step, batchingStepLogic]
    unfold FullTranscript.mk2
    dsimp only [batchingProverComputeMsg]
    rw [h_t'_eq_t_packed]
  -- Fact 1: Verifier check passes
  have hVCheck_passed : step.verifierCheck stmtIn transcript := by
    simp only [step, batchingStepLogic, batchingVerifierCheck]
    have res := batching_check_correctness (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
      (ℓ' := ℓ') (h_l := h_l) (t := witIn.t) (eval_point := stmtIn.t_eval_point)
    rw [← h_s_hat_eq] at res
    rw [h_original_evaluation_claim]
    exact res
  -- Fact 2: Output relation holds (strictSumcheckRoundRelation 0)
  have hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    simp only [step, batchingStepLogic, strictSumcheckRoundRelation, strictSumcheckRoundRelationProp,
      Set.mem_setOf_eq]
    dsimp only [masterStrictKStateProp]
    refine ⟨trivial, ?_, ?_, ?_⟩
    · -- ⊢ witnessStructuralInvariant κ L K P ℓ ℓ' h_l verifierStmtOut proverWitOut
      rfl
    · -- ⊢ sumcheckConsistencyProp (boolDomain L _) verifierStmtOut.sumcheck_target proverWitOut.H
      exact batching_target_consistency κ L K P ℓ ℓ' h_l witIn.t'
        (transcript.messages ⟨0, rfl⟩) verifierStmtOut.ctx
        (by
          rw [h_t'_eq_t_packed]
          change transcript.messages ⟨0, rfl⟩ =
            embedded_MLP_eval κ L K P ℓ ℓ' h_l (packMLE κ L K ℓ ℓ' h_l P.basis witIn.t)
              stmtIn.t_eval_point
          exact h_s_hat_eq)
    · -- ⊢ aOStmtIn.strictInitialCompatibility (proverWitOut.t', verifierOStmtOut)
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
    rfl
  -- Combine all facts
  exact ⟨hVCheck_passed, hRelOut, hStmtOut_eq, hOStmtOut_eq⟩

/-! ## Security Properties -/

/-- Perfect completeness for the batching phase oracle reduction (strict frame).

This theorem proves that the honest prover-verifier interaction for the batching phase
always succeeds (with probability 1) and produces valid outputs.

**Proof Strategy:** (ported from HEAD `batchingReduction_perfectCompleteness`, `β/𝓑 → P`)
1. Unroll the 2-message reduction to convert probabilistic statement to logical statement
2. Split into safety (no failures) and correctness (valid outputs)
3. For safety: prove the verifier never crashes on honest prover messages
4. For correctness: apply `batchingStep_is_logic_complete` (`IsStronglyComplete`)
-/
theorem batchingReduction_perfectCompleteness [IsDomain K] [IsDomain L] (hInit : NeverFail init) :
  OracleReduction.perfectCompleteness
    (oracleReduction := batchingOracleReduction κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn))
    (relIn := strictBatchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := strictSumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (init := init) (impl := impl) := by
  classical
  -- Step 1: Unroll the 2-message reduction to convert from probability to logic
  rw [OracleReduction.unroll_2_message_reduction_perfectCompleteness
    (pSpec := pSpecBatching κ L K P)
    (reduction := batchingOracleReduction κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn))
    (relIn := strictBatchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := strictSumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (init := init) (impl := impl) hInit (by rfl) (by rfl)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- Step 2: Convert probability 1 to universal quantification over support.
  simp only [probEvent_eq_one_iff]
  -- Step 3: Unfold protocol definitions
  dsimp only [batchingOracleReduction, oracleProver, oracleVerifier,
    OracleVerifier.toVerifier, FullTranscript.mk2]
  let step := (batchingStepLogic (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (aOStmtIn := aOStmtIn))
  let strongly_complete : step.IsStronglyComplete := batchingStep_is_logic_complete (κ := κ)
    (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn)
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
        liftComp_eq_liftM, OptionT.probFailure_lift, probFailure_eq_zero]
    rw [true_and]
    intro r_i' h_r_i'_mem_query_1_support
    conv =>
      enter [1];
      simp only [probFailure_eq_zero_iff]
      simp only [liftM, monadLift, MonadLift.monadLift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        Fin.succ_one_eq_two, Message, Fin.succ_zero_eq_one, Fin.castSucc_one, liftComp_eq_liftM,
        OptionT.probFailure_lift, probFailure_eq_zero]
    rw [true_and]
    intro h_receive_challenge_fn h_receive_challenge_fn_mem_support
    conv =>
      enter [1];
      simp only [probFailure_eq_zero_iff]
      simp only [liftM, monadLift, MonadLift.monadLift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        Fin.succ_one_eq_two, Message, Fin.succ_zero_eq_one, Fin.castSucc_one, liftComp_eq_liftM,
        OptionT.probFailure_lift, probFailure_eq_zero]
    rw [true_and]
    -- ⊢ ∀ x ∈ .. support, ... ∧ ... ∧ ...
    intro h_prover_final_output h_prover_final_output_support
    conv =>
      simp only [guard_eq] -- simplify the `guard`
      enter [2];
      simp only [bind_pure_comp, NeverFail.probFailure_eq_zero, implies_true]
    rw [and_true]
    erw [OptionT.probFailure_liftComp_of_OracleComp_Option
      (superSpec := []ₒ + [(pSpecBatching κ L K P).Challenge]ₒ)]
    conv_lhs =>
      enter [1]
      simp only [MessageIdx, Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one,
        id_eq, bind_pure_comp, OptionT.run_map, probFailure_eq_zero]
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
    conv at h_vStmtOut_mem_support =>
      erw [simulateQ_bind]
      erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      change vStmtOut ∈ support (Bind.bind (m := (OracleComp []ₒ)) _ _)
      erw [_root_.bind_pure_simulateQ_comp]
      simp only [Matrix.cons_val_zero, guard_eq]
      rw [bind_pure_comp]
      dsimp only [Functor.map]
      erw [OptionT.simulateQ_bind]
      erw [support_bind]
      erw [OptionT.simulateQ_ite]
      simp only [Fin.isValue, Message, Matrix.cons_val_zero, id_eq, MessageIdx, support_ite,
        toPFunctor_emptySpec, Function.comp_apply, OptionT.simulateQ_pure, Set.mem_iUnion,
        exists_prop]
      simp only [OptionT.simulateQ_failure]
      erw [_root_.simulateQ_pure]
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk2
        (msg0 := _)
        (msg1 := (FullTranscript.mk2 (batchingProverComputeMsg κ L K P ℓ ℓ' h_l stmtIn witIn)
          r_i').challenges ⟨1, rfl⟩))
      with h_V_check_def
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecBatching κ L K P).dir 0 ≠ Direction.V_to_P := by
            simp only [ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue, Matrix.cons_val_zero,
              Direction.not_P_to_V_eq_V_to_P]
          exfalso
          exact hj_ne hj
        | 1 => exact r_i'
      )
    have h_inputState_eq : inputState = (batchingProverComputeMsg κ L K P ℓ ℓ' h_l stmtIn witIn,
        stmtIn, oStmtIn, witIn, batchingProverComputeMsg κ L K P ℓ ℓ' h_l stmtIn witIn) :=
      hInputState_mem_support
    have h_inputState1 : inputState.1 = batchingProverComputeMsg κ L K P ℓ ℓ' h_l stmtIn witIn := by
      rw [h_inputState_eq]
    have h_V_check_is_true : V_check := by
      rw [h_V_check_def]
      convert h_V_check using 2
      rw [h_inputState1]
      show FullTranscript.mk2 (OracleInterface.toOC.impl ()
          (batchingProverComputeMsg κ L K P ℓ ℓ' h_l stmtIn witIn)) r_i'
        = (batchingStepLogic κ L K P ℓ ℓ' h_l aOStmtIn).honestProverTranscript stmtIn witIn oStmtIn _
      rfl
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
      erw [ReduceClaim.support_mk _, support_pure]
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
      Fin.reduceLast, MessageIdx, Message, exists_eq_left, exists_eq_left', Set.mem_setOf_eq,
      exists_prop] at hx_mem_support
    -- Step 2b: Extract the challenge r1 and the trace equations
    obtain ⟨r1, ⟨_h_r1_mem_challenge_support, h_trace_support⟩⟩ := hx_mem_support
    rcases h_trace_support with ⟨prvOut_eq, h_verOut_mem_support⟩
    -- Step 2c: Simplify the verifier computation
    conv at h_verOut_mem_support =>
      erw [simulateQ_bind]
      erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      erw [_root_.bind_pure_simulateQ_comp]
      simp only [Matrix.cons_val_zero, guard_eq]
      erw [simulateQ_bind]
      simp only [show OptionT.pure (m := (OracleComp ([]ₒ +
        [(pSpecBatching κ L K P).Challenge]ₒ))) = pure by rfl]
      erw [OptionT.simulateQ_ite]
      simp only [Fin.isValue, Message, Matrix.cons_val_zero, id_eq, MessageIdx, support_ite,
        toPFunctor_emptySpec, Function.comp_apply, simulateQ_pure, Set.mem_iUnion,
        exists_prop]
      simp only [OptionT.simulateQ_failure]
      erw [_root_.simulateQ_pure]
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk2
        (msg0 := _)
        (msg1 := (FullTranscript.mk2 (batchingProverComputeMsg κ L K P ℓ ℓ' h_l stmtIn witIn)
          r1).challenges ⟨1, rfl⟩))
      with h_V_check_def
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecBatching κ L K P).dir 0 ≠ Direction.V_to_P := by
            simp only [ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue, Matrix.cons_val_zero,
              Direction.not_P_to_V_eq_V_to_P]
          exfalso
          exact hj_ne hj
        | 1 => exact r1
      )
    have h_V_check_is_true : V_check := h_V_check
    simp only [h_V_check_is_true, ↓reduceIte, Fin.isValue, pure_bind] at h_verOut_mem_support
    obtain ⟨h_prvOut_fn, h_prvOut_eq, h_verOut_eq⟩ := h_verOut_mem_support
    subst h_prvOut_fn
    simp only [Fin.isValue] at h_prvOut_eq
    -- `h_prvOut_eq` : prover output membership in a `pure` support
    erw [liftM_pure] at h_prvOut_eq
    simp only [Fin.isValue, support_pure, Set.mem_singleton_iff] at h_prvOut_eq
    -- `h_verOut_eq` : verifier output membership in a `pure` support
    erw [OptionT.simulateQ_pure, map_pure, liftM_pure] at h_verOut_eq
    simp only [Fin.isValue, support_pure, Set.mem_singleton_iff, Option.some.injEq,
      Prod.mk.injEq] at h_verOut_eq
    obtain ⟨rfl, rfl⟩ := h_verOut_eq
    rw [Prod.mk.injEq, Prod.mk.injEq] at h_prvOut_eq
    obtain ⟨⟨prvStmtOut_eq, prvOStmtOut_eq⟩, prvWitOut_eq⟩ := h_prvOut_eq
    constructor
    · rw [prvWitOut_eq]
      exact h_rel
    · refine ⟨?_, ?_⟩
      · rw [prvStmtOut_eq]; rfl
      · rw [prvOStmtOut_eq]
        exact h_agree.2

/-- Repacking the unpacked polynomial is identity for multilinear `t'`. -/
lemma batching_pack_unpack_id [IsDomain K] [IsDomain L]
    (t' : Sumcheck.Structured.MultilinearPoly L ℓ') :
    packMLE κ L K ℓ ℓ' h_l P.basis (unpackMLE κ L K ℓ ℓ' h_l P.basis t') = t' := by
  apply Subtype.ext
  simp [packMLE, unpackMLE]
  change MvPolynomial.MLE t'.val.toEvalsZeroOne = t'.val
  exact (MvPolynomial.is_multilinear_iff_eq_evals_zeroOne (p := t'.val)).mp t'.property

/-- `compute_s0` is evaluation of the column-MLE at the batching challenge. -/
lemma batching_compute_s0_eq_eval_MLE
    (s_hat : P.A) (y : Fin κ → L) :
    compute_s0 κ L K P s_hat y =
      MvPolynomial.eval y
        (MvPolynomial.MLE (fun u : Fin κ → Fin 2 =>
          P.decomposeColumns s_hat u)) := by
  classical
  rw [compute_s0, MvPolynomial.MLE]
  simp_rw [MvPolynomial.eqTilde]
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

/-- Mismatch polynomial from column-decomposition difference `msg0 - s_bar`. -/
def batchingMismatchPoly (msg0 s_bar : P.A) : MvPolynomial (Fin κ) L :=
  MvPolynomial.MLE (fun u : Fin κ → Fin 2 =>
    P.decomposeColumns msg0 u -
    P.decomposeColumns s_bar u)

/-- The mismatch polynomial evaluates to the `compute_s0` difference. -/
lemma batching_compute_s0_sub_eq_eval_mismatch
    (msg0 s_bar : P.A) (y : Fin κ → L) :
    compute_s0 κ L K P msg0 y - compute_s0 κ L K P s_bar y =
      MvPolynomial.eval y
        (batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar) := by
  rw [batching_compute_s0_eq_eval_MLE (κ := κ) (L := L) (K := K) (P := P)
    (s_hat := msg0) (y := y)]
  rw [batching_compute_s0_eq_eval_MLE (κ := κ) (L := L) (K := K) (P := P)
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
    (msg0 s_bar : P.A) :
    (batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar).totalDegree ≤ κ := by
  let Q := batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar
  have h_mem : Q ∈ MvPolynomial.restrictDegree (Fin κ) L 1 := by
    dsimp [Q, batchingMismatchPoly]
    exact (MvPolynomial.MLE_mem_restrictDegree (σ := Fin κ) (R := L)
      (evals := fun u : Fin κ → Fin 2 =>
        P.decomposeColumns msg0 u -
        P.decomposeColumns s_bar u))
  have h_degOf : ∀ i : Fin κ, MvPolynomial.degreeOf i Q ≤ 1 := by
    intro i
    exact (MvPolynomial.mem_restrictDegree_iff_degreeOf_le (p := Q) (n := 1)).1 h_mem i
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
      have h_card : m.support.card ≤ Fintype.card (Fin κ) := Finset.card_le_univ (s := m.support)
      rw [Fintype.card_fin] at h_card
      exact h_card

/-- If embedded evaluation mismatches `msg0`, the mismatch polynomial is nonzero. -/
lemma batchingMismatchPoly_nonzero_of_embed_ne [IsDomain L]
    (stmt : BatchingStmtIn L ℓ)
    (msg0 : P.A)
    (t' : Sumcheck.Structured.MultilinearPoly L ℓ')
    (h_embed_ne : embedded_MLP_eval κ L K P ℓ ℓ' h_l t' stmt.t_eval_point ≠ msg0) :
    batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0
      (embedded_MLP_eval κ L K P ℓ ℓ' h_l t' stmt.t_eval_point) ≠ 0 := by
  let s_bar := embedded_MLP_eval κ L K P ℓ ℓ' h_l t' stmt.t_eval_point
  have h_rows_ne :
      (P.decomposeColumns msg0) ≠
      (P.decomposeColumns s_bar) := by
    intro h_eq
    have hs : msg0 = s_bar := P.decomposeColumns_injective h_eq
    have hs' : s_bar = msg0 := hs.symm
    dsimp [s_bar] at hs'
    exact h_embed_ne hs'
  have h_diff_ne :
      (fun u : Fin κ → Fin 2 =>
        P.decomposeColumns msg0 u -
        P.decomposeColumns s_bar u) ≠ 0 := by
    intro h_zero
    apply h_rows_ne
    funext u
    exact sub_eq_zero.mp (congrFun h_zero u)
  intro h_poly_zero
  have h_poly_zero' :
      batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar = 0 := by
    dsimp [s_bar] at h_poly_zero ⊢
    exact h_poly_zero
  apply h_diff_ne
  funext u
  have hu_eval_zero :
      MvPolynomial.eval (fun i => ((u i : Fin 2) : L))
        (batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar) = 0 := by
    rw [h_poly_zero']
    simp
  have hu_eval_mle :
      MvPolynomial.eval (fun i => ((u i : Fin 2) : L))
        (batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar) =
      P.decomposeColumns msg0 u -
        P.decomposeColumns s_bar u := by
    simp [batchingMismatchPoly, MvPolynomial.MLE_eval_zeroOne]
  rw [hu_eval_mle] at hu_eval_zero
  exact hu_eval_zero

/-- If `msg0 ≠ s_bar` in the tensor algebra, the mismatch polynomial is nonzero.
  Generalization of `batchingMismatchPoly_nonzero_of_embed_ne`. -/
lemma batchingMismatchPoly_nonzero_of_ne
    (msg0 s_bar : P.A)
    (h_ne : msg0 ≠ s_bar) :
    batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar ≠ 0 := by
  have h_rows_ne :
      (P.decomposeColumns msg0) ≠
      (P.decomposeColumns s_bar) := by
    intro h_eq
    exact h_ne (P.decomposeColumns_injective h_eq)
  have h_diff_ne :
      (fun u : Fin κ → Fin 2 =>
        P.decomposeColumns msg0 u -
        P.decomposeColumns s_bar u) ≠ 0 := by
    intro h_zero
    apply h_rows_ne
    funext u
    exact sub_eq_zero.mp (congrFun h_zero u)
  intro h_poly_zero
  apply h_diff_ne
  funext u
  have hu_eval_zero :
      MvPolynomial.eval (fun i => ((u i : Fin 2) : L))
        (batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar) = 0 := by
    rw [h_poly_zero]; simp
  have hu_eval_mle :
      MvPolynomial.eval (fun i => ((u i : Fin 2) : L))
        (batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar) =
      P.decomposeColumns msg0 u -
        P.decomposeColumns s_bar u := by
    simp [batchingMismatchPoly, MvPolynomial.MLE_eval_zeroOne]
  rw [hu_eval_mle] at hu_eval_zero
  exact hu_eval_zero

/-- From `KState 2` truth, derive equality of the two `compute_s0` forms. -/
lemma batching_compute_eq_from_hafter [IsDomain L]
    (stmtOStmtIn : (BatchingStmtIn L ℓ) × (∀ j, aOStmtIn.OStmtIn j))
    (msg0 : (pSpecBatching (κ := κ) (L := L) (K := K) (P := P)).Message ⟨0, rfl⟩)
    (y : Fin κ → L)
    (witMid : batchingWitMid L K ℓ ℓ' 2)
    (h_after : batchingKStateProp (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (aOStmtIn := aOStmtIn) (tr := FullTranscript.mk2 msg0 y) stmtOStmtIn.1
      witMid stmtOStmtIn.2) :
    compute_s0 κ L K P msg0 y =
      compute_s0 κ L K P
        (embedded_MLP_eval κ L K P ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point) y := by
  dsimp [batchingKStateProp] at h_after
  have h_sumcheck_msg0 := h_after.1
  dsimp [sumcheckRoundRelationProp, masterKStateProp] at h_sumcheck_msg0
  have h_msg :
      sumcheckConsistencyProp (boolDomain L _)
        (compute_s0 κ L K P msg0 y)
        (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
          (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
          (ctx := { t_eval_point := stmtOStmtIn.1.t_eval_point,
                    original_claim := stmtOStmtIn.1.original_claim,
                    s_hat := msg0,
                    r_batching := y })
          (t := witMid.t') (i := 0) (challenges := Fin.elim0)) := h_sumcheck_msg0.2.2.1
  have h_bar :
      sumcheckConsistencyProp (boolDomain L _)
        (compute_s0 κ L K P
          (embedded_MLP_eval κ L K P ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point) y)
        (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
          (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
          (ctx := { t_eval_point := stmtOStmtIn.1.t_eval_point,
                    original_claim := stmtOStmtIn.1.original_claim,
                    s_hat := msg0,
                    r_batching := y })
          (t := witMid.t') (i := 0) (challenges := Fin.elim0)) := by
    exact batching_target_consistency (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
      (ℓ' := ℓ') (h_l := h_l) (t' := witMid.t')
      (msg0 := embedded_MLP_eval κ L K P ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point)
      (ctx := { t_eval_point := stmtOStmtIn.1.t_eval_point,
                original_claim := stmtOStmtIn.1.original_claim,
                s_hat := msg0,
                r_batching := y })
      rfl
  unfold Sumcheck.Structured.sumcheckConsistencyProp at h_msg h_bar
  exact h_msg.trans h_bar.symm

/-- The "bad batching event": the prover's ŝ (`msg0`) disagrees with the honest ŝ (`s_bar`),
  but their `compute_s0` values agree at the batching challenges `y`.
  Corresponds to $S(r''_0, \ldots, r''_{\kappa-1}) = 0$ in Theorem 3.5 of the spec, where
  $S(X) := \sum_{u \in \mathcal{B}_\kappa} (\hat{s}_u - \bar{s}_u) \cdot \widetilde{eq}(u, X)$. -/
def badBatchingEventProp (y : Fin κ → L) (msg0 s_bar : P.A) : Prop :=
  msg0 ≠ s_bar ∧ compute_s0 κ L K P msg0 y = compute_s0 κ L K P s_bar y

/-- **Schwartz-Zippel bound for the bad batching event.**
  When `msg0 = s_bar`, the event never holds (first conjunct is `False`).
  When `msg0 ≠ s_bar`, the mismatch polynomial $S$ is nonzero with `totalDegree ≤ κ`,
  so Schwartz-Zippel gives `Pr[S(y) = 0] ≤ κ / |L|`. -/
lemma probability_bound_badBatchingEventProp [IsDomain L]
    (msg0 s_bar : P.A) :
    Pr_{ let y ← $ᵖ (Fin κ → L) }[
      badBatchingEventProp (κ := κ) (L := L) (K := K) (P := P) y msg0 s_bar ] ≤
      batchingRBRKnowledgeError (κ := κ) (L := L) (K := K) (P := P) ⟨1, rfl⟩ := by
  classical
  unfold badBatchingEventProp
  by_cases h_ne : msg0 ≠ s_bar
  · -- msg0 ≠ s_bar: reduce to S.eval(y) = 0, apply Schwartz-Zippel
    simp only [ne_eq, h_ne, not_false_eq_true, true_and]
    -- Rewrite compute_s0 equality as mismatch polynomial root
    have h_mono := Probability.Pr_le_Pr_of_implies (D := $ᵖ (Fin κ → L))
      (f := fun y => compute_s0 κ L K P msg0 y = compute_s0 κ L K P s_bar y)
      (g := fun y => MvPolynomial.eval y
        (batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar) = 0)
      (h_imp := by
        intro y h_eq
        rw [← batching_compute_s0_sub_eq_eval_mismatch (κ := κ) (L := L) (K := K) (P := P)
          (msg0 := msg0) (s_bar := s_bar) (y := y)]
        exact sub_eq_zero.mpr h_eq)
    apply le_trans h_mono
    have h_nonzero : batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar ≠ 0 :=
      batchingMismatchPoly_nonzero_of_ne (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar h_ne
    have h_sz := Probability.prob_schwartz_zippel_mv_polynomial
      (P := batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar) h_nonzero
      (batchingMismatchPoly_totalDegree_le (κ := κ) (L := L) (K := K) (P := P)
        (msg0 := msg0) (s_bar := s_bar))
    simpa [batchingRBRKnowledgeError, pSpecBatching, ENNReal.coe_div] using h_sz
  · -- msg0 = s_bar: event is False ∧ _, which never holds
    simp only [h_ne, false_and]
    simp only [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.bind_const, PMF.pure_apply,
      eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte, _root_.zero_le]

/-- Extraction failure implies a witness-dependent bad batching event.
  The extracted `witMid` also carries oracle compatibility at the same `oStmt`. -/
lemma batching_rbrExtractionFailureEvent_imply_badBatchingEvent [IsDomain K] [IsDomain L]
    (stmtOStmtIn : (BatchingStmtIn L ℓ) × (∀ j, aOStmtIn.OStmtIn j))
    (msg0 : (pSpecBatching (κ := κ) (L := L) (K := K) (P := P)).Message ⟨0, rfl⟩)
    (y : Fin κ → L)
    (doomEscape : rbrExtractionFailureEvent
      (kSF := batchingKnowledgeStateFunction (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
        (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) (init := init) (impl := impl))
      (extractor := batchingRbrExtractor (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
        (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
      ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 msg0) y) :
    ∃ witMid : batchingWitMid L K ℓ ℓ' 2,
      aOStmtIn.initialCompatibility ⟨witMid.t', stmtOStmtIn.2⟩ ∧
      let s_bar := embedded_MLP_eval κ L K P ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point
      badBatchingEventProp (κ := κ) (L := L) (K := K) (P := P) y msg0 s_bar := by
  classical
  unfold rbrExtractionFailureEvent at doomEscape
  rcases doomEscape with ⟨witMid, h_kState_before_false, h_kState_after_true⟩
  have h_after :
      batchingKStateProp (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
        (h_l := h_l) (aOStmtIn := aOStmtIn) (tr := FullTranscript.mk2 msg0 y)
        stmtOStmtIn.1 witMid stmtOStmtIn.2 := by
    dsimp [batchingKnowledgeStateFunction] at h_kState_after_true ⊢
    exact h_kState_after_true
  have h_before_false := by
    dsimp [batchingKnowledgeStateFunction] at h_kState_before_false ⊢
    exact h_kState_before_false
  have h_compute_eq :=
    batching_compute_eq_from_hafter (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (aOStmtIn := aOStmtIn) (stmtOStmtIn := stmtOStmtIn) (msg0 := msg0)
      (y := y) (witMid := witMid) (h_after := h_after)
  dsimp [batchingKStateProp] at h_after
  have h_check_true :
      performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmtOStmtIn.1.original_claim
        stmtOStmtIn.1.t_eval_point msg0 = true := h_after.2.1
  have h_compat_mid : aOStmtIn.initialCompatibility ⟨witMid.t', stmtOStmtIn.2⟩ := h_after.2.2
  have h_embed_ne :
      embedded_MLP_eval κ L K P ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point ≠ msg0 := by
    intro h_embed_eq
    apply h_before_false
    dsimp [batchingKStateProp]
    refine ⟨?_, ?_, h_check_true, h_compat_mid⟩
    · simp [batchingRbrExtractor, batching_pack_unpack_id]
    · exact h_embed_eq
  have h_msg0_ne :
      msg0 ≠ embedded_MLP_eval κ L K P ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point := by
    intro h_eq
    exact h_embed_ne h_eq.symm
  have h_bad :
      badBatchingEventProp (κ := κ) (L := L) (K := K) (P := P) y msg0
        (embedded_MLP_eval κ L K P ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point) := by
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
lemma batching_doom_escape_probability_bound [IsDomain K] [IsDomain L]
    (stmtOStmtIn : (BatchingStmtIn L ℓ) × (∀ j, aOStmtIn.OStmtIn j))
    (msg0 : (pSpecBatching (κ := κ) (L := L) (K := K) (P := P)).Message ⟨0, rfl⟩) :
    Pr_{ let y ← $ᵖ (Fin κ → L) }[
      rbrExtractionFailureEvent
        (kSF := batchingKnowledgeStateFunction (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) (init := init) (impl := impl))
        (extractor := batchingRbrExtractor (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 msg0) y ] ≤
      batchingRBRKnowledgeError (κ := κ) (L := L) (K := K) (P := P) ⟨1, rfl⟩ := by
  classical
  let compatPred : Sumcheck.Structured.MultilinearPoly L ℓ' → Prop := fun t =>
    aOStmtIn.initialCompatibility ⟨t, stmtOStmtIn.2⟩
  by_cases hCompat : ∃ t : Sumcheck.Structured.MultilinearPoly L ℓ', compatPred t
  · rcases hCompat with ⟨t_fixed, h_t_fixed_compat⟩
    let s_bar_fixed :=
      embedded_MLP_eval κ L K P ℓ ℓ' h_l t_fixed stmtOStmtIn.1.t_eval_point
    have h_prob_mono := Probability.Pr_le_Pr_of_implies (D := $ᵖ (Fin κ → L))
      (f := fun y => rbrExtractionFailureEvent
        (kSF := batchingKnowledgeStateFunction (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) (init := init)
          (impl := impl))
        (extractor := batchingRbrExtractor (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 msg0) y)
      (g := fun y =>
        badBatchingEventProp (κ := κ) (L := L) (K := K) (P := P) y msg0 s_bar_fixed)
      (h_imp := by
        -- Uniqueness proof of `witMid` and `s_bar_fixed`
        intro y h_doomEscape
        obtain ⟨witMid, h_mid_compat, h_bad_extracted⟩ :=
          batching_rbrExtractionFailureEvent_imply_badBatchingEvent
            (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
            (aOStmtIn := aOStmtIn) (init := init) (impl := impl)
            (stmtOStmtIn := stmtOStmtIn) (msg0 := msg0) (y := y)
            (doomEscape := h_doomEscape)
        have h_t_eq : witMid.t' = t_fixed :=
          aOStmtIn.initialCompatibility_unique stmtOStmtIn.2 witMid.t' t_fixed
            h_mid_compat h_t_fixed_compat
        dsimp [s_bar_fixed] at ⊢
        rw [← h_t_eq]
        dsimp [s_bar_fixed] at h_bad_extracted
        exact h_bad_extracted)
    apply le_trans h_prob_mono
    exact probability_bound_badBatchingEventProp (κ := κ) (L := L) (K := K) (P := P)
      (msg0 := msg0) (s_bar := s_bar_fixed)
  · have h_prob_mono_false := Probability.Pr_le_Pr_of_implies (D := $ᵖ (Fin κ → L))
      (f := fun y => rbrExtractionFailureEvent
        (kSF := batchingKnowledgeStateFunction (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) (init := init)
          (impl := impl))
        (extractor := batchingRbrExtractor (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 msg0) y)
      (g := fun _ => False)
      (h_imp := by
        intro y h_doomEscape
        obtain ⟨witMid, h_mid_compat, _h_bad_extracted⟩ :=
          batching_rbrExtractionFailureEvent_imply_badBatchingEvent
            (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
            (aOStmtIn := aOStmtIn) (init := init) (impl := impl)
            (stmtOStmtIn := stmtOStmtIn) (msg0 := msg0) (y := y)
            (doomEscape := h_doomEscape)
        exact (hCompat ⟨witMid.t', h_mid_compat⟩).elim)
    refine le_trans h_prob_mono_false ?_
    simp only [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.bind_const, PMF.pure_apply,
      eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte, _root_.zero_le]

/-- RBR knowledge soundness for the batching phase oracle verifier. -/
theorem batchingOracleVerifier_rbrKnowledgeSoundness [IsDomain K] [IsDomain L] :
  OracleVerifier.rbrKnowledgeSoundness
    (verifier := oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn))
    (init := init) (impl := impl)
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (rbrKnowledgeError := batchingRBRKnowledgeError (κ:=κ) (L:=L) (K:=K) (P:=P)) := by
  classical
  -- One-liner via the reusable round-reducer (same lemma as the fold and sumcheck steps).
  exact OracleReduction.rbrKnowledgeSoundness_of_2msg_PtoV_uniformChallenge
    (WitMid := batchingWitMid L K ℓ ℓ')
    (rbrKnowledgeError := batchingRBRKnowledgeError (κ:=κ) (L:=L) (K:=K) (P:=P))
    (kSF := batchingKnowledgeStateFunction κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)
      (init:=init) (impl:=impl))
    (extractor := batchingRbrExtractor κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn))
    (hDir0 := rfl) (hDir1 := rfl)
    (hbound := fun stmtOStmtIn msg₀ => batching_doom_escape_probability_bound (κ := κ) (L := L)
      (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) (init := init)
      (impl := impl) (stmtOStmtIn := stmtOStmtIn) (msg0 := msg₀))

end BatchingPhase
end RingSwitching
