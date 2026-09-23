/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
public import ArkLib.ProofSystem.RingSwitching.Packing.Spec
public import ArkLib.OracleReduction.Basic
public import ArkLib.ToVCVio.Simulation.Basic
public import ArkLib.OracleReduction.Completeness
public import ArkLib.ProofSystem.RingSwitching.Packing.BatchingPhase.Algebra
public import ArkLib.ProofSystem.RingSwitching.Packing.Compatibility

/-!
# ArkLib.ProofSystem.RingSwitching.Packing.BatchingPhase

Definitions and results for this component of ArkLib.
-/

@[expose] public section

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal ProbabilityTheory
open ProbabilityTheory
open Sumcheck.Structured

/-!
# Batching phase — relocating the claim into the carrier

First phase of the interactive packing reduction. Input: an evaluation claim `t(r) = s` over
the small ring, held by a prover who also knows the packed polynomial `t'`. Output: a single
sumcheck statement over the large ring. The phase does two things:

* **Relocate.** The prover sends the folded carrier element `ŝ` — the packed polynomial,
  coefficients embedded via `φ₁`, evaluated at the `φ₀`-image of the point's tail
  (`embedded_MLP_eval`). The verifier reconstructs the original claim from `ŝ`'s *column*
  coordinates (`eqWeightedCoordSum` against the point's head) and rejects on mismatch: an
  `ŝ` that passes is consistent with the claimed `s`.
* **Batch.** `ŝ`'s *row* coordinates carry `2^κ` separate evaluation claims about `t'`. A
  random batching vector `r'' ∈ L^κ` collapses them into the single target
  `s₀ := eqWeightedCoordSum (rows of ŝ) r''`, at soundness cost `κ/|L|` (Schwartz–Zippel);
  the prover forms the matching sumcheck polynomial `h := A · t'`, where `A` is the public
  multiplier assembled from the basis decomposition of eq̃ (`compute_A_MLE`).

The verifier is the family-shared check-then-update scalar-round verifier
(`RingSwitching.scalarRoundOracleVerifier`); the statement/witness types at the two
boundaries are `BatchingStmtIn`/`BatchingWitIn` in and the round-0 sumcheck
statement/witness out.

## Protocol steps ([DP24] Construction 3.1, steps 1–5)

Common input `[f]`, `s ∈ L`, `(r_0, ..., r_{ℓ-1}) ∈ L^ℓ`; the prover additionally holds
`t(X_0, ..., X_{ℓ-1}) ∈ K[X_0, ..., X_{ℓ-1}]^⪯1`.

1. `P` computes `ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1}))` and sends `V` the A-element `ŝ`.
2. `V` decomposes `ŝ =: Σ_{v ∈ {0,1}^κ} ŝ_v ⊗ β_v` (column coordinates on the left
  tensor factor, per the profile's reconstruction laws).
  `V` requires `s ?= Σ_{v ∈ {0,1}^κ} eq̃(v_0, ..., v_{κ-1}, r_0, ..., r_{κ-1}) ⋅ ŝ_v`.
3. `V` samples batching scalars `(r''_0, ..., r''_{κ-1}) ← L^κ` and sends them to `P`.
4. For each `w ∈ {0,1}^{ℓ'}`,
  `P` decomposes `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})`
    `=: Σ_{u ∈ {0,1}^κ} A_{w, u} ⋅ β_u`.
  `P` defines the function
    `A: w ↦ Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ A_{w, u}`
    on `{0,1}^{ℓ'}` and writes `A(X_0, ..., X_{ℓ'-1})` for its multilinear extension.
  `P` defines `h(X_0, ..., X_{ℓ'-1}) := A(X_0, ..., X_{ℓ'-1}) ⋅ t'(X_0, ..., X_{ℓ'-1})`.
5. `V` decomposes `ŝ =: Σ_{u ∈ {0,1}^κ} β_u ⊗ ŝ_u` (row coordinates on the right tensor
  factor), and
  sets `s_0 := Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ ŝ_u`.

## Security proofs

The round-by-round extractor (`batchingRbrExtractor`, which unpacks `t` from `t'`), the
knowledge-state function, the per-challenge knowledge error (`κ/|L|` at the batching
challenge), and the completeness/soundness proofs use the explicit `CoordinateLaws` conditions.
Soundness additionally requires functional oracle compatibility, so a fixed commitment determines
one packed witness before the batching challenge is sampled.

## References

* [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over
  Binary Towers." Cryptology ePrint Archive (2024).
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
      -- Step 1: P computes ŝ and sends it.
      let s_hat := embedded_MLP_eval κ L K P ℓ ℓ' h_l wit.t' stmt.t_eval_point
      return ⟨s_hat, (stmt, oStmt, wit, s_hat)⟩
    | ⟨1, h⟩ => fun _ => do nomatch h -- V to P round

  receiveChallenge
    | ⟨0, h⟩ => nomatch h -- i.e. contradiction
    | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, s_hat⟩ => do
      return fun r_batching => (stmt, oStmt, wit, s_hat, r_batching)

  output := fun ⟨stmt, oStmt, wit, s_hat, r_batching⟩ => do
    -- Step 4: P computes the batched polynomial h.
    let ctx: RingSwitchingBaseContext κ L K ℓ P := {
      t_eval_point := stmt.t_eval_point,
      original_claim := stmt.original_claim,
      s_hat := s_hat,
      r_batching := r_batching
    }
    let h_poly: ↥L⦃≤ 2⦄[X Fin ℓ'] :=
      projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
        (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
        (ctx := ctx) (t := wit.t') (i := 0) (challenges := Fin.elim0)
    -- Prover computes s₀ locally for its output witness.
    let s₀ := compute_s0 κ L K P s_hat r_batching
    let stmtOut : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0 := {
      ctx := ctx,
      sumcheck_target := s₀,
      challenges := Fin.elim0
    }
    let witOut : SumcheckWitness L ℓ' 0 := {
      t' := wit.t',
      H := h_poly
    }
    return (⟨stmtOut, oStmt⟩, witOut)

def batchingVerifierCheck (stmtIn : BatchingStmtIn L ℓ) (msg0 : P.A) : Prop :=
  performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l
    stmtIn.original_claim stmtIn.t_eval_point msg0 = true

/-- Pure verifier output: computes the output statement given the transcript. -/
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
def batchingProverComputeMsg (stmtIn : BatchingStmtIn L ℓ) (witIn : BatchingWitIn L K ℓ ℓ') :
    P.A :=
  embedded_MLP_eval κ L K P ℓ ℓ' h_l witIn.t' stmtIn.t_eval_point

/-- Pure prover output: computes the output witness given the transcript. -/
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

/-- Query the folded carrier, reject an invalid original claim, then batch the row coordinates. -/
noncomputable def oracleVerifier :
  OracleVerifier (oSpec := []ₒ)
    (StmtIn := BatchingStmtIn L ℓ) (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecBatching (κ := κ) (L := L) (K := K) (P := P)) where
  verify stmt challenges := do
    let s_hat : P.A ← query (spec := [pSpecBatching κ L K P |>.Message]ₒ)
      ⟨⟨0, rfl⟩, ()⟩
    let r_batching : Fin κ → L := challenges ⟨1, rfl⟩
    guard (performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l
      stmt.original_claim stmt.t_eval_point s_hat = true)
    pure {
      ctx := {
        t_eval_point := stmt.t_eval_point
        original_claim := stmt.original_claim
        s_hat := s_hat
        r_batching := r_batching }
      sumcheck_target := compute_s0 κ L K P s_hat r_batching
      challenges := Fin.elim0 }
  outputOracle := .inl {
    embed := ⟨Sum.inl, fun _ _ h => Sum.inl.inj h⟩
    hEq := fun _ => rfl
    outputInterface_heq := by intro j; rfl }

open Classical in
omit [NeZero κ] [Nontrivial L] [Fintype L] [SampleableType L] [Fintype K] [DecidableEq K] [NeZero
  ℓ] [NeZero ℓ'] in
/-- Running the verifier exposes the original-claim guard and preserves the input oracle. -/
lemma oracleVerifier_run_eq_guarded (stmt : BatchingStmtIn L ℓ)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (tr : (pSpecBatching κ L K P).FullTranscript) :
    Verifier.run (stmt, oStmt) tr
      (oracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier =
    if batchingVerifierCheck κ L K P ℓ ℓ' h_l stmt (tr.messages ⟨0, rfl⟩) then
      pure (batchingVerifierStmtOut κ L K P ℓ ℓ' stmt
        (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩), oStmt)
    else failure := by
  classical
  simp only [Verifier.run, OracleVerifier.toVerifier, oracleVerifier]
  erw [simulateQ_bind]
  erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
  erw [_root_.bind_pure_simulateQ_comp]
  simp only [guard_eq]
  erw [simulateQ_bind]
  erw [simulateQ_ite]
  simp only [OptionT.simulateQ_failure]
  dsimp only [batchingVerifierCheck, batchingVerifierStmtOut]
  split
  · rename_i h_check
    erw [ite_eq_left h_check]
    erw [simulateQ_pure]
    simp only [pure_bind]
    erw [simulateQ_pure]
    rfl
  · rename_i h_check
    erw [ite_eq_right h_check]
    rfl

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

def batchingInputRelationProp (stmt : BatchingStmtIn L ℓ)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) (wit : BatchingWitIn L K ℓ ℓ') : Prop :=
  wit.t' = packMLE κ L K ℓ ℓ' h_l P.basis wit.t
  ∧ stmt.original_claim = wit.t.val.aeval stmt.t_eval_point
  ∧ aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩

/-- Input relation: the witness `t` and `t'` are consistent,
and `t` satisfies the original claim. -/
def batchingInputRelation :
    Set ((BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)) × BatchingWitIn L K ℓ ℓ') :=
  {⟨⟨stmt, oStmt⟩, wit⟩ | batchingInputRelationProp κ L K P ℓ ℓ' h_l aOStmtIn stmt oStmt wit }

/-- Batching inputs with honest oracle compatibility, used for perfect completeness. -/
def strictBatchingInputRelation :=
  batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn.strictView

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
  | ⟨1, _⟩ => by -- P sends the folded carrier ŝ.
    let ⟨msgsUpTo, _⟩ := Transcript.equivMessagesChallenges (k := 1)
      (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) tr
    let i_msg1 : ((pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)).take 1 (by omega)).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le (by omega)⟩, by simp [pSpecBatching]; rfl⟩
    let s_hat: P.A := msgsUpTo i_msg1
    exact
      witMid.t' = packMLE κ L K ℓ ℓ' h_l P.basis witMid.t -- implied by `extractMid`
      -- The embedded evaluation and verifier check imply the original evaluation claim.
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

omit [Nontrivial L] in
/-- Knowledge state function for the batching phase. -/
noncomputable def batchingKnowledgeStateFunction (hCoord : CoordinateLaws P)
    [IsDomain K] [NoZeroDivisors L] :
  (oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)).KnowledgeStateFunction init impl
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (batchingRbrExtractor κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)) := by
  let : IsDomain L := NoZeroDivisors.to_isDomain L
  exact {
    toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
      batchingKStateProp κ L K P ℓ ℓ' h_l aOStmtIn tr stmt witMid oStmt
    toFun_empty _ _ := by rfl
    toFun_next := fun m hDir stmtIn tr msg witMid =>
      match m with
      | ⟨0, _⟩ => by -- from accumulative KState
        intro hSuccTrue
        simp only [batchingKStateProp, Fin.zero_eta, Fin.isValue, Fin.succ_zero_eq_one,
          Transcript.equivMessagesChallenges_apply, Fin.castSucc_zero,
          batchingRbrExtractor, Fin.mk_one, Fin.succ_one_eq_two,
          batchingInputRelationProp] at ⊢ hSuccTrue
        obtain ⟨h_t'_eq, h_embed_eq, h_check_true, h_compat⟩ := hSuccTrue
        refine ⟨h_t'_eq, ?_, ?_⟩
        · -- stmt.original_claim = witMid.t.val.aeval stmt.t_eval_point
          -- from `performCheck(original_claim, s_hat) = true` and
          -- The same coordinate reconstruction equals both claims.
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
              batching_check_correctness (hCoord := hCoord) (κ := κ) (L := L) (K := K) (P := P)
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
      simp only [StateT.run'_eq, gt_iff_lt, OracleComp.OptionT.prEvent_mk_pos_iff,
        Prod.exists] at h_relOut
      rcases h_relOut with ⟨stmtOut, oStmtOut, h_output, h_relOut⟩
      erw [oracleVerifier_run_eq_guarded] at h_output
      simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output
      rcases h_output with ⟨s, _hs_init, h_output⟩
      by_cases h_check : batchingVerifierCheck κ L K P ℓ ℓ' h_l stmtIn
          ((show (pSpecBatching κ L K P).FullTranscript from tr).messages ⟨0, rfl⟩)
      · rw [ite_eq_left h_check] at h_output
        change some (stmtOut, oStmtOut) ∈ MonadAttach.support
          ((simulateQ impl (pure (some _) : OracleComp []ₒ (Option _))).run' s) at h_output
        rw [simulateQ_pure] at h_output
        change some (stmtOut, oStmtOut) ∈ MonadAttach.support
          (Prod.fst <$> (pure (some _) : StateT σ ProbComp _).run s) at h_output
        rw [StateT.run_pure] at h_output
        simp only [map_pure, support_pure, Set.mem_singleton_iff,
          Option.some.injEq] at h_output
        have h_stmt := congrArg Prod.fst h_output
        have h_oracle := congrArg Prod.snd h_output
        change stmtOut = _ at h_stmt
        change oStmtOut = oStmtIn at h_oracle
        rw [h_stmt, h_oracle] at h_relOut
        simp only [Fin.reduceLast, Fin.isValue]
        unfold batchingKStateProp
        simp only [Fin.isValue]
        dsimp only [Transcript.equivMessagesChallenges, Equiv.coe_fn_mk,
          Transcript.toMessagesChallenges, Transcript.toMessagesUpTo, Transcript.toChallengesUpTo]
        dsimp only [sumcheckRoundRelation, sumcheckRoundRelationProp, masterKStateProp,
          Set.mem_ofPred_eq] at h_relOut
        refine ⟨?_, h_check, h_relOut.2.2.2⟩
        change sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l aOStmtIn 0 _ oStmtIn _
        unfold sumcheckRoundRelationProp masterKStateProp
        refine ⟨trivial, rfl, ?_, h_relOut.2.2.2⟩
        have hH := h_relOut.2.1
        have hCons := h_relOut.2.2.1
        change witOut.H.val = _ at hH
        have hH' := Subtype.ext hH
        rw [hH'] at hCons
        exact hCons
      · rw [ite_eq_right h_check] at h_output
        change some (stmtOut, oStmtOut) ∈ MonadAttach.support
          ((simulateQ impl (pure none : OracleComp []ₒ (Option _))).run' s) at h_output
        rw [simulateQ_pure] at h_output
        change some (stmtOut, oStmtOut) ∈ MonadAttach.support
          (Prod.fst <$> (pure none : StateT σ ProbComp _).run s) at h_output
        rw [StateT.run_pure] at h_output
        simp only [map_pure, support_pure, Set.mem_singleton_iff, reduceCtorEq] at h_output
  }

/-! ## Security Properties -/

omit [NeZero κ] [Fintype L] [DecidableEq L] [SampleableType L] [Fintype K] [DecidableEq K]
  [NeZero ℓ] [NeZero ℓ'] in
/-- The honest message passes the guard and the honest output satisfies the round relation. -/
lemma batching_honest_output_relation (hCoord : CoordinateLaws P)
    [IsDomain K] [NoZeroDivisors L]
    (stmt : BatchingStmtIn L ℓ) (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : BatchingWitIn L K ℓ ℓ') (r : Fin κ → L)
    (hIn : batchingInputRelationProp κ L K P ℓ ℓ' h_l aOStmtIn stmt oStmt wit) :
    sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l aOStmtIn 0
      (batchingVerifierStmtOut κ L K P ℓ ℓ' stmt
        (batchingProverComputeMsg κ L K P ℓ ℓ' h_l stmt wit) r) oStmt
      (batchingProverWitOut κ L K P ℓ ℓ' h_l stmt wit
        (batchingProverComputeMsg κ L K P ℓ ℓ' h_l stmt wit) r) := by
  let : IsDomain L := NoZeroDivisors.to_isDomain L
  refine ⟨trivial, rfl, ?_, hIn.2.2⟩
  exact batching_target_consistency κ L K P ℓ ℓ' h_l hCoord wit.t'
    (batchingProverComputeMsg κ L K P ℓ ℓ' h_l stmt wit)
    { t_eval_point := stmt.t_eval_point
      original_claim := stmt.original_claim
      s_hat := batchingProverComputeMsg κ L K P ℓ ℓ' h_l stmt wit
      r_batching := r } rfl

omit [NeZero κ] [Fintype L] [Fintype K] [DecidableEq K] [NeZero ℓ'] in
/-- Perfect completeness for the batching phase oracle reduction. -/
theorem batchingReduction_perfectCompleteness (hCoord : CoordinateLaws P)
    [IsDomain K] [NoZeroDivisors L] :
    OracleReduction.perfectCompleteness
    (oracleReduction := batchingOracleReduction κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn))
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (init := init) (impl := impl) := by
  classical
  let : IsDomain L := NoZeroDivisors.to_isDomain L
  let : ∀ j, OracleInterface ((pSpecBatching κ L K P).Challenge j) :=
    ProtocolSpec.challengeOracleInterface
  rw [OracleReduction.unroll_2_message_reduction_perfectCompleteness (oSpec := []ₒ)
    (pSpec := pSpecBatching κ L K P) (init := init) (impl := impl)
    (hDir0 := rfl) (hDir1 := rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  apply OptionT.prEvent_mk_simulateQ_run'_eq_one_of_support
  intro output h_output
  dsimp only [batchingOracleReduction, oracleProver, oracleVerifier, PrvState,
    OracleVerifier.toVerifier] at h_output
  simp only [liftComp_pure, liftM_pure, pure_bind, OptionT.run_bind,
    OptionT.run_pure] at h_output
  simp only [liftComp_eq_liftM, OptionT.run_monadLift, Option.elimM,
    bind_map_left, support_bind, Set.mem_iUnion, exists_prop] at h_output
  obtain ⟨r1, _, h_output⟩ := h_output
  change Fin κ → L at r1
  dsimp only [liftM, monadLift, MonadLift.monadLift] at h_output
  simp only [Option.elim] at h_output
  have h_relation := batching_honest_output_relation κ L K P ℓ ℓ' h_l aOStmtIn
    hCoord stmtIn oStmtIn witIn r1 h_relIn
  obtain ⟨hPack, hClaim, hCompat⟩ := h_relIn
  have h_check : performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l
      stmtIn.original_claim stmtIn.t_eval_point
      (embedded_MLP_eval κ L K P ℓ ℓ' h_l witIn.t' stmtIn.t_eval_point) = true := by
    rw [hPack, hClaim]
    exact batching_check_correctness κ L K P ℓ ℓ' h_l hCoord witIn.t stmtIn.t_eval_point
  simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output
  simp only [OptionT.run, OptionT.mk, support_liftComp, support_map,
    Set.mem_image] at h_output
  erw [simulateQ_bind, OptionT.simulateQ_simOracle2_liftM_query_T2, pure_bind] at h_output
  dsimp only [OracleInterface.answer, FullTranscript.mk2, FullTranscript.messages,
    FullTranscript.challenges] at h_output
  simp only [guard_eq, ↓existsAndEq, and_true] at h_output
  have h_answer : ReaderT.run (OracleInterface.toOC.impl ())
      (embedded_MLP_eval κ L K P ℓ ℓ' h_l witIn.t' stmtIn.t_eval_point) =
      embedded_MLP_eval κ L K P ℓ ℓ' h_l witIn.t' stmtIn.t_eval_point := rfl
  simp only [h_answer, h_check, ite_eq_left, pure_bind] at h_output
  erw [OptionT.simulateQ_pure] at h_output
  simp only [OptionT.pure, OptionT.mk,
    support_pure, Set.mem_singleton_iff, exists_eq_left, Option.map_some] at h_output
  refine ⟨_, h_output, ?_⟩
  change sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l aOStmtIn 0 _ oStmtIn _ ∧ _
  exact ⟨h_relation, rfl, rfl⟩

omit [NeZero κ] [Nontrivial L] [Fintype L] [DecidableEq L] [SampleableType L] [Fintype K]
  [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
lemma batching_pack_unpack_id [IsDomain K] [IsDomain L]
    (t' : Sumcheck.Structured.MultilinearPoly L ℓ') :
    packMLE κ L K ℓ ℓ' h_l P.basis (unpackMLE κ L K ℓ ℓ' h_l P.basis t') = t' := by
  apply Subtype.ext
  have hPack : (packMLE κ L K ℓ ℓ' h_l P.basis
      (unpackMLE κ L K ℓ ℓ' h_l P.basis t')).val =
      MvPolynomial.MLE (fun w : Fin ℓ' → Fin 2 =>
        MvPolynomial.eval (w : Fin ℓ' → L) t'.val) := by
    simp [packMLE, unpackMLE]
  rw [hPack]
  exact (MvPolynomial.is_multilinear_iff_eq_evals_zeroOne (p := t'.val)).mp t'.property

omit [NeZero κ] [Nontrivial L] [Fintype L] [DecidableEq L] [SampleableType L] [Fintype K]
  [DecidableEq K] in
/-- `compute_s0` is evaluation of the row-coordinate MLE at the batching challenge. -/
lemma batching_compute_s0_eq_eval_MLE
    (s_hat : P.A) (y : Fin κ → L) :
    compute_s0 κ L K P s_hat y =
      MvPolynomial.eval y
        (MvPolynomial.MLE (fun u : Fin κ → Fin 2 =>
          P.decomposeRows s_hat u)) := by
  classical
  rw [compute_s0, eqWeightedCoordSum, MvPolynomial.MLE]
  simp_rw [MvPolynomial.eqTilde]
  simp only [Fin.isValue, beq_iff_eq, map_prod, map_add,
    MonoidWithZeroHom.map_ite_one_zero, map_mul, map_sub, map_one, MvPolynomial.eval_X,
    ite_mul, one_mul, zero_mul, map_sum, map_natCast, MvPolynomial.eval_C]
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

/-- Mismatch polynomial from the row-coordinate difference between `msg0` and `s_bar`. -/
def batchingMismatchPoly (msg0 s_bar : P.A) : MvPolynomial (Fin κ) L :=
  MvPolynomial.MLE (fun u : Fin κ → Fin 2 =>
    P.decomposeRows msg0 u -
    P.decomposeRows s_bar u)

omit [NeZero κ] [Nontrivial L] [Fintype L] [DecidableEq L] [SampleableType L] [Fintype K]
  [DecidableEq K] in
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
  simp only [MLE, map_sum, MvPolynomial.eval_mul, map_prod, map_add, map_natCast,
    sub_eq_add_neg, map_one, map_neg, MvPolynomial.eval_X, MvPolynomial.eval_C]
  rw [← Finset.sum_neg_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  ring

omit [NeZero κ] [Nontrivial L] [Fintype L] [DecidableEq L] [SampleableType L] [Fintype K]
  [DecidableEq K] in
/-- Degree bound for mismatch polynomial: multilinear in `κ` vars, so total degree ≤ `κ`. -/
lemma batchingMismatchPoly_totalDegree_le
    (msg0 s_bar : P.A) :
    (batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar).totalDegree ≤ κ := by
  let Q := batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar
  have h_mem : Q ∈ MvPolynomial.restrictDegree (Fin κ) L 1 := by
    dsimp [Q, batchingMismatchPoly]
    exact (MvPolynomial.MLE_mem_restrictDegree (σ := Fin κ) (R := L)
      (evals := fun u : Fin κ → Fin 2 =>
        P.decomposeRows msg0 u -
        P.decomposeRows s_bar u))
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

omit [NeZero κ] [Nontrivial L] [Fintype L] [DecidableEq L] [SampleableType L] [Fintype K]
  [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
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
      (P.decomposeRows msg0) ≠
      (P.decomposeRows s_bar) := by
    intro h_eq
    have hs : msg0 = s_bar := P.rows_injective h_eq
    have hs' : s_bar = msg0 := hs.symm
    dsimp [s_bar] at hs'
    exact h_embed_ne hs'
  have h_diff_ne :
      (fun u : Fin κ → Fin 2 =>
        P.decomposeRows msg0 u -
        P.decomposeRows s_bar u) ≠ 0 := by
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
      P.decomposeRows msg0 u -
        P.decomposeRows s_bar u := by
    simp [batchingMismatchPoly, MvPolynomial.MLE_eval_zeroOne]
  rw [hu_eval_mle] at hu_eval_zero
  exact hu_eval_zero

omit [NeZero κ] [Nontrivial L] [Fintype L] [DecidableEq L] [SampleableType L] [Fintype K]
  [DecidableEq K] in
/-- If `msg0 ≠ s_bar` in the tensor algebra, the mismatch polynomial is nonzero.
  Generalization of `batchingMismatchPoly_nonzero_of_embed_ne`. -/
lemma batchingMismatchPoly_nonzero_of_ne
    (msg0 s_bar : P.A)
    (h_ne : msg0 ≠ s_bar) :
    batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar ≠ 0 := by
  have h_rows_ne :
      (P.decomposeRows msg0) ≠
      (P.decomposeRows s_bar) := by
    intro h_eq
    exact h_ne (P.rows_injective h_eq)
  have h_diff_ne :
      (fun u : Fin κ → Fin 2 =>
        P.decomposeRows msg0 u -
        P.decomposeRows s_bar u) ≠ 0 := by
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
      P.decomposeRows msg0 u -
        P.decomposeRows s_bar u := by
    simp [batchingMismatchPoly, MvPolynomial.MLE_eval_zeroOne]
  rw [hu_eval_mle] at hu_eval_zero
  exact hu_eval_zero

omit [NeZero κ] [Fintype L] [SampleableType L] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- From `KState 2` truth, derive equality of the two `compute_s0` forms. -/
lemma batching_compute_eq_from_hafter (hCoord : CoordinateLaws P) [NoZeroDivisors L]
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
  let : IsDomain L := NoZeroDivisors.to_isDomain L
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
    exact batching_target_consistency (hCoord := hCoord) (κ := κ) (L := L) (K := K) (P := P) (ℓ :=
      ℓ)
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

omit [Nontrivial L] in
omit [NeZero κ] [Fintype K] [DecidableEq K] [DecidableEq L] in
/-- **Schwartz-Zippel bound for the bad batching event.**
  When `msg0 = s_bar`, the event never holds (first conjunct is `False`).
  When `msg0 ≠ s_bar`, the mismatch polynomial $S$ is nonzero with `totalDegree ≤ κ`,
  so Schwartz-Zippel gives `Pr[S(y) = 0] ≤ κ / |L|`. -/
lemma probability_bound_badBatchingEventProp [IsDomain L]
    (msg0 s_bar : P.A) :
    Pr{ let y ← $ᵗ (Fin κ → L) }[
      badBatchingEventProp (κ := κ) (L := L) (K := K) (P := P) y msg0 s_bar ] ≤
      batchingRBRKnowledgeError (κ := κ) (L := L) (K := K) (P := P) ⟨1, rfl⟩ := by
  classical
  unfold badBatchingEventProp
  let : DecidableEq L := Classical.decEq L
  by_cases h_ne : msg0 ≠ s_bar
  · -- msg0 ≠ s_bar: reduce to S.eval(y) = 0, apply Schwartz-Zippel
    simp only [ne_eq, h_ne, not_false_eq_true, true_and]
    -- Rewrite compute_s0 equality as mismatch polynomial root
    have h_mono := prEvent_mono ($ᵗ (Fin κ → L))
      (fun y => compute_s0 κ L K P msg0 y = compute_s0 κ L K P s_bar y)
      (fun y => MvPolynomial.eval y
        (batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar) = 0)
      (by
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
    exact (prEvent_eq_zero_of_forall_not _ _ (fun _ h => h)).le.trans _root_.zero_le

omit [NeZero κ] [Fintype L] [SampleableType L] [Fintype K] [DecidableEq K] [NeZero ℓ'] in
/-- Extraction failure implies a witness-dependent bad batching event.
  The extracted `witMid` also carries oracle compatibility at the same `oStmt`. -/
lemma batching_rbrExtractionFailureEvent_imply_badBatchingEvent (hCoord : CoordinateLaws P)
    [IsDomain K] [NoZeroDivisors L]
    (stmtOStmtIn : (BatchingStmtIn L ℓ) × (∀ j, aOStmtIn.OStmtIn j))
    (msg0 : (pSpecBatching (κ := κ) (L := L) (K := K) (P := P)).Message ⟨0, rfl⟩)
    (y : Fin κ → L)
    (doomEscape : rbrExtractionFailureEvent
      (kSF := batchingKnowledgeStateFunction (hCoord := hCoord) (κ := κ) (L := L) (K := K) (P :=
        P) (ℓ := ℓ)
        (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) (init := init) (impl := impl))
      (extractor := batchingRbrExtractor (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
        (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
      ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 msg0) y) :
    ∃ witMid : batchingWitMid L K ℓ ℓ' 2,
      aOStmtIn.initialCompatibility ⟨witMid.t', stmtOStmtIn.2⟩ ∧
      let s_bar := embedded_MLP_eval κ L K P ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point
      badBatchingEventProp (κ := κ) (L := L) (K := K) (P := P) y msg0 s_bar := by
  let : IsDomain L := NoZeroDivisors.to_isDomain L
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
    batching_compute_eq_from_hafter (hCoord := hCoord) (κ := κ) (L := L) (K := K) (P := P) (ℓ :=
      ℓ) (ℓ' := ℓ')
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

omit [Fintype K] [DecidableEq K] in
omit [NeZero κ] [NeZero ℓ'] in
/-- Per-transcript batching bound: for a fixed prover message `msg0`, the probability
  (over batching challenges `y : Fin κ → L`) that extraction fails is bounded by
  `batchingRBRKnowledgeError`.
  **Proof strategy** (follows `foldStep_doom_escape_probability_bound`):
  1. **Implication**: Show that extraction failure implies the
     `badBatchingEventProp` (Theorem 3.5, $S(r'') = 0$).
  2. **Monotonicity**: Conclude `Pr[doom] ≤ Pr[badBatchingEvent]` via `prob_mono`.
  3. **Schwartz–Zippel**: Bound `Pr[badBatchingEvent]` by `κ/|L|`. -/
lemma batching_doom_escape_probability_bound (hCoord : CoordinateLaws P)
    (hUnique : aOStmtIn.Functional) [IsDomain K] [NoZeroDivisors L]
    (stmtOStmtIn : (BatchingStmtIn L ℓ) × (∀ j, aOStmtIn.OStmtIn j))
    (msg0 : (pSpecBatching (κ := κ) (L := L) (K := K) (P := P)).Message ⟨0, rfl⟩) :
    Pr{ let y ← $ᵗ (Fin κ → L) }[
      rbrExtractionFailureEvent
        (kSF := batchingKnowledgeStateFunction (hCoord := hCoord) (κ := κ) (L := L) (K := K) (P :=
          P) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) (init := init) (impl := impl))
        (extractor := batchingRbrExtractor (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 msg0) y ] ≤
      batchingRBRKnowledgeError (κ := κ) (L := L) (K := K) (P := P) ⟨1, rfl⟩ := by
  let : IsDomain L := NoZeroDivisors.to_isDomain L
  classical
  let compatPred : Sumcheck.Structured.MultilinearPoly L ℓ' → Prop := fun t =>
    aOStmtIn.initialCompatibility ⟨t, stmtOStmtIn.2⟩
  by_cases hCompat : ∃ t : Sumcheck.Structured.MultilinearPoly L ℓ', compatPred t
  · rcases hCompat with ⟨t_fixed, h_t_fixed_compat⟩
    let s_bar_fixed :=
      embedded_MLP_eval κ L K P ℓ ℓ' h_l t_fixed stmtOStmtIn.1.t_eval_point
    have h_prob_mono := prEvent_mono ($ᵗ (Fin κ → L))
      (fun y => rbrExtractionFailureEvent
        (kSF := batchingKnowledgeStateFunction (hCoord := hCoord) (κ := κ) (L := L) (K := K) (P :=
          P) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) (init := init)
          (impl := impl))
        (extractor := batchingRbrExtractor (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 msg0) y)
      (fun y =>
        badBatchingEventProp (κ := κ) (L := L) (K := K) (P := P) y msg0 s_bar_fixed)
      (by
        -- Uniqueness proof of `witMid` and `s_bar_fixed`
        intro y h_doomEscape
        obtain ⟨witMid, h_mid_compat, h_bad_extracted⟩ :=
          batching_rbrExtractionFailureEvent_imply_badBatchingEvent
            (hCoord := hCoord) (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
            (aOStmtIn := aOStmtIn) (init := init) (impl := impl)
            (stmtOStmtIn := stmtOStmtIn) (msg0 := msg0) (y := y)
            (doomEscape := h_doomEscape)
        have h_t_eq : witMid.t' = t_fixed :=
          hUnique stmtOStmtIn.2 witMid.t' t_fixed
            h_mid_compat h_t_fixed_compat
        dsimp [s_bar_fixed] at ⊢
        rw [← h_t_eq]
        dsimp [s_bar_fixed] at h_bad_extracted
        exact h_bad_extracted)
    apply le_trans h_prob_mono
    exact probability_bound_badBatchingEventProp (κ := κ) (L := L) (K := K) (P := P)
      (msg0 := msg0) (s_bar := s_bar_fixed)
  · have h_prob_mono_false := prEvent_mono ($ᵗ (Fin κ → L))
      (fun y => rbrExtractionFailureEvent
        (kSF := batchingKnowledgeStateFunction (hCoord := hCoord) (κ := κ) (L := L) (K := K) (P :=
          P) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) (init := init)
          (impl := impl))
        (extractor := batchingRbrExtractor (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 msg0) y)
      (fun _ => False)
      (by
        intro y h_doomEscape
        obtain ⟨witMid, h_mid_compat, _h_bad_extracted⟩ :=
          batching_rbrExtractionFailureEvent_imply_badBatchingEvent
            (hCoord := hCoord) (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
            (aOStmtIn := aOStmtIn) (init := init) (impl := impl)
            (stmtOStmtIn := stmtOStmtIn) (msg0 := msg0) (y := y)
            (doomEscape := h_doomEscape)
        exact (hCompat ⟨witMid.t', h_mid_compat⟩).elim)
    refine le_trans h_prob_mono_false ?_
    exact (prEvent_eq_zero_of_forall_not _ _ (fun _ h => h)).le.trans _root_.zero_le

omit [Fintype K] [DecidableEq K] in
omit [NeZero κ] [NeZero ℓ'] in
/-- RBR knowledge soundness for the batching phase oracle verifier. -/
theorem batchingOracleVerifier_rbrKnowledgeSoundness (hCoord : CoordinateLaws P)
    (hUnique : aOStmtIn.Functional) [IsDomain K] [NoZeroDivisors L] :
    OracleVerifier.rbrKnowledgeSoundness
    (verifier := oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn))
    (init := init) (impl := impl)
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (rbrKnowledgeError := batchingRBRKnowledgeError (κ:=κ) (L:=L) (K:=K) (P:=P)) := by
  let _ : IsDomain L := NoZeroDivisors.to_isDomain L
  classical
  let : ∀ j, Fintype ((pSpecBatching κ L K P).Challenge j)
    | ⟨0, hj⟩ => by nomatch hj
    | ⟨1, _⟩ => inferInstanceAs (Fintype (Fin κ → L))
  let : ∀ j, Inhabited ((pSpecBatching κ L K P).Challenge j)
    | ⟨0, hj⟩ => by nomatch hj
    | ⟨1, _⟩ => (⟨fun _ => (0 : L)⟩ : Inhabited (Fin κ → L))
  let : ∀ j, OracleInterface ((pSpecBatching κ L K P).Challenge j) :=
    ProtocolSpec.challengeOracleInterface
  -- Reduce global RBR soundness to the fixed-transcript batching bound.
  refine OracleReduction.rbrKnowledgeSoundness_of_2msg_PtoV_uniformChallenge
    (pSpec := pSpecBatching κ L K P)
    (verifier := (oracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier)
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (WitMid := batchingWitMid L K ℓ ℓ')
    (rbrKnowledgeError := batchingRBRKnowledgeError (κ:=κ) (L:=L) (K:=K) (P:=P))
    (kSF := batchingKnowledgeStateFunction κ L K P ℓ ℓ' h_l (hCoord := hCoord) (aOStmtIn:=aOStmtIn)
      (init:=init) (impl:=impl))
    (extractor := batchingRbrExtractor κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn))
    (hDir0 := rfl) (hDir1 := rfl)
    (hbound := ?_)
  intro stmtOStmtIn msg₀
  exact batching_doom_escape_probability_bound (hCoord := hCoord)
      (hUnique := hUnique) (κ := κ) (L := L)
      (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) (init := init)
      (impl := impl) (stmtOStmtIn := stmtOStmtIn) (msg0 := msg₀)

end BatchingPhase
end RingSwitching
