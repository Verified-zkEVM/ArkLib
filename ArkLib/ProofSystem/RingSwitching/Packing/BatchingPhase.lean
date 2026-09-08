/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.RingSwitching.Packing.BatchingAlgebra
import ArkLib.ProofSystem.RingSwitching.Packing.Spec
import ArkLib.ProofSystem.RingSwitching.Packing.FullFamily.Separation
import ArkLib.OracleReduction.Basic
import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness
import CompPoly.Fields.Binary.Tower.TensorAlgebra

/-!
# ArkLib.ProofSystem.RingSwitching.Packing.BatchingPhase

Definitions and results for this component of ArkLib.
-/

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal ENNReal
open Sumcheck.Structured

/-!
# Batching phase — relocating the claim into the carrier

First phase of the interactive packing reduction. Input: an evaluation claim `t(r) = s` over
the small ring, held by a prover who also knows the packed polynomial `t'`. Output: a single
sumcheck statement over the large ring. The phase does two things:

* **Relocate.** The prover sends the folded carrier element `ŝ` — the packed polynomial,
  coefficients embedded via `φ₁`, evaluated at the `φ₀`-image of the point's tail
  (`embedded_MLP_eval`). The verifier reconstructs the original claim from `ŝ`'s *row*
  coordinates (`eqWeightedCoordSum` against the point's head) and rejects on mismatch: an
  `ŝ` that passes is consistent with the claimed `s`.
* **Batch.** `ŝ`'s *column* coordinates carry `2^κ` separate evaluation claims about `t'`. A
  random batching vector `r'' ∈ L^κ` collapses them into the single target
  `s₀ := eqWeightedCoordSum (columns of ŝ) r''`, at soundness cost `κ/|L|` (Schwartz–Zippel);
  the prover forms the matching sumcheck polynomial `h := A · t'`, where `A` is the public
  multiplier assembled from the basis decomposition of eq̃ (`compute_A_MLE`).

The verifier is the family-shared check-then-update scalar-round verifier
(`RingSwitching.guardedScalarRoundOracleVerifier`); the statement/witness types at the two
boundaries are `BatchingStmtIn`/`BatchingWitIn` in and the round-0 sumcheck
statement/witness out.

## Protocol steps ([DP24] Construction 3.1, steps 1–5)

Common input `[f]`, `s ∈ L`, `(r_0, ..., r_{ℓ-1}) ∈ L^ℓ`; the prover additionally holds
`t(X_0, ..., X_{ℓ-1}) ∈ K[X_0, ..., X_{ℓ-1}]^⪯1`.

1. `P` computes `ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1}))` and sends `V` the A-element `ŝ`.
2. `V` decomposes `ŝ =: Σ_{v ∈ {0,1}^κ} ŝ_v ⊗ β_v` (row coordinates with the basis in the right
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
5. `V` decomposes `ŝ =: Σ_{u ∈ {0,1}^κ} β_u ⊗ ŝ_u` (column coordinates on the left tensor
  factor), and
  sets `s_0 := Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ ŝ_u`.

## Security

The native extractor unpacks `t` from `t'`. Its knowledge state retains the original guard,
commitment compatibility, and the exact initial residual. Completeness follows from the
shared checked-observation and finite-coordinate identities. The fixed-prefix knowledge bound
uses compatibility-only shared separation with an explicit functionality premise over a domain;
the averaged contract follows from that bound. The loss is `κ/|L|` at the one vector challenge.

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

/-! ## Prover and Verifier Implementation -/

/-- The state maintained by the prover throughout the batching phase. -/
def PrvState : Fin (2 + 1) → Type
  | ⟨0, _⟩ => BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j) × BatchingWitIn L K ℓ ℓ'
  | ⟨1, _⟩ => BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)
    × BatchingWitIn L K ℓ ℓ' × P.A
  | _ => BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)
    × BatchingWitIn L K ℓ ℓ' × P.A × (Fin κ → L)

/-- The native output keeps the received carrier and batching challenge in the original context. -/
def nextStatement (stmt : BatchingStmtIn L ℓ) (z : P.A) (c : Fin κ → L) :
    Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0 :=
  { ctx := {
      t_eval_point := stmt.t_eval_point
      original_claim := stmt.original_claim
      s_hat := z
      r_batching := c }
    sumcheck_target := compute_s0 κ L K P z c
    challenges := Fin.elim0 }

/-- The native witness keeps the supplied packed polynomial and its exact initial residual. -/
def nextWitness (stmt : BatchingStmtIn L ℓ) (z : P.A) (c : Fin κ → L)
    (p : MultilinearPoly L ℓ') : SumcheckWitness L ℓ' 0 :=
  { t' := p
    H := projectToMidSumcheckPolyWithParam ℓ'
      (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
      (nextStatement κ L K P ℓ ℓ' stmt z c).ctx p 0 Fin.elim0 }

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

  output := fun ⟨stmt, oStmt, wit, s_hat, r_batching⟩ =>
    pure ((nextStatement κ L K P ℓ ℓ' stmt s_hat r_batching, oStmt),
      nextWitness κ L K P ℓ ℓ' h_l stmt s_hat r_batching wit.t')

/-- The batching-phase verifier as an instance of the family-shared check-then-update
scalar-round verifier (`RingSwitching.guardedScalarRoundOracleVerifier`, `RoundVerifiers.lean`):
query ŝ (step 1), run Check 1 against the row decomposition (step 2, abort on failure),
then update the statement with the batched sumcheck target `s₀`
from the batching scalars `r''` (steps 3 and 5). -/
noncomputable def oracleVerifier :
  OracleVerifier (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn L ℓ) (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) :=
  guardedScalarRoundOracleVerifier
    -- Step 2: Check 1.
    (check := fun stmt (s_hat : P.A) =>
      performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l
        stmt.original_claim stmt.t_eval_point s_hat)
    -- Steps 3 & 5: absorb the batching scalars, compute s₀, build the sumcheck statement.
    (accept := nextStatement κ L K P ℓ ℓ')

/-- The Oracle Reduction for the Batching Phase. -/
noncomputable def batchingOracleReduction : OracleReduction (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn L ℓ) (OStmtIn := aOStmtIn.OStmtIn) (WitIn := BatchingWitIn L K ℓ ℓ')
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' 0)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) where
  prover := oracleProver κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)
  verifier := oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)

omit [NeZero κ] [Nontrivial L] [Fintype L] [Fintype K] [DecidableEq K]
    [SampleableType L] [NeZero ℓ] [NeZero ℓ'] in
/-- Exact native verification on every carrier and challenge, including absorbing rejection. -/
theorem oracleVerifier_verify (stmt : BatchingStmtIn L ℓ) (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (tr : FullTranscript (pSpecBatching κ L K P)) :
    (oracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier.verify (stmt, oStmt) tr =
      (if performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim
          stmt.t_eval_point (tr.messages ⟨0, rfl⟩) then
        pure (nextStatement κ L K P ℓ ℓ' stmt (tr.messages ⟨0, rfl⟩)
          (tr.challenges ⟨1, rfl⟩), oStmt)
      else failure) := by
  apply guardedScalarRoundOracleVerifier_verify

/-- The native verifier's exact guard and deterministic output, for sequential composition. -/
def guardedForm : (oracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier.GuardedForm where
  check stmt tr := performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.1.original_claim
    stmt.1.t_eval_point (tr.messages ⟨0, rfl⟩)
  out stmt tr := (nextStatement κ L K P ℓ ℓ' stmt.1 (tr.messages ⟨0, rfl⟩)
    (tr.challenges ⟨1, rfl⟩), stmt.2)
  verify_eq stmt tr := oracleVerifier_verify κ L K P ℓ ℓ' h_l aOStmtIn stmt.1 stmt.2 tr

omit [NeZero κ] [Nontrivial L] [Fintype L] [Fintype K] [DecidableEq K]
    [DecidableEq L] [SampleableType L] [NeZero ℓ] [NeZero ℓ'] in
/-- The honest native prover issues exactly its existing vector challenge query. -/
theorem oracleProver_run (stmt : BatchingStmtIn L ℓ) (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : BatchingWitIn L K ℓ ℓ') :
    (oracleProver κ L K P ℓ ℓ' h_l aOStmtIn).run (stmt, oStmt) wit = (do
      let c ← liftComp ((pSpecBatching κ L K P).getChallenge ⟨1, rfl⟩)
        ([]ₒ + [(pSpecBatching κ L K P).Challenge]ₒ'challengeOracleInterface)
      let z := embedded_MLP_eval κ L K P ℓ ℓ' h_l wit.t' stmt.t_eval_point
      pure (FullTranscript.mk2 z c, (nextStatement κ L K P ℓ ℓ' stmt z c, oStmt),
        nextWitness κ L K P ℓ ℓ' h_l stmt z c wit.t')) := by
  have h0 : (pSpecBatching κ L K P).dir 0 = .P_to_V := rfl
  have h1 : (pSpecBatching κ L K P).dir 1 = .V_to_P := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_two,
    Prover.processRound_of_dir_eq_P_to_V 0 h0,
    Prover.processRound_of_dir_eq_V_to_P 1 h1]
  simp only [oracleProver, pure_bind, liftM_pure, bind_assoc]
  congr 1
  funext c
  exact congrArg (fun tr =>
    (pure (tr,
      (nextStatement κ L K P ℓ ℓ' stmt
        (embedded_MLP_eval κ L K P ℓ ℓ' h_l wit.t' stmt.t_eval_point) c, oStmt),
      nextWitness κ L K P ℓ ℓ' h_l stmt
        (embedded_MLP_eval κ L K P ℓ ℓ' h_l wit.t' stmt.t_eval_point) c wit.t') :
      OracleComp ([]ₒ + [(pSpecBatching κ L K P).Challenge]ₒ'challengeOracleInterface) _))
    (FullTranscript.mk2_eq_snoc_snoc _ _).symm

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

omit [Fintype L] [Fintype K] [DecidableEq K] [SampleableType L] [NeZero ℓ']
    [Nontrivial L] in
/-- The actual honest message passes the original scalar guard for every related native input. -/
theorem honest_check {stmt : BatchingStmtIn L ℓ} {oStmt : ∀ j, aOStmtIn.OStmtIn j}
    {wit : BatchingWitIn L K ℓ ℓ'}
    (hIn : ((stmt, oStmt), wit) ∈ batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn) :
    performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim stmt.t_eval_point
      (embedded_MLP_eval κ L K P ℓ ℓ' h_l wit.t' stmt.t_eval_point) = true := by
  obtain ⟨hp, hs, _⟩ := hIn
  rw [hp, hs]
  exact performCheckOriginalEvaluation_honest P h_l wit.t stmt.t_eval_point

omit [Fintype L] [Fintype K] [DecidableEq K] [DecidableEq L] [SampleableType L]
    [NeZero ℓ] [NeZero ℓ'] in
set_option backward.isDefEq.respectTransparency false in
/-- Every challenge gives the exact native initial-core relation with the same packed witness. -/
theorem honest_relOut {stmt : BatchingStmtIn L ℓ} {oStmt : ∀ j, aOStmtIn.OStmtIn j}
    {wit : BatchingWitIn L K ℓ ℓ'}
    (hIn : ((stmt, oStmt), wit) ∈ batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (c : Fin κ → L) :
    ((nextStatement κ L K P ℓ ℓ' stmt
      (embedded_MLP_eval κ L K P ℓ ℓ' h_l wit.t' stmt.t_eval_point) c, oStmt),
      nextWitness κ L K P ℓ ℓ' h_l stmt
        (embedded_MLP_eval κ L K P ℓ ℓ' h_l wit.t' stmt.t_eval_point) c wit.t') ∈
      sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0 := by
  refine ⟨trivial, rfl, ?_, hIn.2.2⟩
  exact initial_consistency_of_slices P h_l
    (nextStatement κ L K P ℓ ℓ' stmt
      (embedded_MLP_eval κ L K P ℓ ℓ' h_l wit.t' stmt.t_eval_point) c).ctx wit.t'
    (embedded_MLP_eval_sliceRel P h_l wit.t' stmt.t_eval_point)

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

omit [Fintype L] [Fintype K] [DecidableEq K] [SampleableType L]
    [NeZero κ] [NeZero ℓ] [NeZero ℓ'] in
set_option backward.isDefEq.respectTransparency false in
/-- A positive native output pins its actual guard and exact structured output relation. -/
theorem positive_output (stmt : BatchingStmtIn L ℓ) (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (tr : FullTranscript (pSpecBatching κ L K P)) (wit : SumcheckWitness L ℓ' 0)
    (h : Pr[ fun out => (out, wit) ∈ sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0 |
      OptionT.mk do (simulateQ impl
        ((oracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier.run
          (stmt, oStmt) tr)).run' (← init)] > 0) :
    performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim
      stmt.t_eval_point (tr.messages ⟨0, rfl⟩) = true ∧
      ((nextStatement κ L K P ℓ ℓ' stmt (tr.messages ⟨0, rfl⟩)
        (tr.challenges ⟨1, rfl⟩), oStmt), wit) ∈
          sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0 := by
  rw [gt_iff_lt, probEvent_pos_iff] at h
  obtain ⟨out, hout, hrel⟩ := h
  rw [OptionT.mem_support_iff] at hout
  simp only [Verifier.run, oracleVerifier_verify] at hout
  split at hout
  · rename_i hc
    change some out ∈ support (init >>= fun _ => pure (some
      (nextStatement κ L K P ℓ ℓ' stmt (tr.messages ⟨0, rfl⟩)
        (tr.challenges ⟨1, rfl⟩), oStmt))) at hout
    simp only [support_bind_const, support_pure, Set.mem_ofPred_eq] at hout
    obtain rfl := Option.some.inj hout.1
    exact ⟨hc, hrel⟩
  · change some out ∈ support (init >>= fun _ => pure none) at hout
    simp at hout

omit [Fintype L] [Fintype K] [DecidableEq K] [SampleableType L]
    [NeZero ℓ] [NeZero ℓ'] in
set_option backward.isDefEq.respectTransparency false in
/-- The endpoint knowledge state retains the exact native residual and oracle compatibility. -/
theorem batchingKStateProp_full (stmt : BatchingStmtIn L ℓ)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) (tr : FullTranscript (pSpecBatching κ L K P))
    (witOut : SumcheckWitness L ℓ' 0)
    (h : Pr[ fun out => (out, witOut) ∈ sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0 |
      OptionT.mk do (simulateQ impl
        ((oracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier.run
          (stmt, oStmt) tr)).run' (← init)] > 0) :
    batchingKStateProp κ L K P ℓ ℓ' h_l aOStmtIn (m := Fin.last 2) tr stmt witOut oStmt := by
  obtain ⟨hc, hr⟩ := positive_output κ L K P ℓ ℓ' h_l aOStmtIn stmt oStmt tr witOut h
  change sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l aOStmtIn 0
    (nextStatement κ L K P ℓ ℓ' stmt (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩))
    oStmt (nextWitness κ L K P ℓ ℓ' h_l stmt (tr.messages ⟨0, rfl⟩)
      (tr.challenges ⟨1, rfl⟩) witOut.t') ∧ _ ∧ _
  obtain ⟨_, hs, hsum, hcompat⟩ := hr
  refine ⟨⟨trivial, rfl, ?_, hcompat⟩, hc, hcompat⟩
  unfold witnessStructuralInvariant at hs
  unfold sumcheckConsistencyProp at hsum ⊢
  change _ = ∑ x ∈ _, eval x
    (projectToMidSumcheckPolyWithParam ℓ'
      (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) _ witOut.t' 0 Fin.elim0).val
  erw [← hs]
  exact hsum

/-- Knowledge state function for the batching phase. -/
noncomputable def batchingKnowledgeStateFunction :
  (oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)).KnowledgeStateFunction init impl
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (batchingRbrExtractor κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)) where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    batchingKStateProp κ L K P ℓ ℓ' h_l aOStmtIn tr stmt witMid oStmt
  toFun_empty _ _ := by rfl
  toFun_next := fun m hDir stmtIn tr msg witMid =>
    match m with
    | ⟨0, _⟩ => by
      intro hSuccTrue
      simp only [batchingKStateProp, Fin.zero_eta, Fin.isValue, Fin.succ_zero_eq_one,
        Transcript.equivMessagesChallenges_apply, Fin.castSucc_zero,
        batchingRbrExtractor, Fin.mk_one, Fin.succ_one_eq_two,
        batchingInputRelationProp] at ⊢ hSuccTrue
      obtain ⟨hp, he, hc, ho⟩ := hSuccTrue
      refine ⟨hp, ?_, ho⟩
      apply original_claim_of_check P h_l witMid.t stmtIn.1.t_eval_point
        stmtIn.1.original_claim _ ?_ hc
      rw [← hp]
      exact he
    | ⟨1, h⟩ => nomatch h
  toFun_full := fun ⟨stmt, oStmt⟩ tr witOut h =>
    batchingKStateProp_full κ L K P ℓ ℓ' h_l aOStmtIn stmt oStmt tr witOut h

/-! ## Security Properties -/

omit [Fintype L] [Fintype K] [DecidableEq K] [NeZero ℓ'] in
/-- Perfect completeness for the batching phase oracle reduction. -/
theorem batchingReduction_perfectCompleteness :
    OracleReduction.perfectCompleteness
    (oracleReduction := batchingOracleReduction κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn))
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (init := init) (impl := impl) := by
  classical
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt wit hIn x hx
  rw [Reduction.run_eq_of_guarded_verifier _ (guardedForm κ L K P ℓ ℓ' h_l aOStmtIn)] at hx
  change x ∈ support ((oracleProver κ L K P ℓ ℓ' h_l aOStmtIn).run stmt wit >>= fun r =>
    pure (if (guardedForm κ L K P ℓ ℓ' h_l aOStmtIn).check stmt r.1 then
      some (r, (guardedForm κ L K P ℓ ℓ' h_l aOStmtIn).out stmt r.1) else none)) at hx
  rw [oracleProver_run] at hx
  simp only [bind_assoc, pure_bind, mem_support_bind_iff] at hx
  obtain ⟨c, _, hx⟩ := hx
  have hc := honest_check κ L K P ℓ ℓ' h_l aOStmtIn hIn
  simp only [guardedForm, FullTranscript.messages, FullTranscript.mk2,
    hc, if_true, mem_support_pure_iff] at hx
  subst x
  exact ⟨_, rfl, honest_relOut κ L K P ℓ ℓ' h_l aOStmtIn hIn c, rfl⟩

omit [Fintype K] [DecidableEq K] [NeZero ℓ'] in
set_option backward.isDefEq.respectTransparency false in
/-- Exact fixed-prefix knowledge soundness for the existing native carrier/vector transcript. -/
theorem batchingOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith [NoZeroDivisors L]
    (hfunctional : aOStmtIn.Functional) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
      (sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
      (oracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier
      (batchingWitMid L K ℓ ℓ') (batchingRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn)
      (batchingKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn)
      (batchingRBRKnowledgeError κ L K P) := by
  let _ : IsDomain L := NoZeroDivisors.to_isDomain L
  let _ : Algebra (Packing.sameAlgebra P.basis).P L := inferInstanceAs (Algebra L L)
  let _ : IsScalarTower K (Packing.sameAlgebra P.basis).P L :=
    inferInstanceAs (IsScalarTower K L L)
  classical
  intro stmt i tr
  rcases i with ⟨i, hdir⟩
  fin_cases i
  · contradiction
  · change Transcript (1 : Fin 3) (pSpecBatching κ L K P) at tr
    dsimp only [batchingKnowledgeStateFunction, batchingRbrExtractor]
    change Pr[fun c : Fin κ → L => ∃ wit : SumcheckWitness L ℓ' 0,
      ¬ batchingKStateProp κ L K P ℓ ℓ' h_l aOStmtIn (m := 1) tr stmt.1
        { t := unpackMLE κ L K ℓ ℓ' h_l P.basis wit.t', t' := wit.t' } stmt.2 ∧
        batchingKStateProp κ L K P ℓ ℓ' h_l aOStmtIn (m := 2)
          (tr.concat (m := (1 : Fin 2)) c) stmt.1 wit stmt.2 | $ᵗ (Fin κ → L)] ≤
      (↑((κ : ℝ≥0) / (Fintype.card L : ℝ≥0)) : ℝ≥0∞)
    rw [probEvent_uniformSample_eq_prob_uniformOfFintype]
    refine (Probability.Pr_le_Pr_of_implies _ _ _ ?_).trans
      (Packing.FullFamily.compatibility_badEvent_le (Packing.sameAlgebra P.basis) ℓ'
        (Packing.BatchingStrategy.eqFold L κ)
        (fun o p => aOStmtIn.initialCompatibility (p, o))
        (fun {o p p'} => hfunctional o p p') (by intro x y h; exact h)
        (getEvaluationPointSuffix κ L ℓ ℓ' h_l stmt.1.t_eval_point) stmt.2
        (P.decomposeColumns (tr ⟨0, by decide⟩)))
    rintro c ⟨wit, hbefore, hafter⟩
    change sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l aOStmtIn 0
      (nextStatement κ L K P ℓ ℓ' stmt.1 (tr ⟨0, by decide⟩) c) stmt.2
      (nextWitness κ L K P ℓ ℓ' h_l stmt.1 (tr ⟨0, by decide⟩) c wit.t') ∧
        performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.1.original_claim
          stmt.1.t_eval_point (tr ⟨0, by decide⟩) = true ∧
        aOStmtIn.initialCompatibility (wit.t', stmt.2) at hafter
    obtain ⟨hrel, hc, ho⟩ := hafter
    refine ⟨wit.t', ho, ?_, ?_⟩
    · intro hslice
      apply hbefore
      change wit.t' = packMLE κ L K ℓ ℓ' h_l P.basis
          (unpackMLE κ L K ℓ ℓ' h_l P.basis wit.t') ∧
        embedded_MLP_eval κ L K P ℓ ℓ' h_l wit.t' stmt.1.t_eval_point = tr ⟨0, by decide⟩ ∧
        performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.1.original_claim
          stmt.1.t_eval_point (tr ⟨0, by decide⟩) = true ∧
        aOStmtIn.initialCompatibility (wit.t', stmt.2)
      exact ⟨(packMLE_unpackMLE h_l P.basis wit.t').symm,
        (embedded_MLP_eval_eq_iff_sliceRel P h_l wit.t' stmt.1.t_eval_point (tr ⟨0, by decide⟩)).mpr
          hslice, hc, ho⟩
    · have hsum := (initial_consistency_iff P h_l
        (nextStatement κ L K P ℓ ℓ' stmt.1 (tr ⟨0, by decide⟩) c).ctx wit.t'
        (compute_s0 κ L K P (tr ⟨0, by decide⟩) c)).mp hrel.2.2.1
      rw [compute_s0_eq_sum] at hsum
      exact hsum

omit [Fintype K] [DecidableEq K] [NeZero ℓ'] in
/-- RBR knowledge soundness for the batching phase oracle verifier. -/
theorem batchingOracleVerifier_rbrKnowledgeSoundness [NoZeroDivisors L]
    (hfunctional : aOStmtIn.Functional) :
    OracleVerifier.rbrKnowledgeSoundness
    (verifier := oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn))
    (init := init) (impl := impl)
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (rbrKnowledgeError := batchingRBRKnowledgeError (κ:=κ) (L:=L) (K:=K) (P:=P)) := by
  exact ⟨batchingWitMid L K ℓ ℓ', batchingRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn,
    batchingKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn,
    Verifier.rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith init impl
      (batchingOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith
        κ L K P ℓ ℓ' h_l aOStmtIn hfunctional)⟩

end BatchingPhase
end RingSwitching
