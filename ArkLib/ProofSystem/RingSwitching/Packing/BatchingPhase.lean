/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
import ArkLib.ProofSystem.RingSwitching.Packing.Spec
import ArkLib.OracleReduction.Basic
import CompPoly.Fields.Binary.Tower.TensorAlgebra

/-!
# ArkLib.ProofSystem.RingSwitching.Packing.BatchingPhase

Definitions and results for this component of ArkLib.
-/

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal
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
2. `V` decomposes `ŝ =: Σ_{v ∈ {0,1}^κ} β_v ⊗ ŝ_v` (column coordinates on the right
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
5. `V` decomposes `ŝ =: Σ_{u ∈ {0,1}^κ} ŝ_u ⊗ β_u` (row coordinates on the left tensor
  factor), and
  sets `s_0 := Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ ŝ_u`.

## Security scaffolding

The round-by-round extractor (`batchingRbrExtractor`, which unpacks `t` from `t'`), the
knowledge-state function, the per-challenge knowledge error (`κ/|L|` at the batching
challenge), and the completeness/soundness statements. Leaf proofs are open (`sorry`).

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

/-- The batching-phase verifier as an instance of the family-shared check-then-update
scalar-round verifier (`RingSwitching.scalarRoundOracleVerifier`, `RoundVerifiers.lean`):
query ŝ (step 1), run Check 1 against the column decomposition (step 2, reject to
`failureState` on failure), then update the statement with the batched sumcheck target `s₀`
from the batching scalars `r''` (steps 3 and 5). -/
noncomputable def oracleVerifier :
  OracleVerifier (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn L ℓ) (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) :=
  scalarRoundOracleVerifier
    -- Step 2: Check 1.
    (check := fun stmt (s_hat : P.A) =>
      performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l
        stmt.original_claim stmt.t_eval_point s_hat)
    -- Steps 3 & 5: absorb the batching scalars, compute s₀, build the sumcheck statement.
    (accept := fun stmt s_hat r_batching =>
      { ctx := {
          t_eval_point := stmt.t_eval_point,
          original_claim := stmt.original_claim,
          s_hat := s_hat,
          r_batching := r_batching },
        sumcheck_target := compute_s0 κ L K P s_hat r_batching,
        challenges := Fin.elim0 })
    (reject := fun stmt s_hat => failureState κ L K P ℓ ℓ' stmt s_hat)

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
    | ⟨0, _⟩ => by -- from accumulative KState
      intro hSuccTrue
      simp only [batchingKStateProp, Fin.zero_eta, Fin.isValue, Fin.succ_zero_eq_one,
        Transcript.equivMessagesChallenges_apply, Fin.castSucc_zero,
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

omit [Fintype L] [Fintype K] [DecidableEq K] in
/-- Perfect completeness for the batching phase oracle reduction. -/
theorem batchingReduction_perfectCompleteness :
    OracleReduction.perfectCompleteness
    (oracleReduction := batchingOracleReduction κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn))
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (init := init) (impl := impl) := by
  classical
  -- The honest prover's computations are deterministic. If the input relation holds,
  -- the prover correctly computes ŝ, h, and s₀, so the output relation will also hold.
  unfold OracleReduction.perfectCompleteness
  sorry

omit [Fintype K] [DecidableEq K] in
/-- RBR knowledge soundness for the batching phase oracle verifier. -/
theorem batchingOracleVerifier_rbrKnowledgeSoundness [NoZeroDivisors L] :
    OracleVerifier.rbrKnowledgeSoundness
    (verifier := oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn))
    (init := init) (impl := impl)
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (rbrKnowledgeError := batchingRBRKnowledgeError (κ:=κ) (L:=L) (K:=K) (P:=P)) := by
  let _ : IsDomain L := NoZeroDivisors.to_isDomain L
  classical
  -- Proof follows by constructing the extractor and knowledge state function.
  use batchingWitMid L K ℓ ℓ'
  use batchingRbrExtractor κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)
  use batchingKnowledgeStateFunction κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn) (init:=init) (impl:=impl)
  intro stmtIn witIn prover iChal
  -- `KState 1 = (t' = packMLE t) ∧ (ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1})))`
    -- `∧ (s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v.`
  -- `KState 2 = (s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v) ∧`
    -- `h = projectSumcheckPoly t' 0 r r' ∧ s_0 = Σ_{w ∈ {0,1}^{ℓ'}} h(w)`
  -- ⊢ `Pr[KState(2, witMidSucc) ∧ ¬KState(1, extractMid(iChal, witMidSucc))] ≤ (κ/|L|)`
  sorry

end BatchingPhase
end RingSwitching
