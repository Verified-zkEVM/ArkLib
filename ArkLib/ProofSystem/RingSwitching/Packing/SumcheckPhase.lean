/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
import ArkLib.ProofSystem.RingSwitching.Packing.Spec
import ArkLib.OracleReduction.Completeness
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness

-- This file bundles the per-round + final + core sumcheck phases with their soundness proofs, which
-- exceeds the default long-file cap; raise the local limit.
set_option linter.style.longFile 2200

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix Binius.BinaryBasefold ProbabilityTheory
open scoped NNReal
open Sumcheck.Structured

/-!
# Ring-Switching Core Interaction Phase

This module implements the core interactive sumcheck phase of the ring-switching protocol.

### Iterated Sumcheck Steps
6. P and V execute the following loop:
   for `i ∈ {0, ..., ℓ'-1}` do
     P sends V the polynomial `hᵢ(X) := Σ_{w ∈ {0,1}^{ℓ'-i-1}} h(r'₀, ..., r'_{i-1}, X, w₀, ...,
     w_{ℓ'-i-2})`.
     V requires `sᵢ ?= hᵢ(0) + hᵢ(1)`. V samples `r'ᵢ ← L`, sets `s_{i+1} := hᵢ(r'ᵢ)`,
     and sends P `r'ᵢ`.

Each iteration of the loop constitutes a single round:
- Round i (for i = 1, ..., ℓ'):
  1. Prover sends sumcheck polynomial h_i(X) over large field L
  2. Verifier samples challenge α_i ∈ L
    - Prover & verifier updates state based on challenge

This is the core computational phase with ℓ' rounds, each with 2 messages, and is the main
source of RBR knowledge soundness error.

### Final Sumcheck Step
7. `P` computes `s' := t'(r'_0, ..., r'_{ℓ'-1})` and sends `V` `s'`.
8. `V` sets `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` and
    decomposes `e =: Σ_{u ∈ {0,1}^κ} β_u ⊗ e_u`.
9. `V` requires `s_{ℓ'} ?= (Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ e_u) ⋅ s'`.
-/

namespace RingSwitching.SumcheckPhase
noncomputable section

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (aOStmtIn : AbstractOStmtIn L ℓ')

section IteratedSumcheckStep
variable (i : Fin ℓ')

/-! ## Per-round prover / verifier (`ReductionLogicStep`-based)

Ported from our HEAD ring-switching architecture, Profile-parameterized (`β/𝓑 → P`). Uses our
`ReductionLogicStep` (from `BinaryBasefold`). The boolean-hypercube embedding `𝓑 := boolEmbedding L`
bridges the BBF `𝓑`-form lemmas (`getSumcheckRoundPoly ℓ' 𝓑`, BBF `sumcheckConsistencyProp`) with
the `Sumcheck.Structured.sumcheckConsistencyProp (boolDomain L _)` used inside `masterKStateProp`:
`(boolDomain L k).cube = (univ.map (boolEmbedding L)) ^ᶠ k` definitionally, so the two
consistency props are `rfl`-equal. -/

/-- Pure verifier check: validates that `s = h(0) + h(1)` (sum over the boolean hypercube). -/
@[reducible]
def sumcheckVerifierCheck (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ P) i.castSucc) (h_i : L⦃≤ 2⦄[X]) : Prop :=
  h_i.val.eval (boolEmbedding L 0) + h_i.val.eval (boolEmbedding L 1) = stmtIn.sumcheck_target

/-- Pure verifier output: computes the output statement given the transcript. -/
@[reducible]
def sumcheckVerifierStmtOut (stmtIn : Statement (L := L) (ℓ := ℓ')
    (RingSwitchingBaseContext κ L K ℓ P) i.castSucc) (h_i : L⦃≤ 2⦄[X]) (r_i' : L) :
    Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ := {
      ctx := stmtIn.ctx,
      sumcheck_target := h_i.val.eval r_i',
      challenges := Fin.snoc stmtIn.challenges r_i'
    }

/-- Pure prover message computation: computes `h_i` from the witness. -/
@[reducible]
def sumcheckProverComputeMsg (witIn : SumcheckWitness L ℓ' i.castSucc) : L⦃≤ 2⦄[X] :=
  getSumcheckRoundPoly ℓ' (boolEmbedding L) (i := i) witIn.H

/-- Pure prover output: computes the output witness given the transcript. -/
@[reducible]
def sumcheckProverWitOut (_stmtIn : Statement (L := L) (ℓ := ℓ')
  (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (witIn : SumcheckWitness L ℓ' i.castSucc) (r_i' : L) : SumcheckWitness L ℓ' i.succ :=
  {
      t' := witIn.t',
      H := Binius.BinaryBasefold.projectToNextSumcheckPoly (L := L) (ℓ := ℓ') (i := i)
        (Hᵢ := witIn.H) (rᵢ := r_i')
  }

/-- The Logic Instance for the `i`-th round of Ring Switching Sumcheck. -/
def sumcheckStepLogic :
    Binius.BinaryBasefold.ReductionLogicStep
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
      (SumcheckWitness L ℓ' i.castSucc)
      (aOStmtIn.OStmtIn)
      (aOStmtIn.OStmtIn)
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ)
      (SumcheckWitness L ℓ' i.succ)
      (pSpecSumcheckRound L) where
  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictSumcheckRoundRelation κ L K P ℓ ℓ' h_l
      aOStmtIn i.castSucc
  completeness_relOut := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictSumcheckRoundRelation κ L K P ℓ ℓ' h_l
      aOStmtIn i.succ
  verifierCheck := fun stmtIn transcript =>
    sumcheckVerifierCheck (κ:=κ) (L:=L) (K:=K) (P:=P) (ℓ:=ℓ) (ℓ':=ℓ')
      i stmtIn (transcript.messages ⟨0, rfl⟩)
  verifierOut := fun stmtIn transcript =>
    sumcheckVerifierStmtOut (κ:=κ) (L:=L) (K:=K) (P:=P) (ℓ:=ℓ) (ℓ':=ℓ') i stmtIn
      (transcript.messages ⟨0, rfl⟩) (transcript.challenges ⟨1, rfl⟩)
  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun i => rfl
  honestProverTranscript := fun _stmtIn witIn _oStmtIn chal =>
    let msg := sumcheckProverComputeMsg (L:=L) (ℓ':=ℓ') i witIn
    FullTranscript.mk2 msg (chal ⟨1, rfl⟩)
  proverOut := fun stmtIn witIn oStmtIn transcript =>
    let h_i := transcript.messages ⟨0, rfl⟩
    let r_i' := transcript.challenges ⟨1, rfl⟩
    let stmtOut := sumcheckVerifierStmtOut (κ:=κ) (L:=L) (K:=K) (P:=P) (ℓ:=ℓ) (ℓ':=ℓ')
      i stmtIn h_i r_i'
    let witOut := sumcheckProverWitOut (κ:=κ) (L:=L) (K:=K) (P:=P) (ℓ:=ℓ) (ℓ':=ℓ')
      i stmtIn witIn r_i'
    ((stmtOut, oStmtIn), witOut)

/-! ## Prover and Verifier Implementation -/

/-- The state maintained by the prover throughout the sumcheck phase. -/
def iteratedSumcheckPrvState (i : Fin ℓ') : Fin (2 + 1) → Type := fun
  | ⟨0, _⟩ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc
    × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' i.castSucc
  | ⟨1, _⟩ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc
    × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' i.castSucc × L⦃≤ 2⦄[X]
  | _ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc ×
    (∀ j, aOStmtIn.OStmtIn j) ×
    SumcheckWitness L ℓ' i.castSucc × L⦃≤ 2⦄[X] × L

/-- The prover for the `i`-th round of Ring Switching. -/
noncomputable def iteratedSumcheckOracleProver (i : Fin ℓ') :
  OracleProver (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L) where
  PrvState := iteratedSumcheckPrvState κ L K P ℓ ℓ' aOStmtIn i
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage
  | ⟨0, _⟩ => fun ⟨stmt, oStmt, wit⟩ => do
    let h_i := sumcheckProverComputeMsg (L:=L) (ℓ':=ℓ') i wit
    pure ⟨h_i, (stmt, oStmt, wit, h_i)⟩
  | ⟨1, _⟩ => by contradiction
  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, h_i⟩ => do
    pure (fun r_i' => (stmt, oStmt, wit, h_i, r_i'))
  output := fun finalPrvState =>
    let (stmt, oStmt, wit, h_i, r_i') := finalPrvState
    let logic := sumcheckStepLogic (κ:=κ) (L:=L) (K:=K) (P:=P) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l)
      (aOStmtIn:=aOStmtIn) i
    let t := FullTranscript.mk2 h_i r_i'
    pure (logic.proverOut stmt wit oStmt t)

open Classical in
/-- The oracle verifier for the `i`-th round of Ring Switching. -/
noncomputable def iteratedSumcheckOracleVerifier (i : Fin ℓ') :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecSumcheckRound L) where
  verify := fun stmtIn pSpecChallenges => do
    let h_i : L⦃≤ 2⦄[X] ← query (spec := [(pSpecSumcheckRound L).Message]ₒ)
       ⟨⟨0, by rfl⟩, (by exact ())⟩
    let r_i' : L := pSpecChallenges ⟨1, rfl⟩
    let t := FullTranscript.mk2 h_i r_i'
    let logic := sumcheckStepLogic (κ:=κ) (L:=L) (K:=K) (P:=P) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l)
      (aOStmtIn:=aOStmtIn) i
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)
  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun _ => rfl

/-- The oracle reduction that is the `i`-th round of Ring Switching. -/
noncomputable def iteratedSumcheckOracleReduction (i : Fin ℓ') :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L) where
  prover := iteratedSumcheckOracleProver κ L K P ℓ ℓ' h_l aOStmtIn i
  verifier := iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn i

-- Pin the challenge `OracleInterface` for the (reducible-`abbrev`) `pSpecSumcheckRound L`, so
-- instance synthesis for `[…Challenge]ₒ` succeeds without unfolding the abbrev (the "conflict"
-- noted in the HEAD proof).
instance instOracleInterfacePSpecSumcheckRoundChallenge :
    ∀ i, OracleInterface ((pSpecSumcheckRound L).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

/-- Per-index `Fintype` for the per-round sumcheck challenges, needed by the soundness-unrolling
lemma `probEvent_soundness_goal_unroll_log'` (which takes `[∀ i, Fintype (pSpec.Challenge i)]`). -/
instance instFintypePSpecSumcheckRoundChallengeIdx :
    ∀ j, Fintype ((pSpecSumcheckRound L).Challenge j)
  | ⟨0, h0⟩ => by nomatch h0
  | ⟨1, _⟩ => by
    change Fintype L
    infer_instance

/-- Per-index `Inhabited` for the per-round sumcheck challenges, needed by
`probEvent_soundness_goal_unroll_log'` (which takes `[∀ i, Inhabited (pSpec.Challenge i)]`). -/
instance instInhabitedPSpecSumcheckRoundChallengeIdx :
    ∀ j, Inhabited ((pSpecSumcheckRound L).Challenge j)
  | ⟨0, h0⟩ => by nomatch h0
  | ⟨1, _⟩ => by
    change Inhabited L
    exact ⟨0⟩

/-- `Fintype` for the per-round sumcheck challenge oracle spec. -/
instance instFintypePSpecSumcheckRoundChallenge :
    [(pSpecSumcheckRound L).Challenge]ₒ.Fintype := by
  refine { fintypeB := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  match i with
  | ⟨0, _⟩ => simp [pSpecSumcheckRound, pSpecSumcheckRoundWithDegree,
      Sumcheck.Structured.pSpecSumcheckRound] at hi
  | ⟨1, _⟩ =>
    cases q
    change _root_.Fintype L
    infer_instance

/-- `Inhabited` for the per-round sumcheck challenge oracle spec. -/
instance instInhabitedPSpecSumcheckRoundChallenge :
    [(pSpecSumcheckRound L).Challenge]ₒ.Inhabited := by
  refine { inhabitedB := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  match i with
  | ⟨0, _⟩ => simp [pSpecSumcheckRound, pSpecSumcheckRoundWithDegree,
      Sumcheck.Structured.pSpecSumcheckRound] at hi
  | ⟨1, _⟩ =>
    cases q
    change Inhabited L
    exact ⟨0⟩

/-- `IsUniformSpec` (VCVio v4.30 opt-in) for the per-round sumcheck challenge oracle spec, needed by
`unroll_2_message_reduction_perfectCompleteness` in the iterated-sumcheck completeness proof. -/
noncomputable instance instIsUniformSpecPSpecSumcheckRoundChallenge :
    IsUniformSpec [(pSpecSumcheckRound L).Challenge]ₒ := IsUniformSpec.ofFintypeInhabited _

/-! ## Strong Completeness Theorem -/

section FixFirstBridge
variable {L' : Type} [CommRing L'] {ℓ'' : ℕ} [NeZero ℓ'']

/-- The promoted `MvPolynomial.fixFirstVariablesOfMQP` and the legacy
`Binius.BinaryBasefold.fixFirstVariablesOfMQP` compute the same substitution (fix the first `v`
variables to `challenges`); both agree with the `bind₁` normal form. -/
lemma mvPoly_fixFirst_eq_bbf_fixFirst (v : Fin (ℓ'' + 1))
    (poly : MvPolynomial (Fin ℓ'') L') (challenges : Fin v → L') :
    MvPolynomial.fixFirstVariablesOfMQP ℓ'' v poly challenges =
      Binius.BinaryBasefold.fixFirstVariablesOfMQP ℓ'' v poly challenges := by
  rw [Binius.BinaryBasefold.fixFirstVariablesOfMQP_eq_bind₁]
  let subst : Fin ℓ'' → MvPolynomial (Fin (ℓ'' - v)) L' := fun j =>
    if hj : j.val < v.val then MvPolynomial.C (challenges ⟨j.val, hj⟩)
    else MvPolynomial.X (⟨j.val - v, by omega⟩ : Fin (ℓ'' - v))
  have hX : ∀ j : Fin ℓ'',
      MvPolynomial.fixFirstVariablesOfMQP ℓ'' v (MvPolynomial.X j) challenges =
        MvPolynomial.bind₁ subst (MvPolynomial.X j) := by
    intro j
    rw [MvPolynomial.bind₁_X_right]
    unfold subst MvPolynomial.fixFirstVariablesOfMQP
    dsimp only
    rw [MvPolynomial.rename_X]
    by_cases hj : j.val < v.val
    · have hsym : (finSumFinEquiv (m := ↑v) (n := ℓ'' - ↑v)).symm (Fin.cast (by omega) j)
          = Sum.inl (⟨j.val, hj⟩ : Fin ↑v) := by
        rw [Equiv.symm_apply_eq, finSumFinEquiv_apply_left]; apply Fin.ext; simp
      have hmap : (((finCongr (by omega : ℓ'' = ↑v + (ℓ'' - ↑v))).trans
          ((finSumFinEquiv (m := ↑v) (n := ℓ'' - ↑v)).symm.trans (Equiv.sumComm _ _))) j)
          = Sum.inr (⟨j.val, hj⟩ : Fin ↑v) := by
        simp only [Equiv.trans_apply, finCongr_apply, Equiv.sumComm_apply, hsym, Sum.swap_inl]
      rw [hmap]
      simp only [MvPolynomial.sumAlgEquiv_apply, MvPolynomial.sumToIter_Xr, MvPolynomial.map_C,
        MvPolynomial.eval_X, hj, ↓reduceDIte]
    · have hsym : (finSumFinEquiv (m := ↑v) (n := ℓ'' - ↑v)).symm (Fin.cast (by omega) j)
          = Sum.inr (⟨j.val - v, by omega⟩ : Fin (ℓ'' - ↑v)) := by
        rw [Equiv.symm_apply_eq, finSumFinEquiv_apply_right]
        apply Fin.ext; simp only [Fin.natAdd_mk, Fin.coe_cast]; omega
      have hmap : (((finCongr (by omega : ℓ'' = ↑v + (ℓ'' - ↑v))).trans
          ((finSumFinEquiv (m := ↑v) (n := ℓ'' - ↑v)).symm.trans (Equiv.sumComm _ _))) j)
          = Sum.inl (⟨j.val - v, by omega⟩ : Fin (ℓ'' - ↑v)) := by
        simp only [Equiv.trans_apply, finCongr_apply, Equiv.sumComm_apply, hsym, Sum.swap_inr]
      rw [hmap]
      simp only [MvPolynomial.sumAlgEquiv_apply, MvPolynomial.sumToIter_Xl, MvPolynomial.map_X,
        hj, ↓reduceDIte]
  induction poly using MvPolynomial.induction_on with
  | C a =>
    unfold MvPolynomial.fixFirstVariablesOfMQP
    simp only [MvPolynomial.rename_C, MvPolynomial.sumAlgEquiv_apply, MvPolynomial.sumToIter_C,
      MvPolynomial.map_C, MvPolynomial.eval_C, MvPolynomial.bind₁_C_right]
  | add p q hp hq =>
    have h_add : MvPolynomial.fixFirstVariablesOfMQP ℓ'' v (p + q) challenges =
        MvPolynomial.fixFirstVariablesOfMQP ℓ'' v p challenges +
          MvPolynomial.fixFirstVariablesOfMQP ℓ'' v q challenges := by
      unfold MvPolynomial.fixFirstVariablesOfMQP; simp only [map_add]
    rw [h_add, hp, hq, map_add]
  | mul_X p j hp =>
    have h_mul : MvPolynomial.fixFirstVariablesOfMQP ℓ'' v (p * MvPolynomial.X j) challenges =
        MvPolynomial.fixFirstVariablesOfMQP ℓ'' v p challenges *
          MvPolynomial.fixFirstVariablesOfMQP ℓ'' v (MvPolynomial.X j) challenges := by
      unfold MvPolynomial.fixFirstVariablesOfMQP; simp only [map_mul]
    rw [h_mul, hp, hX, map_mul]

end FixFirstBridge

omit [NeZero κ] [Fintype L] [DecidableEq L] [SampleableType L]
    [Fintype K] [DecidableEq K] [NeZero ℓ] in
/-- The `WithParam` analog of `projectToMidSumcheckPoly_succ` for the ring-switching multiplier
(combinator `X`, so `computeRoundPoly` reduces to `computeInitialSumcheckPoly t (multpoly ctx)`):
advancing the mid-poly by one round (fixing `X₀ := r_i'`) equals the projection at `i.succ`. -/
lemma projectToMidSumcheckPolyWithParam_succ_ringswitching
    (ctx : RingSwitchingBaseContext κ L K ℓ P) (t : Sumcheck.Structured.MultilinearPoly L ℓ')
    (i : Fin ℓ') (challenges : Fin i.castSucc → L) (r_i' : L) :
    (Binius.BinaryBasefold.projectToNextSumcheckPoly (L := L) (ℓ := ℓ') (i := i)
      (Hᵢ := projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
        (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
        (ctx := ctx) (t := t) (i := i.castSucc) (challenges := challenges)) (rᵢ := r_i')).val =
    (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
      (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
      (ctx := ctx) (t := t) (i := i.succ)
      (challenges := Fin.snoc challenges r_i')).val := by
  -- `computeRoundPoly` for the ring-switching param (combinator `X`) has value
  -- `(multpoly ctx).val * t.val = (computeInitialSumcheckPoly t (multpoly ctx)).val`.
  set m := (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly ctx with hm
  have h_H0 :
      (Sumcheck.Structured.computeRoundPoly (L := L) (ℓ := ℓ')
        (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx t).val =
      (Binius.BinaryBasefold.computeInitialSumcheckPoly (L := L) (ℓ := ℓ') t m).val := by
    simp only [Sumcheck.Structured.computeRoundPoly,
      Binius.BinaryBasefold.computeInitialSumcheckPoly, RingSwitching_SumcheckMultParam,
      Polynomial.aeval_X, hm, mul_comm]
  -- Both `WithParam` projections agree with the identity-combinator `projectToMidSumcheckPoly`
  -- at their respective indices (same `H₀`, same `fixFirstVariablesOfMQP`).
  have h_mid_eq : ∀ (j : Fin (ℓ' + 1)) (ch : Fin j → L),
      (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
        (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
        (ctx := ctx) (t := t) (i := j) (challenges := ch)).val =
      (Binius.BinaryBasefold.projectToMidSumcheckPoly (L := L) (ℓ := ℓ') t m j ch).val := by
    intro j ch
    show MvPolynomial.fixFirstVariablesOfMQP ℓ' ⟨j.val, by omega⟩
        (Sumcheck.Structured.computeRoundPoly (L := L) (ℓ := ℓ')
          (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx t).val ch = _
    rw [mvPoly_fixFirst_eq_bbf_fixFirst, h_H0]
    rfl
  rw [h_mid_eq i.succ (Fin.snoc challenges r_i')]
  rw [Binius.BinaryBasefold.projectToNextSumcheckPoly]
  simp only [Binius.BinaryBasefold.fixFirstVariablesOfMQP]
  rw [show (Binius.BinaryBasefold.projectToMidSumcheckPoly (L := L) (ℓ := ℓ') t m i.succ
      (Fin.snoc challenges r_i')) =
      Binius.BinaryBasefold.projectToNextSumcheckPoly (L := L) (ℓ := ℓ') i
        (Binius.BinaryBasefold.projectToMidSumcheckPoly (L := L) (ℓ := ℓ') t m i.castSucc challenges)
        r_i' from projectToMidSumcheckPoly_succ (L := L) (ℓ := ℓ') t m i challenges r_i']
  rw [Binius.BinaryBasefold.projectToNextSumcheckPoly]
  simp only [Binius.BinaryBasefold.fixFirstVariablesOfMQP]
  rw [h_mid_eq i.castSucc challenges]

omit [NeZero κ] [Fintype L] [DecidableEq L] [SampleableType L]
    [Fintype K] [DecidableEq K] [NeZero ℓ] in
/-- The `WithParam` analog of `projectToMidSumcheckPoly_at_last_eval` for the ring-switching
multiplier (combinator `X`): at `Fin.last ℓ'` the projected mid-poly (a constant, since
`ℓ' - Fin.last ℓ' = 0`) evaluates to `(multpoly ctx)(challenges) · t(challenges)`. Reduces to the
identity-combinator `projectToMidSumcheckPoly_at_last_eval` via the `computeRoundPoly = m · t`
bridge. -/
lemma projectToMidSumcheckPolyWithParam_at_last_eval_ringswitching
    (ctx : RingSwitchingBaseContext κ L K ℓ P) (t : Sumcheck.Structured.MultilinearPoly L ℓ')
    (challenges : Fin (Fin.last ℓ') → L) (x : Fin (ℓ' - (Fin.last ℓ' : Fin (ℓ' + 1))) → L) :
    (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
      (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
      (ctx := ctx) (t := t) (i := Fin.last ℓ') (challenges := challenges)).val.eval x =
    ((RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly ctx).val.eval challenges *
      t.val.eval challenges := by
  set m := (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly ctx with hm
  -- `WithParam` at `Fin.last` agrees (`.val`) with the identity-combinator projection.
  have h_mid_eq :
      (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
        (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
        (ctx := ctx) (t := t) (i := Fin.last ℓ') (challenges := challenges)).val =
      (Binius.BinaryBasefold.projectToMidSumcheckPoly (L := L) (ℓ := ℓ') t m
        (Fin.last ℓ') challenges).val := by
    have h_H0 :
        (Sumcheck.Structured.computeRoundPoly (L := L) (ℓ := ℓ')
          (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx t).val =
        (Binius.BinaryBasefold.computeInitialSumcheckPoly (L := L) (ℓ := ℓ') t m).val := by
      simp only [Sumcheck.Structured.computeRoundPoly,
        Binius.BinaryBasefold.computeInitialSumcheckPoly, RingSwitching_SumcheckMultParam,
        Polynomial.aeval_X, hm, mul_comm]
    show MvPolynomial.fixFirstVariablesOfMQP ℓ' ⟨(Fin.last ℓ').val, by omega⟩
        (Sumcheck.Structured.computeRoundPoly (L := L) (ℓ := ℓ')
          (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) ctx t).val challenges = _
    rw [mvPoly_fixFirst_eq_bbf_fixFirst, h_H0]
    rfl
  rw [h_mid_eq]
  exact projectToMidSumcheckPoly_at_last_eval (L := L) (ℓ := ℓ') t m challenges x

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [NeZero κ] [Fintype L] [DecidableEq L] [SampleableType L]
    [Fintype K] [DecidableEq K] [NeZero ℓ] in
/-- The sumcheck logic step is strongly complete: on any input in the strict round relation, the
honest transcript passes the verifier check and the outputs satisfy the strict round relation.
Ported from HEAD `sumcheckStep_is_logic_complete`, adapted to the Profile frame's flat
`masterStrictKStateProp` (`boolDomain`-keyed `sumcheckConsistencyProp` + `WithParam`
`witnessStructuralInvariant` + `strictInitialCompatibility`). -/
lemma sumcheckStep_is_logic_complete (i : Fin ℓ') :
    (sumcheckStepLogic (κ:=κ) (L:=L) (K:=K) (P:=P) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l)
      (aOStmtIn:=aOStmtIn) i).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := sumcheckStepLogic (κ:=κ) (L:=L) (K:=K) (P:=P) (ℓ:=ℓ)
    (ℓ':=ℓ') (h_l:=h_l) (aOStmtIn:=aOStmtIn) i
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
    oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2
  simp only [sumcheckStepLogic, strictSumcheckRoundRelation, strictSumcheckRoundRelationProp,
    masterStrictKStateProp, Set.mem_setOf_eq] at h_relIn
  obtain ⟨_h_trivial, h_wit_struct_In, h_sumcheck_cons, h_oStmtIn_compat⟩ := h_relIn
  -- Fact 1: Verifier check passes
  have h_VCheck_passed : step.verifierCheck stmtIn transcript := by
    simp only [sumcheckStepLogic, step, sumcheckVerifierCheck, transcript,
      FullTranscript.mk2, sumcheckProverComputeMsg]
    rw [h_sumcheck_cons]
    exact getSumcheckRoundPoly_sum_eq (𝓑 := boolEmbedding L) (i := i) (h := witIn.H)
  have hStmtOut_eq : proverStmtOut = verifierStmtOut := rfl
  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.2
      = OracleVerifier.mkVerifierOStmtOut step.embed step.hEq oStmtIn transcript
    simp only [step, sumcheckStepLogic]
    unfold OracleVerifier.mkVerifierOStmtOut
    funext j
    split
    · rename_i j' heq
      simp only [MessageIdx, Function.Embedding.coeFn_mk, Sum.inl.injEq] at heq
      cases heq
      rfl
    · rename_i heq
      simp only [MessageIdx, Function.Embedding.coeFn_mk, reduceCtorEq] at heq
  have h_verifierOStmtOut_eq : verifierOStmtOut = oStmtIn := by
    rw [← hOStmtOut_eq]
    simp only [proverOStmtOut, proverOutput, step, sumcheckStepLogic]
  have hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    simp only [step, sumcheckStepLogic, strictSumcheckRoundRelation,
      strictSumcheckRoundRelationProp, masterStrictKStateProp, Set.mem_setOf_eq]
    rw [h_verifierOStmtOut_eq]
    refine ⟨trivial, ?_, ?_, ?_⟩
    · -- witnessStructuralInvariant at i.succ
      show witnessStructuralInvariant κ L K P ℓ ℓ' h_l verifierStmtOut proverWitOut
      unfold witnessStructuralInvariant
      dsimp only [proverWitOut, proverOutput, step, sumcheckStepLogic, verifierStmtOut,
        sumcheckVerifierStmtOut, sumcheckProverWitOut, transcript,
        FullTranscript.mk2, sumcheckProverComputeMsg]
      rw [show witIn.H = projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
          (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
          (ctx := stmtIn.ctx) (t := witIn.t') (i := i.castSucc)
          (challenges := stmtIn.challenges) from Subtype.ext h_wit_struct_In]
      exact projectToMidSumcheckPolyWithParam_succ_ringswitching κ L K P ℓ ℓ' h_l
        stmtIn.ctx witIn.t' i stmtIn.challenges (challenges ⟨1, rfl⟩)
    · -- sumcheckConsistencyProp at i.succ
      dsimp only [verifierStmtOut, proverWitOut, proverOutput, step, sumcheckStepLogic,
        sumcheckVerifierStmtOut, sumcheckProverWitOut, transcript,
        FullTranscript.mk2, sumcheckProverComputeMsg]
      show Sumcheck.Structured.sumcheckConsistencyProp (boolDomain L _) _ _
      unfold Sumcheck.Structured.sumcheckConsistencyProp
      exact projectToNextSumcheckPoly_sum_eq (L := L) (𝓑 := boolEmbedding L) (ℓ := ℓ')
        (i := i) (Hᵢ := witIn.H) (rᵢ := challenges ⟨1, rfl⟩)
    · -- initialCompatibility (t' unchanged)
      exact h_oStmtIn_compat
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

theorem iteratedSumcheckOracleReduction_perfectCompleteness (i : Fin ℓ')
    (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecSumcheckRound L)
      (relIn := strictSumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := strictSumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (oracleReduction := iteratedSumcheckOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn i)
      (init := init)
      (impl := impl) := by
  classical
  -- Step 1: Unroll the 2-message reduction to convert from probability to logic
  rw [OracleReduction.unroll_2_message_reduction_perfectCompleteness (oSpec := []ₒ)
    (pSpec := pSpecSumcheckRound L) (init := init) (impl := impl)
    (hInit := hInit) (hDir0 := by rfl) (hDir1 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image,
      IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- Step 2: Convert probability 1 to universal quantification over support
  rw [probEvent_eq_one_iff]
  -- Step 3: Unfold protocol definitions
  dsimp only [iteratedSumcheckOracleReduction, iteratedSumcheckOracleProver,
    iteratedSumcheckOracleVerifier, OracleVerifier.toVerifier, FullTranscript.mk2]
  let step := (sumcheckStepLogic (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (aOStmtIn := aOStmtIn)) (i := i)
  let strongly_complete : step.IsStronglyComplete := sumcheckStep_is_logic_complete (κ := κ)
    (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) (i := i)
  -- Step 4: Split into safety and correctness goals
  refine ⟨?_, ?_⟩
  -- GOAL 1: SAFETY - Prove the verifier never crashes ([⊥|...] = 0)
  · simp only [probFailure_bind_eq_zero_iff]
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
    intro h_prover_final_output h_prover_final_output_support
    conv =>
      simp only [guard_eq]
      enter [2];
      simp only [bind_pure_comp, NeverFail.probFailure_eq_zero, implies_true]
    rw [and_true]
    erw [OptionT.probFailure_liftComp_of_OracleComp_Option
      (superSpec := []ₒ + [(pSpecSumcheckRound L).Challenge]ₒ)]
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
        (msg1 := (FullTranscript.mk2 (sumcheckProverComputeMsg L ℓ' i witIn) r_i').challenges
          ⟨1, rfl⟩))
      with h_V_check_def
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecSumcheckRound L).dir 0 ≠ Direction.V_to_P := by
            simp only [ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue, Matrix.cons_val_zero,
              Direction.not_P_to_V_eq_V_to_P]
          exfalso
          exact hj_ne hj
        | 1 => exact r_i'
      )
    have h_inputState1 : inputState.1 = sumcheckProverComputeMsg L ℓ' i witIn := by
      rw [hInputState_mem_support]
    have h_V_check_is_true : V_check := by
      rw [h_V_check_def, h_inputState1]; exact h_V_check
    split at h_vStmtOut_mem_support
    · simp only [support_pure, Set.mem_singleton_iff,
        Fin.isValue, exists_eq_left, exists_prop, exists_eq_left',
        OptionT.support_OptionT_pure_run] at h_vStmtOut_mem_support
      rw [h_vStmtOut_mem_support]
      simp only [Fin.isValue, OptionT.run_pure, probOutput_none_pure_some_eq_zero]
    · rename_i h_neg
      exact absurd (h_V_check_def ▸ h_V_check_is_true)
        (by subst hInputState_mem_support; exact h_neg)
  · -- GOAL 2: CORRECTNESS - Prove all outputs in support satisfy the relation
    intro x hx_mem_support
    rcases x with ⟨⟨prvStmtOut, prvOStmtOut⟩, ⟨verStmtOut, verOStmtOut⟩, witOut⟩
    simp only
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
    obtain ⟨r1, ⟨_h_r1_mem_challenge_support, h_trace_support⟩⟩ := hx_mem_support
    rcases h_trace_support with ⟨prvOut_eq, h_verOut_mem_support⟩
    conv at h_verOut_mem_support =>
      erw [simulateQ_bind]
      erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      erw [_root_.bind_pure_simulateQ_comp]
      simp only [Matrix.cons_val_zero, guard_eq]
      erw [simulateQ_bind]
      simp only [show OptionT.pure (m := (OracleComp []ₒ)) = pure by rfl]
      erw [simulateQ_ite]
      simp only [Fin.isValue, Message, Matrix.cons_val_zero, id_eq, MessageIdx, support_ite,
        toPFunctor_emptySpec, Function.comp_apply, simulateQ_pure, Set.mem_iUnion,
        exists_prop]
      simp only [OptionT.simulateQ_failure]
      erw [_root_.simulateQ_pure]
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk2
        (msg0 := sumcheckProverComputeMsg L ℓ' i witIn)
        (msg1 := r1)) with h_V_check_def
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecSumcheckRound L).dir 0 ≠ Direction.V_to_P := by
            simp only [ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue, Matrix.cons_val_zero,
              Direction.not_P_to_V_eq_V_to_P]
          exfalso
          exact hj_ne hj
        | 1 => exact r1
      )
    have h_V_check_is_true : V_check := h_V_check
    simp only [FullTranscript.mk2, FullTranscript.messages, FullTranscript.challenges,
      OracleInterface.answer, OracleInterface.toOC, OracleInterface.instDefault, ReaderT.run,
      read, readThe, MonadReaderOf.read, Fin.isValue] at h_verOut_mem_support
    erw [if_pos h_V_check_is_true] at h_verOut_mem_support
    simp only [Fin.isValue, pure_bind] at h_verOut_mem_support
    erw [OptionT.simulateQ_pure, liftM_pure] at h_verOut_mem_support
    simp only [Fin.isValue, support_pure, Set.mem_singleton_iff, Option.some.injEq,
      Prod.mk.injEq] at h_verOut_mem_support
    obtain ⟨h_prvOut_fn, h_prvOut_eq, h_verOut_eq⟩ := h_verOut_mem_support
    subst h_prvOut_fn
    simp only [Fin.isValue] at h_prvOut_eq
    erw [_root_.map_pure] at h_verOut_eq
    erw [support_liftM_optionT] at h_verOut_eq
    erw [OptionT.support_OptionT_pure] at h_verOut_eq
    simp only [Fin.isValue, Set.mem_singleton_iff, Prod.mk.injEq] at h_verOut_eq
    obtain ⟨h_verStmtOut_eq, h_verOStmtOut_eq⟩ := h_verOut_eq
    rw [Prod.mk.injEq, Prod.mk.injEq] at h_prvOut_eq
    obtain ⟨⟨prvStmtOut_eq, prvOStmtOut_eq⟩, prvWitOut_eq⟩ := h_prvOut_eq
    constructor
    · rw [prvWitOut_eq, h_verStmtOut_eq, h_verOStmtOut_eq]
      exact h_rel
    · constructor
      · rw [h_verStmtOut_eq, prvStmtOut_eq]; rfl
      · rw [h_verOStmtOut_eq, prvOStmtOut_eq]
        exact h_agree.2

open scoped NNReal

-- Lifted to `Sumcheck.Structured.roundKnowledgeError` (degree-neutral). Binius ring-switching is
-- the degree-2 case, so this Binius-local abbrev pins `d := 2`.
abbrev roundKnowledgeError (L : Type) [Fintype L] (ℓ : ℕ) (i : Fin ℓ) : NNReal :=
  Sumcheck.Structured.roundKnowledgeError L ℓ i 2

/-- Witness type at each message index for the iterated sumcheck step
  (counterpart of BBF `foldWitMid`, ported from HEAD `iteratedSumcheckWitMid`).
  At m=0,1 we have the input-round witness; at m=2 we have the output-round witness so that
  `extractOut` can be the identity. The reprojection back to the input witness happens in
  `extractMid` at m=1. -/
def iteratedSumcheckWitMid (i : Fin ℓ') : Fin (2 + 1) → Type :=
  fun m => match m with
  | ⟨0, _⟩ => SumcheckWitness L ℓ' i.castSucc
  | ⟨1, _⟩ => SumcheckWitness L ℓ' i.castSucc
  | ⟨2, _⟩ => SumcheckWitness L ℓ' i.succ

noncomputable def iteratedSumcheckRbrExtractor (i : Fin ℓ') :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ P) i.castSucc) × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L)
    (WitMid := iteratedSumcheckWitMid (L := L) (ℓ' := ℓ') (i := i)) where
  eqIn := rfl
  extractMid := fun m ⟨stmtIn, _⟩ _tr witMidSucc =>
    match m with
    | ⟨0, _⟩ => witMidSucc  -- WitMid 1 → WitMid 0, both SumcheckWitness i.castSucc
    | ⟨1, _⟩ =>
      -- WitMid 2 → WitMid 1: extract backward from the output witness using input challenges
      {
        t' := witMidSucc.t',
        H := projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
          (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
          (ctx := stmtIn.ctx) (t := witMidSucc.t')
          (i := i.castSucc) (challenges := stmtIn.challenges)
      }
  extractOut := fun _stmtIn _fullTranscript witOut => witOut

/-- KState for the iterated sumcheck step, ported from HEAD `iteratedSumcheckKStateProp`
(Profile frame, `𝓑 := boolEmbedding L`; the built-in `sumcheckConsistencyProp` conjunct of the
flat `masterKStateProp` carries the round-consistency check):
- m=0: same as relIn (`masterKStateProp` at `i.castSucc`, `localChecks := True`).
- m=1: after P sends hᵢ(X), before V sends r'ᵢ (`explicitVCheck ∧ localizedRoundPolyCheck`).
- m=2: after V sends r'ᵢ — OUTPUT state (`masterKStateProp` at `i.succ` with `stmtOut`,
  `witMid : SumcheckWitness i.succ`, `localChecks := explicitVCheck`). -/
def iteratedSumcheckKStateProp (i : Fin ℓ') (m : Fin (2 + 1))
    (tr : Transcript m (pSpecSumcheckRound L))
    (stmtMid : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (witMid : iteratedSumcheckWitMid (L := L) (ℓ' := ℓ') (i := i) m)
    (oStmtMid : ∀ j, aOStmtIn.OStmtIn j) :
    Prop :=
  match m with
  | ⟨0, _⟩ => -- Same as relIn
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l
      aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmtMid) (oStmt := oStmtMid) (wit := witMid)
      (localChecks := True)
  | ⟨1, _⟩ => -- After P sends hᵢ(X), before V sends r'ᵢ
    let h_star : ↥L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ' (boolEmbedding L) (i := i) (h := witMid.H)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmtMid) (oStmt := oStmtMid) (wit := witMid)
      (localChecks :=
        let explicitVCheck :=
          h_i.val.eval (boolEmbedding L 0) + h_i.val.eval (boolEmbedding L 1) = stmtMid.sumcheck_target
        let localizedRoundPolyCheck := h_i = h_star
        explicitVCheck ∧ localizedRoundPolyCheck
      )
  | ⟨2, _⟩ => -- After V sends r'ᵢ: use OUTPUT state (witMid is already SumcheckWitness i.succ)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    let r_i' : L := tr.challenges ⟨1, rfl⟩
    let stmtOut : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ :=
      sumcheckVerifierStmtOut (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') i stmtMid h_i r_i'
    let oStmtOut := oStmtMid
    let witOut := witMid
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn
      (stmtIdx := i.succ)
      (stmt := stmtOut) (oStmt := oStmtOut) (wit := witOut)
      (localChecks :=
        h_i.val.eval (boolEmbedding L 0) + h_i.val.eval (boolEmbedding L 1) = stmtMid.sumcheck_target
      )

/-- Knowledge state function (KState) for single round -/
def iteratedSumcheckKnowledgeStateFunction (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn i).KnowledgeStateFunction init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (extractor := iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i) where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    iteratedSumcheckKStateProp κ L K P ℓ ℓ' h_l
      (i := i) (m := m) (tr := tr) (stmtMid := stmt) (witMid := witMid) (oStmtMid := oStmt)
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witMid => by
    simp only [iteratedSumcheckKStateProp, sumcheckRoundRelation, sumcheckRoundRelationProp,
      Set.mem_setOf_eq, Fin.val_castSucc, cast_eq]
    rfl
  toFun_next := fun m hDir ⟨stmtMid, oStmtMid⟩ tr msg witMid => by
    -- For pSpecSumcheckRound, the only P_to_V message is at index 0.
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => simp only [ne_eq, reduceCtorEq, not_false_eq_true, Matrix.cons_val_succ,
        Matrix.cons_val_fin_one, Direction.not_V_to_P_eq_P_to_V] at hDir
    subst h_m_eq_0
    intro h_kState_round1
    unfold iteratedSumcheckKStateProp at h_kState_round1 ⊢
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Nat.reduceAdd, Fin.mk_one,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod] at h_kState_round1
    simp only [Fin.castSucc_zero]
    -- At round 1: masterKStateProp with (explicitVCheck ∧ localizedRoundPolyCheck).
    -- At round 0: masterKStateProp with `localChecks := True`.
    obtain ⟨⟨h_explicit, h_localized⟩, h_core⟩ := h_kState_round1
    -- The extractMid at m=0 is the identity, so witMid is unchanged.
    refine ⟨trivial, ?_⟩
    exact h_core
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
    -- h_relOut: ∃ stmtOut oStmtOut, verifier outputs (stmtOut, oStmtOut) with prob > 0
    --   and ((stmtOut, oStmtOut), witOut) ∈ relOut
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, Prod.exists] at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩
    have h_output_mem_V_run_support' :
        some (stmtOut, oStmtOut) ∈
          support (do
            let s ← init
            Prod.fst <$>
              (simulateQ impl
                (Verifier.run (stmtIn, oStmtIn) tr
                  (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn i).toVerifier).run s)) := by
      exact (OptionT.mem_support_iff
        (mx := OptionT.mk (do
          let s ← init
          Prod.fst <$>
            (simulateQ impl
              (Verifier.run (stmtIn, oStmtIn) tr
                (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn i).toVerifier).run s)))
        (x := (stmtOut, oStmtOut))).1 h_output_mem_V_run_support
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output_mem_V_run_support'
    rcases h_output_mem_V_run_support' with ⟨s, hs_init, h_output_mem_V_run_support⟩
    conv at h_output_mem_V_run_support =>
      simp only [Verifier.run, OracleVerifier.toVerifier]
      simp only [iteratedSumcheckOracleVerifier]
      simp only [support_bind, Set.mem_iUnion]
      dsimp only [StateT.run]
      simp only [simulateQ_bind]
      unfold OracleInterface.answer
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
      simp only [Fin.isValue, FullTranscript.mk1_eq_snoc, Function.comp_apply]
    erw [support_bind] at h_output_mem_V_run_support
    let step := (sumcheckStepLogic (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (aOStmtIn := aOStmtIn)) (i := i)
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk2 (msg0 := _) (msg1 := _)) with h_V_check_def
    by_cases h_V_check : V_check
    · simp only [Fin.isValue, Matrix.cons_val_zero, id_eq, h_V_check, ↓reduceIte, OptionT.run_pure,
        simulateQ_pure, Function.comp_apply, Set.mem_iUnion, exists_prop, Prod.exists,
        exists_and_right] at h_output_mem_V_run_support
      erw [simulateQ_bind] at h_output_mem_V_run_support
      erw [simulateQ_pure] at h_output_mem_V_run_support
      simp only [Fin.isValue, Function.comp_apply,
        pure_bind] at h_output_mem_V_run_support
      rw [if_pos (h_V_check_def ▸ h_V_check)] at h_output_mem_V_run_support
      erw [_root_.map_pure] at h_output_mem_V_run_support
      erw [simulateQ_pure] at h_output_mem_V_run_support
      (try erw [simulateQ_pure] at h_output_mem_V_run_support)
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Fin.isValue, Set.mem_singleton_iff, Prod.mk.injEq, exists_eq_right,
        exists_eq_left] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Fin.isValue, Set.mem_singleton_iff, Option.some.injEq,
        Prod.mk.injEq] at h_output_mem_V_run_support
      rcases h_output_mem_V_run_support with ⟨h_stmtOut_eq, h_oStmtOut_eq⟩
      simp only [Fin.reduceLast, Fin.isValue] -- simp the `match`
      dsimp only [sumcheckRoundRelation, sumcheckRoundRelationProp, masterKStateProp] at h_relOut
      simp only [Fin.val_succ, Set.mem_setOf_eq] at h_relOut
      dsimp only [iteratedSumcheckKStateProp]
      set h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨(0 : Fin 2), rfl⟩ with h_i_def
      set r_i' : L := tr.challenges ⟨(1 : Fin 2), rfl⟩ with h_r_i_def
      have h_oStmtOut_eq_oStmtIn : oStmtOut = oStmtIn := by
        rw [h_oStmtOut_eq]
        funext j
        simp only [MessageIdx, Function.Embedding.coeFn_mk, Sum.inl.injEq,
          OracleVerifier.mkVerifierOStmtOut_inl, cast_eq]
      rw [h_oStmtOut_eq_oStmtIn] at h_relOut
      dsimp only [sumcheckVerifierStmtOut]
      have h_stmtOut_sumcheck_target_eq : stmtOut.sumcheck_target = (Polynomial.eval r_i' ↑h_i)
        := by rw [h_stmtOut_eq]; rfl
      dsimp only [masterKStateProp]
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- localChecks: explicitVCheck (from the verifier check that passed)
        exact h_V_check
      · -- witnessStructuralInvariant at i.succ
        have h_wit_struct : witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmtOut witOut :=
          h_relOut.2.1
        unfold witnessStructuralInvariant at h_wit_struct ⊢
        rw [h_stmtOut_eq] at h_wit_struct
        exact h_wit_struct
      · -- sumcheckConsistencyProp at i.succ
        have h_cons := h_relOut.2.2.1
        rw [h_stmtOut_sumcheck_target_eq] at h_cons
        exact h_cons
      · -- initialCompatibility
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
      obtain ⟨a, b, hab, hsome⟩ := h_output_mem_V_run_support
      rw [OracleComp.failure_def] at hab
      unfold OptionT.fail at hab
      erw [simulateQ_pure] at hab
      rw [pure_bind] at hab
      erw [simulateQ_pure] at hab
      rw [show ((pure none : StateT σ ProbComp (Option _)) s) = pure (none, s) from rfl] at hab
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hab
      obtain ⟨ha, hb⟩ := hab
      subst ha
      erw [support_pure] at hsome
      simp only [Set.mem_singleton_iff, reduceCtorEq] at hsome

/-- A finite integral domain `L` (our `CommRing L` + `IsDomain L` + `Fintype L`) is a `Field`.
Needed to invoke the BBF `[Field L]`-keyed `badSumcheckEventProp` /
`probability_bound_badSumcheckEventProp`. Its `toCommRing` is definitionally the ambient `CommRing L`,
so `L⦃≤ 2⦄[X]` (elaborated via the `CommRing`-`Semiring` path) is unchanged. -/
noncomputable local instance instFieldOfIsDomainSumcheckPhase [IsDomain L] : Field L :=
  Fintype.fieldOfDomain L

/-- Extraction failure implies a witness-dependent bad sumcheck event (no folding here).
  The extracted `witMid` also carries oracle compatibility at the same `oStmt`.
  Ported from HEAD `iteratedSumcheck_rbrExtractionFailureEvent_imply_badSumcheck`
  (`𝓑 := boolEmbedding L`, `β → P`); template `batching_rbrExtractionFailureEvent_imply_badBatchingEvent`. -/
lemma iteratedSumcheck_rbrExtractionFailureEvent_imply_badSumcheck [IsDomain L] (i : Fin ℓ')
    (stmtOStmtIn : (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
      × (∀ j, aOStmtIn.OStmtIn j))
    (h_i : (pSpecSumcheckRound L).Message ⟨0, rfl⟩) (r_i' : L)
    (doomEscape : rbrExtractionFailureEvent
      (kSF := iteratedSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn
        (init := init) (impl := impl) i)
      (extractor := iteratedSumcheckRbrExtractor.{0} κ L K P ℓ ℓ' h_l aOStmtIn i)
      (i := ⟨1, rfl⟩) (stmtIn := stmtOStmtIn) (transcript := FullTranscript.mk1 h_i)
      (challenge := r_i')) :
    ∃ witMid : SumcheckWitness L ℓ' i.succ,
      aOStmtIn.initialCompatibility (witMid.t', stmtOStmtIn.2) ∧
      let witBefore : SumcheckWitness L ℓ' i.castSucc :=
        (iteratedSumcheckRbrExtractor.{0} κ L K P ℓ ℓ' h_l aOStmtIn i).extractMid
          (m := 1) stmtOStmtIn (FullTranscript.mk2 h_i r_i') witMid
      let h_star : L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ' (boolEmbedding L) (i := i) (h := witBefore.H)
      badSumcheckEventProp r_i' h_i h_star := by
  classical
  unfold rbrExtractionFailureEvent at doomEscape
  rcases doomEscape with ⟨witMid, h_kState_before_false, h_kState_after_true⟩
  simp only [iteratedSumcheckKnowledgeStateFunction] at h_kState_before_false h_kState_after_true
  unfold iteratedSumcheckKStateProp at h_kState_before_false h_kState_after_true
  simp only [Fin.isValue, Fin.castSucc_one, Fin.succ_one_eq_two, Nat.reduceAdd]
    at h_kState_before_false h_kState_after_true
  simp only [Transcript.concat, sumcheckVerifierStmtOut]
    at h_kState_before_false h_kState_after_true
  unfold masterKStateProp witnessStructuralInvariant at h_kState_before_false h_kState_after_true
  simp only [iteratedSumcheckRbrExtractor, Fin.isValue]
    at h_kState_before_false h_kState_after_true
  -- After-state (m=2) truths.
  have h_explicit_after :
      h_i.val.eval (boolEmbedding L 0) + h_i.val.eval (boolEmbedding L 1)
        = stmtOStmtIn.1.sumcheck_target := h_kState_after_true.1
  have h_sumcheck_after :
      sumcheckConsistencyProp (boolDomain L _) (Polynomial.eval r_i' h_i.val) witMid.H
        := h_kState_after_true.2.2.1
  have h_wit_struct_after :
      witMid.H.val = (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
        (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
        (ctx := stmtOStmtIn.1.ctx) (t := witMid.t')
        (i := i.succ) (challenges := Fin.snoc stmtOStmtIn.1.challenges r_i')).val
        := h_kState_after_true.2.1
  have h_init_compat : aOStmtIn.initialCompatibility (witMid.t', stmtOStmtIn.2)
    := h_kState_after_true.2.2.2
  -- The extracted before-witness at m=1.
  let H_before : L⦃≤ 2⦄[X Fin (ℓ' - i.castSucc)] :=
    projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
      (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
      (ctx := stmtOStmtIn.1.ctx) (t := witMid.t')
      (i := i.castSucc) (challenges := stmtOStmtIn.1.challenges)
  let h_star_extracted : L⦃≤ 2⦄[X] :=
    Binius.BinaryBasefold.getSumcheckRoundPoly ℓ' (boolEmbedding L) (i := i) (h := H_before)
  have h_eval_eq_extracted : Polynomial.eval r_i' h_i.val
      = Polynomial.eval r_i' h_star_extracted.val := by
    unfold Sumcheck.Structured.sumcheckConsistencyProp at h_sumcheck_after
    -- Advance the mid-poly by one round (fix `X₀ := r_i'`) — the ring-switching `WithParam` variant.
    have h_next :=
      projectToMidSumcheckPolyWithParam_succ_ringswitching (κ := κ) (L := L) (K := K) (P := P)
        (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (ctx := stmtOStmtIn.1.ctx) (t := witMid.t')
        (i := i) (challenges := stmtOStmtIn.1.challenges) (r_i' := r_i')
    -- Rewrite `witMid.H` as the next projection of `H_before`.
    rw [h_wit_struct_after] at h_sumcheck_after
    rw [← h_next] at h_sumcheck_after
    -- `∑ over cube = eval of round poly` for `H_before` (`(boolDomain L k).cube` is defeq to
    -- `(univ.map (boolEmbedding L)) ^ᶠ k`, so `.trans` unifies the two sum forms).
    have h_proj_sum :=
      Binius.BinaryBasefold.projectToNextSumcheckPoly_sum_eq (L := L) (𝓑 := boolEmbedding L)
        (ℓ := ℓ') (i := i) (Hᵢ := H_before) (rᵢ := r_i')
    exact h_sumcheck_after.trans h_proj_sum.symm
  have h_hi_ne_extracted : h_i ≠ h_star_extracted := by
    intro h_eq
    apply h_kState_before_false
    refine ⟨⟨h_explicit_after, ?_⟩, ?_, ?_, ?_⟩
    · dsimp only [h_star_extracted, H_before] at h_eq ⊢
      exact h_eq
    · -- witnessStructuralInvariant at m=1 collapses to `True` (input witness is the projection).
      trivial
    · -- sumcheckConsistencyProp of the before-witness follows from `getSumcheckRoundPoly_sum_eq`.
      show sumcheckConsistencyProp (boolDomain L _) stmtOStmtIn.1.sumcheck_target _
      unfold Sumcheck.Structured.sumcheckConsistencyProp
      -- goal: sumcheck_target = ∑ over cube of H_before
      have h_sum_eq :=
        Binius.BinaryBasefold.getSumcheckRoundPoly_sum_eq (L := L) (𝓑 := boolEmbedding L)
          (ℓ := ℓ') (i := i) (h := H_before)
      rw [h_eq] at h_explicit_after
      rw [← h_explicit_after]
      dsimp only [h_star_extracted, H_before] at h_sum_eq ⊢
      exact h_sum_eq
    · -- initialCompatibility is preserved by extractMid(m=1) since t' is unchanged.
      exact h_init_compat
  have h_bad_extracted : badSumcheckEventProp r_i' h_i h_star_extracted :=
    ⟨h_hi_ne_extracted, h_eval_eq_extracted⟩
  refine ⟨witMid, h_init_compat, ?_⟩
  dsimp only [h_star_extracted, H_before, iteratedSumcheckRbrExtractor]
  exact h_bad_extracted

/-- Per-transcript bound: for prover message `h_i`, the probability (over verifier challenge `y`)
  that extraction fails is at most `roundKnowledgeError L ℓ' i` (`2/|L|`).
  Ported from HEAD `iteratedSumcheck_doom_escape_probability_bound`; template
  `batching_doom_escape_probability_bound`. -/
lemma iteratedSumcheck_doom_escape_probability_bound [IsDomain L] (i : Fin ℓ')
    (stmtOStmtIn : (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
      × (∀ j, aOStmtIn.OStmtIn j))
    (h_i : (pSpecSumcheckRound L).Message ⟨0, rfl⟩) :
    Pr_{ let y ← $ᵖ L }[
      rbrExtractionFailureEvent
        (kSF := iteratedSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn
          (init := init) (impl := impl) i)
        (extractor := iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i)
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 h_i) y ] ≤
      roundKnowledgeError L ℓ' i := by
  classical
  let compatPred : Sumcheck.Structured.MultilinearPoly L ℓ' → Prop := fun t =>
    aOStmtIn.initialCompatibility (t, stmtOStmtIn.2)
  by_cases hCompat : ∃ t : Sumcheck.Structured.MultilinearPoly L ℓ', compatPred t
  · rcases hCompat with ⟨t_fixed, h_t_fixed_compat⟩
    let H_fixed : L⦃≤ 2⦄[X Fin (ℓ' - i.castSucc)] :=
      projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
        (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
        (ctx := stmtOStmtIn.1.ctx) (t := t_fixed)
        (i := i.castSucc) (challenges := stmtOStmtIn.1.challenges)
    let h_star_fixed : L⦃≤ 2⦄[X] :=
      getSumcheckRoundPoly ℓ' (boolEmbedding L) (i := i) (h := H_fixed)
    have h_prob_mono := Probability.Pr_le_Pr_of_implies (D := $ᵖ L)
      (f := fun y => rbrExtractionFailureEvent
        (kSF := iteratedSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn
          (init := init) (impl := impl) i)
        (extractor := iteratedSumcheckRbrExtractor.{0} κ L K P ℓ ℓ' h_l aOStmtIn i)
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 h_i) y)
      (g := fun y => badSumcheckEventProp y h_i h_star_fixed)
      (h_imp := by
        intro y h_doom
        obtain ⟨witMid, h_mid_compat, h_bad_extracted⟩ :=
          iteratedSumcheck_rbrExtractionFailureEvent_imply_badSumcheck
            (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
            (aOStmtIn := aOStmtIn) (impl := impl) (init := init)
            (i := i) (stmtOStmtIn := stmtOStmtIn) (h_i := h_i) (r_i' := y)
            (doomEscape := h_doom)
        have h_t_eq : witMid.t' = t_fixed :=
          aOStmtIn.initialCompatibility_unique stmtOStmtIn.2 witMid.t' t_fixed
            h_mid_compat h_t_fixed_compat
        dsimp only [h_star_fixed, H_fixed]
        rw [← h_t_eq]
        dsimp only [iteratedSumcheckRbrExtractor] at h_bad_extracted ⊢
        exact h_bad_extracted)
    apply le_trans h_prob_mono
    have h_sz := probability_bound_badSumcheckEventProp (h_i := h_i) (h_star := h_star_fixed)
    conv_rhs =>
      simp only [roundKnowledgeError, Sumcheck.Structured.roundKnowledgeError]
      rw [ENNReal.coe_div (hr := by simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero,
        not_false_eq_true])]
      simp only [ENNReal.coe_ofNat, ENNReal.coe_natCast]
    exact h_sz
  · have h_prob_mono_false := Probability.Pr_le_Pr_of_implies (D := $ᵖ L)
      (f := fun y => rbrExtractionFailureEvent
        (kSF := iteratedSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn
          (init := init) (impl := impl) i)
        (extractor := iteratedSumcheckRbrExtractor.{0} κ L K P ℓ ℓ' h_l aOStmtIn i)
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 h_i) y)
      (g := fun _ => False)
      (h_imp := by
        intro y h_doom
        obtain ⟨witMid, h_mid_compat, _h_bad_extracted⟩ :=
          iteratedSumcheck_rbrExtractionFailureEvent_imply_badSumcheck
            (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
            (aOStmtIn := aOStmtIn) (impl := impl) (init := init)
            (i := i) (stmtOStmtIn := stmtOStmtIn) (h_i := h_i) (r_i' := y)
            (doomEscape := h_doom)
        exact (hCompat ⟨witMid.t', h_mid_compat⟩).elim)
    refine le_trans h_prob_mono_false ?_
    simp only [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.bind_const, PMF.pure_apply,
      eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte, _root_.zero_le]

/-- RBR knowledge soundness for a single round oracle verifier -/
theorem iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness [IsDomain L] (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn i).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (fun j => roundKnowledgeError L ℓ' i) := by
  classical
  -- One-liner via the reusable round-reducer (same lemma as the Binius fold step): reduce r.b.r.
  -- knowledge soundness to the per-message sumcheck doom bound.
  exact OracleReduction.rbrKnowledgeSoundness_of_2msg_PtoV_uniformChallenge
    (WitMid := iteratedSumcheckWitMid (L := L) (ℓ' := ℓ') (i := i))
    (rbrKnowledgeError := fun _ => roundKnowledgeError L ℓ' i)
    (kSF := iteratedSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn i)
    (extractor := iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i)
    (hDir0 := rfl) (hDir1 := rfl)
    (hbound := fun stmtOStmtIn msg₀ => iteratedSumcheck_doom_escape_probability_bound
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn)
      (i := i) (stmtOStmtIn := stmtOStmtIn) (h_i := msg₀))

end IteratedSumcheckStep

section FinalSumcheckStep
/-!
## Final Sumcheck Step
-/

-- `pSpecFinalSumcheck L` has a single `P_to_V` message and **no** challenges, so its challenge
-- oracle spec is empty. Pin the empty-spec `Fintype`/`Inhabited`/`IsUniformSpec` instances that the
-- 1-message-completeness unrolling requires (analogous to the per-round challenge instances above).
instance instFintypePSpecFinalSumcheckChallenge :
    [(pSpecFinalSumcheck L).Challenge]ₒ.Fintype := by
  refine { fintypeB := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  match i with
  | ⟨0, _⟩ => simp only [pSpecFinalSumcheck, Matrix.cons_val_fin_one, reduceCtorEq] at hi

instance instInhabitedPSpecFinalSumcheckChallenge :
    [(pSpecFinalSumcheck L).Challenge]ₒ.Inhabited := by
  refine { inhabitedB := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  match i with
  | ⟨0, _⟩ => simp only [pSpecFinalSumcheck, Matrix.cons_val_fin_one, reduceCtorEq] at hi

noncomputable instance instIsUniformSpecPSpecFinalSumcheckChallenge :
    IsUniformSpec [(pSpecFinalSumcheck L).Challenge]ₒ := IsUniformSpec.ofFintypeInhabited _

/-! ## Pure Logic Functions (`ReductionLogicStep` for the final sumcheck step) -/

/-- Pure verifier check: `s_{ℓ'} = eqTilde_eval · s'`. -/
@[reducible]
def finalSumcheckVerifierCheck
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (s' : L) : Prop :=
  let eq_tilde_eval : L := compute_final_eq_value κ L K P ℓ ℓ' h_l
    stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
  stmtIn.sumcheck_target = eq_tilde_eval * s'

/-- Pure verifier output. -/
@[reducible]
def finalSumcheckVerifierStmtOut
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (s' : L) : MLPEvalStatement L ℓ' := {
      t_eval_point := stmtIn.challenges
      original_claim := s'
    }

/-- Pure prover message computation: `s' := t'(challenges)`. -/
@[reducible]
def finalSumcheckProverComputeMsg
    (witIn : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ')) : L :=
  witIn.t'.val.eval stmtIn.challenges

/-- Pure prover output witness. -/
@[reducible]
def finalSumcheckProverWitOut (witIn : SumcheckWitness L ℓ' (Fin.last ℓ')) : WitMLP L ℓ' :=
  { t := witIn.t' }

/-- The Logic Instance for the final sumcheck step (a 1-message protocol: P sends the constant s'). -/
def finalSumcheckStepLogic :
    Binius.BinaryBasefold.ReductionLogicStep
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
      (SumcheckWitness L ℓ' (Fin.last ℓ'))
      (aOStmtIn.OStmtIn)
      (aOStmtIn.OStmtIn)
      (MLPEvalStatement L ℓ')
      (WitMLP L ℓ')
      (pSpecFinalSumcheck L) where
  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ strictSumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ')
  completeness_relOut := fun ((stmtOut, oStmtOut), witOut) =>
    ((stmtOut, oStmtOut), witOut) ∈ aOStmtIn.toStrictRelInput
  verifierCheck := fun stmtIn transcript =>
    finalSumcheckVerifierCheck κ L K P ℓ ℓ' h_l stmtIn (transcript.messages ⟨0, rfl⟩)
  verifierOut := fun stmtIn transcript =>
    finalSumcheckVerifierStmtOut κ L K P ℓ ℓ' stmtIn (transcript.messages ⟨0, rfl⟩)
  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun _ => rfl
  honestProverTranscript := fun stmtIn witIn _oStmtIn _chal =>
    let s' : L := finalSumcheckProverComputeMsg κ L K P ℓ ℓ' witIn stmtIn
    FullTranscript.mk1 s'
  proverOut := fun stmtIn witIn oStmtIn transcript =>
    let s' : L := transcript.messages ⟨0, rfl⟩
    let stmtOut := finalSumcheckVerifierStmtOut κ L K P ℓ ℓ' stmtIn s'
    let witOut := finalSumcheckProverWitOut (L := L) (ℓ' := ℓ') witIn
    ((stmtOut, oStmtIn), witOut)

/-! ## Helper Lemmas for Strong Completeness -/

omit [Fintype L] [DecidableEq L] [SampleableType L] [NeZero ℓ'] in
/-- At `Fin.last ℓ'`, the sumcheck consistency sum is over 0 variables, so
`target = H.eval 0`. -/
lemma sumcheckConsistency_at_last_simplifies
    (target : L) (H : L⦃≤ 2⦄[X Fin (ℓ' - (Fin.last ℓ' : Fin (ℓ' + 1)))])
    (h_cons : sumcheckConsistencyProp (boolDomain L _) target H) :
    target = H.val.eval (fun _ => (0 : L)) := by
  simp only [Fin.val_last] at H h_cons ⊢
  simp only [Sumcheck.Structured.sumcheckConsistencyProp] at h_cons
  haveI : IsEmpty (Fin 0) := Fin.isEmpty
  rw [Finset.sum_eq_single (a := fun _ => 0)
    (h₀ := fun b _ hb_ne => by
      exfalso; apply hb_ne
      funext i
      simp only [tsub_self] at i
      exact i.elim0)
    (h₁ := fun h_not_mem => by
      exfalso; apply h_not_mem
      simp only [SumcheckDomain.cube, Fintype.mem_piFinset]
      intro i
      simp only [tsub_self] at i
      exact i.elim0)] at h_cons
  exact h_cons

omit [NeZero κ] [Fintype L] [DecidableEq L] [SampleableType L]
  [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- The honest prover's message equals `t'(challenges)`. -/
lemma finalSumcheck_honest_message_eq_t'_eval
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (witIn : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (oStmtIn : ∀ j, aOStmtIn.OStmtIn j)
    (challenges : (pSpecFinalSumcheck L).Challenges) :
    let step := finalSumcheckStepLogic κ L K P ℓ ℓ' h_l aOStmtIn
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    transcript.messages ⟨0, rfl⟩ = witIn.t'.val.eval stmtIn.challenges := by
  simp only [finalSumcheckStepLogic, finalSumcheckProverComputeMsg]

/-- **Main helper**: the verifier check passes in the final sumcheck step. Combines
sumcheck consistency at `Fin.last` (single evaluation), the witness structural invariant
(`H = A · t'`), the at-last projection eval, and `A_MLE.eval = compute_final_eq_value`. -/
lemma finalSumcheckStep_verifierCheck_passed [IsDomain L]
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (witIn : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (oStmtIn : ∀ j, aOStmtIn.OStmtIn j)
    (challenges : (pSpecFinalSumcheck L).Challenges)
    (h_sumcheck_cons :
      sumcheckConsistencyProp (boolDomain L _) stmtIn.sumcheck_target witIn.H)
    (h_wit_struct : witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmtIn witIn) :
    let step := finalSumcheckStepLogic κ L K P ℓ ℓ' h_l aOStmtIn
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    step.verifierCheck stmtIn transcript := by
  intro step transcript
  have h_target_eq_H_eval : stmtIn.sumcheck_target = witIn.H.val.eval (fun _ => 0) :=
    sumcheckConsistency_at_last_simplifies (L := L) (ℓ' := ℓ')
      stmtIn.sumcheck_target witIn.H h_sumcheck_cons
  have h_H_eq : witIn.H.val = (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
    (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
    (ctx := stmtIn.ctx) (t := witIn.t')
    (i := Fin.last ℓ') (challenges := stmtIn.challenges)).val := h_wit_struct
  have h_proj_eval : (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
    (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
    (ctx := stmtIn.ctx) (t := witIn.t')
    (i := Fin.last ℓ') (challenges := stmtIn.challenges)).val.eval (fun _ => 0) =
    ((RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly
      stmtIn.ctx).val.eval stmtIn.challenges * witIn.t'.val.eval stmtIn.challenges :=
      projectToMidSumcheckPolyWithParam_at_last_eval_ringswitching (κ := κ) (L := L) (K := K)
        (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
        stmtIn.ctx witIn.t' stmtIn.challenges (fun _ => 0)
  have h_mult_eq_eq_value : ((RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly
    stmtIn.ctx).val.eval stmtIn.challenges =
    compute_final_eq_value κ L K P ℓ ℓ' h_l stmtIn.ctx.t_eval_point stmtIn.challenges
      stmtIn.ctx.r_batching :=
      compute_A_MLE_eval_eq_final_eq_value κ L K P ℓ ℓ' h_l
        stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
  have h_msg_eq : transcript.messages ⟨0, rfl⟩ = witIn.t'.val.eval stmtIn.challenges :=
    finalSumcheck_honest_message_eq_t'_eval κ L K P ℓ ℓ' h_l aOStmtIn stmtIn witIn
      oStmtIn challenges
  simp only [step, finalSumcheckStepLogic, finalSumcheckVerifierCheck]
  rw [h_target_eq_H_eval, h_H_eq, h_proj_eval, h_mult_eq_eq_value, h_msg_eq]

/-! ## Strong Completeness Theorem -/

/-- The final sumcheck logic step is strongly complete. -/
lemma finalSumcheckStep_is_logic_complete [IsDomain L] :
    (finalSumcheckStepLogic κ L K P ℓ ℓ' h_l aOStmtIn).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := finalSumcheckStepLogic κ L K P ℓ ℓ' h_l aOStmtIn
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2
  simp only [finalSumcheckStepLogic, strictSumcheckRoundRelation,
    strictSumcheckRoundRelationProp, Set.mem_setOf_eq, masterStrictKStateProp] at h_relIn
  obtain ⟨_, h_wit_struct, h_sumcheck_cons, h_oStmtIn_compat⟩ := h_relIn
  let h_VCheck_passed : step.verifierCheck stmtIn transcript :=
    finalSumcheckStep_verifierCheck_passed κ L K P ℓ ℓ' h_l aOStmtIn
      stmtIn witIn oStmtIn challenges h_sumcheck_cons h_wit_struct
  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    simp only [step, finalSumcheckStepLogic, finalSumcheckVerifierStmtOut,
      finalSumcheckProverWitOut]
  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by rfl
  have hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    simp only [step, finalSumcheckStepLogic]
    constructor
    · -- MLPEvalRelation: stmtOut.original_claim = witOut.t.val.eval stmtOut.t_eval_point
      rfl
    · exact h_oStmtIn_compat
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

/-! ## Prover and Verifier Implementation -/

/-- The prover for the final sumcheck step. -/
noncomputable def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheck L) where
  PrvState := fun
    | 0 => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' (Fin.last ℓ')
    | _ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' (Fin.last ℓ') × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    let s' := finalSumcheckProverComputeMsg κ L K P ℓ ℓ' witIn stmtIn
    pure ⟨s', (stmtIn, oStmtIn, witIn, s')⟩
  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- No challenges in this step
  output := fun ⟨stmtIn, oStmtIn, witIn, s'⟩ => do
    let logic := finalSumcheckStepLogic κ L K P ℓ ℓ' h_l aOStmtIn
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheck L) s'
    pure (logic.proverOut stmtIn witIn oStmtIn t)

open Classical in
/-- The verifier for the final sumcheck step. -/
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecFinalSumcheck L) where
  verify := fun stmtIn _ => do
    let s' : L ← query (spec := [(pSpecFinalSumcheck L).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheck L) s'
    let logic := finalSumcheckStepLogic κ L K P ℓ ℓ' h_l aOStmtIn
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)
  embed := (finalSumcheckStepLogic κ L K P ℓ ℓ' h_l aOStmtIn).embed
  hEq := (finalSumcheckStepLogic κ L K P ℓ ℓ' h_l aOStmtIn).hEq

/-- The oracle reduction for the final sumcheck step. -/
noncomputable def finalSumcheckOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheck L) where
  prover := finalSumcheckProver κ L K P ℓ ℓ' h_l aOStmtIn
  verifier := finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn

/-- Perfect completeness for the final sumcheck step (strict frame, matching the
strict completeness chain consumed by `coreInteraction_perfectCompleteness` / `General`). -/
theorem finalSumcheckOracleReduction_perfectCompleteness [IsDomain L] {σ : Type}
  (init : ProbComp σ) (hInit : NeverFail init)
  (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  OracleReduction.perfectCompleteness
    (pSpec := pSpecFinalSumcheck L)
    (relIn := strictSumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
    (relOut := aOStmtIn.toStrictRelInput)
    (oracleReduction := finalSumcheckOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
      (init := init) (impl := impl) := by
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_P_to_V (hInit := hInit)
    (hDir0 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  rw [probEvent_eq_one_iff]
  dsimp only [finalSumcheckOracleReduction, finalSumcheckProver, finalSumcheckVerifier,
    OracleVerifier.toVerifier, FullTranscript.mk1]
  let step := (finalSumcheckStepLogic κ L K P ℓ ℓ' h_l aOStmtIn)
  let strongly_complete : step.IsStronglyComplete := finalSumcheckStep_is_logic_complete
    (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn)
  refine ⟨?_, ?_⟩
  · -- SAFETY
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
    intro h_prover_final_output h_prover_final_output_support
    conv =>
      simp only [guard_eq]
      enter [2];
      simp only [bind_pure_comp, NeverFail.probFailure_eq_zero, implies_true]
    rw [and_true]
    rw [OptionT.probFailure_liftComp_of_OracleComp_Option]
    conv_lhs =>
      enter [1]
      simp only [MessageIdx, Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one,
        id_eq, bind_pure_comp, OptionT.run_map, probFailure_eq_zero]
    rw [zero_add]
    simp only [probOutput_eq_zero_iff]
    rw [OptionT.support_run_eq]
    simp only [←probOutput_eq_zero_iff]
    (try simp_all only)
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
      (FullTranscript.mk1 (msg0 := _)) with h_V_check_def
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecFinalSumcheck L).dir 0 ≠ Direction.V_to_P := by
            dsimp only [pSpecFinalSumcheck, Fin.isValue, Matrix.cons_val_zero]
            simp only [ne_eq, reduceCtorEq, not_false_eq_true]
          exfalso
          exact hj_ne hj
      )
    have h_inputState_eq : inputState = (finalSumcheckProverComputeMsg κ L K P ℓ ℓ'
        witIn stmtIn, stmtIn, oStmtIn, witIn,
        finalSumcheckProverComputeMsg κ L K P ℓ ℓ' witIn stmtIn) :=
      hInputState_mem_support
    have h_inputState1 :
        inputState.1 = finalSumcheckProverComputeMsg κ L K P ℓ ℓ' witIn stmtIn := by
      rw [h_inputState_eq]
    have h_V_check_is_true : V_check := by
      rw [h_V_check_def]
      convert h_V_check using 2
      rw [h_inputState1]
      rfl
    simp only [h_V_check_is_true, ↓reduceIte, support_pure, Set.mem_singleton_iff, Fin.isValue,
      Fin.val_last, exists_eq_left, OptionT.support_OptionT_pure_run] at h_vStmtOut_mem_support
    rw [h_vStmtOut_mem_support]
    simp only [Fin.isValue, Fin.val_last, OptionT.run_pure, probOutput_eq_zero_iff, support_pure,
      Set.mem_singleton_iff, reduceCtorEq, not_false_eq_true]
  · -- CORRECTNESS
    intro x hx_mem_support
    rcases x with ⟨⟨prvStmtOut, prvOStmtOut⟩, ⟨verStmtOut, verOStmtOut⟩, witOut⟩
    simp only
    simp only [
      support_bind, support_pure,
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
    simp only [ChallengeIdx, Challenge, liftComp_eq_liftM, liftM_pure, liftComp_id, support_pure,
      Set.mem_singleton_iff, MessageIdx, Message, Fin.isValue] at hx_mem_support
    rcases hx_mem_support with ⟨h_prvOut_mem_support, h_verOut_mem_support⟩
    conv at h_prvOut_mem_support =>
      dsimp only [finalSumcheckStepLogic]
      simp only [Fin.val_last, Fin.isValue, Prod.mk.injEq, and_true]
    conv at h_verOut_mem_support =>
      erw [simulateQ_bind]
      erw [support_liftM_optionT]
      erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      erw [_root_.bind_pure_simulateQ_comp]
      erw [OptionT.simulateQ_map]
      erw [OptionT.simulateQ_ite]
      simp only [Fin.isValue, Message, Matrix.cons_val_zero, id_eq, MessageIdx,
        toPFunctor_emptySpec, Function.comp_apply, OptionT.simulateQ_pure,
        OptionT.simulateQ_failure, map_pure, support_ite, support_pure]
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk1 (msg0 := _)) with h_V_check_def
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecFinalSumcheck L).dir 0 ≠ Direction.V_to_P := by
            dsimp only [pSpecFinalSumcheck, Fin.isValue, Matrix.cons_val_zero]
            simp only [ne_eq, reduceCtorEq, not_false_eq_true]
          exfalso
          exact hj_ne hj
      )
    have h_V_check_is_true : V_check := h_V_check
    simp only [h_V_check_is_true, ↓reduceIte, Fin.isValue,
      Function.comp_apply] at h_verOut_mem_support
    erw [OptionT.support_OptionT_pure] at h_verOut_mem_support
    simp only [Set.mem_singleton_iff, Fin.isValue, Prod.mk.injEq] at h_verOut_mem_support
    obtain ⟨verStmtOut_eq, verOStmtOut_eq⟩ := h_verOut_mem_support
    obtain ⟨⟨prvStmtOut_eq, prvOStmtOut_eq⟩, prvWitOut_eq⟩ := h_prvOut_mem_support
    subst verStmtOut_eq verOStmtOut_eq
    constructor
    · rw [prvWitOut_eq]
      exact h_rel
    · constructor
      · rw [prvStmtOut_eq]; rfl
      · rw [prvOStmtOut_eq]
        exact h_agree.2

/-- RBR knowledge error for the final sumcheck step -/
def finalSumcheckRbrKnowledgeError : ℝ≥0 := (1 : ℝ≥0) / (Fintype.card L)

/-- The round-by-round extractor for the final sumcheck step -/
noncomputable def finalSumcheckRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheck L)
    (WitMid := fun _m => SumcheckWitness L ℓ' (Fin.last ℓ')) where
  eqIn := rfl
  extractMid := fun _m ⟨_, _⟩ _trSucc witMidSucc => witMidSucc

  extractOut := fun ⟨stmtIn, _⟩ _tr witOut => {
    t' := witOut.t,
    H := projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
      (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
      (ctx := stmtIn.ctx) (t := witOut.t)
      (i := Fin.last ℓ') (challenges := stmtIn.challenges)
  }

/- This follows the KState of `finalSumcheckKStateProp` in `BinaryBasefold`.
though the multiplier poly is different. -/
def finalSumcheckKStateProp {m : Fin (1 + 1)} (tr : Transcript m (pSpecFinalSumcheck L))
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (witMid : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn (masterKStateProp with default `True` localChecks)
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn
      (stmtIdx := Fin.last ℓ')
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks := True)
  | ⟨1, _⟩ => -- implied by relOut + local checks via extractOut proofs
    let c : L := tr.messages ⟨0, rfl⟩
    let stmtOut : MLPEvalStatement L ℓ' := {
      t_eval_point := stmt.challenges,
      original_claim := c
    }
    let sumcheckFinalVCheck : Prop :=
      let eq_tilde_eval : L := compute_final_eq_value κ L K P ℓ ℓ' h_l
        stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching
      stmt.sumcheck_target = eq_tilde_eval * c
    let finalEvalCheck : Prop := witMid.t'.val.eval stmtOut.t_eval_point = stmtOut.original_claim
    let oracleCompatProp : Prop := aOStmtIn.initialCompatibility ⟨witMid.t', oStmt⟩
    let witnessStructProp : Prop := witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmt witMid
    sumcheckFinalVCheck ∧ finalEvalCheck ∧ oracleCompatProp ∧ witnessStructProp

/-- The knowledge state function for the final sumcheck step -/
noncomputable def finalSumcheckKnowledgeStateFunction [IsDomain L] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).KnowledgeStateFunction init impl
    (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
    (relOut := aOStmtIn.toRelInput)
    (extractor := finalSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn)
  where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    finalSumcheckKStateProp κ L K P ℓ ℓ' h_l
    (m := m) (tr := tr) (stmt := stmt) (witMid := witMid) (oStmt := oStmt)
  toFun_empty := fun stmt witMid => by
    simp only [sumcheckRoundRelation, sumcheckRoundRelationProp, Fin.val_last, cast_eq,
      Set.mem_setOf_eq, finalSumcheckKStateProp, masterKStateProp, true_and]
  toFun_next := fun m hDir (stmt, oStmt) tr msg witMid => by
    -- Only round is m=0 → m=1; extractMid is identity (RS keeps full SumcheckWitness).
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => omega
    subst h_m_eq_0
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.castSucc_zero]
    intro h_kState_round1
    unfold finalSumcheckKStateProp at h_kState_round1 ⊢
    simp only [Fin.isValue, Nat.reduceAdd, Fin.mk_one, Fin.coe_ofNat_eq_mod, Nat.reduceMod]
      at h_kState_round1
    obtain ⟨h_sumcheckFinalCheck, h_finalEvalCheck, h_oracleCompat, h_witStruct⟩ := h_kState_round1
    -- Goal: masterKStateProp at m=0 = True ∧ witnessStructuralInvariant ∧ sumcheckConsistencyProp
    --   ∧ initialCompatibility
    unfold RingSwitching.masterKStateProp
    refine ⟨trivial, h_witStruct, ?_, h_oracleCompat⟩
    -- sumcheckConsistencyProp: at Fin.last ℓ' the sum is a single term witMid.H.val.eval 0
    unfold Sumcheck.Structured.sumcheckConsistencyProp
    simp only [Fin.val_last]
    rw [Finset.sum_eq_single (a := fun _ => (0 : L))
      (h₀ := fun b _ hb_ne => by
        exfalso; apply hb_ne
        funext i; simp only [tsub_self] at i; exact i.elim0)
      (h₁ := fun h_not_mem => by
        exfalso; apply h_not_mem
        simp only [SumcheckDomain.cube, Fintype.mem_piFinset]
        intro i; simp only [tsub_self] at i; exact i.elim0)]
    have h_H_eval : witMid.H.val.eval (fun _ => 0) =
        ((RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly stmt.ctx).val.eval
          stmt.challenges * witMid.t'.val.eval stmt.challenges := by
      rw [show witMid.H.val = _ from h_witStruct]
      exact projectToMidSumcheckPolyWithParam_at_last_eval_ringswitching (κ := κ) (L := L) (K := K)
        (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
        stmt.ctx witMid.t' stmt.challenges (fun _ => 0)
    have h_mult_eq :
      ((RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly stmt.ctx).val.eval
        stmt.challenges = compute_final_eq_value κ L K P ℓ ℓ' h_l stmt.ctx.t_eval_point
        stmt.challenges stmt.ctx.r_batching :=
      compute_A_MLE_eval_eq_final_eq_value κ L K P ℓ ℓ' h_l
        stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching
    -- `boolDomain L 0` at `Fin.last` collapses the sum; the single term is `witMid.H.eval 0`.
    show stmt.sumcheck_target = witMid.H.val.eval (fun _ => 0)
    rw [h_H_eval, h_mult_eq]
    -- `c` (the message) equals `t'(challenges)` via finalEvalCheck.
    refine Eq.trans h_sumcheckFinalCheck ?_
    congr 1
    exact h_finalEvalCheck.symm
  toFun_full := fun (stmtIn, oStmtIn) tr witOut probEvent_relOut_gt_0 => by
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, Prod.exists] at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩
    have h_output_mem_V_run_support' :
        some (stmtOut, oStmtOut) ∈
          support (do
            let s ← init
            Prod.fst <$>
              (simulateQ impl
                (Verifier.run (stmtIn, oStmtIn) tr
                  (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier)).run
                    s) := by
      exact (OptionT.mem_support_iff
        (mx := OptionT.mk (do
          let s ← init
          Prod.fst <$>
            (simulateQ impl
              (Verifier.run (stmtIn, oStmtIn) tr
                (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier)).run s))
        (x := (stmtOut, oStmtOut))).1 h_output_mem_V_run_support
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output_mem_V_run_support'
    rcases h_output_mem_V_run_support' with ⟨s, hs_init, h_output_mem_V_run_support⟩
    conv at h_output_mem_V_run_support =>
      simp only [Verifier.run, OracleVerifier.toVerifier]
      simp only [finalSumcheckVerifier]
      simp only [support_bind, Set.mem_iUnion]
      dsimp only [StateT.run]
      simp only [simulateQ_bind]
      simp only [MessageIdx, Fin.isValue, Matrix.cons_val_zero, simulateQ_pure, Message, guard_eq,
        pure_bind, Function.comp_apply, simulateQ_map, simulateQ_ite,
        OptionT.simulateQ_failure, bind_map_left]
      simp only [MessageIdx, Message, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        bind_pure_comp, simulateQ_map, simulateQ_ite, simulateQ_pure, OptionT.simulateQ_failure,
        bind_map_left, Function.comp_apply]
      simp only [support_ite]
      simp only [Fin.isValue, Set.mem_ite_empty_right, Set.mem_singleton_iff, Prod.mk.injEq,
        exists_and_left, exists_eq', exists_eq_right, exists_and_right]
      simp only [Fin.isValue, id_eq, FullTranscript.mk1_eq_snoc, support_map, Set.mem_image,
        Prod.exists, exists_and_right, exists_eq_right]
      erw [simulateQ_bind]
      enter [1, x, 1, 1, 1, 2];
      erw [simulateQ_bind]
      erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      simp only [Fin.isValue, FullTranscript.mk1_eq_snoc, pure_bind, OptionT.simulateQ_map]
    conv at h_output_mem_V_run_support =>
      simp only [Fin.isValue, FullTranscript.mk1_eq_snoc, Function.comp_apply]
    erw [support_bind] at h_output_mem_V_run_support
    let step := (finalSumcheckStepLogic κ L K P ℓ ℓ' h_l aOStmtIn)
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk1 (msg0 := _)) with h_V_check_def
    by_cases h_V_check : V_check
    ·
      simp only [Fin.isValue, h_V_check, ↓reduceIte, OptionT.run_pure, simulateQ_pure,
        Set.mem_iUnion, exists_prop, Prod.exists] at h_output_mem_V_run_support
      erw [simulateQ_bind] at h_output_mem_V_run_support
      erw [simulateQ_pure] at h_output_mem_V_run_support
      simp only [Fin.isValue, Function.comp_apply,
        pure_bind] at h_output_mem_V_run_support
      rw [if_pos (h_V_check_def ▸ h_V_check)] at h_output_mem_V_run_support
      erw [LawfulApplicative.map_pure] at h_output_mem_V_run_support
      erw [simulateQ_pure] at h_output_mem_V_run_support
      (try erw [simulateQ_pure] at h_output_mem_V_run_support)
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, ↓existsAndEq, and_true, exists_eq_left,
        simulateQ_pure] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Fin.isValue, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq,
        exists_eq_right] at h_output_mem_V_run_support
      rcases h_output_mem_V_run_support with ⟨h_stmtOut_eq, h_oStmtOut_eq⟩
      simp only [Fin.reduceLast, Fin.isValue]
      simp only [AbstractOStmtIn.toRelInput, MLPEvalRelation, Set.mem_setOf_eq] at h_relOut
      unfold finalSumcheckKStateProp
      dsimp only
      simp only [h_stmtOut_eq] at h_relOut ⊢
      have h_oStmtOut_eq_oStmtIn : oStmtOut = oStmtIn := by rw [h_oStmtOut_eq]; rfl
      rw [h_oStmtOut_eq_oStmtIn] at h_relOut
      refine ⟨h_V_check, ?_, ?_, ?_⟩
      · -- finalEvalCheck: `witMid.t'.eval stmtOut.t_eval_point = stmtOut.original_claim`.
        --   `witMid.t' = witOut.t` (extractOut identity on `t'`); reduces to `h_relOut.1.symm`.
        dsimp only [finalSumcheckRbrExtractor]
        exact h_relOut.1.symm
      · -- oracleCompatProp
        exact h_relOut.2
      · -- witnessStructProp: `extractOut` sets `H := projectToMidSumcheckPolyWithParam …` (rfl)
        dsimp only [witnessStructuralInvariant, finalSumcheckRbrExtractor]
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
      rw [show ((pure none : StateT σ ProbComp (Option (MLPEvalStatement L ℓ'))) s)
        = pure (none, s) from rfl] at hab
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hab
      obtain ⟨ha, hb⟩ := hab
      subst ha
      dsimp only at hsome
      erw [simulateQ_pure] at hsome
      change (some (stmtOut, oStmtOut), x) ∈ _root_.support (pure (none, b)) at hsome
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq,
        false_and] at hsome

/-- Round-by-round knowledge soundness for the final sumcheck step. `pSpecFinalSumcheck` has zero
challenge indices, so the per-`j` obligation is vacuous. -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness [Fintype L] [IsDomain L] {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
      (relOut := aOStmtIn.toRelInput)
      (rbrKnowledgeError := fun _ => finalSumcheckRbrKnowledgeError (L := L)) := by
  use (fun _ => SumcheckWitness L ℓ' (Fin.last ℓ'))
  use finalSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn
  use finalSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn init impl
  intro stmtIn witIn prover ⟨j, hj⟩
  -- pSpecFinalSumcheck has 1 message (a P_to_V message), so no challenge index.
  cases j using Fin.cases with
  | zero => simp only [pSpecFinalSumcheck, ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue,
    Matrix.cons_val_fin_one, Direction.not_P_to_V_eq_V_to_P] at hj
  | succ j' => exact Fin.elim0 j'

end FinalSumcheckStep

section LargeFieldReduction

/-- Composed oracle verifier for the SumcheckStep (seqCompose over ℓ') -/
@[reducible]
def sumcheckLoopOracleVerifier :=
  OracleVerifier.seqCompose (m := ℓ') (oSpec := []ₒ)
    (pSpec := fun _ => pSpecSumcheckRound L)
    (OStmt := fun _ => aOStmtIn.OStmtIn)
    (Stmt := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P))
    (V := fun (i: Fin ℓ') => iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn i)

/-- Composed oracle reduction for the SumcheckStep (seqCompose over ℓ') -/
@[reducible]
def sumcheckLoopOracleReduction :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecSumcheckLoop L ℓ')
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := SumcheckWitness L ℓ' (Fin.last ℓ')) :=
  OracleReduction.seqCompose (m:=ℓ') (oSpec:=[]ₒ)
    (OStmt := fun _ => aOStmtIn.OStmtIn)
    (Stmt := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P))
    (Wit := fun i => SumcheckWitness L ℓ' i)
    (R := fun (i: Fin ℓ') => iteratedSumcheckOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn i)

/-- Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum -/
@[reducible]
def coreInteractionOracleVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:=sumcheckLoopOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn)
    (pSpec₁:=pSpecSumcheckLoop L ℓ')
    (V₂:=finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn)
    (pSpec₂:=pSpecFinalSumcheck L)

/-- Large-field reduction: Sumcheck seqCompose, then append FinalSum -/
@[reducible]
def coreInteractionOracleReduction :=
  OracleReduction.append
    (R₁ := sumcheckLoopOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
    (pSpec₁:=pSpecSumcheckLoop L ℓ')
    (R₂ := finalSumcheckOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
    (pSpec₂:=pSpecFinalSumcheck L)

/-!
## RBR Knowledge Soundness Components for Single Round
-/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for large-field reduction (Sumcheck ++ FinalSum) -/
theorem coreInteraction_perfectCompleteness [IsDomain L] (hInit : NeverFail init) :
  OracleReduction.perfectCompleteness
    (oracleReduction := coreInteractionOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := WitMLP L ℓ')
    (relIn := strictSumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (relOut := aOStmtIn.toStrictRelInput)
    (init := init)
    (impl := impl) := by
  -- Follows from append_perfectCompleteness of interactionPhase and finalSumcheck
  apply OracleReduction.append_perfectCompleteness
  · apply OracleReduction.seqCompose_perfectCompleteness
      (rel := fun i => strictSumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i)
      (R := fun i => iteratedSumcheckOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn i)
      (h := fun i =>
        iteratedSumcheckOracleReduction_perfectCompleteness (κ:=κ) (L:=L) (K:=K)
          (P:=P) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l) (aOStmtIn:=aOStmtIn)
          (init:=init) (impl:=impl) i hInit
      )
  · exact finalSumcheckOracleReduction_perfectCompleteness (κ:=κ) (L:=L) (K:=K)
      (P:=P) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l) (aOStmtIn:=aOStmtIn) (init:=init) (hInit:=hInit) (impl:=impl)

/-- RBR knowledge error for a degree-`d` sumcheck loop, obtained from the `seqCompose`
challenge-index decomposition. -/
def sumcheckLoopRbrKnowledgeErrorWithDegree (d : ℕ)
    (j : (pSpecSumcheckLoopWithDegree L ℓ' d).ChallengeIdx) : ℝ≥0 :=
  let ij := ProtocolSpec.seqComposeChallengeIdxToSigma
    (pSpec := fun _ : Fin ℓ' => pSpecSumcheckRoundWithDegree L d) j
  Sumcheck.Structured.roundKnowledgeError L ℓ' ij.1 d

def sumcheckLoopRbrKnowledgeError (j : (pSpecSumcheckLoop L ℓ').ChallengeIdx) : ℝ≥0 :=
  sumcheckLoopRbrKnowledgeErrorWithDegree L ℓ' 2 j

/-- RBR knowledge error for the core interaction with a degree-`d` sumcheck loop. The loop
contributes `d / |L|` per sumcheck challenge; the final sumcheck contributes `1 / |L|`. -/
def coreInteractionRbrKnowledgeErrorWithDegree (d : ℕ)
    (j : (pSpecCoreInteractionWithDegree L ℓ' d).ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (f := sumcheckLoopRbrKnowledgeErrorWithDegree L ℓ' d)
    (g := fun _ => finalSumcheckRbrKnowledgeError (L := L))
    (ChallengeIdx.sumEquiv.symm j)

/-- Standard Binius ring-switching RBR knowledge error (`d = 2`) with exact final-step splitting. -/
def coreInteractionRbrKnowledgeError (j : (pSpecCoreInteraction L ℓ').ChallengeIdx) : ℝ≥0 :=
  coreInteractionRbrKnowledgeErrorWithDegree L ℓ' 2 j

/-- RBR knowledge soundness for the sumcheck loop (`seqCompose` over `ℓ'`). -/
theorem sumcheckLoopOracleVerifier_rbrKnowledgeSoundness [IsDomain L] :
  (sumcheckLoopOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn).rbrKnowledgeSoundness
    (init := init) (impl := impl)
    (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
    (rbrKnowledgeError := fun _ => (2 : ℝ≥0) / Fintype.card L) :=
  OracleVerifier.seqCompose_rbrKnowledgeSoundness
    (init := init) (impl := impl)
    (rel := fun i => sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i)
    (V := fun i => iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn i)
    (rbrKnowledgeError := fun roundIdx _challengeIdx =>
      roundKnowledgeError L ℓ' roundIdx)
    (h := fun i =>
      iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness κ L K P ℓ ℓ' h_l aOStmtIn i)

/-- RBR knowledge soundness for large-field reduction (Sumcheck ++ FinalSum) -/
theorem coreInteraction_rbrKnowledgeSoundness [IsDomain L] :
  OracleVerifier.rbrKnowledgeSoundness
    (verifier := coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := WitMLP L ℓ')
    (init := init)
    (impl := impl)
    (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (relOut := aOStmtIn.toRelInput)
    (rbrKnowledgeError := coreInteractionRbrKnowledgeError (L:=L) (ℓ':=ℓ')) := by
  let hAppend := OracleVerifier.append_rbrKnowledgeSoundness
    (init := init) (impl := impl)
    (rel₁ := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (rel₂ := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
    (rel₃ := aOStmtIn.toRelInput)
    (V₁ := sumcheckLoopOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn)
    (V₂ := finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn)
    (rbrKnowledgeError₁ := fun _ => (2 : ℝ≥0) / Fintype.card L)
    (rbrKnowledgeError₂ := fun _ => finalSumcheckRbrKnowledgeError (L := L))
    (h₁ := by
      exact sumcheckLoopOracleVerifier_rbrKnowledgeSoundness
        (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
        (aOStmtIn := aOStmtIn) (init := init) (impl := impl))
    (h₂ := by
      exact finalSumcheckOracleVerifier_rbrKnowledgeSoundness
        (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
        (aOStmtIn := aOStmtIn) (init := init) (impl := impl))
  exact OracleVerifier.rbrKnowledgeSoundness_of_eq_error
    (init := init) (impl := impl)
    (h_ε := by
      intro i
      simp only [Function.comp_apply, coreInteractionRbrKnowledgeError,
        coreInteractionRbrKnowledgeErrorWithDegree]
      set x := ChallengeIdx.sumEquiv.symm i with hx
      rcases x with i₁ | i₂
      · exact hx ▸ rfl
      · rcases i₂ with ⟨j, hj⟩
        fin_cases j
        simp only [pSpecFinalSumcheck, Matrix.cons_val_fin_one, reduceCtorEq] at hj)
    (h := hAppend)

end LargeFieldReduction
end
end RingSwitching.SumcheckPhase
