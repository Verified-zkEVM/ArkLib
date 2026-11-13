/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
public import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase
public import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase
public import ArkLib.OracleReduction.Security.Basic

/-!
## Full Binary Basefold Protocol

Sequential composition of:
1. Core Interaction Phase (ℓ rounds of sumcheck + folding, and a final sumcheck)
2. Query Phase (final non-interactive proximity testing)

## Error ledger

The core-and-query challenge sum is bounded by
`2ℓ/|L| + 2^(ℓ+𝓡)/|L| + (1/2 + 1/(2·2^𝓡))^γ`; it excludes ring-switching batching.
This is the corresponding part of DP24 §5.2, equation (43). The middle term bounds the folding
loss and the final term bounds repeated query acceptance. The exports prove perfect completeness
on exact encodings and round-by-round knowledge soundness for
unique-decoding-radius compatibility.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Statement numbering follows the archived revision of [DP24].
* [Zeilberger, H., Chen, B. and Fisch, B., *BaseFold: Efficient Field-Agnostic Polynomial
  Commitment Schemes from Foldable Codes*][ZCF24]

The block size `ϑ` divides `ℓ`. At round zero, the strict relation for perfect completeness
is contained in the relaxed relation for round-by-round knowledge soundness.
The exact-encoding completeness and nearby-encoding security relations follow the distinction
in [ZCF24], Definition 8 and §5.
-/

@[expose] public section

open AdditiveNTT Polynomial

namespace Binius.BinaryBasefold.FullBinaryBasefold
open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q]
local instance [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) :=
  ⟨CharP.prime_ringChar 𝔽q⟩
variable [Fintype 𝔽q] [DecidableEq 𝔽q]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable [hdiv : Fact (ϑ ∣ ℓ)]
variable {𝓑 : Fin 2 ↪ L}

open CoreInteraction QueryPhase

/-- The oracle verifier for the full Binary Basefold protocol -/
@[reducible]
noncomputable def fullOracleVerifier :
  OracleProofVerifier (oSpec:=[]ₒ)
    (Statement := Statement (L := L) (ℓ:=ℓ) (SumcheckBaseContext L ℓ) 0)
    (OStatement:= OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (Stmt₁ := Statement (L := L) (SumcheckBaseContext L ℓ) 0)
    (Stmt₂ := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (Stmt₃ := Bool)
    (OStmt₁ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := pSpecCoreInteraction 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (Oₛ₃ := fun i : Empty => nomatch i)
    (V₁ := CoreInteraction.coreInteractionOracleVerifier 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ) (𝓑 := 𝓑))
    (V₂ := QueryPhase.queryOracleVerifier 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))

/-- The reduction for the full Binary Basefold protocol -/
@[reducible]
noncomputable def fullOracleReduction :
  OracleProof (oSpec:=[]ₒ)
    (Statement := Statement (L := L) (ℓ:=ℓ) (SumcheckBaseContext L ℓ) 0)
    (OStatement:= OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (Witness := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) 0)
    (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleReduction.append (oSpec:=[]ₒ)
    (Stmt₁ := Statement (L := L) (ℓ:=ℓ) (SumcheckBaseContext L ℓ) 0)
    (Stmt₂ := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (Stmt₃ := Bool)
    (Wit₁ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) 0)
    (Wit₂ := Unit)
    (Wit₃ := Unit)
    (OStmt₁ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := pSpecCoreInteraction 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (Oₛ₃ := fun i : Empty => nomatch i)
    (R₁ := CoreInteraction.coreInteractionOracleReduction 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ) (𝓑 := 𝓑))
    (R₂ := QueryPhase.queryOracleReduction 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))

/-!
## Security Properties
-/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

-- Strict-to-relaxed initial transport unfolds dependent fold-domain indices.
set_option backward.isDefEq.respectTransparency false in
omit [SampleableType L] [DecidableEq 𝔽q] in
/-- At the initial frontier, strict completeness inputs satisfy the relaxed relation used by
round-by-round knowledge soundness. -/
theorem strictRoundRelation_subset_roundRelation_zero :
    strictRoundRelation (multpoly := multiplier) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0
      ⊆ roundRelation (multpoly := multiplier) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0 := by
  rintro ⟨⟨stmt, oStmt⟩, wit⟩ h_strict
  simp only [strictRoundRelation, StrictRoundRelated, Set.mem_ofPred_eq,
    StrictOracleWitnessConsistent] at h_strict
  obtain ⟨h_sumcheck, h_struct, h_strict_fold⟩ := h_strict
  simp only [roundRelation, RoundRelated, Set.mem_ofPred_eq, KnowledgeInvariant]
  right
  refine ⟨h_sumcheck, h_struct, ?_, ?_⟩
  · have h_eq := QueryPhase.polyToOracleFunc_eq_getFirstOracle 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := wit.t)
      (i := (OracleFrontierIndex.mkFromStmtIdx (0 : Fin (ℓ + 1))).val)
      (challenges := Fin.take (m := (OracleFrontierIndex.mkFromStmtIdx
        (0 : Fin (ℓ + 1))).val) (v := stmt.challenges)
        (h := by simp only [Fin.val_fin_le, OracleFrontierIndex.val_le_i]))
      (oStmt := oStmt) h_strict_fold
    dsimp only [FirstOracleWitnessConsistent]
    rw [h_eq]
    dsimp only [PairUniqueDecodingClose]
    have h_dist_pos := codeDistance_pos 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (0 : Fin r)
    simp only [hammingDist_self, mul_zero, h_dist_pos]
  · dsimp only [OracleFoldingConsistent]
    intro j hj
    have h_count :
        toOutCodewordsCount ℓ ϑ
          (OracleFrontierIndex.mkFromStmtIdx (0 : Fin (ℓ + 1))).val = 1 := by
      rw [OracleFrontierIndex.val_mkFromStmtIdx]
      exact toOutCodewordsCount_zero ℓ ϑ
    omega

/-- Perfect completeness for exact, honestly encoded inputs to Binary Basefold.
-/
theorem fullOracleReduction_perfectCompleteness :
    OracleProof.perfectCompleteness
      (oracleProof := fullOracleReduction 𝔽q β γ_repetitions (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
      (relation := strictRoundRelation (multpoly := multiplier) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (init := init)
      (impl := impl) :=
  OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (R₁ := CoreInteraction.coreInteractionOracleReduction 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ) )
    (R₂ := QueryPhase.queryOracleReduction 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))
    (Oₛ₃ := fun i : Empty => nomatch i)
      (rel₁ := strictRoundRelation (multpoly := multiplier) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
    (rel₂ := strictFinalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (rel₃ := acceptRejectOracleRel)
    (V₁ := Verifier.GuardedForm.ofEmpty _ (fun input =>
      (⟨⟨0, fun _ => 0, input.1.ctx⟩, 0⟩, fun _ _ => 0)))
    (V₂ := Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i => nomatch i)))
    (hSeam := fun _ => Or.inl inferInstance)
    (h₁ := CoreInteraction.coreInteractionOracleReduction_perfectCompleteness 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
      (init := init) (impl := impl))
    (h₂ := fun s => QueryPhase.queryOracleReduction_perfectCompleteness 𝔽q β γ_repetitions
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (pure s) impl)

open scoped NNReal

/-- Combined RBR knowledge soundness error for the full protocol -/
noncomputable def fullRbrKnowledgeError (i : (fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) : ℝ≥0 :=
  Sum.elim (f := CoreInteraction.coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (g := QueryPhase.queryRbrKnowledgeError 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (ChallengeIdx.sumEquiv.symm i)

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Round-by-round knowledge soundness for the core-and-query protocol. -/
theorem fullOracleVerifier_rbrKnowledgeSoundness :
    ((fullOracleVerifier 𝔽q β γ_repetitions (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).toVerifier
      (Oₛₒ := fun i : Empty => nomatch i)).rbrKnowledgeSoundness
      init impl
      (relIn := roundRelation (multpoly := multiplier) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (relOut := acceptRejectOracleRel)
      (rbrKnowledgeError := fullRbrKnowledgeError 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  unfold fullOracleVerifier fullRbrKnowledgeError fullPSpec
  exact OracleVerifier.append_rbrKnowledgeSoundness_of_guarded_first
    (Oₛ₃ := fun i : Empty => nomatch i) _ _
    (Verifier.GuardedForm.ofEmpty _ (fun input =>
      (⟨⟨0, fun _ => 0, input.1.ctx⟩, 0⟩, fun _ _ => 0)))
    (CoreInteraction.coreInteractionOracleVerifier_rbrKnowledgeSoundness 𝔽q β)
    (QueryPhase.queryOracleVerifier_rbrKnowledgeSoundness 𝔽q β γ_repetitions init impl)

/-- Upper bound `2ℓ/|L| + 2^(ℓ+𝓡)/|L| + (1/2 + 1/(2·2^𝓡))^γ_rep` for the core-and-query
RBR error sum, excluding batching. -/
noncomputable def concreteBinaryBasefoldKnowledgeError (L : Type) [Fintype L] (ℓ 𝓡 γ_rep : ℕ) :
    ℝ≥0 :=
  2 * (ℓ : ℝ≥0) / (Fintype.card L : ℝ≥0)
    + (2 ^ (ℓ + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0)
    + ((1 / 2 : ℝ≥0) + 1 / (2 * 2 ^ 𝓡)) ^ γ_rep

omit [DecidableEq 𝔽q] h_β₀_eq_1 [SampleableType L] in
/-- The challenge-index RBR error sum is at most the core-and-query closed-form bound. -/
theorem fullRbrKnowledgeError_sum_le_concrete :
    (∑ i : (fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        fullRbrKnowledgeError 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      ≤ concreteBinaryBasefoldKnowledgeError L ℓ 𝓡 γ_repetitions := by
  classical
  have h_full :
      (∑ i : (fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        fullRbrKnowledgeError 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      =
      (∑ i : (pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        CoreInteraction.coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      +
      (∑ i : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        QueryPhase.queryRbrKnowledgeError 𝔽q β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
    unfold fullRbrKnowledgeError
    let f :
      ((pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx
        ⊕ (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) → ℝ≥0 :=
      Sum.elim
        (CoreInteraction.coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (QueryPhase.queryRbrKnowledgeError 𝔽q β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    change (∑ i : (fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
      f (ChallengeIdx.sumEquiv.symm i)) = _
    have hsum :
        (∑ i : (fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
          f (ChallengeIdx.sumEquiv.symm i))
        =
        (∑ i : ((pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx
          ⊕ (pSpecQuery 𝔽q β γ_repetitions
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx), f i) := by
      exact Equiv.sum_comp (e := Equiv.symm ChallengeIdx.sumEquiv) (g := f)
    rw [hsum, Fintype.sum_sum_type]
    simp only [f, Sum.elim_inl, Sum.elim_inr]
  rw [h_full]
  have h_core_le :
      (∑ i : (pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        CoreInteraction.coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      ≤ 2 * (ℓ : ℝ≥0) / (Fintype.card L : ℝ≥0)
          + (2 ^ (ℓ + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0) := by
    unfold CoreInteraction.coreInteractionOracleRbrKnowledgeError
    simp only [Function.comp_apply]
    rw [Equiv.sum_comp (Equiv.symm ChallengeIdx.sumEquiv)]
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have h_final :
        (∑ i : (pSpecFinalSumcheckStep (L := L)).ChallengeIdx,
          CoreInteraction.finalSumcheckKnowledgeError (L := L) i) = 0 := by
      exact Finset.sum_eq_zero (fun i _ => nomatch i)
    rw [h_final, add_zero]
    exact Binius.BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError_le (L := L)
      (𝔽q := 𝔽q) (β := β) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
  have h_query :
      (∑ i : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        QueryPhase.queryRbrKnowledgeError 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      = ((1 / 2 : ℝ≥0) + 1 / (2 * 2 ^ 𝓡)) ^ γ_repetitions := by
    simp [QueryPhase.queryRbrKnowledgeError, QueryPhase.queryRbrKnowledgeErrorSingleRepetition,
      pSpecQuery, ChallengeIdx]
  have h_mid :
      (∑ i : (pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        CoreInteraction.coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      +
      (∑ i : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        QueryPhase.queryRbrKnowledgeError 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      ≤ concreteBinaryBasefoldKnowledgeError L ℓ 𝓡 γ_repetitions := by
    rw [concreteBinaryBasefoldKnowledgeError, ← h_query]
    exact add_le_add h_core_le (le_refl _)
  exact h_mid

/-- Ordinary knowledge soundness of full Binary Basefold, with the sum of its challenge errors. -/
theorem fullOracleVerifier_knowledgeSoundness :
    OracleProof.knowledgeSoundness init impl
      (roundRelation (multpoly := multiplier) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (fullOracleVerifier 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
      (∑ i, fullRbrKnowledgeError 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  Verifier.GuardedForm.knowledgeSoundness_of_rbrKnowledgeSoundness
    (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i : Empty => nomatch i)))
    (fullOracleVerifier_rbrKnowledgeSoundness 𝔽q β γ_repetitions)

/-- Full Binary Basefold is perfectly complete on exact encodings and ordinarily
knowledge sound for unique-radius compatibility, with the concrete core-and-query error. -/
theorem fullOracleReduction_perfectCompleteness_and_knowledgeSoundness :
    OracleProof.perfectCompleteness
      (oracleProof := fullOracleReduction 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
      (relation := strictRoundRelation (multpoly := multiplier) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (init := init) (impl := impl) ∧
    OracleProof.knowledgeSoundness init impl
      (roundRelation (multpoly := multiplier) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (fullOracleVerifier 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
      (concreteBinaryBasefoldKnowledgeError L ℓ 𝓡 γ_repetitions) :=
  ⟨fullOracleReduction_perfectCompleteness 𝔽q β γ_repetitions,
    Verifier.knowledgeSoundness_error_mono init impl
      (fullRbrKnowledgeError_sum_le_concrete 𝔽q β γ_repetitions)
      (fullOracleVerifier_knowledgeSoundness 𝔽q β γ_repetitions)⟩

end Binius.BinaryBasefold.FullBinaryBasefold
