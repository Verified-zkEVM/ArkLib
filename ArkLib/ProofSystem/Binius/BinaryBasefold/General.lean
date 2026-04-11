/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase
import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase
import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Security.Implications

/-!
## Full Binary Basefold Protocol

Sequential composition of:
1. Core Interaction Phase (ℓ rounds of sumcheck + folding, and a final sumcheck)
2. Query Phase (final non-interactive proximity testing)

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Statement numbering follows the archived revision of [DP24].
-/

open AdditiveNTT Polynomial

namespace Binius.BinaryBasefold.FullBinaryBasefold
open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT

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

instance {_ : Empty} : OracleInterface (Unit) := OracleInterface.instDefault

open CoreInteraction QueryPhase
/-- Canonical full verifier over the computable core-interaction stack and computable query-domain
challenges. -/
@[reducible]
def fullOracleVerifier :
  OracleVerifier (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleVerifier.append (oSpec := []ₒ)
    (Stmt₁ := Statement (L := L) (SumcheckBaseContext L ℓ) 0)
    (Stmt₂ := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (Stmt₃ := Bool)
    (OStmt₁ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₁ := CoreInteraction.coreInteractionOracleVerifier 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (𝓑 := 𝓑))
    (V₂ := QueryPhase.queryOracleVerifier 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ))

/-- Canonical full reduction API on the computable core-interaction/query stack. -/
@[reducible]
def fullOracleReduction :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
      0)
    (WitOut := Unit)
    (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleReduction.append (oSpec := []ₒ)
    (Stmt₁ := Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0)
    (Stmt₂ := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (Stmt₃ := Bool)
    (Wit₁ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
      0)
    (Wit₂ := Unit)
    (Wit₃ := Unit)
    (OStmt₁ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (R₁ := CoreInteraction.coreInteractionOracleReduction 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (𝓑 := 𝓑))
    (R₂ := QueryPhase.queryOracleReduction 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ))

/-- Canonical full proof API on the computable core-interaction/query stack. -/
@[reducible]
def fullOracleProof :
  OracleProof []ₒ
    (Statement := Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0)
    (OStatement := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (Witness := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) 0)
    (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  fullOracleReduction 𝔽q β γ_repetitions (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)

/-!
## Security Properties
-/

variable {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for the full Binary Basefold protocol (reduction) -/
theorem fullOracleReduction_perfectCompleteness (hInit : NeverFail init) :
  OracleReduction.perfectCompleteness
    (oracleReduction := fullOracleReduction 𝔽q β γ_repetitions
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    (relIn := strictRoundRelation
      (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
    (relOut := acceptRejectOracleRel)
    (init := init)
    (impl := impl) := by
  sorry

open scoped NNReal

/-- Combined RBR knowledge soundness error for the full protocol -/
noncomputable def fullRbrKnowledgeError (i : (fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) : ℝ≥0 :=
  Sum.elim (f := CoreInteraction.coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (g := QueryPhase.queryRbrKnowledgeError 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (ChallengeIdx.sumEquiv.symm i)

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Round-by-round knowledge soundness for the full Binary Basefold oracle verifier -/
theorem fullOracleVerifier_rbrKnowledgeSoundness :
  (fullOracleVerifier 𝔽q β γ_repetitions (ϑ:=ϑ) (𝓑 := 𝓑)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).rbrKnowledgeSoundness init impl
    (relIn := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)  0)
    (relOut := acceptRejectOracleRel)
    (rbrKnowledgeError := fullRbrKnowledgeError 𝔽q β γ_repetitions (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  sorry

/-!
### Scalar knowledge soundness (DP24-style concrete bound)

Full protocol is **core interaction + query only** (no ring-switching batching). The scalar target
matches **DP24 §5.2 eq. (43)** with the **first summand** `(κ+2ℓ')/|L|` omitted—compare
`Binius.FRIBinius.FullFRIBinius.concreteFRIBiniusKnowledgeError` for the full **Construction 5.1**
stack (Diamond–Posen ePrint 2024/504). Fold/query terms align with **Theorem 4.17** /
**Propositions 4.23** (middle term) and **4.24** (query tail); sumcheck rounds with **Thaler** as in the
**Construction 4.12** proof.

Important audit note: DP24 states these as **soundness** terms. This file proves `knowledgeSoundness`
with the same scalar error. Also, this module-level `ℓ` corresponds to the Basefold core variable
count (paper `ℓ'` when embedded into Construction 5.1).

Proof obligations: decompose `∑ fullRbrKnowledgeError` using `sumcheckFoldKnowledgeError_le`
in `CoreInteractionPhase` and the query-phase sum, then
`Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness` and
`Verifier.knowledgeSoundness_error_mono`.
-/

/-- Concrete KS upper bound for **Binary Basefold (core + query)** without the `κ/|L|` batching term:
`2ℓ/|L| + 2^{ℓ+𝓡}/|L| + (43)₃`.

Here `(43)₃` denotes the third summand of **DP24 §5.2 (43)**. The middle term is the **Proposition 4.23**
style fold charge; the first matches sumcheck soundness as in **Theorem 4.17** / Thaler (see paper).

`γ_rep`, `L`, `ℓ`, `𝓡` are explicit so elaboration does not curry section `γ_repetitions` or lose
`Fintype`. -/
noncomputable def concreteBinaryBasefoldKnowledgeError (L : Type) [Fintype L] (ℓ 𝓡 γ_rep : ℕ) :
    ℝ≥0 :=
  2 * (ℓ : ℝ≥0) / (Fintype.card L : ℝ≥0)
    + (2 ^ (ℓ + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0)
    + ((1 / 2 : ℝ≥0) + 1 / (2 * 2 ^ 𝓡)) ^ γ_rep

/-- Per-challenge RBR KS errors sum **at most** `concreteBinaryBasefoldKnowledgeError …` (core fold
mass may be strictly below the paper display; see doc on `sumcheckFoldKnowledgeError_le`). -/
theorem fullRbrKnowledgeError_sum_le_concrete :
    (∑ i : (fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        fullRbrKnowledgeError 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      ≤ concreteBinaryBasefoldKnowledgeError L ℓ 𝓡 γ_repetitions := by
  sorry

/-- Scalar KS for the full verifier with error `concreteBinaryBasefoldKnowledgeError`, matching the
**DP24 §5.2 (43)**-style bound minus batching (**Theorem 3.5** / ring-switching not present here).

Depends on: `fullRbrKnowledgeError_sum_le_concrete` for
`Verifier.knowledgeSoundness_error_mono` and `Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness`. -/
theorem fullOracleVerifier_knowledgeSoundness :
    (fullOracleVerifier 𝔽q β γ_repetitions (ϑ := ϑ) (𝓑 := 𝓑)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).toVerifier.knowledgeSoundness init impl
      (relIn := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (relOut := acceptRejectOracleRel)
      (knowledgeError := concreteBinaryBasefoldKnowledgeError L ℓ 𝓡 γ_repetitions) := by
  sorry

end Binius.BinaryBasefold.FullBinaryBasefold
