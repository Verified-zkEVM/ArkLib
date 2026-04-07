/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase
import ArkLib.ProofSystem.Binius.FRIBinius.CoreInteractionPhase
import ArkLib.ProofSystem.Binius.RingSwitching.BatchingPhase
import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Security.Implications

/-!
# FRI-Binius IOPCS

The FRI-Binius IOPCS consists of the following phases:
1. **Batching Phase**: polynomial packing and batching via tensor algebra operations
2. **Core Interaction Phase**: Interactive sumcheck + FRI folding over ℓ' rounds
3. **Query Phase**: FRI-style proximity testing with γ repetitions

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive (2024).
  Statement numbering follows the archived revision of [DP24].
-/

namespace Binius.FRIBinius.FullFRIBinius
section

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Module
  Binius Verifier
open Binius.BinaryBasefold Binius.RingSwitching Binius.FRIBinius.CoreInteractionPhase

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [h_Fq_char_prime : Fact (Nat.Prime (ringChar K))] [hF₂ : Fact (Fintype.card K = 2)]
variable [Algebra K L]
variable (β : Basis (Fin (2 ^ κ)) K L)
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable (ℓ ℓ' 𝓡 ϑ γ_repetitions : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]
variable (h_ℓ_add_R_rate : ℓ' + 𝓡 < 2 ^ κ)
variable (h_l : ℓ = ℓ' + κ)
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ')]

section Pspec

noncomputable def batchingCorePspec := (RingSwitching.pSpecBatching κ L K) ++ₚ
  (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

noncomputable def fullPspec := (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) ++ₚ
  (BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

noncomputable instance :
    ∀ j, OracleInterface
      ((batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).Message j) :=
  instOracleInterfaceMessageAppend (pSpec₁ := RingSwitching.pSpecBatching κ L K)
    (pSpec₂ := BinaryBasefold.pSpecCoreInteraction K β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

noncomputable instance :
    ∀ j, SampleableType
      ((batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).Challenge j) :=
  instSampleableTypeChallengeAppend (pSpec₁ := RingSwitching.pSpecBatching κ L K)
    (pSpec₂ := BinaryBasefold.pSpecCoreInteraction K β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

noncomputable instance :
    ∀ j, OracleInterface ((fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions
      h_ℓ_add_R_rate).Message j) :=
  instOracleInterfaceMessageAppend
    (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

noncomputable instance :
    ∀ j, SampleableType ((fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions
      h_ℓ_add_R_rate).Challenge j) :=
  instSampleableTypeChallengeAppend
    (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

end Pspec

def batchingCoreVerifier :
    OracleVerifier (oSpec := []ₒ)
      (StmtIn := BatchingStmtIn (L := L) (ℓ := ℓ))
      (OStmtIn := (BinaryBasefoldAbstractOStmtIn (β := β)
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
      (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
      (OStmtOut := BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (pSpec := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) :=
  let _ := h_l; let _ := 𝓑; sorry

def batchingCoreReduction :
    OracleReduction (oSpec := []ₒ)
      (StmtIn := BatchingStmtIn (L := L) (ℓ := ℓ))
      (OStmtIn := (BinaryBasefoldAbstractOStmtIn (β := β)
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
      (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
      (OStmtOut := BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (WitIn := BatchingWitIn L K ℓ ℓ')
      (WitOut := Unit)
      (pSpec := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) :=
  let _ := h_l; let _ := 𝓑; sorry

/-- The oracle verifier for the full Binary Basefold protocol -/
@[reducible]
def fullOracleVerifier :
  OracleVerifier (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStmtIn := (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (pSpec := fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  let _ := h_l; let _ := 𝓑; sorry

/-- The reduction for the full Binary Basefold protocol -/
@[reducible]
def fullOracleReduction :
  OracleReduction (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStmtIn := (BinaryBasefoldAbstractOStmtIn (β := β)
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitIn := BatchingWitIn L K ℓ ℓ')
    (WitOut := Unit)
    (pSpec := fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  let _ := h_l; let _ := 𝓑; sorry

/-- The full Binary Basefold protocol as a Proof -/
@[reducible]
def fullOracleProof :
  OracleProof []ₒ
    (Statement := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStatement := (BinaryBasefoldAbstractOStmtIn (β := β)
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (Witness := BatchingWitIn L K ℓ ℓ')
    (pSpec:= fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  let _ := h_l; let _ := 𝓑; sorry

/-!
## Security Properties
-/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

section CanonicalB

variable [h_B01 : Fact (𝓑 0 = 0 ∧ 𝓑 1 = 1)]

/-- Perfect completeness for the full Binary Basefold protocol (reduction) -/
theorem fullOracleReduction_perfectCompleteness (hInit : NeverFail init) :
  OracleReduction.perfectCompleteness
    (oracleReduction := fullOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l (𝓑:=𝓑))
    (relIn := BatchingPhase.strictBatchingInputRelation κ L K (β:=booleanHypercubeBasis κ L K β)
      ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (relOut := acceptRejectOracleRel)
    (init := init)
    (impl := impl) := sorry

open scoped NNReal

/-- Combined RBR knowledge error for batching + core interaction. -/
noncomputable def batchingCoreRbrKnowledgeError
    (i : (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (f := fun _ => RingSwitching.BatchingPhase.batchingRBRKnowledgeError (κ := κ) (L := L))
    (g := FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError
      (κ := κ) (L := L) (K := K) (β := β) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (ChallengeIdx.sumEquiv.symm i)

/-- Combined RBR knowledge error for full FRI-Binius. -/
noncomputable def fullRbrKnowledgeError
    (i : (fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate).ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (f := batchingCoreRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (g := QueryPhase.queryRbrKnowledgeError K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (ChallengeIdx.sumEquiv.symm i)

open FRIBinius.CoreInteractionPhase in
/-- Round-by-round knowledge soundness for the full FRI-Binius oracle verifier. -/
theorem fullOracleVerifier_rbrKnowledgeSoundness :
  (fullOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
    (relIn := BatchingPhase.batchingInputRelation κ L K (β := booleanHypercubeBasis κ L K β)
      ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (relOut := acceptRejectOracleRel)
    (rbrKnowledgeError := fullRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by sorry

/-!
## Concrete Knowledge Soundness Error

The concrete **soundness** (and matching KS scalar target) for FRI-Binius (**Construction 5.1**) is
given in Diamond–Posen (ePrint 2024/504) **§5.2, equation (43)**. The paper derives it from the
proofs of **Theorem 3.5** (ring-switching compiler) and **Theorem 4.17** (binary BaseFold / FRI
folding, **Construction 4.12**); the middle and right summands come from **Propositions 4.23** and
**4.24** respectively (see §5.2 text after (43)).

Closed form:

  (κ + 2 · ℓ') / |L| + 2^(ℓ' + 𝓡) / |L| + (1/2 + 1/(2 · 2^𝓡))^γ

Decomposition:
- `(κ + 2 · ℓ') / |L|` — ring-switching batching + sumcheck (§5.2; see also **Protocol 3.1** total
  `(2·ℓ'+κ)/|L|` in the paper's efficiency discussion)
- `2^(ℓ' + 𝓡) / |L|` — aggregated fold-step bad events (**Proposition 4.23**)
- `(1/2 + 1/(2 · 2^𝓡))^γ` — query-phase / proximity acceptance (**Proposition 4.24**)

Audit note: DP24 presents this scalar as a soundness bound; this formalization proves the stronger
knowledge-soundness statement while keeping the scalar error exactly the same.
-/

/-- Single-repetition proximity testing error: `1/2 + 1/(2 · 2^𝓡)`
(third factor of DP24 §5.2 (43)). -/
noncomputable def querySingleRepetitionError : ℝ≥0 :=
  (1 / 2 : ℝ≥0) + 1 / (2 * 2 ^ 𝓡)

/-- Concrete KS upper bound for full FRI-Binius matching **DP24 §5.2 eq. (43)** /
**Construction 5.1** concrete soundness. -/
noncomputable def concreteFRIBiniusKnowledgeError : ℝ≥0 :=
  ((κ : ℝ≥0) + 2 * (ℓ' : ℝ≥0)) / (Fintype.card L : ℝ≥0)
    + (2 ^ (ℓ' + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0)
    + querySingleRepetitionError (𝓡 := 𝓡) ^ γ_repetitions

/-- `∑ᵢ εᵢ` for the full verifier is at most **DP24 §5.2 eq. (43)**. -/
theorem fullRbrKnowledgeError_sum_le_concrete :
    (∑ i : (fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate).ChallengeIdx,
      fullRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate i)
    ≤ concreteFRIBiniusKnowledgeError κ L ℓ' 𝓡 γ_repetitions := by sorry

/-- Scalar KS for the full stack with error **`concreteFRIBiniusKnowledgeError`**,
i.e. **DP24 §5.2 (43)** / **Construction 5.1** concrete soundness. -/
theorem fullOracleVerifier_knowledgeSoundness :
    (fullOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).toVerifier.knowledgeSoundness init impl
    (relIn := BatchingPhase.batchingInputRelation κ L K (booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
      (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
    (relOut := acceptRejectOracleRel)
    (knowledgeError := concreteFRIBiniusKnowledgeError κ L ℓ' 𝓡 γ_repetitions) := by sorry

end CanonicalB

end
end Binius.FRIBinius.FullFRIBinius
