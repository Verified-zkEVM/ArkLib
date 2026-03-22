/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase
import ArkLib.ProofSystem.Binius.FRIBinius.CoreInteractionPhase
import ArkLib.ProofSystem.Binius.RingSwitching.BatchingPhase

/-!
# FRI-Binius IOPCS

The FRI-Binius IOPCS consists of the following phases:
1. **Batching Phase**: polynomial packing and batching via tensor algebra operations
2. **Core Interaction Phase**: Interactive sumcheck + FRI folding over ℓ' rounds
3. **Query Phase**: FRI-style proximity testing with γ repetitions

## References
- State RBR KS

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive (2024).
-/

namespace Binius.FRIBinius.FullFRIBinius
noncomputable section

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Module
  Binius
open Binius.BinaryBasefold Binius.RingSwitching

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

def batchingCorePspec := (RingSwitching.pSpecBatching κ L K) ++ₚ
  (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

def fullPspec := (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) ++ₚ
  (BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance : ∀ j, OracleInterface ((batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).Message j) :=
  instOracleInterfaceMessageAppend (pSpec₁ := RingSwitching.pSpecBatching κ L K)
    (pSpec₂ := BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance : ∀ j, SampleableType ((batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).Challenge j) :=
  instSampleableTypeChallengeAppend (pSpec₁ := RingSwitching.pSpecBatching κ L K)
    (pSpec₂ := BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance : ∀ j, OracleInterface ((fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions
    h_ℓ_add_R_rate).Message j) :=
  instOracleInterfaceMessageAppend (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance : ∀ j, SampleableType ((fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions
    h_ℓ_add_R_rate).Challenge j) :=
  instSampleableTypeChallengeAppend (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

end Pspec

def batchingCoreVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:= RingSwitching.BatchingPhase.batchingOracleVerifier κ (L := L) (K := K) (𝓑 := 𝓑)
      (β:=booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
      (aOStmtIn :=  (BinaryBasefoldAbstractOStmtIn (β := β) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))))
    (pSpec₁ := RingSwitching.pSpecBatching κ L K)
    (pSpec₂:=BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₃ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (V₂:= FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier κ (L := L) (K := K) (β := β)
      (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (𝓡 := 𝓡) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))

def batchingCoreReduction :=
  OracleReduction.append (oSpec:=[]ₒ)
    (R₁ := RingSwitching.BatchingPhase.batchingOracleReduction κ (L := L) (K := K) (𝓑 := 𝓑)
      (β:=booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
      (aOStmtIn :=  (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))))
    (pSpec₁ := RingSwitching.pSpecBatching κ L K)
    (pSpec₂:=BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₃ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (R₂ := FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction κ L K
      β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))

/-- The oracle verifier for the full Binary Basefold protocol -/
@[reducible]
noncomputable def fullOracleVerifier :
  OracleVerifier (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStmtIn := (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (pSpec := fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (Stmt₁ := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (Stmt₂ := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (Stmt₃ := Bool)
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₁ := batchingCoreVerifier κ (L := L) (K := K) (𝓑 := 𝓑) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₂ := QueryPhase.queryOracleVerifier K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))

/-- The reduction for the full Binary Basefold protocol -/
@[reducible]
noncomputable def fullOracleReduction :
  OracleReduction (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStmtIn := (BinaryBasefoldAbstractOStmtIn (β := β)
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitIn := BatchingWitIn L K ℓ ℓ')
    (WitOut := Unit)
    (pSpec := fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleReduction.append (oSpec:=[]ₒ)
    (Stmt₁ := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (Stmt₂ := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (Stmt₃ := Bool)
    (Wit₁ := BatchingWitIn L K ℓ ℓ')
    (Wit₂ := Unit)
    (Wit₃ := Unit)
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn (β := β)
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (R₁ := batchingCoreReduction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
    )
    (R₂ := QueryPhase.queryOracleReduction K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))

/-- The full Binary Basefold protocol as a Proof -/
@[reducible]
noncomputable def fullOracleProof :
  OracleProof []ₒ
    (Statement := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStatement := (BinaryBasefoldAbstractOStmtIn (β := β)
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (Witness := BatchingWitIn L K ℓ ℓ')
    (pSpec:= fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  fullOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l (𝓑:=𝓑)

/-!
## Security Properties
-/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

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
    (impl := impl) :=
  OracleReduction.append_perfectCompleteness
    (R₁ := batchingCoreReduction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
    (R₂ := QueryPhase.queryOracleReduction K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn (β := β)
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := fun _ : Empty => Unit)
    (Oₛ₁:= (BinaryBasefoldAbstractOStmtIn (β := β)
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Oₛᵢ)
    (Oₛ₂:=Binius.BinaryBasefold.instOracleStatementBinaryBasefold K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (i := Fin.last ℓ'))
    (Oₛ₃:=by exact fun i ↦ by exact OracleInterface.instDefault)
    (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (rel₁ := BatchingPhase.strictBatchingInputRelation κ L K (β:=booleanHypercubeBasis κ L K β)
      ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (rel₂ := BinaryBasefold.strictFinalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (rel₃ := acceptRejectOracleRel)
    (h₁ := by
      apply OracleReduction.append_perfectCompleteness
        (rel₁ := BatchingPhase.strictBatchingInputRelation κ L K (β:=booleanHypercubeBasis κ L K β)
          ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn (β := β)
            (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
        (rel₂ := RingSwitching.strictSumcheckRoundRelation κ L K (booleanHypercubeBasis κ L K β)
        ℓ ℓ' h_l (𝓑 := 𝓑) (aOStmtIn := BinaryBasefoldAbstractOStmtIn (β := β)
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
        (rel₃ := BinaryBasefold.strictFinalSumcheckRelOut K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      · apply BatchingPhase.batchingReduction_perfectCompleteness (hInit:=hInit) κ L K
          (β:=booleanHypercubeBasis κ L K β) ℓ ℓ' h_l (𝓑 := 𝓑)
          (BinaryBasefoldAbstractOStmtIn (β := β)
            (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      · apply CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness
          κ (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (𝓡 := 𝓡) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (hInit:=hInit)
    )
    (h₂ := QueryPhase.queryOracleProof_perfectCompleteness K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ) (hInit:=hInit) init impl)

open scoped NNReal

/-- Combined RBR knowledge error for batching + core interaction. -/
def batchingCoreRbrKnowledgeError
    (i : (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (f := fun _ => RingSwitching.BatchingPhase.batchingRBRKnowledgeError (κ := κ) (L := L))
    (g := FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError
      (κ := κ) (L := L) (K := K) (β := β) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (ChallengeIdx.sumEquiv.symm i)

/-- Combined RBR knowledge error for full FRI-Binius. -/
def fullRbrKnowledgeError
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
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  let V₁_batchingCore : OracleVerifier (oSpec := []ₒ)
      (StmtIn := BatchingStmtIn (L := L) (ℓ := ℓ))
      (OStmtIn := (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
      (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
      (OStmtOut := BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (pSpec := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) :=
    batchingCoreVerifier κ (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
      (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)
  let res :=
    OracleVerifier.append_rbrKnowledgeSoundness
      (init := init) (impl := impl)
      (rel₁ := BatchingPhase.batchingInputRelation κ L K (β := booleanHypercubeBasis κ L K β)
        ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
      (rel₂ := BinaryBasefold.finalSumcheckRelOut K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (rel₃ := acceptRejectOracleRel)
      (V₁ := V₁_batchingCore)
      (V₂ := QueryPhase.queryOracleVerifier K β γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ))
      (Oₛ₃ := by exact fun _ => OracleInterface.instDefault)
      (rbrKnowledgeError₁ := batchingCoreRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
      (rbrKnowledgeError₂ := QueryPhase.queryRbrKnowledgeError K β γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (h₁ := by
        dsimp [V₁_batchingCore]
        unfold batchingCoreVerifier batchingCorePspec batchingCoreRbrKnowledgeError
          BinaryBasefold.pSpecCoreInteraction
        exact
          OracleVerifier.append_rbrKnowledgeSoundness
            (init := init) (impl := impl)
            (rel₁ := BatchingPhase.batchingInputRelation κ L K
              (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
              (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
            (rel₂ := RingSwitching.sumcheckRoundRelation κ L K (booleanHypercubeBasis κ L K β)
              ℓ ℓ' h_l (𝓑 := 𝓑) (aOStmtIn := BinaryBasefoldAbstractOStmtIn (β := β)
                (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
            (rel₃ := BinaryBasefold.finalSumcheckRelOut K β (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
            (V₁ := RingSwitching.BatchingPhase.batchingOracleVerifier κ (L := L) (K := K)
              (β := booleanHypercubeBasis κ L K β)
              (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (𝓑 := 𝓑)
              (aOStmtIn :=  (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))))
            (V₂ := coreInteractionOracleVerifier κ (L := L) (K := K)
              (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (𝓡 := 𝓡) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
            (rbrKnowledgeError₁ := fun _ =>
              RingSwitching.BatchingPhase.batchingRBRKnowledgeError (κ := κ) (L := L))
            (rbrKnowledgeError₂ :=
              coreInteractionOracleRbrKnowledgeError
                (κ := κ) (L := L) (K := K) (β := β) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
            (h₁ := RingSwitching.BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundness
              (κ := κ) (L := L) (K := K) (β := booleanHypercubeBasis κ L K β)
              (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (𝓑 := 𝓑)
              (aOStmtIn :=  (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))))
            (h₂ := coreInteractionOracleVerifier_rbrKnowledgeSoundness
              (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
              (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)))
      (h₂ := QueryPhase.queryOracleVerifier_rbrKnowledgeSoundness K β γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) init impl)
  dsimp only [ChallengeIdx, fullOracleVerifier, batchingCorePspec,
    BinaryBasefold.pSpecCoreInteraction, batchingCoreVerifier, MessageIdx] at res ⊢
  exact res

end
end Binius.FRIBinius.FullFRIBinius
