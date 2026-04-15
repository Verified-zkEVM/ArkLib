/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase
import ArkLib.ProofSystem.Binius.FRIBinius.CoreInteractionPhase
import ArkLib.ProofSystem.Binius.FRIBinius.Prelude
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
open Binius.BinaryBasefold Binius.RingSwitching Binius.FRIBinius Binius.FRIBinius.CoreInteractionPhase

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [h_Fq_char_prime : Fact (Nat.Prime (ringChar K))] [hF₂ : Fact (Fintype.card K = 2)]
variable [Algebra K L]
variable (β : Basis (Fin (2 ^ κ)) K L) [h_β₀_eq_1 : Fact (β 0 = 1)]
variable (ℓ ℓ' 𝓡 ϑ γ_repetitions : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]
variable (h_ℓ_add_R_rate : ℓ' + 𝓡 < 2 ^ κ)
variable (h_l : ℓ = ℓ' + κ)
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ')]

instance betaFun_linearIndependent : Fact (LinearIndependent K (fun i => β i)) := by
  exact ⟨β.linearIndependent⟩

instance betaFun_zero_eq_one : Fact ((fun i => β i) 0 = 1) := by
  exact h_β₀_eq_1

section Pspec

private def batchingCorePspecExec
    (βfun : Fin (2 ^ κ) → L) [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)] :=
  (RingSwitching.pSpecBatching κ L K) ++ₚ
    (BinaryBasefold.pSpecCoreInteraction K βfun
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

private def fullPspecExec
    (βfun : Fin (2 ^ κ) → L) [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)] :=
  (batchingCorePspecExec κ L K ℓ' 𝓡 ϑ h_ℓ_add_R_rate βfun) ++ₚ
    (BinaryBasefold.pSpecQuery K βfun γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance
    (βfun : Fin (2 ^ κ) → L) [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)] :
    ∀ j, OracleInterface ((batchingCorePspecExec κ L K ℓ' 𝓡 ϑ h_ℓ_add_R_rate βfun).Message j) :=
  instOracleInterfaceMessageAppend (pSpec₁ := RingSwitching.pSpecBatching κ L K)
    (pSpec₂ := BinaryBasefold.pSpecCoreInteraction K βfun
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance
    (βfun : Fin (2 ^ κ) → L) [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)] :
    ∀ j, SampleableType ((batchingCorePspecExec κ L K ℓ' 𝓡 ϑ h_ℓ_add_R_rate βfun).Challenge j) :=
  instSampleableTypeChallengeAppend (pSpec₁ := RingSwitching.pSpecBatching κ L K)
    (pSpec₂ := BinaryBasefold.pSpecCoreInteraction K βfun
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance
    (βfun : Fin (2 ^ κ) → L) [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)] :
    ∀ j, OracleInterface ((fullPspecExec κ L K ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate βfun).Message j) :=
  instOracleInterfaceMessageAppend
    (pSpec₁ := batchingCorePspecExec κ L K ℓ' 𝓡 ϑ h_ℓ_add_R_rate βfun)
    (pSpec₂ := BinaryBasefold.pSpecQuery K βfun γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance
    (βfun : Fin (2 ^ κ) → L) [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)] :
    ∀ j, SampleableType ((fullPspecExec κ L K ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate βfun).Challenge j) :=
  instSampleableTypeChallengeAppend
    (pSpec₁ := batchingCorePspecExec κ L K ℓ' 𝓡 ϑ h_ℓ_add_R_rate βfun)
    (pSpec₂ := BinaryBasefold.pSpecQuery K βfun γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

@[reducible]
def batchingCorePspec
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)] :=
  batchingCorePspecExec κ L K ℓ' 𝓡 ϑ h_ℓ_add_R_rate βfun

@[reducible]
def fullPspec
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)] :=
  fullPspecExec κ L K ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate βfun

instance
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)] :
    ∀ j, OracleInterface ((batchingCorePspec κ L K ℓ' 𝓡 ϑ h_ℓ_add_R_rate βfun).Message j) := by
  unfold batchingCorePspec
  infer_instance

instance
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)] :
    ∀ j, SampleableType ((batchingCorePspec κ L K ℓ' 𝓡 ϑ h_ℓ_add_R_rate βfun).Challenge j) := by
  unfold batchingCorePspec
  infer_instance

instance
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)] :
    ∀ j, OracleInterface ((fullPspec κ L K ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate βfun).Message j) := by
  unfold fullPspec
  infer_instance

instance
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)] :
    ∀ j, SampleableType ((fullPspec κ L K ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate βfun).Challenge j) := by
  unfold fullPspec
  infer_instance

end Pspec

/-- Canonical executable batching + core-interaction verifier. -/
private def batchingCoreVerifierExec
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (βcube : Basis (Fin κ → Fin 2) K L)
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :
    OracleVerifier (oSpec := []ₒ)
      (StmtIn := BatchingStmtIn (L := L) (ℓ := ℓ))
      (OStmtIn := (Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn (𝔽q := K)
        (β := βfun) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).OStmtIn)
      (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
      (OStmtOut := BinaryBasefold.OracleStatement K βfun
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (pSpec := batchingCorePspecExec κ L K ℓ' 𝓡 ϑ h_ℓ_add_R_rate βfun) :=
  OracleVerifier.append (oSpec := []ₒ)
    (Stmt₁ := BatchingStmtIn (L := L) (ℓ := ℓ))
    (Stmt₂ := Statement (L := L) (ℓ := ℓ') (RingSwitching.RingSwitchingBaseContext κ L K ℓ) 0)
    (Stmt₃ := BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
    (OStmt₁ := (Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn (𝔽q := K)
      (β := βfun) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).OStmtIn)
    (OStmt₂ := (Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn (𝔽q := K)
      (β := βfun) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).OStmtIn)
    (OStmt₃ := BinaryBasefold.OracleStatement K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec₁ := RingSwitching.pSpecBatching κ L K)
    (pSpec₂ := BinaryBasefold.pSpecCoreInteraction K βfun
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₁ := BatchingPhase.batchingOracleVerifier κ L K βcube ℓ ℓ' h_l
      (𝓑 := 𝓑)
      (aOStmtIn := Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn (𝔽q := K)
        (β := βfun) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)))
    (V₂ := coreInteractionOracleVerifier (κ := κ) (L := L) (K := K) (βfun := βfun)
      (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_l := h_l) (𝓑 := 𝓑) mp)

@[reducible]
def batchingCoreVerifier
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (βcube : Basis (Fin κ → Fin 2) K L)
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :=
  batchingCoreVerifierExec (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
    (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
    (𝓑 := 𝓑) βfun βcube mp

/-- Canonical executable batching + core-interaction reduction. -/
private def batchingCoreReductionExec
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (βcube : Basis (Fin κ → Fin 2) K L)
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :
    OracleReduction (oSpec := []ₒ)
      (StmtIn := BatchingStmtIn (L := L) (ℓ := ℓ))
      (OStmtIn := (Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn (𝔽q := K)
        (β := βfun) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).OStmtIn)
      (WitIn := BatchingWitIn L K ℓ ℓ')
      (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
      (OStmtOut := BinaryBasefold.OracleStatement K βfun
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (WitOut := Unit)
      (pSpec := batchingCorePspecExec κ L K ℓ' 𝓡 ϑ h_ℓ_add_R_rate βfun) :=
  OracleReduction.append (oSpec := []ₒ)
    (Stmt₁ := BatchingStmtIn (L := L) (ℓ := ℓ))
    (Stmt₂ := Statement (L := L) (ℓ := ℓ') (RingSwitching.RingSwitchingBaseContext κ L K ℓ) 0)
    (Stmt₃ := BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
    (Wit₁ := BatchingWitIn L K ℓ ℓ')
    (Wit₂ := RingSwitching.SumcheckWitness L ℓ' 0)
    (Wit₃ := Unit)
    (OStmt₁ := (Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn (𝔽q := K)
      (β := βfun) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).OStmtIn)
    (OStmt₂ := (Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn (𝔽q := K)
      (β := βfun) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).OStmtIn)
    (OStmt₃ := BinaryBasefold.OracleStatement K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec₁ := RingSwitching.pSpecBatching κ L K)
    (pSpec₂ := BinaryBasefold.pSpecCoreInteraction K βfun
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (R₁ := BatchingPhase.batchingOracleReduction κ L K βcube ℓ ℓ' h_l
      (𝓑 := 𝓑)
      (aOStmtIn := Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn (𝔽q := K)
        (β := βfun) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)))
    (R₂ := coreInteractionOracleReduction (κ := κ) (L := L) (K := K) (βfun := βfun)
      (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_l := h_l) (𝓑 := 𝓑) mp)

@[reducible]
def batchingCoreReduction
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (βcube : Basis (Fin κ → Fin 2) K L)
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :=
  batchingCoreReductionExec (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
    (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
    (𝓑 := 𝓑) βfun βcube mp

/-- Canonical computable full verifier over explicit executable basis/multiplier inputs. -/
private def fullOracleVerifierExec
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (βcube : Basis (Fin κ → Fin 2) K L)
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :
    OracleVerifier (oSpec := []ₒ)
      (StmtIn := BatchingStmtIn (L := L) (ℓ := ℓ))
      (OStmtIn := (Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn (𝔽q := K)
        (β := βfun) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).OStmtIn)
      (StmtOut := Bool)
      (OStmtOut := fun _ : Empty => Unit)
      (pSpec := fullPspecExec κ L K ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate βfun) :=
  OracleVerifier.append (oSpec := []ₒ)
    (Stmt₁ := BatchingStmtIn (L := L) (ℓ := ℓ))
    (Stmt₂ := BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
    (Stmt₃ := Bool)
    (OStmt₁ := (Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn (𝔽q := K)
      (β := βfun) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := batchingCorePspecExec κ L K ℓ' 𝓡 ϑ h_ℓ_add_R_rate βfun)
    (pSpec₂ := BinaryBasefold.pSpecQuery K βfun γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₁ := batchingCoreVerifierExec (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
      (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)
      βfun βcube mp)
    (V₂ := QueryPhase.queryOracleVerifier K βfun γ_repetitions (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

@[reducible]
def fullOracleVerifier
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (βcube : Basis (Fin κ → Fin 2) K L)
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :=
  fullOracleVerifierExec (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
    (𝓡 := 𝓡) (ϑ := ϑ) (γ_repetitions := γ_repetitions)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)
    βfun βcube mp

/-- Canonical computable full reduction over explicit executable basis/multiplier inputs. -/
private def fullOracleReductionExec
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (βcube : Basis (Fin κ → Fin 2) K L)
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :
    OracleReduction (oSpec := []ₒ)
      (StmtIn := BatchingStmtIn (L := L) (ℓ := ℓ))
      (OStmtIn := (Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn (𝔽q := K)
        (β := βfun) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).OStmtIn)
      (WitIn := BatchingWitIn L K ℓ ℓ')
      (StmtOut := Bool)
      (OStmtOut := fun _ : Empty => Unit)
      (WitOut := Unit)
      (pSpec := fullPspecExec κ L K ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate βfun) :=
  OracleReduction.append (oSpec := []ₒ)
    (Stmt₁ := BatchingStmtIn (L := L) (ℓ := ℓ))
    (Stmt₂ := BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
    (Stmt₃ := Bool)
    (Wit₁ := BatchingWitIn L K ℓ ℓ')
    (Wit₂ := Unit)
    (Wit₃ := Unit)
    (OStmt₁ := (Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn (𝔽q := K)
      (β := βfun) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K βfun
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := batchingCorePspecExec κ L K ℓ' 𝓡 ϑ h_ℓ_add_R_rate βfun)
    (pSpec₂ := BinaryBasefold.pSpecQuery K βfun γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (R₁ := batchingCoreReductionExec (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
      (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)
      βfun βcube mp)
    (R₂ := QueryPhase.queryOracleReduction K βfun γ_repetitions (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

@[reducible]
def fullOracleReduction
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (βcube : Basis (Fin κ → Fin 2) K L)
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :=
  fullOracleReductionExec (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
    (𝓡 := 𝓡) (ϑ := ϑ) (γ_repetitions := γ_repetitions)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)
    βfun βcube mp

/-- Canonical computable full proof over explicit executable basis/multiplier inputs. -/
private def fullOracleProofExec
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (βcube : Basis (Fin κ → Fin 2) K L)
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :
    OracleProof []ₒ
      (Statement := BatchingStmtIn (L := L) (ℓ := ℓ))
      (OStatement := (Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn (𝔽q := K)
        (β := βfun) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).OStmtIn)
      (Witness := BatchingWitIn L K ℓ ℓ')
      (pSpec := fullPspecExec κ L K ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate βfun) :=
  fullOracleReductionExec (κ := κ) (L := L) (K := K) (ℓ := ℓ)
    (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (γ_repetitions := γ_repetitions)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)
    βfun βcube mp

@[reducible]
def fullOracleProof
    (βfun : Fin (2 ^ κ) → L)
    [Fact (LinearIndependent K βfun)] [Fact (βfun 0 = 1)]
    (βcube : Basis (Fin κ → Fin 2) K L)
    (mp : SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ)) :=
  fullOracleProofExec (κ := κ) (L := L) (K := K) (ℓ := ℓ) (ℓ' := ℓ')
    (𝓡 := 𝓡) (ϑ := ϑ) (γ_repetitions := γ_repetitions)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)
    βfun βcube mp

/-!
## Security Properties
-/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

open scoped NNReal

/-- Combined RBR knowledge error for batching + core interaction. -/
noncomputable def batchingCoreRbrKnowledgeError
    (i : (batchingCorePspec κ L K ℓ' 𝓡 ϑ h_ℓ_add_R_rate (fun j => β j)).ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (f := fun _ => RingSwitching.BatchingPhase.batchingRBRKnowledgeError (κ := κ) (L := L))
    (g := fun j => Sum.elim
      (f := BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError K (fun i => β i) (ϑ := ϑ))
      (g := fun i => FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError (L := L) i)
      (ChallengeIdx.sumEquiv.symm j))
    (ChallengeIdx.sumEquiv.symm i)

/-- Combined RBR knowledge error for full FRI-Binius. -/
noncomputable def fullRbrKnowledgeError
    (i : (fullPspec κ L K ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate (fun j => β j)).ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (f := batchingCoreRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (g := QueryPhase.queryRbrKnowledgeError K (fun i => β i) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (ChallengeIdx.sumEquiv.symm i)

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

section CanonicalB

variable (𝓑 : Fin 2 ↪ L)
variable [h_B01 : Fact (𝓑 0 = 0 ∧ 𝓑 1 = 1)]

-- Use the same `bbfAbstractOStmtIn` as exec-path defs, ensuring consistent `OStmtIn` types.
local notation "aOStmtIn" =>
  Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn (𝔽q := K) (β := (fun i => β i))
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)

/-- Perfect completeness for the full Binary Basefold protocol (reduction) -/
theorem fullOracleReduction_perfectCompleteness
    (hInit : NeverFail init) :
  OracleReduction.perfectCompleteness
    (oracleReduction :=
      fullOracleReduction (κ := κ) (L := L) (K := K) (ℓ := ℓ)
        (ℓ' := ℓ') (ϑ := ϑ) (γ_repetitions := γ_repetitions)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)
        (βfun := fun i => β i)
        (βcube := booleanHypercubeBasis κ L K β)
        (mp := RingSwitching_SumcheckMultParam κ L K
          (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l))
    (relIn := BatchingPhase.strictBatchingInputRelation κ L K
      (β := booleanHypercubeBasis κ L K β)
      ℓ ℓ' h_l aOStmtIn)
    (relOut := acceptRejectOracleRel)
    (init := init)
    (impl := impl) := sorry

open FRIBinius.CoreInteractionPhase in
/-- Round-by-round knowledge soundness for the full FRI-Binius oracle verifier. -/
theorem fullOracleVerifier_rbrKnowledgeSoundness :
  (fullOracleVerifier (κ := κ) (L := L) (K := K) (ℓ := ℓ)
    (ℓ' := ℓ') (ϑ := ϑ) (γ_repetitions := γ_repetitions)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)
    (βfun := fun i => β i)
    (βcube := booleanHypercubeBasis κ L K β)
    (mp := RingSwitching_SumcheckMultParam κ L K
      (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
    ).rbrKnowledgeSoundness init impl
    (relIn := BatchingPhase.batchingInputRelation κ L K
      (β := booleanHypercubeBasis κ L K β)
      ℓ ℓ' h_l aOStmtIn)
    (relOut := acceptRejectOracleRel)
    (rbrKnowledgeError := fullRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by sorry

/-- `∑ᵢ εᵢ` for the full verifier is at most **DP24 §5.2 eq. (43)**. -/
theorem fullRbrKnowledgeError_sum_le_concrete :
    (∑ i : (fullPspec κ L K ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate (fun j => β j)).ChallengeIdx,
      fullRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate i)
    ≤ concreteFRIBiniusKnowledgeError κ L ℓ' 𝓡 γ_repetitions := by sorry

/-- Scalar KS for the full stack with error **`concreteFRIBiniusKnowledgeError`**,
i.e. **DP24 §5.2 (43)** / **Construction 5.1** concrete soundness. -/
theorem fullOracleVerifier_knowledgeSoundness :
    (fullOracleVerifier (κ := κ) (L := L) (K := K) (ℓ := ℓ)
      (ℓ' := ℓ') (ϑ := ϑ) (γ_repetitions := γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)
      (βfun := fun i => β i)
      (βcube := booleanHypercubeBasis κ L K β)
      (mp := RingSwitching_SumcheckMultParam κ L K
        (β := booleanHypercubeBasis κ L K β) ℓ ℓ' h_l)
    ).toVerifier.knowledgeSoundness
      init impl
    (relIn := BatchingPhase.batchingInputRelation κ L K
      (booleanHypercubeBasis κ L K β) ℓ ℓ' h_l aOStmtIn)
    (relOut := acceptRejectOracleRel)
    (knowledgeError := concreteFRIBiniusKnowledgeError κ L ℓ' 𝓡 γ_repetitions) := by sorry

end CanonicalB

end
end Binius.FRIBinius.FullFRIBinius
