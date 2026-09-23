/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
public import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase
public import ArkLib.ProofSystem.Binius.FRIBinius.CoreInteractionPhase
public import ArkLib.ProofSystem.RingSwitching.Packing.BatchingPhase

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

This initial development assumes `ϑ ∣ ℓ'`. DP24 §5.2's early-termination variant removes that
notational-convenience assumption. TODO: formalize that variant.
-/

@[expose] public section

namespace Binius.FRIBinius.FullFRIBinius
noncomputable section

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Module
  Binius
open Binius.BinaryBasefold _root_.RingSwitching

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
variable [hdiv : Fact (ϑ ∣ ℓ')]

/-- The shared concrete tensor profile used by the batching and core-interaction phases. -/
abbrev biniusProfile : RingSwitching.RingSwitchingProfile K L κ :=
  Binius.FRIBinius.bbfSumcheckProfile κ L K (booleanHypercubeBasis κ L K β)

section Pspec

@[reducible] def batchingCorePspec :=
  (RingSwitching.pSpecBatching κ L K (biniusProfile κ L K β)) ++ₚ
  (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

@[reducible] def fullPspec := (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) ++ₚ
  (BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance : ∀ j, OracleInterface ((batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).Message j) :=
  instOracleInterfaceMessageAppend
    (pSpec₁ := RingSwitching.pSpecBatching κ L K (biniusProfile κ L K β))
    (pSpec₂ := BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance : ∀ j, SampleableType ((batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).Challenge j) :=
  instSampleableTypeChallengeAppend
    (pSpec₁ := RingSwitching.pSpecBatching κ L K (biniusProfile κ L K β))
    (pSpec₂ := BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

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
    (V₁:= RingSwitching.BatchingPhase.oracleVerifier κ L K (biniusProfile κ L K β)
      ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
    (pSpec₁ := RingSwitching.pSpecBatching κ L K (biniusProfile κ L K β))
    (pSpec₂:=BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₃ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (V₂:= FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier κ L K
      β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l )

def batchingCoreReduction :=
  OracleReduction.append (oSpec:=[]ₒ)
    (R₁ := RingSwitching.BatchingPhase.batchingOracleReduction κ L K
      (biniusProfile κ L K β) ℓ ℓ' h_l
      (aOStmtIn := BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
    (pSpec₁ := RingSwitching.pSpecBatching κ L K (biniusProfile κ L K β))
    (pSpec₂:=BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₃ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (R₂ := FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction κ L K
      β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l )

/-- The oracle verifier for the full Binary Basefold protocol -/
@[reducible]
noncomputable def fullOracleVerifier :
  OracleProofVerifier (oSpec:=[]ₒ)
    (Statement := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStatement := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ
      h_ℓ_add_R_rate).OStmtIn)
    (pSpec := fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (Stmt₁ := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (Stmt₂ := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (Stmt₃ := Bool)
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (Oₛ₃ := fun i : Empty => nomatch i)
    (V₁ := batchingCoreVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l )
    (V₂ := QueryPhase.queryOracleVerifier K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))

/-- The reduction for the full Binary Basefold protocol -/
@[reducible]
noncomputable def fullOracleReduction :
  OracleProof (oSpec:=[]ₒ)
    (Statement := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStatement := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ
      h_ℓ_add_R_rate).OStmtIn)
    (Witness := BatchingWitIn L K ℓ ℓ')
    (pSpec := fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleReduction.append (oSpec:=[]ₒ)
    (Stmt₁ := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (Stmt₂ := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (Stmt₃ := Bool)
    (Wit₁ := BatchingWitIn L K ℓ ℓ')
    (Wit₂ := Unit)
    (Wit₃ := Unit)
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (Oₛ₃ := fun i : Empty => nomatch i)
    (R₁ := batchingCoreReduction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
    )
    (R₂ := QueryPhase.queryOracleReduction K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))

/-- The full Binary Basefold protocol as a Proof -/
@[reducible]
noncomputable def fullOracleProof :
  OracleProof []ₒ
    (Statement := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStatement := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
    (Witness := BatchingWitIn L K ℓ ℓ')
    (pSpec:= fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  fullOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l

/-!
## Security Properties
-/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- The full FRI-Binius oracle proof is perfectly complete on honest, exact oracle inputs.
Knowledge soundness below retains the relaxed decoding-proximity relation. -/
theorem fullOracleReduction_perfectCompleteness :
    OracleProof.perfectCompleteness
      (oracleProof := fullOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l )
      (relation := BatchingPhase.strictBatchingInputRelation κ L K (biniusProfile κ L K β)
        ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
      (init := init)
      (impl := impl) :=
  OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (R₁ := batchingCoreReduction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l )
    (R₂ := QueryPhase.queryOracleReduction K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := fun _ : Empty => Unit)
    (Oₛ₁:= (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).Oₛᵢ)
    (Oₛ₂:=Binius.BinaryBasefold.instOracleStatementBinaryBasefold K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (i := Fin.last ℓ'))
    (Oₛ₃ := fun i : Empty => nomatch i)
    (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (rel₁ := BatchingPhase.strictBatchingInputRelation κ L K (biniusProfile κ L K β)
      ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
    (rel₂ := BinaryBasefold.strictFinalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (rel₃ := acceptRejectOracleRel)
    (V₁ := Verifier.GuardedForm.ofEmpty _ (fun _ =>
      (⟨⟨0, fun _ => 0, ⟨0, 0⟩⟩, 0⟩, fun _ _ => 0)))
    (V₂ := Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i => nomatch i)))
    (hSeam := fun _ => Or.inl inferInstance)
    (h₁ := by
      apply OracleReduction.append_perfectCompleteness_of_guarded_verifiers
        (rel₁ := BatchingPhase.strictBatchingInputRelation κ L K (biniusProfile κ L K β)
          ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
        (rel₂ := RingSwitching.strictSumcheckRoundRelation κ L K (biniusProfile κ L K β)
        ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn κ L K β ℓ'
          𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
        (rel₃ := BinaryBasefold.strictFinalSumcheckRelOut K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (V₁ := Verifier.GuardedForm.ofEmpty _ (fun input =>
          (⟨0, fun _ => 0,
            ⟨⟨input.1.t_eval_point, input.1.original_claim⟩, 0, 0⟩⟩, input.2)))
        (V₂ := Verifier.GuardedForm.ofEmpty _ (fun _ =>
          (⟨⟨0, fun _ => 0, ⟨0, 0⟩⟩, 0⟩, fun _ _ => 0)))
        (hSeam := fun _ => Or.inl inferInstance)
      · apply BatchingPhase.batchingReduction_perfectCompleteness κ L K
          (biniusProfile κ L K β) ℓ ℓ' h_l
          (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).strictView
          (hCoord := bbfSumcheckProfile_coordinateLaws κ L K (booleanHypercubeBasis κ L K β))
      · intro s
        apply CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness
          κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
        infer_instance
    )
    (h₂ := fun s => QueryPhase.queryOracleProof_perfectCompleteness K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ) (pure s) (by infer_instance) impl)

open scoped NNReal

/-- Combined RBR knowledge error for batching + core interaction. -/
def batchingCoreRbrKnowledgeError
    (i : (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (f := RingSwitching.BatchingPhase.batchingRBRKnowledgeError
      (κ := κ) (L := L) (K := K) (P := biniusProfile κ L K β))
    (g := FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError
      κ L K β ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
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
/-- RBR-KS for the batching + core-interaction sub-reduction (batching ++ core), composed via
`OracleVerifier.append_rbrKnowledgeSoundness` along the seam
`batchingInputRelation → sumcheckRoundRelation 0 → finalSumcheckRelOut`. -/
theorem batchingCoreVerifier_rbrKnowledgeSoundness :
    (batchingCoreVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l).rbrKnowledgeSoundness init impl
    (relIn := BatchingPhase.batchingInputRelation κ L K (biniusProfile κ L K β)
      ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
    (relOut := BinaryBasefold.finalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (rbrKnowledgeError := batchingCoreRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) := by
  unfold batchingCoreVerifier batchingCoreRbrKnowledgeError
  exact OracleVerifier.append_rbrKnowledgeSoundness
    (oSpec := []ₒ) (init := init) (impl := impl)
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₃ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (Wit₁ := BatchingWitIn L K ℓ ℓ')
    (Wit₂ := SumcheckWitness L ℓ' 0)
    (Wit₃ := Unit)
    (rel₁ := BatchingPhase.batchingInputRelation κ L K (biniusProfile κ L K β)
      ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
    (rel₂ := RingSwitching.sumcheckRoundRelation κ L K (biniusProfile κ L K β)
      ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) 0)
    (rel₃ := BinaryBasefold.finalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₁ := RingSwitching.BatchingPhase.oracleVerifier κ L K (biniusProfile κ L K β)
      ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
    (V₂ := coreInteractionOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l)
    (Oₛ₃ := Binius.BinaryBasefold.instOracleStatementBinaryBasefold K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (i := Fin.last ℓ'))
    (rbrKnowledgeError₁ := RingSwitching.BatchingPhase.batchingRBRKnowledgeError
      (κ := κ) (L := L) (K := K) (P := biniusProfile κ L K β))
    (rbrKnowledgeError₂ := coreInteractionOracleRbrKnowledgeError
      κ L K β ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (h₁ := RingSwitching.BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundness
      (κ := κ) (L := L) (K := K) (P := biniusProfile κ L K β)
      (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
      (hCoord := bbfSumcheckProfile_coordinateLaws κ L K (booleanHypercubeBasis κ L K β))
      (hUnique := Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn_functional K β))
    (h₂ := coreInteractionOracleVerifier_rbrKnowledgeSoundness
      (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

/-- Round-by-round knowledge soundness for the full FRI-Binius oracle verifier.

Composes the three phase RBR-KS theorems along the (non-strict) seam relations
`batchingInputRelation → sumcheckRoundRelation 0 → finalSumcheckRelOut → acceptRejectOracleRel`
via `OracleVerifier.append_rbrKnowledgeSoundness` (nested: batching ++ core, then ++ query):
`BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundness`,
`CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness`, and
`QueryPhase.queryOracleVerifier_rbrKnowledgeSoundness`. -/
theorem fullOracleVerifier_rbrKnowledgeSoundness :
    (fullOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l).rbrKnowledgeSoundness
    (Oₛₒ := fun i : Empty => nomatch i) init impl
    (relIn := BatchingPhase.batchingInputRelation κ L K (biniusProfile κ L K β)
      ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
    (relOut := acceptRejectOracleRel)
    (rbrKnowledgeError := fullRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  unfold fullOracleVerifier fullRbrKnowledgeError
  exact OracleVerifier.append_rbrKnowledgeSoundness
    (oSpec := []ₒ) (init := init) (impl := impl)
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := fun _ : Empty => Unit)
    (Wit₁ := BatchingWitIn L K ℓ ℓ')
    (Wit₂ := Unit)
    (Wit₃ := Unit)
    (rel₁ := BatchingPhase.batchingInputRelation κ L K (biniusProfile κ L K β)
      ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
    (rel₂ := BinaryBasefold.finalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (rel₃ := acceptRejectOracleRel)
    (V₁ := batchingCoreVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l)
    (V₂ := QueryPhase.queryOracleVerifier K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ))
    (Oₛ₃ := fun i : Empty => nomatch i)
    (rbrKnowledgeError₁ := batchingCoreRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (rbrKnowledgeError₂ := QueryPhase.queryRbrKnowledgeError K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (h₁ := batchingCoreVerifier_rbrKnowledgeSoundness κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l)
    (h₂ := QueryPhase.queryOracleVerifier_rbrKnowledgeSoundness K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) init impl)

/-!
## Concrete Knowledge Soundness Error (DP24 §5.2 eq. (43) / Construction 5.1)

Closed form: `(κ + 2·ℓ')/|L| + 2^(ℓ'+𝓡)/|L| + (1/2 + 1/(2·2^𝓡))^γ`, decomposed as
ring-switching batching (`κ/|L|`), core-interaction sumcheck + fold
(`2·ℓ'/|L| + 2^(ℓ'+𝓡)/|L|`, Props 4.23), and query-phase proximity (`(…)^γ`, Prop 4.24).
This formalization proves the stronger knowledge-soundness statement with the same scalar through
explicit round-by-round extractors for its phases; DP24 is cited here for the numerical bound. -/

/-- Single-repetition proximity testing error `1/2 + 1/(2·2^𝓡)` (third factor of DP24 §5.2 (43)). -/
def querySingleRepetitionError : ℝ≥0 :=
  (1 / 2 : ℝ≥0) + 1 / (2 * 2 ^ 𝓡)

/-- Concrete KS upper bound for full FRI-Binius (DP24 §5.2 eq. (43) / Construction 5.1). -/
def concreteFRIBiniusKnowledgeError : ℝ≥0 :=
  ((κ : ℝ≥0) + 2 * (ℓ' : ℝ≥0)) / (Fintype.card L : ℝ≥0)
    + (2 ^ (ℓ' + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0)
    + querySingleRepetitionError (𝓡 := 𝓡) ^ γ_repetitions

omit [DecidableEq K] [CharP L 2] h_β₀_eq_1 in
/-- `∑ᵢ εᵢ` for the full verifier is at most the concrete DP24 §5.2 (43) bound. -/
theorem fullRbrKnowledgeError_sum_le_concrete :
    (∑ i : (fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate).ChallengeIdx,
      fullRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate i)
    ≤ concreteFRIBiniusKnowledgeError κ L ℓ' 𝓡 γ_repetitions := by
  classical
  have h_full :
      (∑ i : (fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate).ChallengeIdx,
        fullRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate i)
      =
      (∑ i : (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).ChallengeIdx,
        batchingCoreRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate i)
      + (∑ i : (BinaryBasefold.pSpecQuery K β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        QueryPhase.queryRbrKnowledgeError K β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
    unfold fullRbrKnowledgeError
    let f :
        ((batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).ChallengeIdx
          ⊕ (BinaryBasefold.pSpecQuery K β γ_repetitions
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) → ℝ≥0 :=
      Sum.elim
        (batchingCoreRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
        (QueryPhase.queryRbrKnowledgeError K β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    change (∑ i : (fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate).ChallengeIdx,
        f (ChallengeIdx.sumEquiv.symm i))
      =
      (∑ i : (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).ChallengeIdx,
        batchingCoreRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate i)
      + (∑ i : (BinaryBasefold.pSpecQuery K β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        QueryPhase.queryRbrKnowledgeError K β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    rw [Equiv.sum_comp (e := Equiv.symm ChallengeIdx.sumEquiv) (g := f)]
    rw [Fintype.sum_sum_type]
    simp only [f, Sum.elim_inl, Sum.elim_inr]
  rw [h_full]
  have h_batchingCore :
      (∑ i : (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).ChallengeIdx,
        batchingCoreRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate i)
        =
      (∑ i : (RingSwitching.pSpecBatching κ L K (biniusProfile κ L K β)).ChallengeIdx,
        RingSwitching.BatchingPhase.batchingRBRKnowledgeError
          (κ := κ) (L := L) (K := K) (P := biniusProfile κ L K β) i)
        +
      (∑ i : (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ
          h_ℓ_add_R_rate i) := by
    unfold batchingCoreRbrKnowledgeError
    let f :
        ((RingSwitching.pSpecBatching κ L K (biniusProfile κ L K β)).ChallengeIdx
          ⊕ (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) → ℝ≥0 :=
      Sum.elim
        (RingSwitching.BatchingPhase.batchingRBRKnowledgeError
          (κ := κ) (L := L) (K := K) (P := biniusProfile κ L K β))
        (FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ
          h_ℓ_add_R_rate)
    change (∑ i : (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).ChallengeIdx,
        f (ChallengeIdx.sumEquiv.symm i)) = _
    rw [Equiv.sum_comp (e := Equiv.symm ChallengeIdx.sumEquiv) (g := f)]
    rw [Fintype.sum_sum_type]
    simp only [f, Sum.elim_inl, Sum.elim_inr]
  rw [h_batchingCore]
  have h_batching :
      (∑ i : (RingSwitching.pSpecBatching κ L K (biniusProfile κ L K β)).ChallengeIdx,
        RingSwitching.BatchingPhase.batchingRBRKnowledgeError
          (κ := κ) (L := L) (K := K) (P := biniusProfile κ L K β) i)
      = (κ : ℝ≥0) / (Fintype.card L : ℝ≥0) := by
    rw [Fintype.sum_eq_single (⟨1, rfl⟩ :
      (RingSwitching.pSpecBatching κ L K (biniusProfile κ L K β)).ChallengeIdx)]
    · simp [RingSwitching.BatchingPhase.batchingRBRKnowledgeError]
    · rintro ⟨i, hi⟩ hne
      fin_cases i
      · simp at hi
      · exact absurd (Subtype.ext rfl) hne
  rw [h_batching]
  have h_core_le :
      (∑ i : (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ
          h_ℓ_add_R_rate i)
      ≤ 2 * (ℓ' : ℝ≥0) / (Fintype.card L : ℝ≥0)
          + (2 ^ (ℓ' + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0) :=
    FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError_le
      (κ := κ) (L := L) (K := K) (β := β) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  have h_query :
      (∑ i : (BinaryBasefold.pSpecQuery K β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        QueryPhase.queryRbrKnowledgeError K β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      = querySingleRepetitionError (𝓡 := 𝓡) ^ γ_repetitions := by
    simp [QueryPhase.queryRbrKnowledgeError, QueryPhase.queryRbrKnowledgeError_singleRepetition,
      querySingleRepetitionError, BinaryBasefold.pSpecQuery, ChallengeIdx]
  calc
    (κ : ℝ≥0) / (Fintype.card L : ℝ≥0)
        + (∑ i : (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
            FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ
              h_ℓ_add_R_rate i)
        + (∑ i : (BinaryBasefold.pSpecQuery K β γ_repetitions
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
            QueryPhase.queryRbrKnowledgeError K β γ_repetitions
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      ≤ (κ : ℝ≥0) / (Fintype.card L : ℝ≥0)
          + (2 * (ℓ' : ℝ≥0) / (Fintype.card L : ℝ≥0)
              + (2 ^ (ℓ' + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0))
          + querySingleRepetitionError (𝓡 := 𝓡) ^ γ_repetitions :=
        add_le_add (add_le_add (le_refl _) h_core_le) (le_of_eq h_query)
    _ = concreteFRIBiniusKnowledgeError κ L ℓ' 𝓡 γ_repetitions := by
        rw [concreteFRIBiniusKnowledgeError, add_div]; ring

/-- Scalar knowledge soundness for the full FRI-Binius stack with the concrete DP24 §5.2 eq. (43)
error `concreteFRIBiniusKnowledgeError`.  Lifts `fullOracleVerifier_rbrKnowledgeSoundness` to plain
KS (`rbrKnowledgeSoundness_implies_knowledgeSoundness`) and inflates `∑ᵢ εᵢ` to the concrete bound
via `knowledgeSoundness_error_mono` and `fullRbrKnowledgeError_sum_le_concrete`. -/
theorem fullOracleVerifier_knowledgeSoundness :
    (OracleVerifier.toVerifier (Oₛₒ := fun i : Empty => nomatch i)
      (fullOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)).knowledgeSoundness init impl
    (relIn := BatchingPhase.batchingInputRelation κ L K (biniusProfile κ L K β) ℓ ℓ' h_l
      (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
    (relOut := acceptRejectOracleRel)
    (knowledgeError := concreteFRIBiniusKnowledgeError κ L ℓ' 𝓡 γ_repetitions) := by
  let relInFull := BatchingPhase.batchingInputRelation κ L K (biniusProfile κ L K β) ℓ ℓ' h_l
    (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
  let fullV := fullOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l
  let plainV := OracleVerifier.toVerifier (Oₛₒ := fun i : Empty => nomatch i) fullV
  let εFull := fullRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  have h_rbr : plainV.rbrKnowledgeSoundness init impl relInFull
      acceptRejectOracleRel εFull := by
    change OracleVerifier.rbrKnowledgeSoundness (Oₛₒ := fun i : Empty => nomatch i)
      init impl relInFull acceptRejectOracleRel
      fullV εFull
    exact fullOracleVerifier_rbrKnowledgeSoundness
      (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
      (γ_repetitions := γ_repetitions) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
      (init := init) (impl := impl)
  have h_ks : plainV.knowledgeSoundness init impl relInFull acceptRejectOracleRel
      (∑ i, εFull i) :=
    (Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness (init := init) (impl := impl)
      relInFull acceptRejectOracleRel plainV εFull) h_rbr
  exact Verifier.knowledgeSoundness_error_mono
    (init := init) (impl := impl)
    (hε := fullRbrKnowledgeError_sum_le_concrete (κ := κ) (L := L) (K := K) (β := β)
      (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (γ_repetitions := γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    h_ks

end
end Binius.FRIBinius.FullFRIBinius
