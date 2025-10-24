/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.RingSwitching.Spec
import ArkLib.ProofSystem.Binius.RingSwitching.BatchingPhase
import ArkLib.ProofSystem.Binius.RingSwitching.SumcheckPhase
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# Full Ring-Switching Protocol

This module contains specifications and security properties for the full
ring-switching protocol. The protocol is a sequential composition of:
1. **Batching Phase** (polynomial packing and batching via tensor algebra operations)
2. **Sumcheck Phase** (ℓ' rounds of sumcheck, and the final sumcheck step)
3. **Large Field Invocation** (invocation to underlying large-field IOPCS)

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive (2024).
-/

namespace Binius.RingSwitching.FullRingSwitching
noncomputable section
open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Module

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SelectableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (β : Basis (Fin κ → Fin 2) K L)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable {𝓑 : Fin 2 ↪ L}
variable (mlIOPCS : MLIOPCS L ℓ')

def batchingCoreVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:= BatchingPhase.oracleVerifier κ L K β ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (pSpec₁:=pSpecBatching κ L K)
    (V₂:=SumcheckPhase.coreInteractionOracleVerifier κ L K β ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (pSpec₂:=pSpecCoreInteraction L ℓ')

/-- The oracle verifier for the full Binary Basefold protocol -/
@[reducible]
def fullOracleVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:=batchingCoreVerifier κ L K β ℓ ℓ' h_l mlIOPCS)
    (pSpec₁:=pSpecLargeFieldReduction κ L K ℓ')
    (V₂:=mlIOPCS.oracleReduction.verifier)
    (pSpec₂:=mlIOPCS.pSpec)

def batchingCoreReduction :=
  OracleReduction.append
    (R₁ := BatchingPhase.batchingOracleReduction κ L K β ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (pSpec₁:=pSpecBatching κ L K)
    (R₂ := SumcheckPhase.coreInteractionOracleReduction κ L K β ℓ ℓ' h_l
      (𝓑 := 𝓑) mlIOPCS.toAbstractOStmtIn)
    (pSpec₂:=pSpecCoreInteraction L ℓ')

/-- The reduction for the full Binary Basefold protocol -/
@[reducible]
def fullOracleReduction :
  OracleReduction (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn (L:=L) (ℓ := ℓ)) (StmtOut := Bool)
    (OStmtIn:= mlIOPCS.OStmtIn)
    (OStmtOut := fun _ : Empty => Unit)
    (pSpec := fullPspec κ L K ℓ' mlIOPCS)
    (WitIn := BatchingWitIn (L:=L) (K:=K) (ℓ := ℓ) (ℓ' := ℓ')) (WitOut := Unit)
    :=
  (batchingCoreReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) mlIOPCS).append mlIOPCS.oracleReduction

/-- The full Binary Basefold protocol as a Proof -/
@[reducible]
def fullOracleProof :
  OracleProof []ₒ
    (Statement := BatchingStmtIn (L:=L) (ℓ := ℓ))
    (OStatement := mlIOPCS.OStmtIn)
    (Witness := BatchingWitIn (L:=L) (K:=K) (ℓ := ℓ) (ℓ' := ℓ'))
    (pSpec:= fullPspec κ L K ℓ' mlIOPCS) :=
    fullOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) mlIOPCS

/-!
## Security Properties
-/

variable [∀ i, SelectableType (mlIOPCS.pSpec.Challenge i)]

/-- Input relation for the full ring-switching protocol -/
abbrev fullInputRelation := BatchingPhase.batchingInputRelation κ L K β ℓ ℓ'
  h_l mlIOPCS.toAbstractOStmtIn
abbrev fullOutputRelation := acceptRejectOracleRel

open scoped NNReal

section SecurityProperties
variable {σ : Type} (init : ProbComp σ) {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [(i : mlIOPCS.pSpec.ChallengeIdx) → SelectableType (mlIOPCS.pSpec.Challenge i)] in
lemma batchingCore_perfectCompleteness (hInit : init.neverFails) :
  (batchingCoreReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) mlIOPCS).perfectCompleteness
  (pSpec := pSpecLargeFieldReduction κ L K ℓ')
  (relIn := BatchingPhase.batchingInputRelation κ L K β ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
  (relOut := mlIOPCS.toRelInput)
  (init:=init) (impl:=impl) := by
  apply OracleReduction.append_perfectCompleteness
  · exact BatchingPhase.batchingReduction_perfectCompleteness κ L K β ℓ ℓ' h_l
      (𝓑 := 𝓑) mlIOPCS.toAbstractOStmtIn hInit
  · exact SumcheckPhase.coreInteraction_perfectCompleteness
      κ L K β ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn hInit (impl:=impl)

omit [(i : mlIOPCS.pSpec.ChallengeIdx) → SelectableType (mlIOPCS.pSpec.Challenge i)] in
theorem fullOracleReduction_perfectCompleteness (hInit : init.neverFails) :
  (fullOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) mlIOPCS).perfectCompleteness
    (relIn := BatchingPhase.batchingInputRelation κ L K β ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (relOut := acceptRejectOracleRel)
    (init := init)
    (impl := impl)
     := by
  apply OracleReduction.append_perfectCompleteness (Oₛ₃:=by
    exact fun _ ↦ OracleInterface.instDefault)
  · exact batchingCore_perfectCompleteness κ L K β ℓ ℓ' h_l mlIOPCS init hInit
  · exact mlIOPCS.perfectCompleteness hInit

def batchingCoreRbrKnowledgeError
    (i : (pSpecBatching κ L K ++ₚ pSpecCoreInteraction L ℓ').ChallengeIdx) : ℝ≥0 :=
  Sum.elim (f:=BatchingPhase.batchingRBRKnowledgeError κ L K)
    (g:=SumcheckPhase.coreInteractionRbrKnowledgeError L ℓ')
    (ChallengeIdx.sumEquiv.symm i)

def fullRbrKnowledgeError (i : (fullPspec κ L K ℓ' mlIOPCS).ChallengeIdx) : ℝ≥0
  := Sum.elim (f:=batchingCoreRbrKnowledgeError κ L K ℓ')
  (g:=mlIOPCS.rbrKnowledgeError)
  (ChallengeIdx.sumEquiv.symm i)

variable [SelectableType L]

/-- Round-by-round knowledge soundness for the full ring-switching oracle verifier -/
theorem fullOracleVerifier_rbrKnowledgeSoundness {𝓑 : Fin 2 ↪ L} :
  OracleVerifier.rbrKnowledgeSoundness
    (verifier := fullOracleVerifier κ L K β ℓ ℓ' h_l mlIOPCS)
    (init := init)
    (impl := impl)
    (relIn := fullInputRelation κ L K β ℓ ℓ' h_l mlIOPCS)
    (relOut := fullOutputRelation)
    (rbrKnowledgeError := fun i => fullRbrKnowledgeError κ L K ℓ' mlIOPCS i) := by
  unfold fullOracleVerifier fullRbrKnowledgeError
  have batchInteractionRBRKS :=
    OracleVerifier.append_rbrKnowledgeSoundness (init:=init) (impl:=impl)
    (rel₁:=fullInputRelation κ L K β ℓ ℓ' h_l mlIOPCS)
    (rel₂:=sumcheckRoundRelation κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) mlIOPCS.toAbstractOStmtIn 0)
    (rel₃:=mlIOPCS.toRelInput)
    (V₁:=BatchingPhase.oracleVerifier κ L K β ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (V₂:=SumcheckPhase.coreInteractionOracleVerifier κ L K β ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (rbrKnowledgeError₁:=BatchingPhase.batchingRBRKnowledgeError κ L K)
    (rbrKnowledgeError₂:=SumcheckPhase.coreInteractionRbrKnowledgeError L ℓ')
    (h₁:=BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundness κ L K β ℓ
      ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (h₂:=SumcheckPhase.coreInteraction_rbrKnowledgeSoundness κ L K β ℓ ℓ' h_l
      mlIOPCS.toAbstractOStmtIn)

  have res :=
    OracleVerifier.append_rbrKnowledgeSoundness (init:=init) (impl:=impl)
    (rel₁:=fullInputRelation κ L K β ℓ ℓ' h_l mlIOPCS)
    (rel₂:=mlIOPCS.toRelInput)
    (rel₃:=fullOutputRelation)
    (V₁:=batchingCoreVerifier κ L K β ℓ ℓ' h_l mlIOPCS)
    (V₂:=mlIOPCS.oracleReduction.verifier)
    (Oₛ₃:=by exact fun i ↦ OracleInterface.instDefault)
    (rbrKnowledgeError₁:=batchingCoreRbrKnowledgeError κ L K ℓ')
    (rbrKnowledgeError₂:=mlIOPCS.rbrKnowledgeError)
    (h₁:=batchInteractionRBRKS) (h₂:=by
      convert mlIOPCS.rbrKnowledgeSoundness (L:=L) (ℓ' := ℓ') (init:=init) (impl:=impl)
      · sorry
    )
  convert res
  · simp only [ChallengeIdx, Challenge, instSelectableTypeChallengeFullPspec]
    sorry

end SecurityProperties
end
end Binius.RingSwitching.FullRingSwitching
