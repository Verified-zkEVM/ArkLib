/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.RingSwitching.Spec
import ArkLib.ProofSystem.Binius.RingSwitching.BatchingPhase
import ArkLib.ProofSystem.Binius.RingSwitching.SumcheckPhase
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Security.Implications
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
  Statement numbering follows the archived revision of [DP24].
-/

namespace Binius.RingSwitching.FullRingSwitching
section
open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Module

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (β : Basis (Fin κ → Fin 2) K L)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable {𝓑 : Fin 2 ↪ L}
variable (mlIOPCS : MLIOPCS L ℓ')

def batchingCoreVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:= BatchingPhase.batchingOracleVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) mlIOPCS.toAbstractOStmtIn)
    (pSpec₁:=pSpecBatching κ L K)
    (V₂:=SumcheckPhase.coreInteractionOracleVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑)
      mlIOPCS.toAbstractOStmtIn)
    (pSpec₂:=pSpecCoreInteraction L ℓ')

/-- The oracle verifier for the full Binary Basefold protocol -/
@[reducible]
def fullOracleVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:=batchingCoreVerifier κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) mlIOPCS)
    (pSpec₁:=pSpecLargeFieldReduction κ L K ℓ')
    (V₂:=mlIOPCS.oracleReduction.verifier)
    (pSpec₂:=mlIOPCS.pSpec)

def batchingCoreReduction :=
  OracleReduction.append
    (R₁ := BatchingPhase.batchingOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑)
      mlIOPCS.toAbstractOStmtIn)
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

variable [∀ i, SampleableType (mlIOPCS.pSpec.Challenge i)]

open scoped NNReal

section SecurityProperties
variable {σ : Type} (init : ProbComp σ) {impl : QueryImpl []ₒ (StateT σ ProbComp)}

section CanonicalB

variable [h_B01 : Fact (𝓑 0 = 0 ∧ 𝓑 1 = 1)]

omit [∀ i, SampleableType (mlIOPCS.pSpec.Challenge i)] in
lemma batchingCore_perfectCompleteness (hInit : NeverFail init) :
  (batchingCoreReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) mlIOPCS).perfectCompleteness
  (pSpec := pSpecLargeFieldReduction κ L K ℓ')
  (relIn := BatchingPhase.strictBatchingInputRelation κ L K β ℓ ℓ' h_l
    mlIOPCS.toAbstractOStmtIn)
  (relOut := mlIOPCS.toStrictRelInput)
  (init:=init) (impl:=impl) := by
  apply OracleReduction.append_perfectCompleteness
  · exact BatchingPhase.batchingReduction_perfectCompleteness (hInit:=hInit) κ L K β ℓ ℓ' h_l
      (𝓑 := 𝓑) mlIOPCS.toAbstractOStmtIn
  · exact SumcheckPhase.coreInteraction_perfectCompleteness
      (hInit:=hInit) κ L K β ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn (impl:=impl)

omit [∀ i, SampleableType (mlIOPCS.pSpec.Challenge i)] in
theorem fullOracleReduction_perfectCompleteness (hInit : NeverFail init) :
  (fullOracleReduction κ L K β ℓ ℓ' h_l (𝓑 := 𝓑) mlIOPCS).perfectCompleteness
    (relIn := BatchingPhase.strictBatchingInputRelation κ L K β ℓ ℓ' h_l
      mlIOPCS.toAbstractOStmtIn)
    (relOut := acceptRejectOracleRel)
    (init := init)
    (impl := impl)
     := by
  apply OracleReduction.append_perfectCompleteness (Oₛ₃:=by
    exact fun _ ↦ OracleInterface.instDefault)
  · exact batchingCore_perfectCompleteness κ L K β ℓ ℓ' h_l
      (𝓑 := 𝓑) mlIOPCS init (hInit := hInit) (impl := impl)
  · exact mlIOPCS.strictPerfectCompleteness hInit

noncomputable def batchingCoreRbrKnowledgeError
    (i : (pSpecBatching κ L K ++ₚ pSpecCoreInteraction L ℓ').ChallengeIdx) : ℝ≥0 :=
  Sum.elim (f:=fun _ => BatchingPhase.batchingRBRKnowledgeError (κ:=κ) (L:=L))
    (g:=SumcheckPhase.coreInteractionRbrKnowledgeError L ℓ')
    (ChallengeIdx.sumEquiv.symm i)

noncomputable def fullRbrKnowledgeError (i : (fullPspec κ L K ℓ' mlIOPCS).ChallengeIdx) : ℝ≥0
  := Sum.elim (f:=batchingCoreRbrKnowledgeError κ L K ℓ')
  (g:=mlIOPCS.rbrKnowledgeError)
  (ChallengeIdx.sumEquiv.symm i)

omit [∀ i, SampleableType (mlIOPCS.pSpec.Challenge i)] in
/-- Round-by-round knowledge soundness for the full ring-switching oracle verifier -/
theorem fullOracleVerifier_rbrKnowledgeSoundness :
  OracleVerifier.rbrKnowledgeSoundness
    (verifier := fullOracleVerifier κ L K β ℓ ℓ' (𝓑 := 𝓑) h_l mlIOPCS)
    (init := init)
    (impl := impl)
    (relIn := BatchingPhase.batchingInputRelation κ L K β ℓ ℓ'
  h_l mlIOPCS.toAbstractOStmtIn)
    (relOut := acceptRejectOracleRel)
    (rbrKnowledgeError := fun i => fullRbrKnowledgeError κ L K ℓ' mlIOPCS i) := by
  unfold fullOracleVerifier fullRbrKnowledgeError
  have batchInteractionRBRKS :=
    OracleVerifier.append_rbrKnowledgeSoundness (init:=init) (impl:=impl)
    (rel₁:=BatchingPhase.batchingInputRelation κ L K β ℓ ℓ'
  h_l mlIOPCS.toAbstractOStmtIn)
    (rel₂:=sumcheckRoundRelation κ L K ℓ ℓ' mlIOPCS.toAbstractOStmtIn 0)
    (rel₃:=mlIOPCS.toRelInput)
    (V₁:=BatchingPhase.batchingOracleVerifier κ L K β ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (V₂:=SumcheckPhase.coreInteractionOracleVerifier κ L K β ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (rbrKnowledgeError₁:=fun _ => BatchingPhase.batchingRBRKnowledgeError (κ:=κ) (L:=L))
    (rbrKnowledgeError₂:=SumcheckPhase.coreInteractionRbrKnowledgeError L ℓ')
    (h₁:=BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundness κ L K β ℓ
      ℓ' h_l (𝓑 := 𝓑) mlIOPCS.toAbstractOStmtIn)
    (h₂:=SumcheckPhase.coreInteraction_rbrKnowledgeSoundness κ L K β ℓ ℓ' h_l
      (𝓑 := 𝓑) mlIOPCS.toAbstractOStmtIn)
  have res :=
    OracleVerifier.append_rbrKnowledgeSoundness (init:=init) (impl:=impl)
    (rel₁:=BatchingPhase.batchingInputRelation κ L K β ℓ ℓ'
  h_l mlIOPCS.toAbstractOStmtIn)
    (rel₂:=mlIOPCS.toRelInput)
    (rel₃:=acceptRejectOracleRel)
    (V₁:=batchingCoreVerifier κ L K β (𝓑 := 𝓑) ℓ ℓ' h_l mlIOPCS)
    (V₂:=mlIOPCS.oracleReduction.verifier)
    (Oₛ₃:=by exact fun i ↦ OracleInterface.instDefault)
    (rbrKnowledgeError₁:=batchingCoreRbrKnowledgeError κ L K ℓ')
    (rbrKnowledgeError₂:=mlIOPCS.rbrKnowledgeError)
    (h₁:=batchInteractionRBRKS)
    (h₂:= mlIOPCS.rbrKnowledgeSoundness)
  exact OracleVerifier.rbrKnowledgeSoundness_of_eq_error
    (init := init) (impl := impl)
    (h_ε := by intro i; rfl)
    (h := res)

/-!
### Scalar knowledge soundness

The large-field tail is abstract (`MLIOPCS`). For the ring-switching **evaluation** layer, the paper
states explicitly: the **soundness error of Protocol 3.1** is \((2 \cdot \ell' + \kappa)/|L|\)
(Diamond–Posen ePrint 2024/504). Algebraically that is \((\kappa + 2\ell')/|L|\), i.e. the sum of the
two explicit terms below. The tail `ε_pcs` must bound the large-field IOPCS RBR sum (security of
the underlying `Π'` in **Theorem 3.5**). **§5.2 eq. (43)** for **Construction 5.1** then combines this
front with the BaseFold+FRI+query analysis (**Theorem 4.17**, **Propositions 4.23–4.24**); those
closed forms are not inlined here—see `Binius.FRIBinius.FullFRIBinius`.

Important audit note: DP24 states this scalar as a **soundness** error. Here we prove the stronger
`knowledgeSoundness`; the scalar error term is intentionally unchanged.

Depends on: `Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness`, front-end summation
lemmas, and `Verifier.knowledgeSoundness_error_mono`.
-/

/-- `((2 * ℓ' + κ)/ |L| + ε_pcs)`: **Protocol 3.1** soundness front `((2 * ℓ' + κ)/ |L|)`
plus an explicit budget `ε_pcs` for the abstract `MLIOPCS` tail.

Written as `κ/|L| + 2ℓ'/|L| + ε_pcs` (same ℝ≥0 value). `L` explicit for `Fintype.card` under `∑ … ≤ …`. -/
noncomputable def fullRingSwitchingConcreteKnowledgeError
    (κ : ℕ) (L : Type) [Fintype L] (ℓ' : ℕ) (ε_pcs : ℝ≥0) : ℝ≥0 :=
  (κ : ℝ≥0) / (Fintype.card L : ℝ≥0)
    + 2 * (ℓ' : ℝ≥0) / (Fintype.card L : ℝ≥0)
    + ε_pcs

/-- Scalar KS with error `∑ᵢ εᵢ` (RBR sum); corresponds to the generic **RBR ⇒ KS** step under
**Theorem 3.5** / **Theorem 4.17** before closing to a single closed form like **§5.2 (43)**. -/
theorem fullOracleVerifier_knowledgeSoundness_sum :
    (fullOracleVerifier κ L K β ℓ ℓ' (𝓑 := 𝓑) h_l mlIOPCS).toVerifier.knowledgeSoundness init impl
      (relIn := BatchingPhase.batchingInputRelation κ L K β ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
      (relOut := acceptRejectOracleRel)
      (knowledgeError :=
        ∑ i : (fullPspec κ L K ℓ' mlIOPCS).ChallengeIdx,
          fullRbrKnowledgeError κ L K ℓ' mlIOPCS i) := by
  let fullV := fullOracleVerifier κ L K β ℓ ℓ' (𝓑 := 𝓑) h_l mlIOPCS
  let relIn0 := BatchingPhase.batchingInputRelation κ L K β ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn
  let ε := fullRbrKnowledgeError κ L K ℓ' mlIOPCS
  have h_rbr : fullV.toVerifier.rbrKnowledgeSoundness init impl relIn0 acceptRejectOracleRel ε := by
    change OracleVerifier.rbrKnowledgeSoundness init impl relIn0 acceptRejectOracleRel fullV ε
    exact fullOracleVerifier_rbrKnowledgeSoundness (κ := κ) (L := L) (K := K) (β := β)
      (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (𝓑 := 𝓑) (mlIOPCS := mlIOPCS)
      (init := init) (impl := impl)
  exact (Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness (init := init) (impl := impl)
    relIn0 acceptRejectOracleRel fullV.toVerifier ε) h_rbr

/-- `∑ᵢ εᵢ` equals **Protocol 3.1** front `((2 * ℓ' + κ)/ |L|)` plus the raw PCS-tail sum
(before bounding that tail by `ε_pcs`). -/
theorem fullRbrKnowledgeError_sum_eq_front_add_pcs :
    (∑ i : (fullPspec κ L K ℓ' mlIOPCS).ChallengeIdx,
        fullRbrKnowledgeError κ L K ℓ' mlIOPCS i)
      = (κ : ℝ≥0) / (Fintype.card L : ℝ≥0)
        + 2 * (ℓ' : ℝ≥0) / (Fintype.card L : ℝ≥0)
        + (∑ i : mlIOPCS.pSpec.ChallengeIdx, mlIOPCS.rbrKnowledgeError i) := by
  classical
  have h_full :
      (∑ i : (fullPspec κ L K ℓ' mlIOPCS).ChallengeIdx,
        fullRbrKnowledgeError κ L K ℓ' mlIOPCS i)
      =
      (∑ i : (pSpecLargeFieldReduction κ L K ℓ').ChallengeIdx,
        batchingCoreRbrKnowledgeError κ L K ℓ' i)
      +
      (∑ i : mlIOPCS.pSpec.ChallengeIdx, mlIOPCS.rbrKnowledgeError i) := by
    unfold fullRbrKnowledgeError
    let f : ((pSpecLargeFieldReduction κ L K ℓ').ChallengeIdx ⊕ mlIOPCS.pSpec.ChallengeIdx) → ℝ≥0 :=
      Sum.elim (batchingCoreRbrKnowledgeError κ L K ℓ') mlIOPCS.rbrKnowledgeError
    change (∑ i : (fullPspec κ L K ℓ' mlIOPCS).ChallengeIdx, f (ChallengeIdx.sumEquiv.symm i)) = _
    have hsum :
        (∑ i : (fullPspec κ L K ℓ' mlIOPCS).ChallengeIdx,
          f (ChallengeIdx.sumEquiv.symm i))
        =
        (∑ i : ((pSpecLargeFieldReduction κ L K ℓ').ChallengeIdx ⊕ mlIOPCS.pSpec.ChallengeIdx), f i) := by
      exact Equiv.sum_comp (e := Equiv.symm ChallengeIdx.sumEquiv) (g := f)
    rw [hsum, Fintype.sum_sum_type]
    simp only [f, Sum.elim_inl, Sum.elim_inr]
  rw [h_full]
  have h_large :
      (∑ i : (pSpecLargeFieldReduction κ L K ℓ').ChallengeIdx,
        batchingCoreRbrKnowledgeError κ L K ℓ' i)
      =
      (∑ i : (RingSwitching.pSpecBatching κ L K).ChallengeIdx,
        RingSwitching.BatchingPhase.batchingRBRKnowledgeError (κ := κ) (L := L))
      +
      (∑ i : (RingSwitching.pSpecCoreInteraction (L := L) (ℓ' := ℓ')).ChallengeIdx,
        RingSwitching.SumcheckPhase.coreInteractionRbrKnowledgeError (L := L) (ℓ' := ℓ') i) := by
    unfold batchingCoreRbrKnowledgeError
    let f : ((RingSwitching.pSpecBatching κ L K).ChallengeIdx
      ⊕ (RingSwitching.pSpecCoreInteraction (L := L) (ℓ' := ℓ')).ChallengeIdx) → ℝ≥0 :=
      Sum.elim (fun _ => RingSwitching.BatchingPhase.batchingRBRKnowledgeError (κ := κ) (L := L))
        (RingSwitching.SumcheckPhase.coreInteractionRbrKnowledgeError (L := L) (ℓ' := ℓ'))
    change (∑ i : (pSpecLargeFieldReduction κ L K ℓ').ChallengeIdx,
      f (ChallengeIdx.sumEquiv.symm i)) = _
    have hsum :
        (∑ i : (pSpecLargeFieldReduction κ L K ℓ').ChallengeIdx,
          f (ChallengeIdx.sumEquiv.symm i))
        =
        (∑ i : ((RingSwitching.pSpecBatching κ L K).ChallengeIdx
          ⊕ (RingSwitching.pSpecCoreInteraction (L := L) (ℓ' := ℓ')).ChallengeIdx), f i) := by
      exact Equiv.sum_comp (e := Equiv.symm ChallengeIdx.sumEquiv) (g := f)
    rw [hsum, Fintype.sum_sum_type]
    simp only [f, Sum.elim_inl, Sum.elim_inr]
  rw [h_large]
  have h_batching :
      (∑ i : (RingSwitching.pSpecBatching κ L K).ChallengeIdx,
        RingSwitching.BatchingPhase.batchingRBRKnowledgeError (κ := κ) (L := L))
      = (κ : ℝ≥0) / (Fintype.card L : ℝ≥0) := by
    have h_batching_card : Fintype.card ((RingSwitching.pSpecBatching κ L K).ChallengeIdx) = 1 := by
      change Fintype.card { i // ![Direction.P_to_V, Direction.V_to_P] i = Direction.V_to_P } = 1
      decide
    rw [Finset.sum_const]
    simp [h_batching_card, RingSwitching.BatchingPhase.batchingRBRKnowledgeError]
  have h_core :
      (∑ i : (RingSwitching.pSpecCoreInteraction (L := L) (ℓ' := ℓ')).ChallengeIdx,
        RingSwitching.SumcheckPhase.coreInteractionRbrKnowledgeError (L := L) (ℓ' := ℓ') i)
      = 2 * (ℓ' : ℝ≥0) / (Fintype.card L : ℝ≥0) := by
    have h_core_card :
      Fintype.card ((RingSwitching.pSpecCoreInteraction (L := L) (ℓ' := ℓ')).ChallengeIdx) = ℓ' := by
      have h_append :
          Fintype.card ((RingSwitching.pSpecCoreInteraction (L := L) (ℓ' := ℓ')).ChallengeIdx)
            = Fintype.card ((RingSwitching.pSpecSumcheckLoop (L := L) (ℓ' := ℓ')).ChallengeIdx)
              + Fintype.card ((RingSwitching.pSpecFinalSumcheck (L := L)).ChallengeIdx) := by
        simpa [RingSwitching.pSpecCoreInteraction] using
          (Fintype.card_congr
            (ChallengeIdx.sumEquiv
              (pSpec₁ := RingSwitching.pSpecSumcheckLoop (L := L) (ℓ' := ℓ'))
              (pSpec₂ := RingSwitching.pSpecFinalSumcheck (L := L)))).symm
      have h_final_zero :
          Fintype.card ((RingSwitching.pSpecFinalSumcheck (L := L)).ChallengeIdx) = 0 := by
        change Fintype.card { i // ![Direction.P_to_V] i = Direction.V_to_P } = 0
        decide
      have h_loop :
          Fintype.card ((RingSwitching.pSpecSumcheckLoop (L := L) (ℓ' := ℓ')).ChallengeIdx) = ℓ' := by
        have h_round_card :
            Fintype.card ((RingSwitching.pSpecSumcheckRound (L := L)).ChallengeIdx) = 1 := by
          change Fintype.card { i // ![Direction.P_to_V, Direction.V_to_P] i = Direction.V_to_P } = 1
          decide
        have h_loop' :
            Fintype.card ((RingSwitching.pSpecSumcheckLoop (L := L) (ℓ' := ℓ')).ChallengeIdx)
              = Fintype.card ((i : Fin ℓ') × (RingSwitching.pSpecSumcheckRound (L := L)).ChallengeIdx) := by
          symm
          exact Fintype.card_congr
            (seqComposeChallengeEquiv
              (pSpec := fun _ : Fin ℓ' => RingSwitching.pSpecSumcheckRound (L := L)))
        rw [h_loop']
        rw [Fintype.card_sigma]
        simp [h_round_card]
      omega
    calc
      (∑ i : (RingSwitching.pSpecCoreInteraction (L := L) (ℓ' := ℓ')).ChallengeIdx,
          RingSwitching.SumcheckPhase.coreInteractionRbrKnowledgeError (L := L) (ℓ' := ℓ') i)
          =
          (ℓ' : ℝ≥0) * ((2 : ℝ≥0) / (Fintype.card L : ℝ≥0)) := by
            simp [RingSwitching.SumcheckPhase.coreInteractionRbrKnowledgeError,
              Finset.sum_const, h_core_card]
      _ = 2 * (ℓ' : ℝ≥0) / (Fintype.card L : ℝ≥0) := by
            ring_nf
  rw [h_batching, h_core]

/-! Exact aggregation when the abstract PCS tail sums to `ε_pcs` (not merely `≤`). -/
theorem fullRbrKnowledgeError_sum_eq_concrete (ε_pcs : ℝ≥0)
    (h_pcs : (∑ i : mlIOPCS.pSpec.ChallengeIdx, mlIOPCS.rbrKnowledgeError i) = ε_pcs) :
    (∑ i : (fullPspec κ L K ℓ' mlIOPCS).ChallengeIdx,
        fullRbrKnowledgeError κ L K ℓ' mlIOPCS i)
      = fullRingSwitchingConcreteKnowledgeError κ L ℓ' ε_pcs := by
  rw [fullRbrKnowledgeError_sum_eq_front_add_pcs]
  unfold fullRingSwitchingConcreteKnowledgeError
  rw [h_pcs]

/-- Scalar KS with error `fullRingSwitchingConcreteKnowledgeError κ L ℓ' ε_pcs` (Protocol 3.1 front +
`ε_pcs`). -/
theorem fullOracleVerifier_knowledgeSoundness (ε_pcs : ℝ≥0)
    (h_pcs : (∑ i : mlIOPCS.pSpec.ChallengeIdx, mlIOPCS.rbrKnowledgeError i) ≤ ε_pcs) :
    (fullOracleVerifier κ L K β ℓ ℓ' (𝓑 := 𝓑) h_l mlIOPCS).toVerifier.knowledgeSoundness init impl
      (relIn := BatchingPhase.batchingInputRelation κ L K β ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
      (relOut := acceptRejectOracleRel)
      (knowledgeError := fullRingSwitchingConcreteKnowledgeError κ L ℓ' ε_pcs) := by
  have h_sum := fullOracleVerifier_knowledgeSoundness_sum (κ := κ) (L := L) (K := K) (β := β)
    (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (𝓑 := 𝓑) (mlIOPCS := mlIOPCS)
    (init := init) (impl := impl)
  have hε :
      (∑ i : (fullPspec κ L K ℓ' mlIOPCS).ChallengeIdx,
          fullRbrKnowledgeError κ L K ℓ' mlIOPCS i)
        ≤ fullRingSwitchingConcreteKnowledgeError κ L ℓ' ε_pcs := by
    rw [fullRbrKnowledgeError_sum_eq_front_add_pcs]
    unfold fullRingSwitchingConcreteKnowledgeError
    let front :=
      (κ : ℝ≥0) / (Fintype.card L : ℝ≥0) + 2 * (ℓ' : ℝ≥0) / (Fintype.card L : ℝ≥0)
    exact add_le_add (le_refl front) h_pcs
  exact Verifier.knowledgeSoundness_error_mono (init := init) (impl := impl) (hε := hε) h_sum

end CanonicalB

end SecurityProperties
end
end Binius.RingSwitching.FullRingSwitching
