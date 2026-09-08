/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Spec
import ArkLib.ProofSystem.RingSwitching.Packing.BatchingPhase
import ArkLib.ProofSystem.RingSwitching.Packing.SumcheckPhase
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
import ArkLib.OracleReduction.Composition.Sequential.NoAmbient

/-!
# The composed interactive packing reduction

The whole interactive `Packing` reduction, assembled by sequential composition, with
its security statements. Input: an evaluation claim over the small ring against a committed
multilinear. Output: accept/reject. The composition is

1. **batching phase** — relocate the claim into the carrier and batch the coordinate claims
   into one sumcheck target (`BatchingPhase.lean`);
2. **relocation sumcheck** — `ℓ'` rounds plus the final consistency step, anchoring the
   claim at a fresh random point (`SumcheckPhase.lean`);
3. **downstream opening** — the residual large-ring evaluation claim is discharged by the
   `MLIOPCS` parameter, an arbitrary multilinear opening protocol bundled with its own
   completeness and round-by-round soundness.

The final deterministic step has proved perfect completeness and zero-error worst-case
knowledge soundness over commutative rings. The declared full error is `κ/|L|` (batching)
`+ 2/|L|` per sumcheck round `+` the downstream protocol's error; root bounds require a
domain. The batching leaf is proved under explicit commitment functionality. The loop and
general knowledge composition retain admitted obligations. The downstream `MLIOPCS` contract
supplies averaged
soundness; a worst-case assembly requires a corresponding downstream opening contract.

See `ArkLib/ProofSystem/RingSwitching/Basic.lean` for the family taxonomy. The batching phase
is reused by `ProofSystem/Binius/FRIBinius/`, whose downstream pipeline interleaves FRI and sumcheck
instead of instantiating this complete sequential wrapper.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over Binary
  Towers*][DP24]
-/

namespace RingSwitching.FullRingSwitching
noncomputable section
open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset Module

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (mlIOPCS : MLIOPCS L ℓ')

def batchingCoreVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:= BatchingPhase.oracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (pSpec₁:=pSpecBatching κ L K P)
    (V₂:=SumcheckPhase.coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (pSpec₂:=pSpecCoreInteraction L ℓ')

/-- The verifier composing tensor batching, relocation sumcheck, and packed opening. -/
@[reducible]
def fullOracleVerifier :=
  OracleVerifier.append (oSpec := []ₒ)
    (V₁ := batchingCoreVerifier κ L K P ℓ ℓ' h_l mlIOPCS)
    (pSpec₁ := pSpecLargeFieldReduction κ L K P ℓ')
    (V₂ := mlIOPCS.oracleReduction.toOracleVerifier)
    (pSpec₂ := mlIOPCS.pSpec)
    (Oₛ₃ := fun i : Empty => nomatch i)

def batchingCoreReduction :=
  OracleReduction.append
    (R₁ := BatchingPhase.batchingOracleReduction κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (pSpec₁:=pSpecBatching κ L K P)
    (R₂ := SumcheckPhase.coreInteractionOracleReduction κ L K P ℓ ℓ' h_l
       mlIOPCS.toAbstractOStmtIn)
    (pSpec₂:=pSpecCoreInteraction L ℓ')

/-- The reduction composing tensor batching, relocation sumcheck, and packed opening. -/
@[reducible]
def fullOracleReduction :
    OracleProof (oSpec:=[]ₒ)
      (Statement := BatchingStmtIn (L:=L) (ℓ := ℓ))
      (OStatement:= mlIOPCS.OStmtIn)
      (pSpec := fullPspec κ L K P ℓ' mlIOPCS)
      (Witness := BatchingWitIn (L:=L) (K:=K) (ℓ := ℓ) (ℓ' := ℓ')) :=
  OracleReduction.append
    (Oₛ₃ := fun i : Empty => nomatch i)
    (batchingCoreReduction κ L K P ℓ ℓ' h_l mlIOPCS)
    mlIOPCS.oracleReduction

/-- The composed tensor-packing and opening argument as a proof system. -/
@[reducible]
def fullOracleProof :
    OracleProof []ₒ
    (Statement := BatchingStmtIn (L:=L) (ℓ := ℓ))
    (OStatement := mlIOPCS.OStmtIn)
    (Witness := BatchingWitIn (L:=L) (K:=K) (ℓ := ℓ) (ℓ' := ℓ'))
    (pSpec:= fullPspec κ L K P ℓ' mlIOPCS) :=
    fullOracleReduction κ L K P ℓ ℓ' (h_l := h_l) mlIOPCS

/-!
## Security Properties
-/

variable [∀ i, SampleableType (mlIOPCS.pSpec.Challenge i)]

/-- Input relation for the full ring-switching protocol -/
abbrev fullInputRelation := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ'
  h_l mlIOPCS.toAbstractOStmtIn
abbrev fullOutputRelation := acceptRejectOracleRel

open scoped NNReal
open Sumcheck.Structured

section SecurityProperties
variable {σ : Type} (init : ProbComp σ) {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [Fintype L] [Fintype K] [DecidableEq K]
  [(i : mlIOPCS.pSpec.ChallengeIdx) → SampleableType (mlIOPCS.pSpec.Challenge i)] in
lemma batchingCore_perfectCompleteness [Finite L] [Finite K] :
    (batchingCoreReduction κ L K P ℓ ℓ' h_l mlIOPCS).perfectCompleteness
  (pSpec := pSpecLargeFieldReduction κ L K P ℓ')
  (relIn := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
  (relOut := mlIOPCS.toRelInput)
  (init:=init) (impl:=impl) := by
  let _ := Fintype.ofFinite L
  let _ := Fintype.ofFinite K
  classical
  refine OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (rel₂ := sumcheckRoundRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn 0) _ _
    (Verifier.GuardedForm.ofEmpty _ (fun stmt =>
      (⟨0, Fin.elim0, ⟨⟨stmt.1.t_eval_point, stmt.1.original_claim⟩, 0, fun _ => 0⟩⟩,
        stmt.2)))
    (Verifier.GuardedForm.ofEmpty _ (fun stmt => (⟨fun _ => 0, 0⟩, stmt.2)))
    (fun _ => Or.inl inferInstance) ?_ ?_
  · exact BatchingPhase.batchingReduction_perfectCompleteness κ L K P ℓ ℓ' h_l
       mlIOPCS.toAbstractOStmtIn
  · intro s
    exact SumcheckPhase.coreInteraction_perfectCompleteness
      κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn (init := pure s) (impl := impl)

omit [Fintype L] [Fintype K] [DecidableEq K]
  [(i : mlIOPCS.pSpec.ChallengeIdx) → SampleableType (mlIOPCS.pSpec.Challenge i)] in
theorem fullOracleReduction_perfectCompleteness [Finite L] [Finite K] :
    OracleProof.perfectCompleteness
      (oracleProof := fullOracleReduction κ L K P ℓ ℓ' (h_l := h_l) mlIOPCS)
      (relation := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ' h_l
        mlIOPCS.toAbstractOStmtIn)
      (init := init)
      (impl := impl) := by
  let _ := Fintype.ofFinite L
  let _ := Fintype.ofFinite K
  classical
  exact OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (Oₛ₃ := fun i : Empty => nomatch i)
    (batchingCoreReduction κ L K P ℓ ℓ' h_l mlIOPCS) mlIOPCS.oracleReduction
    (Verifier.GuardedForm.ofEmpty _ (fun stmt => (⟨fun _ => 0, 0⟩, stmt.2)))
    (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i : Empty => nomatch i)))
    (fun _ => Or.inl inferInstance)
    (batchingCore_perfectCompleteness κ L K P ℓ ℓ' h_l mlIOPCS init)
    (fun _ => mlIOPCS.perfectCompleteness)

def batchingCoreRbrKnowledgeError
    (i : (pSpecBatching κ L K P ++ₚ pSpecCoreInteraction L ℓ').ChallengeIdx) : ℝ≥0 :=
  Sum.elim (f:=BatchingPhase.batchingRBRKnowledgeError κ L K P)
    (g:=SumcheckPhase.coreInteractionRbrKnowledgeError L ℓ')
    (ChallengeIdx.sumEquiv.symm i)

def fullRbrKnowledgeError (i : (fullPspec κ L K P ℓ' mlIOPCS).ChallengeIdx) : ℝ≥0 :=
  Sum.elim (f := batchingCoreRbrKnowledgeError κ L K P ℓ')
  (g:=mlIOPCS.rbrKnowledgeError)
  (ChallengeIdx.sumEquiv.symm i)

omit [Fintype K] [DecidableEq K] in
/-- Round-by-round knowledge soundness for the full ring-switching oracle verifier -/
theorem fullOracleVerifier_rbrKnowledgeSoundness [Finite K] [NoZeroDivisors L]
    (hfunctional : mlIOPCS.toAbstractOStmtIn.Functional) :
    OracleProof.rbrKnowledgeSoundness
      (verifier := fullOracleVerifier κ L K P ℓ ℓ' (h_l := h_l) mlIOPCS)
      (init := init)
      (impl := impl)
      (relIn := fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
      (rbrKnowledgeError := fun i => fullRbrKnowledgeError κ L K P ℓ' mlIOPCS i) := by
  let _ : IsDomain L := NoZeroDivisors.to_isDomain L
  let _ := Fintype.ofFinite K
  classical
  unfold fullOracleVerifier fullRbrKnowledgeError
  have batchInteractionRBRKS :=
    OracleVerifier.append_rbrKnowledgeSoundness (init:=init) (impl:=impl)
    (rel₁:=fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
    (rel₂:=sumcheckRoundRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn 0)
    (rel₃:=mlIOPCS.toRelInput)
    (V₁:=BatchingPhase.oracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (V₂:=SumcheckPhase.coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (rbrKnowledgeError₁:=BatchingPhase.batchingRBRKnowledgeError κ L K P)
    (rbrKnowledgeError₂:=SumcheckPhase.coreInteractionRbrKnowledgeError L ℓ')
    (h₁:=BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundness κ L K P ℓ
      ℓ' h_l mlIOPCS.toAbstractOStmtIn hfunctional)
    (h₂:=SumcheckPhase.coreInteraction_rbrKnowledgeSoundness κ L K P ℓ ℓ' h_l
      mlIOPCS.toAbstractOStmtIn hfunctional)

  have res :=
    OracleVerifier.append_rbrKnowledgeSoundness (init:=init) (impl:=impl)
    (rel₁:=fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
    (rel₂:=mlIOPCS.toRelInput)
    (rel₃:=fullOutputRelation)
    (V₁:=batchingCoreVerifier κ L K P ℓ ℓ' h_l mlIOPCS)
    (V₂:=mlIOPCS.oracleReduction.toOracleVerifier)
    (Oₛ₃:=fun i : Empty => nomatch i)
    (rbrKnowledgeError₁:=batchingCoreRbrKnowledgeError κ L K P ℓ')
    (rbrKnowledgeError₂:=mlIOPCS.rbrKnowledgeError)
    (h₁:=batchInteractionRBRKS) (h₂:=by
      convert mlIOPCS.rbrKnowledgeSoundness (L:=L) (ℓ' := ℓ') (init:=init) (impl:=impl)
      · sorry
    )
  convert res
  · simp only [ChallengeIdx]
    sorry

end SecurityProperties
end
end RingSwitching.FullRingSwitching
