/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Spec
public import ArkLib.ProofSystem.RingSwitching.Packing.CoordinateLaws
public import ArkLib.ProofSystem.RingSwitching.Packing.Compatibility
public import ArkLib.ProofSystem.RingSwitching.Packing.BatchingPhase
public import ArkLib.ProofSystem.RingSwitching.Packing.SumcheckPhase
public import ArkLib.OracleReduction.Security.RoundByRound
public import ArkLib.OracleReduction.Composition.Sequential.Append
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
public import ArkLib.OracleReduction.Composition.Sequential.Append.AveragedEmpty

/-!
# The composed DP24 tensor-packing reduction

The DP24 interactive `Packing` reduction, assembled by sequential composition, with
its security statements. Input: an evaluation claim over the small ring against a committed
multilinear. Output: accept/reject. The composition is

1. **batching phase** — relocate the claim into the carrier and batch the coordinate claims
   into one sumcheck target (`BatchingPhase.lean`);
2. **relocation sumcheck** — `ℓ'` rounds plus the final consistency step, anchoring the
   claim at a fresh random point (`SumcheckPhase.lean`);
3. **downstream opening** — the residual large-ring evaluation claim is discharged by the
   `MLIOPCS` parameter, an arbitrary multilinear opening protocol bundled with its own
   completeness and round-by-round soundness.

Perfect completeness composes from the phases. Round-by-round knowledge soundness composes
with total error `κ/|L|` (batching) `+ 2/|L|` per sumcheck round `+ 1/|L|` (final step)
`+` the downstream protocol's error; the Schwartz–Zippel steps require `[IsDomain L]`.
The leaf proofs use explicit coordinate laws and, for soundness, functional input compatibility.

These are tensor-packing security theorems, not a universal contract for every ring switch.
`CoordinateLaws` is proved for `tensorProductProfile`; it is not imposed on the shared profile
data. Hachi's trace head instead needs its own trace reconstruction and weak-opening contracts,
and is not asserted to instantiate this composed reduction.

This is one construction of the ring-switching family, not the family itself — see the
folder umbrella `ArkLib/ProofSystem/RingSwitching/Basic.lean` for the taxonomy. It is
instantiated by `ProofSystem/Binius/FRIBinius/`.

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over
  Binary Towers." Cryptology ePrint Archive (2024).
-/

@[expose] public section

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

/-- The oracle verifier for the full DP24 ring-switching protocol -/
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

/-- The reduction for the full DP24 ring-switching protocol -/
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

/-- The full DP24 ring-switching protocol as a Proof -/
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

/-- Input relation for the full ring-switching protocol -/
abbrev fullInputRelation := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ'
  h_l mlIOPCS.toAbstractOStmtIn
abbrev fullOutputRelation := acceptRejectOracleRel

open scoped NNReal
open Sumcheck.Structured

section SecurityProperties
variable {σ : Type} (init : ProbComp σ) {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [Fintype L] [Fintype K] [DecidableEq K] in
lemma batchingCore_perfectCompleteness [Finite L] [Finite K] [IsDomain K] [NoZeroDivisors L]
    (hCoord : CoordinateLaws P) :
    (batchingCoreReduction κ L K P ℓ ℓ' h_l mlIOPCS).perfectCompleteness
  (pSpec := pSpecLargeFieldReduction κ L K P ℓ')
  (relIn := BatchingPhase.strictBatchingInputRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
  (relOut := mlIOPCS.toStrictRelInput)
  (init:=init) (impl:=impl) := by
  let _ : IsDomain L := NoZeroDivisors.to_isDomain L
  let _ := Fintype.ofFinite L
  let _ := Fintype.ofFinite K
  classical
  refine OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (rel₂ := strictSumcheckRoundRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn 0) _ _
    (Verifier.GuardedForm.ofEmpty _ (fun stmt =>
      (⟨0, Fin.elim0, ⟨⟨stmt.1.t_eval_point, stmt.1.original_claim⟩, 0, fun _ => 0⟩⟩,
        stmt.2)))
    (Verifier.GuardedForm.ofEmpty _ (fun stmt => (⟨fun _ => 0, 0⟩, stmt.2)))
    (fun _ => Or.inl inferInstance) ?_ ?_
  · exact BatchingPhase.batchingReduction_perfectCompleteness κ L K P ℓ ℓ' h_l
       mlIOPCS.toAbstractOStmtIn.strictView (hCoord := hCoord)
  · intro s
    exact SumcheckPhase.coreInteraction_perfectCompleteness
      κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn.strictView
        (hCoord := hCoord) (init := pure s) (impl := impl)

omit [Fintype L] [Fintype K] [DecidableEq K] in
theorem fullOracleReduction_perfectCompleteness [Finite L] [Finite K] [IsDomain K]
    [NoZeroDivisors L]
    (hCoord : CoordinateLaws P) :
    OracleProof.perfectCompleteness
      (oracleProof := fullOracleReduction κ L K P ℓ ℓ' (h_l := h_l) mlIOPCS)
      (relation := BatchingPhase.strictBatchingInputRelation κ L K P ℓ ℓ' h_l
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
    (batchingCore_perfectCompleteness κ L K P ℓ ℓ' h_l mlIOPCS init hCoord)
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
/-- The batching and sumcheck core has fixed-prefix security independently of the downstream
opening protocol's security certificate. -/
theorem batchingCore_rbrKnowledgeSoundness_fixedPrefix
    [Finite K] [IsDomain K] [NoZeroDivisors L]
    (hCoord : CoordinateLaws P) (hUnique : mlIOPCS.toAbstractOStmtIn.Functional) :
    (batchingCoreVerifier κ L K P ℓ ℓ' h_l mlIOPCS).toVerifier
      |>.rbrKnowledgeSoundness init impl
        (fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS) mlIOPCS.toRelInput
        (batchingCoreRbrKnowledgeError κ L K P ℓ') := by
  let _ : IsDomain L := NoZeroDivisors.to_isDomain L
  let _ := Fintype.ofFinite K
  classical
  exact OracleVerifier.append_rbrKnowledgeSoundness_of_guarded_first init impl
    (rel₂ := sumcheckRoundRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn 0)
    (Verifier.GuardedForm.ofEmpty _ (fun stmt =>
      (⟨0, Fin.elim0, ⟨⟨stmt.1.t_eval_point, stmt.1.original_claim⟩, 0, fun _ => 0⟩⟩,
        stmt.2)))
    (BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundness_fixedPrefix κ L K P ℓ
      ℓ' h_l mlIOPCS.toAbstractOStmtIn hCoord hUnique)
    (SumcheckPhase.coreInteraction_rbrKnowledgeSoundness_fixedPrefix κ L K P ℓ ℓ' h_l
      mlIOPCS.toAbstractOStmtIn hCoord hUnique)

omit [Fintype K] [DecidableEq K] in
/-- Full composition with an explicit fixed-prefix certificate for the downstream opening
protocol. The averaged field of `MLIOPCS` alone is not used as a fixed-prefix bound. -/
theorem fullOracleVerifier_rbrKnowledgeSoundness_fixedPrefix
    [Finite K] [IsDomain K] [NoZeroDivisors L]
    (hCoord : CoordinateLaws P) (hUnique : mlIOPCS.toAbstractOStmtIn.Functional)
    (hTail : (mlIOPCS.oracleReduction.toOracleVerifier.toVerifier
      (Oₛₒ := fun i : Empty => nomatch i)).rbrKnowledgeSoundness init impl
        mlIOPCS.toRelInput fullOutputRelation mlIOPCS.rbrKnowledgeError) :
    ((fullOracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS).toVerifier
      (Oₛₒ := fun i : Empty => nomatch i)).rbrKnowledgeSoundness init impl
        (fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS) fullOutputRelation
        (fullRbrKnowledgeError κ L K P ℓ' mlIOPCS) := by
  classical
  exact OracleVerifier.append_rbrKnowledgeSoundness_of_guarded_first init impl
    (Oₛ₃ := fun i : Empty => nomatch i)
    (Verifier.GuardedForm.ofEmpty _ (fun stmt => (⟨fun _ => 0, 0⟩, stmt.2)))
    (batchingCore_rbrKnowledgeSoundness_fixedPrefix κ L K P ℓ ℓ' h_l mlIOPCS init
      hCoord hUnique) hTail

omit [Fintype K] [DecidableEq K] in
/-- Round-by-round knowledge soundness for the full ring-switching oracle verifier -/
theorem fullOracleVerifier_rbrKnowledgeSoundness [Finite K] [IsDomain K] [NoZeroDivisors L]
    (hCoord : CoordinateLaws P) (hUnique : mlIOPCS.toAbstractOStmtIn.Functional) :
    OracleProof.rbrKnowledgeSoundnessAveraged
      (verifier := fullOracleVerifier κ L K P ℓ ℓ' (h_l := h_l) mlIOPCS)
      (init := init)
      (impl := impl)
      (relIn := fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
      (rbrKnowledgeError := fun i => fullRbrKnowledgeError κ L K P ℓ' mlIOPCS i) := by
  classical
  let : Inhabited (WitMLP L ℓ') := ⟨⟨0⟩⟩
  have h := Verifier.append_rbrKnowledgeSoundnessAveraged_empty init impl
    (Verifier.GuardedForm.ofEmpty _ (fun stmt => (⟨fun _ => 0, 0⟩, stmt.2)))
    (batchingCore_rbrKnowledgeSoundness_fixedPrefix κ L K P ℓ ℓ' h_l mlIOPCS init
      hCoord hUnique) (mlIOPCS.rbrKnowledgeSoundness (init := init) (impl := impl))
  simp only [OracleProof.rbrKnowledgeSoundnessAveraged,
    OracleVerifier.rbrKnowledgeSoundnessAveraged, fullOracleVerifier,
    OracleVerifier.append_toVerifier, fullRbrKnowledgeError]
  convert h using 1
  rfl

end SecurityProperties
end
end RingSwitching.FullRingSwitching
