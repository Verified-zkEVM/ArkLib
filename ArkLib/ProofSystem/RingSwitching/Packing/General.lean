/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Spec
public import ArkLib.ProofSystem.RingSwitching.Packing.Compatibility
public import ArkLib.ProofSystem.RingSwitching.Packing.BatchingPhase
public import ArkLib.ProofSystem.RingSwitching.Packing.SumcheckPhase
public import ArkLib.OracleReduction.Security.RoundByRound
public import ArkLib.OracleReduction.Composition.Sequential.Append
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient

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

**Perfect completeness** (`fullOracleReduction_perfectCompleteness`) composes from the phases
through the guarded-verifier composition theorems, at the *strict* relations: the input relation
`BatchingPhase.strictBatchingInputRelation` and the downstream opening's
`AbstractOStmtIn.toStrictRelInput` use honest oracle compatibility
(`AbstractOStmtIn.strictView`). It is proved from the phase theorems and the downstream
`MLIOPCS.perfectCompleteness` field.

**Round-by-round knowledge soundness** of the full composite has total error `κ/|L|` (batching)
`+ 2/|L|` per sumcheck round `+` the downstream protocol's error, at the relaxed relations; the
final step sends no challenge and adds no error. It assumes `[NoZeroDivisors L]` for the
Schwartz–Zippel steps and `hUnique : mlIOPCS.toAbstractOStmtIn.Functional`, which says the oracle
statement determines the packed polynomial before any challenge.

The phase theorems are sorry-free and axiom-clean under these hypotheses, and are proved in the
worst-case form with the extractor and knowledge-state function named
(`BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_rbrExtractor`,
`SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_rbrExtractor`,
`SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_rbrExtractor`).
They compose by the guarded worst-case composition theorems
(`OracleVerifier.seqCompose_rbrKnowledgeSoundnessWorstCase_of_guarded`,
`OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first`), each verifier guarded by
its own checks (`SumcheckPhase.coreInteractionGuardedForm`, `batchingCoreGuardedForm`). The
results, each sorry-free and axiom-clean under its stated hypotheses, with averaged corollaries:

* the core interaction, `SumcheckPhase.coreInteraction_rbrKnowledgeSoundnessWorstCase`;
* batching followed by the core interaction, `batchingCore_rbrKnowledgeSoundnessWorstCase`;
* the full composite, `fullOracleVerifier_rbrKnowledgeSoundnessWorstCase`, given in addition that
  the downstream opening is worst-case round-by-round knowledge sound
  (`hPCS : mlIOPCS.RbrKnowledgeSoundWorstCase`). Its averaged form is
  `fullOracleVerifier_rbrKnowledgeSoundness_of_worst_case`.

Under a plain `MLIOPCS`, whose `MLIOPCS.rbrKnowledgeSoundness` contract is averaged, the full
composite `fullOracleVerifier_rbrKnowledgeSoundness` remains **conditional**. It applies the
admitted framework contract `OracleVerifier.append_rbrKnowledgeSoundness`, whose statement is
flagged as not derivable from its hypotheses, and inherits its `sorryAx`.

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

/-- The guard and verdict of batching followed by the core interaction, as data: the batching
check (`scalarRoundOracleVerifierGuardedForm`), then the core interaction's checks
(`SumcheckPhase.coreInteractionGuardedForm`). -/
def batchingCoreGuardedForm :
    (batchingCoreVerifier κ L K P ℓ ℓ' h_l mlIOPCS).toVerifier.GuardedForm :=
  .ofEq (OracleVerifier.append_toVerifier _ _).symm
    ((scalarRoundOracleVerifierGuardedForm _ _).append
      (SumcheckPhase.coreInteractionGuardedForm κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn))

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

omit [NeZero κ] [Fintype L] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
lemma batchingCore_perfectCompleteness [Finite L] [Finite K] :
    (batchingCoreReduction κ L K P ℓ ℓ' h_l mlIOPCS).perfectCompleteness
  (pSpec := pSpecLargeFieldReduction κ L K P ℓ')
  (relIn := BatchingPhase.strictBatchingInputRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
  (relOut := mlIOPCS.toStrictRelInput)
  (init:=init) (impl:=impl) := by
  let _ := Fintype.ofFinite L
  let _ := Fintype.ofFinite K
  classical
  refine OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (rel₂ := strictSumcheckRoundRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn 0) _ _
    (scalarRoundOracleVerifierGuardedForm _ _)
    (SumcheckPhase.coreInteractionGuardedForm κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (fun _ => Or.inl inferInstance) ?_ ?_
  · exact BatchingPhase.batchingReduction_perfectCompleteness κ L K P ℓ ℓ' h_l
       mlIOPCS.toAbstractOStmtIn.strictView
  · intro s
    exact SumcheckPhase.coreInteraction_perfectCompleteness
      κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn.strictView (init := pure s) (impl := impl)

omit [NeZero κ] [Fintype L] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- Perfect completeness of the full ring-switching oracle proof, at the strict input relation
with honest oracle compatibility. -/
theorem fullOracleReduction_perfectCompleteness [Finite L] [Finite K] :
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
    (batchingCoreGuardedForm κ L K P ℓ ℓ' h_l mlIOPCS)
    -- An arbitrary opening has no named guard; over the empty ambient oracle `ofEmpty` gives one.
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

omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- Worst-case round-by-round knowledge soundness for the batching phase followed by the core
interaction, with error `κ/|L|` at the batching challenge and `2/|L|` per sumcheck challenge.

Composed from `BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundnessWorstCase` and
`SumcheckPhase.coreInteraction_rbrKnowledgeSoundnessWorstCase` by
`OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first`; the batching verifier is
guarded by its own check (`scalarRoundOracleVerifierGuardedForm`). Sorry-free and axiom-clean
under `hUnique` and `[NoZeroDivisors L]`. -/
theorem batchingCore_rbrKnowledgeSoundnessWorstCase [NoZeroDivisors L]
    (hUnique : mlIOPCS.toAbstractOStmtIn.Functional) :
    Verifier.rbrKnowledgeSoundnessWorstCase init impl
      (verifier := (batchingCoreVerifier κ L K P ℓ ℓ' h_l mlIOPCS).toVerifier)
      (relIn := fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
      (relOut := mlIOPCS.toAbstractOStmtIn.toRelInput)
      (batchingCoreRbrKnowledgeError κ L K P ℓ') :=
  OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first _ _
    (scalarRoundOracleVerifierGuardedForm _ _)
    (BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundnessWorstCase κ L K P ℓ ℓ' h_l
      mlIOPCS.toAbstractOStmtIn (init := init) (impl := impl) hUnique)
    (SumcheckPhase.coreInteraction_rbrKnowledgeSoundnessWorstCase κ L K P ℓ ℓ' h_l
      mlIOPCS.toAbstractOStmtIn (init := init) (impl := impl) hUnique)

omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- Round-by-round knowledge soundness for the batching phase followed by the core interaction:
the averaged form of `batchingCore_rbrKnowledgeSoundnessWorstCase`. Sorry-free and axiom-clean
under `hUnique` and `[NoZeroDivisors L]`. -/
theorem batchingCore_rbrKnowledgeSoundness [NoZeroDivisors L]
    (hUnique : mlIOPCS.toAbstractOStmtIn.Functional) :
    (batchingCoreVerifier κ L K P ℓ ℓ' h_l mlIOPCS).rbrKnowledgeSoundness init impl
      (relIn := fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
      (relOut := mlIOPCS.toAbstractOStmtIn.toRelInput)
      (batchingCoreRbrKnowledgeError κ L K P ℓ') :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (batchingCore_rbrKnowledgeSoundnessWorstCase κ L K P ℓ ℓ' h_l mlIOPCS init hUnique)

omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- Round-by-round knowledge soundness for the full ring-switching oracle verifier.

**Conditional on an admitted composition contract.** The batching-and-core part,
`batchingCore_rbrKnowledgeSoundness`, is sorry-free and axiom-clean. The last step appends the
downstream opening, whose `MLIOPCS.rbrKnowledgeSoundness` contract is averaged, so this composite
applies the admitted `OracleVerifier.append_rbrKnowledgeSoundness`. That contract is stated for
arbitrary verifiers at the averaged notion, and the section note of
`Composition/Sequential/Append/Security.lean` flags its statement as not derivable from its
hypotheses. So this theorem is unverified statement debt, not only a missing proof, and it carries
`sorryAx`.

Under the worst-case hypothesis `MLIOPCS.RbrKnowledgeSoundWorstCase` on the downstream opening,
the same conclusion is sorry-free and axiom-clean:
`fullOracleVerifier_rbrKnowledgeSoundness_of_worst_case`. -/
theorem fullOracleVerifier_rbrKnowledgeSoundness [Finite K] [NoZeroDivisors L]
    (hUnique : mlIOPCS.toAbstractOStmtIn.Functional) :
    OracleProof.rbrKnowledgeSoundness
      (verifier := fullOracleVerifier κ L K P ℓ ℓ' (h_l := h_l) mlIOPCS)
      (init := init)
      (impl := impl)
      (relIn := fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
      (rbrKnowledgeError := fun i => fullRbrKnowledgeError κ L K P ℓ' mlIOPCS i) := by
  let _ := Fintype.ofFinite K
  classical
  unfold fullOracleVerifier fullRbrKnowledgeError
  have batchInteractionRBRKS :=
    batchingCore_rbrKnowledgeSoundness κ L K P ℓ ℓ' h_l mlIOPCS init (impl := impl) hUnique
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
    (h₁:=batchInteractionRBRKS)
    (h₂:=by
      simpa only [OracleProof.rbrKnowledgeSoundness, fullOutputRelation] using
        mlIOPCS.rbrKnowledgeSoundness (init:=init) (impl:=impl))
  simpa only [OracleProof.rbrKnowledgeSoundness, fullOutputRelation, Function.comp_def] using res

omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- Worst-case round-by-round knowledge soundness for the full ring-switching oracle verifier, at
error `κ/|L|` (batching) `+ 2/|L|` per sumcheck round `+` the downstream opening's error, given a
downstream opening that is itself worst-case round-by-round knowledge sound
(`MLIOPCS.RbrKnowledgeSoundWorstCase`).

Composed from `batchingCore_rbrKnowledgeSoundnessWorstCase` and that hypothesis by
`OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first`; batching followed by the
core interaction is guarded by its own checks (`batchingCoreGuardedForm`), and the downstream
opening needs no guard. Sorry-free and axiom-clean under `hUnique`, `hPCS` and
`[NoZeroDivisors L]`. -/
theorem fullOracleVerifier_rbrKnowledgeSoundnessWorstCase [NoZeroDivisors L]
    (hUnique : mlIOPCS.toAbstractOStmtIn.Functional)
    (hPCS : mlIOPCS.RbrKnowledgeSoundWorstCase) :
    OracleProof.rbrKnowledgeSoundnessWorstCase init impl
      (fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
      (fullOracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS)
      (fullRbrKnowledgeError κ L K P ℓ' mlIOPCS) :=
  OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first _ _
    (Oₛ₃ := fun i : Empty => nomatch i)
    (batchingCoreGuardedForm κ L K P ℓ ℓ' h_l mlIOPCS)
    (batchingCore_rbrKnowledgeSoundnessWorstCase κ L K P ℓ ℓ' h_l mlIOPCS init hUnique) hPCS

omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- Round-by-round knowledge soundness for the full ring-switching oracle verifier, given a
worst-case round-by-round knowledge sound downstream opening: the averaged form of
`fullOracleVerifier_rbrKnowledgeSoundnessWorstCase`, with the same statement as
`fullOracleVerifier_rbrKnowledgeSoundness`. Sorry-free and axiom-clean under `hUnique`, `hPCS` and
`[NoZeroDivisors L]`. -/
theorem fullOracleVerifier_rbrKnowledgeSoundness_of_worst_case [NoZeroDivisors L]
    (hUnique : mlIOPCS.toAbstractOStmtIn.Functional)
    (hPCS : mlIOPCS.RbrKnowledgeSoundWorstCase) :
    OracleProof.rbrKnowledgeSoundness
      (verifier := fullOracleVerifier κ L K P ℓ ℓ' (h_l := h_l) mlIOPCS)
      (init := init)
      (impl := impl)
      (relIn := fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
      (rbrKnowledgeError := fun i => fullRbrKnowledgeError κ L K P ℓ' mlIOPCS i) :=
  OracleProof.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness
    (fullOracleVerifier_rbrKnowledgeSoundnessWorstCase κ L K P ℓ ℓ' h_l mlIOPCS init hUnique hPCS)

end SecurityProperties
end
end RingSwitching.FullRingSwitching
