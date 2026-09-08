/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.FullFamily
import ArkLib.ProofSystem.RingSwitching.Packing.ScalarFamily.Security

/-!
# Original scalar claim to the same packed commitment's opening

This is the actual checked scalar/family head followed by the generic product-sumcheck
tail. Its public endpoint is precisely `pc.evalRel` over C. The explicit extractor and state
use the proved guarded append constructor; each challenge keeps its component's error bound.
The checked slice message is part of the declared protocol variant.
-/

noncomputable section
namespace RingSwitching.Packing.ScalarOpening
open OracleSpec OracleComp ProtocolSpec MvPolynomial
open scoped NNReal
variable {B : Type} [CommRing B] (data : PackingData B) (m : ℕ)
  (layout : ScalarHead.ClaimLayout data m)
  {C : Type} [CommRing C] [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C]
  (bat : BatchingStrategy C data.ιE) (pc : PackedCommitment data.P m)

/-- The actual checked head, then the full sequence and terminal opening message. -/
def pSpec : ProtocolSpec (3 + (0 + (Fin.vsum (fun _ : Fin m => 2) + 1))) :=
  ScalarFamily.pSpec data bat ++ₚ FullFamilyTail.pSpec (C := C) m

instance : ∀ j, OracleInterface ((pSpec data m bat).Message j) :=
  ProtocolSpec.instOracleInterfaceMessageAppend
    (pSpec₁ := ScalarFamily.pSpec data bat) (pSpec₂ := FullFamilyTail.pSpec (C := C) m)

instance [Fintype C] : ∀ j, SampleableType ((pSpec data m bat).Challenge j) :=
  ProtocolSpec.instSampleableTypeChallengeAppend
    (pSpec₁ := ScalarFamily.pSpec data bat) (pSpec₂ := FullFamilyTail.pSpec (C := C) m)

/-- The actual oracle verifier keeps the original commitment through its final opening. -/
def verifier : OracleVerifier []ₒ (ScalarHead.Input data m layout) pc.OStmt
    ((Fin m → C) × C) pc.OStmt (pSpec data m bat) :=
  (ScalarFamily.verifier data m layout bat pc).append (FullFamilyTail.verifier data m bat pc)

/-- The actual prover packs the source and retains that same P-polynomial through the tail. -/
def reduction : OracleReduction []ₒ (ScalarHead.Input data m layout) pc.OStmt
    (layout.Source) ((Fin m → C) × C) pc.OStmt data.P⦃≤ 1⦄[X Fin m] (pSpec data m bat) :=
  (ScalarFamily.reduction data m layout bat pc).append (FullFamilyTail.reduction data m bat pc)

omit [IsScalarTower B data.P C] in
/-- Materialization agrees with the actual oracle-verifier append. -/
theorem verifier_toVerifier : (verifier data m layout bat pc).toVerifier =
    (ScalarFamily.verifier data m layout bat pc).toVerifier.append
      (FullFamilyTail.verifier data m bat pc).toVerifier :=
  OracleVerifier.append_toVerifier _ _

/-- Both the checked head and every tail check are retained by the actual guarded verifier. -/
def guardedForm : (verifier data m layout bat pc).toVerifier.GuardedForm := by
  let G := (ScalarFamily.guardedForm data m layout bat pc).append
    (FullFamilyTail.guardedForm data m bat pc)
  exact {
    check := G.check
    out := G.out
    verify_eq := fun stmt tr => by
      rw [verifier_toVerifier]
      exact G.verify_eq stmt tr }

omit [Algebra B C] [IsScalarTower B data.P C] in
/-- The head's output is pure, which validates stateful sequencing with the tail. -/
theorem headOutputIsPure : (ScalarFamily.reduction data m layout bat pc).prover.OutputIsPure :=
  Prover.OutputIsPure.append _ _
    (show (ScalarHead.prover data m layout pc).OutputIsPure from inferInstance)
    (show (FullFamily.prover data m bat pc).OutputIsPure from inferInstance)

instance : (reduction data m layout bat pc).prover.OutputIsPure :=
  Prover.OutputIsPure.append _ _
    (show (ScalarFamily.reduction data m layout bat pc).prover.OutputIsPure from
      headOutputIsPure data m layout bat pc)
    (show (FullFamilyTail.reduction data m bat pc).prover.OutputIsPure from inferInstance)

/-- Stateful perfect completeness reaches the same commitment's exact C-valued opening. -/
theorem perfectCompleteness [Fintype C] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction data m layout bat pc).perfectCompleteness init impl
      (ScalarFamily.relIn data m layout pc) pc.evalRel := by
  exact OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (ScalarFamily.reduction data m layout bat pc) (FullFamilyTail.reduction data m bat pc)
    (ScalarFamily.guardedForm data m layout bat pc) (FullFamilyTail.guardedForm data m bat pc)
    (fun _ => Or.inl
      (show (ScalarFamily.reduction data m layout bat pc).prover.OutputIsPure from
      headOutputIsPure data m layout bat pc))
    (ScalarFamily.perfectCompleteness data m layout bat pc init impl)
    (fun s => FullFamilyTail.perfectCompleteness data m bat pc (pure s) impl)

/-- The actual append witness family retains the source through the head and the packed tail. -/
abbrev Witness : Fin (3 + (0 + (Fin.vsum (fun _ : Fin m => 2) + 1)) + 1) → Type :=
  Verifier.KnowledgeAppend.Witness (ScalarFamily.WitMid data m layout)
    (FullFamilyTail.Witness data m)

/-- The actual append extractor recovers the original source from the same packed polynomial. -/
def extractor : Extractor.RoundByRound []ₒ
    ((ScalarHead.Input data m layout) × (∀ j, pc.OStmt j)) (layout.Source) data.P⦃≤ 1⦄[X Fin m]
    (pSpec data m bat) (Witness data m layout) :=
  (ScalarFamily.extractor data m layout bat pc).append (FullFamilyTail.extractor data m bat pc)
    (ScalarFamily.guardedForm data m layout bat pc).out

/-- Error follows the actual append challenge index, with no terminal loss. -/
def rbrError [Fintype C] : (pSpec data m bat).ChallengeIdx → ℝ≥0 :=
  Sum.elim (ScalarFamily.rbrError data bat) (FullFamilyTail.rbrError (C := C) m) ∘
    ChallengeIdx.sumEquiv.symm

omit [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C] in
set_option backward.isDefEq.respectTransparency false in
/-- Challenges in the checked head carry precisely the declared batching-strategy error. -/
theorem rbrError_head [Fintype C] (i : (ScalarFamily.pSpec data bat).ChallengeIdx) :
    rbrError data m bat (ChallengeIdx.sumEquiv (.inl i)) = bat.error := by
  simp only [rbrError, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
  exact ScalarFamily.rbrError_eq data bat i

omit [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C] in
set_option backward.isDefEq.respectTransparency false in
/-- Each actual tail challenge carries degree-two error and retains its own sampled prefix. -/
theorem rbrError_tail [Fintype C] (i : (FullFamilyTail.pSpec (C := C) m).ChallengeIdx) :
    rbrError data m bat (ChallengeIdx.sumEquiv (.inr i)) = 2 / Fintype.card C := by
  simp only [rbrError, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
  exact FullFamilyTail.rbrError_eq m i

/-- Knowledge states of the actual composed oracle verifier, preserving the head guard. -/
def knowledgeStateFunction [Fintype C] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier data m layout bat pc).toVerifier.KnowledgeStateFunction init impl
      (ScalarFamily.relIn data m layout pc) pc.evalRel (extractor data m layout bat pc) := by
  let K := Verifier.KnowledgeStateFunction.appendGuarded
    (ScalarFamily.guardedForm data m layout bat pc)
    (ScalarFamily.knowledgeStateFunction data m layout bat pc init impl)
    (FullFamilyTail.knowledgeStateFunction data m bat pc init impl)
  exact {
    toFun := K.toFun
    toFun_empty := K.toFun_empty
    toFun_next := K.toFun_next
    toFun_full := fun stmt tr p h => K.toFun_full stmt tr p (by
      simpa only [Verifier.run, verifier_toVerifier] using h) }

/-- The concrete reduction has exact fixed-prefix knowledge security on the original opening. -/
theorem rbrKnowledgeSoundnessWorstCaseWith [IsDomain C] [Fintype C]
    (hfunctional : pc.Functional) (hinj : Function.Injective (algebraMap data.P C))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (ScalarFamily.relIn data m layout pc) pc.evalRel (verifier data m layout bat pc).toVerifier
      (Witness data m layout) (extractor data m layout bat pc)
      (knowledgeStateFunction data m layout bat pc init impl) (rbrError data m bat) := by
  exact Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first
    (ScalarFamily.guardedForm data m layout bat pc)
    (ScalarFamily.knowledgeStateFunction data m layout bat pc init impl)
    (FullFamilyTail.knowledgeStateFunction data m bat pc init impl)
    (ScalarFamily.rbrKnowledgeSoundnessWorstCaseWith data m layout bat pc
      hfunctional hinj init impl)
    (FullFamilyTail.rbrKnowledgeSoundnessWorstCaseWith data m bat pc hfunctional init impl)

/-- The averaged theorem uses the same proved exact extractor and knowledge-state function. -/
theorem rbrKnowledgeSoundnessWith [IsDomain C] [Fintype C]
    (hfunctional : pc.Functional) (hinj : Function.Injective (algebraMap data.P C))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWith init impl
      (ScalarFamily.relIn data m layout pc) pc.evalRel (verifier data m layout bat pc).toVerifier
      (Witness data m layout) (extractor data m layout bat pc)
      (knowledgeStateFunction data m layout bat pc init impl) (rbrError data m bat) :=
  Verifier.rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith init impl
    (rbrKnowledgeSoundnessWorstCaseWith data m layout bat pc hfunctional hinj init impl)

end RingSwitching.Packing.ScalarOpening
