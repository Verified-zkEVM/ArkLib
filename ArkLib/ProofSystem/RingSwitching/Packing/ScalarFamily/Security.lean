/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.ScalarFamily.Phase

/-!
# Exact security and completeness of scalar-to-family composition

The actual append extractor first unpacks the packed polynomial, then reconstructs the original
scalar source. Its knowledge states preserve the first guard beyond the seam. Both component
worst-case proofs are consumed directly; no averaged-to-worst-case inference is used.
Commitment functionality is an explicit premise of the probability bounds. The state
definitions and completeness theorem apply to the underlying commitment relation.
-/

noncomputable section

namespace RingSwitching.Packing.ScalarFamily

open MvPolynomial OracleSpec OracleComp ProtocolSpec
open scoped NNReal

variable {B : Type} [CommRing B] (data : PackingData B) (m : ℕ)
  (layout : ScalarHead.ClaimLayout data m)
  {C : Type} [CommRing C] [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C]
  (bat : BatchingStrategy C data.ιE) (pc : PackedCommitment data.P m)

/-- The appended intermediate witnesses retain the scalar source through its first step. -/
abbrev WitMid : Fin 4 → Type :=
  Verifier.KnowledgeAppend.Witness (ScalarHead.WitMid data m layout) (FullFamily.WitMid data m)

/-- The actual library append extractor, using the first verifier's true passing verdict. -/
def extractor : Extractor.RoundByRound []ₒ
    (ScalarHead.Input data m layout × (∀ j, pc.OStmt j)) layout.Source
    (data.P⦃≤ 1⦄[X Fin m]) (pSpec data bat) (WitMid data m layout) :=
  (ScalarHead.extractor data m layout pc).append (FullFamily.extractor data m bat pc)
    (ScalarHead.guardedForm data m layout pc).out

/-- The concrete error function transported along the actual appended challenge indices. -/
def rbrError : (pSpec data bat).ChallengeIdx → ℝ≥0 :=
  Sum.elim (fun _ => 0) (FullFamily.rbrError data bat) ∘ ChallengeIdx.sumEquiv.symm

omit [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C] in
/-- The scalar head has no challenge, so every composed challenge has the batching error. -/
theorem rbrError_eq (i : (pSpec data bat).ChallengeIdx) : rbrError data bat i = bat.error := by
  obtain ⟨j, rfl⟩ := ChallengeIdx.sumEquiv.surjective i
  rcases j with j | j
  · rcases j with ⟨⟨j, hj⟩, hdir⟩
    have : j = 0 := by omega
    subst j
    contradiction
  · simp only [rbrError, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr,
      FullFamily.rbrError]

/-- Exact appended knowledge states for the actual oracle verifier after materialization. -/
def knowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier data m layout bat pc).toVerifier.KnowledgeStateFunction init impl
      (relIn data m layout pc) (relOut data m bat pc) (extractor data m layout bat pc) := by
  let K := Verifier.KnowledgeStateFunction.appendGuarded (ScalarHead.guardedForm data m layout pc)
    (ScalarHead.knowledgeStateFunction data m layout pc init impl)
    (FullFamily.knowledgeStateFunction data m bat pc init impl)
  exact {
    toFun := K.toFun
    toFun_empty := K.toFun_empty
    toFun_next := K.toFun_next
    toFun_full := fun stmt tr p h => K.toFun_full stmt tr p (by
      simpa only [Verifier.run, verifier_toVerifier] using h) }

/-- Actual scalar-to-family composition, at the exact appended extractor and knowledge state. -/
theorem rbrKnowledgeSoundnessWorstCaseWith
    (hfunctional : pc.Functional) (hinj : Function.Injective (algebraMap data.P C))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (relIn data m layout pc) (relOut data m bat pc) (verifier data m layout bat pc).toVerifier
      (WitMid data m layout) (extractor data m layout bat pc)
      (knowledgeStateFunction data m layout bat pc init impl) (rbrError data bat) := by
  have h := Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first
    (ScalarHead.guardedForm data m layout pc)
    (ScalarHead.knowledgeStateFunction data m layout pc init impl)
    (FullFamily.knowledgeStateFunction data m bat pc init impl)
    (ScalarHead.rbrKnowledgeSoundnessWorstCaseWith data m layout pc init impl)
    (FullFamily.rbrKnowledgeSoundnessWorstCaseWith data m bat pc hfunctional hinj init impl)
  exact h

/-- Averaging the proved fixed-prefix contract preserves the same explicit extractor. -/
theorem rbrKnowledgeSoundnessWith
    (hfunctional : pc.Functional) (hinj : Function.Injective (algebraMap data.P C))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWith init impl
      (relIn data m layout pc) (relOut data m bat pc) (verifier data m layout bat pc).toVerifier
      (WitMid data m layout) (extractor data m layout bat pc)
      (knowledgeStateFunction data m layout bat pc init impl) (rbrError data bat) :=
  Verifier.rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith init impl
    (rbrKnowledgeSoundnessWorstCaseWith data m layout bat pc hfunctional hinj init impl)

/-- The existential library contract follows from the exact composed objects. -/
theorem rbrKnowledgeSoundness
    (hfunctional : pc.Functional) (hinj : Function.Injective (algebraMap data.P C))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier data m layout bat pc).rbrKnowledgeSoundness init impl
      (relIn data m layout pc) (relOut data m bat pc) (rbrError data bat) :=
  ⟨WitMid data m layout, extractor data m layout bat pc,
    knowledgeStateFunction data m layout bat pc init impl,
    rbrKnowledgeSoundnessWith data m layout bat pc hfunctional hinj init impl⟩

/-- Stateful perfect completeness of the actual composed oracle reduction. The full-family
phase is complete from every state at the seam, and its first step is a prover message. -/
theorem perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction data m layout bat pc).perfectCompleteness init impl
      (relIn data m layout pc) (relOut data m bat pc) := by
  change (reduction data m layout bat pc).toReduction.perfectCompleteness init impl _ _
  rw [reduction_toReduction]
  exact Reduction.append_perfectCompleteness_of_guarded_verifiers
    (ScalarHead.reduction data m layout pc).toReduction
    (FullFamily.reduction data m bat pc).toReduction
    (ScalarHead.guardedForm data m layout pc) (FullFamily.guardedForm data m bat pc)
    (fun _ => Or.inr rfl)
    (ScalarHead.perfectCompleteness data m layout pc init impl)
    (fun s => FullFamily.perfectCompleteness data m bat pc (pure s) impl)

end RingSwitching.Packing.ScalarFamily

end
