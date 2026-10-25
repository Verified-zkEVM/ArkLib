/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.FRIBinius.Unrolled.Core
public import ArkLib.ProofSystem.Binius.FRIBinius.Unrolled.Spec

/-!
# Fused tensor batching and Binary Basefold

The DP24 tensor head produces a product claim for the packed polynomial. The tail runs one
interleaved sumcheck/folding loop and the repeated query phase. It does not run the standalone
ring-switching sumcheck before Binary Basefold.

The source witness is one small-field multilinear polynomial `t`; the shared head derives
its packed polynomial rather than asking for an unrelated second witness. `inputRelation_iff`
and `strictInputRelation_iff` expand the two public contracts: both require the claimed
evaluation of `t`, while the former requires unique-radius compatibility of its packed
encoding and the latter requires exact encoding. `honest_input` supplies the exact relation
for every source polynomial. The honest reduction and soundness verifier coincide by
`fullReduction_verifier`.

`outputContext` fills legacy metadata at the query boundary. It does not change the query
computation, as proved by `Core.query_verify_output_context_irrelevant`; the original query
and batching challenge remain available throughout the fused sumcheck itself. No original
claim is reconstructed from the batching target.

The exported security results are worst-case and averaged round-by-round knowledge soundness.
Their challenge-error sum is bounded by `Spec`'s `concreteError`, with one sumcheck loss of
`2ℓ'/|L|`. This module does not use the legacy admitted implication from round-by-round to
plain knowledge soundness.

The full operational definitions currently inherit noncomputability from `Head.verifier`,
`sumcheckFoldOracleVerifier` and `queryOracleVerifier`, and their honest prover counterparts.
The tensor and polynomial representations of those existing phases are mathematical views;
the full composite is not claimed to be an executable implementation. The new terminal
verifier itself is computable and its guard has runtime regression tests.

## Exact completeness and proximity-based extraction

Perfect completeness is proved for exact packed encodings, while round-by-round knowledge
soundness uses unique-decoding-radius compatibility with the same packed polynomial. Both
input relations require the original claimed evaluation. This separation is consistent with
BaseFold [ZCF24], Definition 8 and Theorem 4: completeness concerns honestly generated
commitments, whereas extraction permits a nearby encoding satisfying the claimed evaluation.
We do not identify BaseFold's coset-distance predicate with our compatibility predicate, nor
derive our RBR theorem from its knowledge-soundness theorem. No perfect-completeness claim
is made for arbitrary nearby-but-inexact oracles. See also `BinaryBasefold/Relations.lean`
for the shared relation-level explanation. DP24 remains the reference for the construction.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over Binary
  Towers*][DP24]
* [Zeilberger, H., Chen, B. and Fisch, B., *BaseFold: Efficient Field-Agnostic Polynomial
  Commitment Schemes from Foldable Codes*][ZCF24]
-/

@[expose] public section

namespace Binius.FRIBinius.Unrolled

open OracleSpec OracleComp ProtocolSpec Module RingSwitching RingSwitching.Packing
open Binius.BinaryBasefold
open scoped NNReal

variable (κ : ℕ) {L : Type} [Field L] [Fintype L] [DecidableEq L] [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
  [Fact (Fintype.card K = 2)] [Algebra K L]
variable (β : Basis (Fin (2 ^ κ)) K L) [Fact (β 0 = 1)]
variable {ℓ ℓ' R ϑ : ℕ} [NeZero ℓ'] [NeZero R] [NeZero ϑ] [Fact (ϑ ∣ ℓ')]
variable (h_rate : ℓ' + R < 2 ^ κ) (h_l : ℓ = ℓ' + κ)

/-- The public product multiplier derived from the original query and batching challenge. -/
noncomputable def fusedMultiplier :=
  Head.multiplier (PackingData.ofBasis (biniusProfile κ L K β).basis) ℓ'
    (TensorPrefix.layout (biniusProfile κ L K β) h_l) (BatchingRule.eqFold L κ)

/-- The original tensor-carrier batching verifier, using relaxed initial-oracle compatibility. -/
noncomputable def headVerifier :=
  Head.verifier (PackingData.ofBasis (biniusProfile κ L K β).basis) ℓ'
    (TensorPrefix.layout (biniusProfile κ L K β) h_l)
    (TensorPrefix.messageEquiv (biniusProfile κ L K β)) (BatchingRule.eqFold L κ)
    (Frontier.commitment K β (ϑ := ϑ) (h_rate := h_rate))

omit [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K]
  [Fact (Fintype.card K = 2)] [Fact (β 0 = 1)] [NeZero ℓ'] in
/-- The fused terminal uses exactly the tensor equality multiplier of the original protocol. -/
theorem fusedMultiplier_evaluate_eq (r : Fin ℓ → L) (c : Fin κ → L)
    (r' : Fin ℓ' → L) :
    (fusedMultiplier κ K β h_l).evaluate (r, c) r' =
      compute_final_eq_value κ L K (biniusProfile κ L K β) ℓ ℓ' h_l r r' c :=
  TensorPrefix.multiplier_evaluate_eq_compute_final_eq_value
    (biniusProfile κ L K β) h_l r c r'

variable (outputContext : ((Fin ℓ → L) × (Fin κ → L)) → SumcheckBaseContext L ℓ')

/-- Tensor batching followed directly by the fused folding tail. The context projection only
populates metadata ignored by the query verifier; no extra message or sumcheck is introduced. -/
noncomputable def fullVerifier (γ : ℕ) :=
  OracleVerifier.append (Oₛ₃ := fun i : Empty => nomatch i)
    (headVerifier κ K β (ϑ := ϑ) h_rate h_l)
    (Core.tailVerifier K β (fusedMultiplier κ K β h_l) outputContext γ
      (ϑ := ϑ) (h_rate := h_rate))

/-- The relaxed original evaluation relation, anchored to the same packed oracle. -/
def inputRelation :=
  Head.relIn (PackingData.ofBasis (biniusProfile κ L K β).basis) ℓ'
    (TensorPrefix.layout (biniusProfile κ L K β) h_l)
    (Frontier.commitment K β (ϑ := ϑ) (h_rate := h_rate))

omit [DecidableEq K] [Fact (β 0 = 1)] [NeZero R] in
/-- The tensor batching head contributes exactly `κ/|L|` per batching challenge. -/
theorem head_rbrKnowledgeSoundnessWorstCase {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl ([]ₒ) (StateT σ ProbComp)) :
    (headVerifier κ K β (ϑ := ϑ) h_rate h_l).toVerifier.rbrKnowledgeSoundnessWorstCase
      init impl (inputRelation κ K β (ϑ := ϑ) h_rate h_l)
      (ProductSumcheck.rel (fusedMultiplier κ K β h_l)
        (Frontier.commitment K β (ϑ := ϑ) (h_rate := h_rate)) 0)
      (fun _ => (κ : ℝ≥0) / Fintype.card L) := by
  apply (Verifier.rbrKnowledgeSoundnessWorstCase_iff_exists_with init impl _ _ _ _).mpr
  exact ⟨_, _, _, Head.rbrKnowledgeSoundnessWorstCaseWith
    (PackingData.ofBasis (biniusProfile κ L K β).basis) ℓ'
    (TensorPrefix.layout (biniusProfile κ L K β) h_l)
    (TensorPrefix.messageEquiv (biniusProfile κ L K β)) (BatchingStrategy.eqFold L κ)
    (Frontier.commitment K β (ϑ := ϑ) (h_rate := h_rate))
    (Frontier.commitment_functional K β) (fun _ _ h => h) init impl⟩

noncomputable instance (γ : ℕ) : ∀ i, OracleInterface
    ((pSpec κ K β (ϑ := ϑ) h_rate γ).Message i) :=
  instOracleInterfaceMessageAppend

noncomputable instance (γ : ℕ) : ∀ i, SampleableType
    ((pSpec κ K β (ϑ := ϑ) h_rate γ).Challenge i) :=
  instSampleableTypeChallengeAppend

/-- Worst-case round-by-round knowledge soundness of the full fused verifier. -/
theorem fullVerifier_rbrKnowledgeSoundnessWorstCase (γ : ℕ) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl ([]ₒ) (StateT σ ProbComp)) :
    ((fullVerifier κ K β (ϑ := ϑ) h_rate h_l outputContext γ).toVerifier
      (Oₛₒ := fun i : Empty => nomatch i)).rbrKnowledgeSoundnessWorstCase init impl
      (inputRelation κ K β (ϑ := ϑ) h_rate h_l) acceptRejectOracleRel
      (fullError κ K β (ϑ := ϑ) h_rate γ) := by
  exact OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first
    (Oₛ₃ := fun i : Empty => nomatch i) _ _
    (Head.guardedForm (PackingData.ofBasis (biniusProfile κ L K β).basis) ℓ'
      (TensorPrefix.layout (biniusProfile κ L K β) h_l)
      (TensorPrefix.messageEquiv (biniusProfile κ L K β)) (BatchingRule.eqFold L κ)
      (Frontier.commitment K β (ϑ := ϑ) (h_rate := h_rate)))
    (head_rbrKnowledgeSoundnessWorstCase κ K β h_rate h_l init impl)
    (Core.tailVerifier_rbrKnowledgeSoundnessWorstCase K β
      (fusedMultiplier κ K β h_l) outputContext γ init impl)

/-- Averaging over prefixes preserves the same fused round-by-round error family. -/
theorem fullVerifier_rbrKnowledgeSoundness (γ : ℕ) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl ([]ₒ) (StateT σ ProbComp)) :
    ((fullVerifier κ K β (ϑ := ϑ) h_rate h_l outputContext γ).toVerifier
      (Oₛₒ := fun i : Empty => nomatch i)).rbrKnowledgeSoundness init impl
      (inputRelation κ K β (ϑ := ϑ) h_rate h_l) acceptRejectOracleRel
      (fullError κ K β (ϑ := ϑ) h_rate γ) :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (fullVerifier_rbrKnowledgeSoundnessWorstCase κ K β h_rate h_l outputContext γ init impl)

/-- The exact input relation used for honest perfect completeness. -/
def strictInputRelation :=
  Head.relIn (PackingData.ofBasis (biniusProfile κ L K β).basis) ℓ'
    (TensorPrefix.layout (biniusProfile κ L K β) h_l)
    (Frontier.strictCommitment K β (ϑ := ϑ) (h_rate := h_rate))

/-- The original tensor head's honest prover followed by the fused folding prover. -/
noncomputable def fullReduction (γ : ℕ) :=
  OracleReduction.append (Oₛ₃ := fun i : Empty => nomatch i)
    (Head.reduction (PackingData.ofBasis (biniusProfile κ L K β).basis) ℓ'
      (TensorPrefix.layout (biniusProfile κ L K β) h_l)
      (TensorPrefix.messageEquiv (biniusProfile κ L K β)) (BatchingRule.eqFold L κ)
      (Frontier.strictCommitment K β (ϑ := ϑ) (h_rate := h_rate)))
    (Core.tailReduction K β (fusedMultiplier κ K β h_l) outputContext γ
      (ϑ := ϑ) (h_rate := h_rate))

/-- Exact versus relaxed compatibility changes the theorem relation, not the verifier. -/
theorem fullReduction_verifier (γ : ℕ) :
    (fullReduction κ K β (ϑ := ϑ) h_rate h_l outputContext γ).verifier
        (Oₛₒ := fun i : Empty => nomatch i) =
      fullVerifier κ K β (ϑ := ϑ) h_rate h_l outputContext γ := rfl

/-- Perfect completeness of the full fused protocol on exact packed encodings. -/
theorem fullReduction_perfectCompleteness (γ : ℕ) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl ([]ₒ) (StateT σ ProbComp)) :
    (fullReduction κ K β (ϑ := ϑ) h_rate h_l outputContext γ).perfectCompleteness
      (Oₛₒ := fun i : Empty => nomatch i) init impl
      (strictInputRelation κ K β (ϑ := ϑ) h_rate h_l) acceptRejectOracleRel := by
  apply OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (Oₛ₃ := fun i : Empty => nomatch i)
    (Head.reduction (PackingData.ofBasis (biniusProfile κ L K β).basis) ℓ'
      (TensorPrefix.layout (biniusProfile κ L K β) h_l)
      (TensorPrefix.messageEquiv (biniusProfile κ L K β)) (BatchingRule.eqFold L κ)
      (Frontier.strictCommitment K β (ϑ := ϑ) (h_rate := h_rate)))
    (Core.tailReduction K β (fusedMultiplier κ K β h_l) outputContext γ
      (ϑ := ϑ) (h_rate := h_rate))
    (Head.guardedForm (PackingData.ofBasis (biniusProfile κ L K β).basis) ℓ'
      (TensorPrefix.layout (biniusProfile κ L K β) h_l)
      (TensorPrefix.messageEquiv (biniusProfile κ L K β)) (BatchingRule.eqFold L κ)
      (Frontier.strictCommitment K β (ϑ := ϑ) (h_rate := h_rate)))
    (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i => nomatch i)))
    (fun _ => Or.inl inferInstance)
    (Head.perfectCompleteness (PackingData.ofBasis (biniusProfile κ L K β).basis) ℓ'
      (TensorPrefix.layout (biniusProfile κ L K β) h_l)
      (TensorPrefix.messageEquiv (biniusProfile κ L K β)) (BatchingRule.eqFold L κ)
      (Frontier.strictCommitment K β (ϑ := ϑ) (h_rate := h_rate)) init impl)
  intro s
  have ht := Core.tailReduction_perfectCompleteness K β (fusedMultiplier κ K β h_l)
    outputContext γ (ϑ := ϑ) (h_rate := h_rate) (pure s) impl
  rw [Frontier.strictInputRelation_eq_shared] at ht
  exact ht

omit [DecidableEq K] [Fact (β 0 = 1)] [NeZero R] [SampleableType L] in
/-- Expanded soundness input: the claimed evaluation is exact and the packed codeword is
uniquely decoding-close to the committed first oracle. -/
theorem inputRelation_iff (r : Fin ℓ → L) (s : L)
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)
    (t : Sumcheck.Structured.MultilinearPoly K ℓ) :
    (((r, s), ost), t) ∈ inputRelation κ K β (ϑ := ϑ) h_rate h_l ↔
      s = MvPolynomial.aeval r t.val ∧ FirstOracleWitnessConsistent K β
        (packMLE κ L K ℓ ℓ' h_l (biniusProfile κ L K β).basis t)
        (getFirstOracle K β ost) := by
  change (s = MvPolynomial.aeval r t.val ∧ _) ↔ _
  rw [TensorPrefix.packedMLE_components_eq_packMLE]
  rfl

omit [DecidableEq K] [Fact (β 0 = 1)] [NeZero R] [SampleableType L] in
/-- Expanded completeness input: the claimed evaluation and the packed first encoding
are both exact. -/
theorem strictInputRelation_iff (r : Fin ℓ → L) (s : L)
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)
    (t : Sumcheck.Structured.MultilinearPoly K ℓ) :
    (((r, s), ost), t) ∈ strictInputRelation κ K β (ϑ := ϑ) h_rate h_l ↔
      s = MvPolynomial.aeval r t.val ∧ getFirstOracle K β ost = firstOracleEncoding K β
        (packMLE κ L K ℓ ℓ' h_l (biniusProfile κ L K β).basis t) := by
  change (s = MvPolynomial.aeval r t.val ∧ _) ↔ _
  rw [TensorPrefix.packedMLE_components_eq_packMLE]
  rfl

omit [DecidableEq K] [Fact (β 0 = 1)] [NeZero R] [SampleableType L] in
/-- Exact honest inputs also satisfy the relaxed knowledge-soundness relation. -/
theorem strictInputRelation_subset_inputRelation :
    strictInputRelation κ K β (ϑ := ϑ) h_rate h_l ⊆
      inputRelation κ K β (ϑ := ϑ) h_rate h_l := by
  rintro ⟨⟨⟨r, s⟩, ost⟩, t⟩ h
  have hs := (strictInputRelation_iff κ K β h_rate h_l r s ost t).mp h
  apply (inputRelation_iff κ K β h_rate h_l r s ost t).mpr
  refine ⟨hs.1, ?_⟩
  rw [hs.2]
  exact firstOracleWitnessConsistent_firstOracleEncoding K β _

omit [DecidableEq K] [Fact (β 0 = 1)] [NeZero R] [SampleableType L] in
/-- Every source polynomial supplies an honest input by committing to its exact packed encoding.
In particular the completeness relation is not an additional constraint on the source. -/
theorem honest_input (r : Fin ℓ → L) (t : Sumcheck.Structured.MultilinearPoly K ℓ) :
    (((r, MvPolynomial.aeval r t.val), honestInitialOracleStatement K β ϑ
      (h_ℓ_add_R_rate := h_rate)
      (packMLE κ L K ℓ ℓ' h_l (biniusProfile κ L K β).basis t)), t) ∈
        strictInputRelation κ K β (ϑ := ϑ) h_rate h_l := by
  rw [strictInputRelation_iff]
  exact ⟨rfl, getFirstOracle_honestInitialOracleStatement K β ϑ _⟩

end Binius.FRIBinius.Unrolled
