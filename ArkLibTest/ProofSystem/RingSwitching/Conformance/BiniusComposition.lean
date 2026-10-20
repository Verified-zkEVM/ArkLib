/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLibTest.ProofSystem.RingSwitching.Conformance.Binius
import ArkLib.ProofSystem.RingSwitching.Packing.General

/-!
# Ring-switching composites at a concrete instance

This file instantiates the composed worst-case round-by-round knowledge-soundness theorems of ring
switching at the GF(4)/GF(2) orientation fixture, with the binding oracle statement
`exactOStmtIn`:

* `core_rbrKnowledgeSoundnessWorstCase` and `batchingCore_rbrKnowledgeSoundnessWorstCase`
  discharge their uniqueness hypothesis at the fixture. `batchingCore_direct` builds the batching
  composite from the guarded composition lemma itself, rather than from its packaged corollary.
* `core_relIn_inhabited` and `batching_relIn_inhabited` show that the composites' input relations
  contain the honest inputs, so the theorems are not vacuous.
* `core_error` and `batchingCore_error` compute the errors: `κ/|L|` at the batching challenge (here
  `κ = 1`) and `2/|L|` at every sum-check challenge.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal
open RingSwitching Sumcheck.Structured
open ConcreteBinaryTower
open ArkLibTest.RingSwitchingOrientation renaming K → GF2, L → GF4, p → P₄, r → r₀, t → tX₀
open ArkLibTest.RingSwitchingOrientation (beta tp shat beta_zero beta_one column_zero)

namespace ArkLibTest.RingSwitchingConformance.BiniusComposition

open ArkLibTest.RingSwitchingConformance.Binius

attribute [local instance] ArkLibTest.RingSwitchingOrientation.algebraKL

noncomputable local instance : SampleableType GF4 := SampleableType.ofFintype GF4

/-- The binding oracle statement determines its packed polynomial. -/
theorem exactOStmtIn_functional : exactOStmtIn.Functional :=
  fun _ _ _ h₁ h₂ => h₁.trans h₂.symm

/-! ## The core interaction -/

/-- The core interaction is worst-case round-by-round knowledge sound at the fixture. -/
theorem core_rbrKnowledgeSoundnessWorstCase {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCase init impl
      (verifier := (SumcheckPhase.coreInteractionOracleVerifier 1 GF4 GF2 P₄ 2 1 rfl
        exactOStmtIn).toVerifier)
      (relIn := sumcheckRoundRelation 1 GF4 GF2 P₄ 2 1 rfl exactOStmtIn 0)
      (relOut := exactOStmtIn.toRelInput) (SumcheckPhase.coreInteractionRbrKnowledgeError GF4 1) :=
  SumcheckPhase.coreInteraction_rbrKnowledgeSoundnessWorstCase 1 GF4 GF2 P₄ 2 1 rfl exactOStmtIn
    (init := init) (impl := impl) exactOStmtIn_functional

/-- The core interaction's input relation holds at the honest accepted round-zero statement. -/
theorem core_relIn_inhabited :
    ((acceptedStatement P₄ (claimAt 0) shat 0, oStmt₀), wit₀) ∈
      sumcheckRoundRelation 1 GF4 GF2 P₄ 2 1 rfl exactOStmtIn 0 :=
  ((batching_conforms P₄ rfl exactOStmtIn (claimAt 0) oStmt₀ shat 0 wit₀).2
    ⟨rfl, (witnessStructuralInvariant_iff P₄ rfl (claimAt 0) shat 0 wit₀).1 rfl,
      honest_sumcheckClaimRel 0, by
        change (0 : GF4) = ∑ v, (prefixLayout P₄ 1).weight (prefixQuery P₄ rfl r₀) v * _
        rw [sum_weight_zero, column_zero]⟩).2

/-- Every core challenge costs exactly `2/|L|`. -/
theorem core_error (j : (pSpecCoreInteraction GF4 1).ChallengeIdx) :
    SumcheckPhase.coreInteractionRbrKnowledgeError GF4 1 j = 2 / (Fintype.card GF4 : ℝ≥0) := by
  obtain ⟨j, rfl⟩ := ChallengeIdx.sumEquiv.surjective j
  rcases j with j | j
  · simp [SumcheckPhase.coreInteractionRbrKnowledgeError,
      SumcheckPhase.coreInteractionRbrKnowledgeErrorWithDegree,
      SumcheckPhase.sumcheckLoopRbrKnowledgeErrorWithDegree, roundKnowledgeError]
  · -- The final step sends no challenge.
    exact absurd j.2 (by
      have := j.1.isLt
      fin_cases j)

/-! ## Batching followed by the core interaction -/

/-- Batching followed by the core interaction is worst-case round-by-round knowledge sound at the
fixture, for every `MLIOPCS` whose oracle statement is `exactOStmtIn`. -/
theorem batchingCore_rbrKnowledgeSoundnessWorstCase {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) (M : MLIOPCS GF4 1)
    (hM : M.toAbstractOStmtIn = exactOStmtIn) :
    Verifier.rbrKnowledgeSoundnessWorstCase init impl
      (verifier := (FullRingSwitching.batchingCoreVerifier 1 GF4 GF2 P₄ 2 1 rfl M).toVerifier)
      (relIn := FullRingSwitching.fullInputRelation 1 GF4 GF2 P₄ 2 1 rfl M)
      (relOut := M.toAbstractOStmtIn.toRelInput)
      (FullRingSwitching.batchingCoreRbrKnowledgeError 1 GF4 GF2 P₄ 1) :=
  FullRingSwitching.batchingCore_rbrKnowledgeSoundnessWorstCase 1 GF4 GF2 P₄ 2 1 rfl M init
    (hM ▸ exactOStmtIn_functional)

/-- The same composite over `exactOStmtIn`, built directly from the guarded composition lemma. -/
theorem batchingCore_direct {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCase init impl
      (verifier := (OracleVerifier.append (oSpec := []ₒ)
        (BatchingPhase.oracleVerifier 1 GF4 GF2 P₄ 2 1 rfl exactOStmtIn)
        (SumcheckPhase.coreInteractionOracleVerifier 1 GF4 GF2 P₄ 2 1 rfl
          exactOStmtIn)).toVerifier)
      (relIn := BatchingPhase.batchingInputRelation 1 GF4 GF2 P₄ 2 1 rfl exactOStmtIn)
      (relOut := exactOStmtIn.toRelInput)
      (FullRingSwitching.batchingCoreRbrKnowledgeError 1 GF4 GF2 P₄ 1) :=
  OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first _ _
    (Verifier.GuardedForm.ofEmpty _ (fun stmt =>
      (⟨0, Fin.elim0, ⟨⟨stmt.1.t_eval_point, stmt.1.original_claim⟩, 0, fun _ => 0⟩⟩, stmt.2)))
    (BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundnessWorstCase 1 GF4 GF2 P₄ 2 1 rfl
      exactOStmtIn (init := init) (impl := impl) exactOStmtIn_functional)
    (core_rbrKnowledgeSoundnessWorstCase init impl)

/-- The batching input relation holds at the honest input: source `X₀`, its packing `tp`, the
claim `X₀(0) = 0`, and the committed oracle `tp`. -/
theorem batching_relIn_inhabited :
    ((claimAt 0, oStmt₀), (⟨tX₀, tp⟩ : BatchingWitIn GF4 GF2 2 1)) ∈
      BatchingPhase.batchingInputRelation 1 GF4 GF2 P₄ 2 1 rfl exactOStmtIn := by
  change BatchingPhase.batchingInputRelationProp 1 GF4 GF2 P₄ 2 1 rfl exactOStmtIn _ _ _
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · simp [claimAt, tX₀, r₀]
  · rfl

/-- The batching challenge costs `κ/|L| = 1/|L|`, and every core challenge costs `2/|L|`. -/
theorem batchingCore_error
    (j : (pSpecBatching 1 GF4 GF2 P₄ ++ₚ pSpecCoreInteraction GF4 1).ChallengeIdx) :
    FullRingSwitching.batchingCoreRbrKnowledgeError 1 GF4 GF2 P₄ 1 j =
      (if j.1.val = 1 then 1 / (Fintype.card GF4 : ℝ≥0) else 0) ∨
    FullRingSwitching.batchingCoreRbrKnowledgeError 1 GF4 GF2 P₄ 1 j =
      2 / (Fintype.card GF4 : ℝ≥0) := by
  obtain ⟨j, rfl⟩ := ChallengeIdx.sumEquiv.surjective j
  rcases j with j | j
  · left
    rcases j with ⟨⟨k, hk⟩, hd⟩
    interval_cases k <;>
      simp_all [FullRingSwitching.batchingCoreRbrKnowledgeError,
        BatchingPhase.batchingRBRKnowledgeError, ChallengeIdx.sumEquiv, ChallengeIdx.inl]
  · right
    simp only [FullRingSwitching.batchingCoreRbrKnowledgeError, Equiv.symm_apply_apply,
      Sum.elim_inr]
    exact core_error j

end ArkLibTest.RingSwitchingConformance.BiniusComposition
