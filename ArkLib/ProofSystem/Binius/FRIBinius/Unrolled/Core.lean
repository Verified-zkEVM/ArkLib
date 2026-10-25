/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.FRIBinius.Unrolled.FinalSumcheck
public import ArkLib.ProofSystem.Binius.FRIBinius.Unrolled.Frontier
public import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase
public import ArkLib.ProofSystem.Binius.BinaryBasefold.General

/-!
# The fused product-sumcheck and folding verifier

One generic sumcheck/folding loop consumes the ring-switching product claim. Its terminal
check uses the same public multiplier, rather than the ordinary opening equality polynomial.
The oracle commitments and the final folding relation are unchanged, so the existing query
phase can consume the output. No separate ring-switching sumcheck is inserted.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over Binary
  Towers*][DP24]
-/

@[expose] public section

namespace Binius.FRIBinius.Unrolled.Core

open Binius.BinaryBasefold Binius.BinaryBasefold.CoreInteraction
open OracleSpec OracleComp ProtocolSpec
open scoped NNReal

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
  [Fact (Fintype.card K = 2)] [Algebra K L]
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
variable (β : Fin r → L) [Fact (LinearIndependent K β)] [Fact (β 0 = 1)]
variable {ℓ R ϑ : ℕ} [NeZero ℓ] [NeZero R] [NeZero ϑ]
  {h_rate : ℓ + R < r} [Fact (ϑ ∣ ℓ)]
variable {Context : Type}
variable (multiplier : RingSwitching.Packing.ProductSumcheck.Multiplier Context L ℓ)
variable (outputContext : Context → SumcheckBaseContext L ℓ) (𝓑 : Fin 2 ↪ L)

/-- Interleave the product sumcheck with folds, then check its terminal scalar. -/
noncomputable def verifier :=
  OracleVerifier.append
    (sumcheckFoldOracleVerifier K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
      (𝓑 := 𝓑) (multpoly := multiplier.polynomial))
    (Terminal.verifier K β multiplier.evaluate outputContext (ϑ := ϑ) (h_rate := h_rate))

omit [DecidableEq K] in
/-- The fused core has the same per-challenge error as one Binary Basefold loop. -/
theorem rbrKnowledgeSoundnessWorstCase {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl ([]ₒ) (StateT σ ProbComp)) :
    (verifier K β multiplier outputContext 𝓑 (ϑ := ϑ)
      (h_rate := h_rate)).toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
        (𝓑 := 𝓑) (multpoly := multiplier.polynomial) 0)
      (finalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate))
      (coreInteractionOracleRbrKnowledgeError K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_rate)) := by
  exact OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first _ _
    (sumcheckFoldOracleVerifierGuardedForm K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
      (𝓑 := 𝓑) (multpoly := multiplier.polynomial))
    (sumcheckFoldOracleVerifier_rbrKnowledgeSoundnessWorstCase K β)
    (Terminal.rbrKnowledgeSoundnessWorstCase K β multiplier outputContext 𝓑 init impl)

/-- The fused core followed by the unchanged repeated query check. -/
noncomputable def queryVerifier (γ : ℕ) :=
  OracleVerifier.append (Oₛ₃ := fun i : Empty => nomatch i)
    (verifier K β multiplier outputContext 𝓑 (ϑ := ϑ) (h_rate := h_rate))
    (QueryPhase.queryOracleVerifier K β γ (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate))

omit [SampleableType L] in
/-- Projecting the terminal context does not change the query verifier's computation.
Only the folding challenges and received constant are inspected by that verifier. -/
theorem query_verify_output_context_irrelevant (γ : ℕ)
    (otherContext : Context → SumcheckBaseContext L ℓ)
    (s : Statement (L := L) Context (Fin.last ℓ)) (c : L) :
    (QueryPhase.queryOracleVerifier K β γ (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate)).verify (Oₛₒ := fun i : Empty => nomatch i)
        (Terminal.output outputContext s c) =
    (QueryPhase.queryOracleVerifier K β γ (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate)).verify (Oₛₒ := fun i : Empty => nomatch i)
        (Terminal.output otherContext s c) := by
  rfl

/-- The complete fold-and-query tail retains the ordinary Binary Basefold error family,
but its input relation uses the ring-switching multiplier. -/
theorem queryVerifier_rbrKnowledgeSoundnessWorstCase (γ : ℕ) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl ([]ₒ) (StateT σ ProbComp)) :
    ((queryVerifier K β multiplier outputContext 𝓑 γ (ϑ := ϑ)
      (h_rate := h_rate)).toVerifier (Oₛₒ := fun i : Empty => nomatch i))
      |>.rbrKnowledgeSoundnessWorstCase init impl
      (roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
        (𝓑 := 𝓑) (multpoly := multiplier.polynomial) 0)
      acceptRejectOracleRel
      (FullBinaryBasefold.fullRbrKnowledgeError K β γ (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_rate)) := by
  unfold queryVerifier FullBinaryBasefold.fullRbrKnowledgeError
  exact OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first
    (Oₛ₃ := fun i : Empty => nomatch i) _ _
    (Verifier.GuardedForm.ofEmpty _ (fun input =>
      (⟨⟨0, fun _ => 0, outputContext input.1.ctx⟩, 0⟩, fun _ _ => 0)))
    (rbrKnowledgeSoundnessWorstCase K β multiplier outputContext 𝓑 init impl)
    (QueryPhase.queryOracleVerifier_rbrKnowledgeSoundnessWorstCase K β γ init impl)

/-- The adapter and fused fold/query tail, ready to receive the batching head's output. -/
noncomputable def tailVerifier (γ : ℕ) :=
  OracleVerifier.append (Oₛ₃ := fun i : Empty => nomatch i)
    (Frontier.verifier K β (Context := Context) (ϑ := ϑ) (h_rate := h_rate))
    (queryVerifier K β multiplier outputContext (boolEmbedding L) γ
      (ϑ := ϑ) (h_rate := h_rate))

/-- No-error reformatting followed by the fold-and-query error family. -/
noncomputable def tailError (γ : ℕ) :=
  Opening.openingError K β γ (ϑ := ϑ) (h_rate := h_rate)

/-- Security of the fused tail from the shared batching relation. -/
theorem tailVerifier_rbrKnowledgeSoundnessWorstCase (γ : ℕ) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl ([]ₒ) (StateT σ ProbComp)) :
    ((tailVerifier K β multiplier outputContext γ (ϑ := ϑ) (h_rate := h_rate)).toVerifier
      (Oₛₒ := fun i : Empty => nomatch i)).rbrKnowledgeSoundnessWorstCase init impl
      (RingSwitching.Packing.ProductSumcheck.rel multiplier
        (Frontier.commitment K β (ϑ := ϑ) (h_rate := h_rate)) 0)
      acceptRejectOracleRel (tailError K β γ (ϑ := ϑ) (h_rate := h_rate)) := by
  rw [← Frontier.inputRelation_eq_shared K β multiplier]
  exact OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first
    (Oₛ₃ := fun i : Empty => nomatch i) _ _
    (Frontier.guardedForm K β)
    (Frontier.rbrKnowledgeSoundnessWorstCase K β multiplier init impl)
    (queryVerifier_rbrKnowledgeSoundnessWorstCase K β multiplier outputContext
      (boolEmbedding L) γ init impl)

/-- Honest execution uses the same interleaved folding loop and the fused scalar terminal. -/
noncomputable def reduction :=
  OracleReduction.append
    (sumcheckFoldOracleReduction K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
      (𝓑 := 𝓑) (multpoly := multiplier.polynomial))
    (Terminal.reduction K β multiplier outputContext (ϑ := ϑ) (h_rate := h_rate))

/-- The fused core is perfectly complete for exact honest encodings. -/
theorem perfectCompleteness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl ([]ₒ) (StateT σ ProbComp)) :
    (reduction K β multiplier outputContext 𝓑 (ϑ := ϑ) (h_rate := h_rate)).perfectCompleteness
      init impl
      (strictRoundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
        (𝓑 := 𝓑) (multpoly := multiplier.polynomial) 0)
      (strictFinalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)) := by
  exact OracleReduction.append_perfectCompleteness_of_guarded_verifiers _ _
    (sumcheckFoldOracleVerifierGuardedForm K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
      (𝓑 := 𝓑) (multpoly := multiplier.polynomial))
    (Terminal.guardedForm K β multiplier.evaluate outputContext)
    (fun _ => Or.inl inferInstance)
    (sumcheckFoldOracleReduction_perfectCompleteness K β)
    (fun s => Terminal.perfectCompleteness K β multiplier outputContext 𝓑 (pure s) impl)

/-- The honest fused loop followed by the repeated query phase. -/
noncomputable def queryReduction (γ : ℕ) :=
  OracleReduction.append (Oₛ₃ := fun i : Empty => nomatch i)
    (reduction K β multiplier outputContext 𝓑 (ϑ := ϑ) (h_rate := h_rate))
    (QueryPhase.queryOracleReduction K β γ (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate))

/-- Perfect completeness through the final query acceptance predicate. -/
theorem queryReduction_perfectCompleteness (γ : ℕ) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl ([]ₒ) (StateT σ ProbComp)) :
    (queryReduction K β multiplier outputContext 𝓑 γ (ϑ := ϑ) (h_rate := h_rate))
      |>.perfectCompleteness (Oₛₒ := fun i : Empty => nomatch i) init impl
      (strictRoundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
        (𝓑 := 𝓑) (multpoly := multiplier.polynomial) 0)
      acceptRejectOracleRel := by
  exact OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (Oₛ₃ := fun i : Empty => nomatch i) _ _
    (Verifier.GuardedForm.ofEmpty _ (fun input =>
      (⟨⟨0, fun _ => 0, outputContext input.1.ctx⟩, 0⟩, fun _ _ => 0)))
    (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i => nomatch i)))
    (fun _ => Or.inl inferInstance)
    (perfectCompleteness K β multiplier outputContext 𝓑 init impl)
    (fun s => QueryPhase.queryOracleReduction_perfectCompleteness K β γ (pure s) impl)

/-- Honest initialization followed by the fused fold-and-query reduction. -/
noncomputable def tailReduction (γ : ℕ) :=
  OracleReduction.append (Oₛ₃ := fun i : Empty => nomatch i)
    (Frontier.reduction K β multiplier (ϑ := ϑ) (h_rate := h_rate))
    (queryReduction K β multiplier outputContext (boolEmbedding L) γ
      (ϑ := ϑ) (h_rate := h_rate))

/-- Exact product-claim inputs are accepted by the complete fused tail with probability one. -/
theorem tailReduction_perfectCompleteness (γ : ℕ) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl ([]ₒ) (StateT σ ProbComp)) :
    (tailReduction K β multiplier outputContext γ (ϑ := ϑ) (h_rate := h_rate))
      |>.perfectCompleteness (Oₛₒ := fun i : Empty => nomatch i) init impl
      (Frontier.strictInputRelation K β multiplier (ϑ := ϑ) (h_rate := h_rate))
      acceptRejectOracleRel := by
  exact OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (Oₛ₃ := fun i : Empty => nomatch i) _ _
    (Frontier.guardedForm K β)
    (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i => nomatch i)))
    (fun _ => Or.inl inferInstance)
    (Frontier.perfectCompleteness K β multiplier init impl)
    (fun s => queryReduction_perfectCompleteness K β multiplier outputContext
      (boolEmbedding L) γ (pure s) impl)

end Binius.FRIBinius.Unrolled.Core
