/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Binius.FRIBinius.Unrolled.Frontier
public import ArkLib.ProofSystem.Binius.FRIBinius.Unrolled.Spec
public import ArkLib.OracleReduction.Security.GuardedBridges
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Opening

/-!
# Unrolled FRI-Binius

The unrolled small-field polynomial commitment of [DP24] runs the ring-switching product
sum-check inside the Binary Basefold sum-check-and-fold loop:

1. the tensor batching head (`TensorPrefix.headVerifier`) checks the carrier message against the
   original claim, samples the batching challenge, and outputs a product claim
   `s₀ = ∑_y A(y) · t'(y)` for the packed polynomial `t'` with the ring-switching multiplier
   `A = TensorPrefix.multiplier`;
2. a zero-message frontier (`Frontier`) passes that claim to Binary Basefold;
3. the Binary Basefold core and query protocol (`FullBinaryBasefold.fullOracleVerifier`) runs
   at the same multiplier: its final check is `s_ℓ' = A(r') · c`, evaluated by
   `compute_final_eq_value` (`TensorPrefix.multiplier_evaluate_eq_compute_final_eq_value`).

The input relation is the one of the composition with a separate ring-switching sum-check,
`TensorPrefix.relIn (biniusProfile κ L K β) h_l (binaryBasefoldInput …)`: the claimed evaluation of
the source `t` and unique-radius compatibility of its packed polynomial with the first oracle
(`Conformance.mem_relIn_iff`). Perfect completeness uses its `strictView`, which requires the
exact encoding.

## What the security statements assert

* `fullVerifier_rbrKnowledgeSoundness` is legacy round-by-round knowledge soundness, with error
  `fullError`. Its extractors may be inefficient; since the source type is inhabited, it is
  equivalent to round-by-round soundness of the languages
  (`Verifier.rbrSoundness_iff_rbrKnowledgeSoundness`).
* `fullVerifier_knowledgeSoundness` is terminal knowledge soundness with an unbounded extractor,
  hence equivalent to relation soundness (`Verifier.knowledgeSoundness_iff_relationSoundness`).
* `fullVerifier_soundness` is soundness for the language of the input relation.

All three use the bound `concreteError`. No efficient-extraction or running-time claim is made.

## Computability

The verifier and reduction are noncomputable because the shared batching head and the Binary
Basefold phases are. Making them executable concerns those phases, not this composition.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over Binary
  Towers*][DP24], Construction 5.1 and §5.2.
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

local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩

/-! ## Protocol definitions -/

noncomputable instance (γ : ℕ) : ∀ i, OracleInterface
    ((pSpec κ K β (ϑ := ϑ) h_rate γ).Message i) :=
  instOracleInterfaceMessageAppend

noncomputable instance (γ : ℕ) : ∀ i, SampleableType
    ((pSpec κ K β (ϑ := ϑ) h_rate γ).Challenge i) :=
  instSampleableTypeChallengeAppend

/-- The frontier followed by the Binary Basefold core and query verifier at the ring-switching
multiplier. -/
noncomputable def tailVerifier (γ : ℕ) :=
  OracleVerifier.append (Oₛ₃ := fun i : Empty => nomatch i)
    (Frontier.verifier K β (ϑ := ϑ) (h_rate := h_rate)
      (Context := (Fin ℓ → L) × (Fin κ → L)))
    (FullBinaryBasefold.fullOracleVerifier K β γ
      (TensorPrefix.multiplier (biniusProfile κ L K β) h_l) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L))

/-- The honest frontier followed by the honest Binary Basefold core and query reduction. -/
noncomputable def tailReduction (γ : ℕ) :=
  OracleReduction.append (Oₛ₃ := fun i : Empty => nomatch i)
    (Frontier.reduction K β (TensorPrefix.multiplier (biniusProfile κ L K β) h_l)
      (ϑ := ϑ) (h_rate := h_rate))
    (FullBinaryBasefold.fullOracleReduction K β γ
      (TensorPrefix.multiplier (biniusProfile κ L K β) h_l) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L))

/-- The unrolled FRI-Binius verifier: the tensor batching head, then `tailVerifier`. -/
noncomputable def fullVerifier (γ : ℕ) :=
  OracleVerifier.append (Oₛ₃ := fun i : Empty => nomatch i)
    (TensorPrefix.headVerifier (biniusProfile κ L K β) h_l
      (binaryBasefoldInput κ L K β ℓ' R ϑ h_rate))
    (tailVerifier κ K β (ϑ := ϑ) h_rate h_l γ)

/-- The unrolled FRI-Binius reduction: the honest head, then `tailReduction`. Its verifier is
`fullVerifier` (`fullReduction_verifier`). -/
noncomputable def fullReduction (γ : ℕ) :=
  OracleReduction.append (Oₛ₃ := fun i : Empty => nomatch i)
    (TensorPrefix.headReduction (biniusProfile κ L K β) h_l
      (binaryBasefoldInput κ L K β ℓ' R ϑ h_rate))
    (tailReduction κ K β (ϑ := ϑ) h_rate h_l γ)

/-- Completeness and soundness concern the same verifier. -/
theorem fullReduction_verifier (γ : ℕ) :
    (fullReduction κ K β (ϑ := ϑ) h_rate h_l γ).verifier (Oₛₒ := fun i : Empty => nomatch i) =
      fullVerifier κ K β (ϑ := ϑ) h_rate h_l γ := rfl

/-! ## Security

### Round-by-round knowledge soundness -/

/-- The frontier and Binary Basefold are round-by-round knowledge sound from the head's product
claim to acceptance. -/
theorem tailVerifier_rbrKnowledgeSoundness (γ : ℕ) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((tailVerifier κ K β (ϑ := ϑ) h_rate h_l γ).toVerifier
      (Oₛₒ := fun i : Empty => nomatch i)).rbrKnowledgeSoundness init impl
      (TensorPrefix.headRelOut (biniusProfile κ L K β) h_l
        (binaryBasefoldInput κ L K β ℓ' R ϑ h_rate))
      acceptRejectOracleRel
      (Sum.elim (fun _ => 0)
        (FullBinaryBasefold.fullRbrKnowledgeError K β γ (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)) ∘
        ChallengeIdx.sumEquiv.symm) :=
  OracleVerifier.append_rbrKnowledgeSoundness_of_guarded_first
    (Oₛ₃ := fun i : Empty => nomatch i) _ _
    (Frontier.guardedForm K β)
    (Frontier.rbrKnowledgeSoundness K β (TensorPrefix.multiplier (biniusProfile κ L K β) h_l)
      init impl)
    (FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness K β γ
      (TensorPrefix.multiplier (biniusProfile κ L K β) h_l) (init := init) (impl := impl))

/-- Round-by-round knowledge soundness of unrolled FRI-Binius, with error `fullError`. -/
theorem fullVerifier_rbrKnowledgeSoundness (γ : ℕ) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((fullVerifier κ K β (ϑ := ϑ) h_rate h_l γ).toVerifier
      (Oₛₒ := fun i : Empty => nomatch i)).rbrKnowledgeSoundness init impl
      (TensorPrefix.relIn (biniusProfile κ L K β) h_l
        (binaryBasefoldInput κ L K β ℓ' R ϑ h_rate))
      acceptRejectOracleRel (fullError κ K β (ϑ := ϑ) h_rate γ) :=
  OracleVerifier.append_rbrKnowledgeSoundness_of_guarded_first
    (Oₛ₃ := fun i : Empty => nomatch i) _ _
    (Head.guardedForm (PackingData.ofBasis (biniusProfile κ L K β).basis) ℓ'
      (TensorPrefix.layout (biniusProfile κ L K β) h_l)
      (TensorPrefix.messageEquiv (biniusProfile κ L K β)) (BatchingRule.eqFold L κ)
      (TensorPrefix.commitment (binaryBasefoldInput κ L K β ℓ' R ϑ h_rate)))
    (TensorPrefix.head_rbrKnowledgeSoundness (biniusProfile κ L K β) h_l _
      (binaryBasefold_initialCompatibility_functional κ L K β ℓ' R ϑ h_rate) init impl)
    (tailVerifier_rbrKnowledgeSoundness κ K β (ϑ := ϑ) h_rate h_l γ init impl)

/-! ### Knowledge soundness and soundness -/

/-- Knowledge soundness at `concreteError`, with an unbounded extractor; equivalently relation
soundness (`Verifier.knowledgeSoundness_iff_relationSoundness`). -/
theorem fullVerifier_knowledgeSoundness (γ : ℕ) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((fullVerifier κ K β (ϑ := ϑ) h_rate h_l γ).toVerifier
      (Oₛₒ := fun i : Empty => nomatch i)).knowledgeSoundness init impl
      (TensorPrefix.relIn (biniusProfile κ L K β) h_l
        (binaryBasefoldInput κ L K β ℓ' R ϑ h_rate))
      acceptRejectOracleRel (concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ) :=
  Verifier.knowledgeSoundness_error_mono init impl
    (fullError_sum_le_concrete κ K β (ϑ := ϑ) h_rate γ)
    (Verifier.GuardedForm.knowledgeSoundness_of_rbrKnowledgeSoundness
      (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i => nomatch i)))
      (fullVerifier_rbrKnowledgeSoundness κ K β (ϑ := ϑ) h_rate h_l γ init impl))

/-- Soundness at `concreteError` for the language of the input relation. -/
theorem fullVerifier_soundness (γ : ℕ) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((fullVerifier κ K β (ϑ := ϑ) h_rate h_l γ).toVerifier
      (Oₛₒ := fun i : Empty => nomatch i)).soundness init impl
      (TensorPrefix.relIn (biniusProfile κ L K β) h_l
        (binaryBasefoldInput κ L K β ℓ' R ϑ h_rate)).language
      acceptRejectOracleRel.language (concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ) := by
  have hS := Verifier.GuardedForm.soundness_of_rbrSoundness
    (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i => nomatch i)))
    (Verifier.rbrSoundness_of_rbrKnowledgeSoundness
      (fullVerifier_rbrKnowledgeSoundness κ K β (ϑ := ϑ) h_rate h_l γ init impl))
  intro Aux Out aux P stmt hstmt
  exact (hS Aux Out aux P stmt hstmt).trans (by
    exact_mod_cast fullError_sum_le_concrete κ K β (ϑ := ϑ) h_rate γ)

/-! ### Perfect completeness -/

/-- Perfect completeness of unrolled FRI-Binius for exact packed encodings. -/
theorem fullReduction_perfectCompleteness (γ : ℕ) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (fullReduction κ K β (ϑ := ϑ) h_rate h_l γ).perfectCompleteness
      (Oₛₒ := fun i : Empty => nomatch i) init impl
      (TensorPrefix.relIn (biniusProfile κ L K β) h_l
        (binaryBasefoldInput κ L K β ℓ' R ϑ h_rate).strictView)
      acceptRejectOracleRel := by
  have hhead := TensorPrefix.head_perfectCompleteness (biniusProfile κ L K β) h_l
    (binaryBasefoldInput κ L K β ℓ' R ϑ h_rate).strictView init impl
  rw [TensorPrefix.headReduction_strictView_eq] at hhead
  apply OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (Oₛ₃ := fun i : Empty => nomatch i)
    (TensorPrefix.headReduction (biniusProfile κ L K β) h_l
      (binaryBasefoldInput κ L K β ℓ' R ϑ h_rate))
    (tailReduction κ K β (ϑ := ϑ) h_rate h_l γ)
    (Head.guardedForm (PackingData.ofBasis (biniusProfile κ L K β).basis) ℓ'
      (TensorPrefix.layout (biniusProfile κ L K β) h_l)
      (TensorPrefix.messageEquiv (biniusProfile κ L K β)) (BatchingRule.eqFold L κ)
      (TensorPrefix.commitment (binaryBasefoldInput κ L K β ℓ' R ϑ h_rate)))
    (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i => nomatch i)))
    (fun _ => Or.inl inferInstance) hhead
  intro s
  exact OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (Oₛ₃ := fun i : Empty => nomatch i)
    (Frontier.reduction K β (TensorPrefix.multiplier (biniusProfile κ L K β) h_l)
      (ϑ := ϑ) (h_rate := h_rate))
    (FullBinaryBasefold.fullOracleReduction K β γ
      (TensorPrefix.multiplier (biniusProfile κ L K β) h_l) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L))
    (Frontier.guardedForm K β)
    (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i => nomatch i)))
    (fun _ => Or.inl inferInstance)
    (Frontier.perfectCompleteness K β (TensorPrefix.multiplier (biniusProfile κ L K β) h_l)
      (pure s) impl)
    (fun s' => FullBinaryBasefold.fullOracleReduction_perfectCompleteness K β γ
      (TensorPrefix.multiplier (biniusProfile κ L K β) h_l) (init := pure s') (impl := impl))

/-- Unrolled FRI-Binius is perfectly complete for exact packed encodings and knowledge sound
at `concreteError` for unique-radius compatibility. -/
theorem fullReduction_perfectCompleteness_and_knowledgeSoundness (γ : ℕ) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (fullReduction κ K β (ϑ := ϑ) h_rate h_l γ).perfectCompleteness
        (Oₛₒ := fun i : Empty => nomatch i) init impl
        (TensorPrefix.relIn (biniusProfile κ L K β) h_l
          (binaryBasefoldInput κ L K β ℓ' R ϑ h_rate).strictView)
        acceptRejectOracleRel ∧
      ((fullVerifier κ K β (ϑ := ϑ) h_rate h_l γ).toVerifier
        (Oₛₒ := fun i : Empty => nomatch i)).knowledgeSoundness init impl
        (TensorPrefix.relIn (biniusProfile κ L K β) h_l
          (binaryBasefoldInput κ L K β ℓ' R ϑ h_rate))
        acceptRejectOracleRel (concreteError κ (L := L) (ℓ' := ℓ') (R := R) γ) :=
  ⟨fullReduction_perfectCompleteness κ K β (ϑ := ϑ) h_rate h_l γ init impl,
    fullVerifier_knowledgeSoundness κ K β (ϑ := ϑ) h_rate h_l γ init impl⟩

end Binius.FRIBinius.Unrolled
