/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.TensorPrefix
public import ArkLib.ProofSystem.Binius.FRIBinius.Prelude
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Opening

/-!
# Prefix ring switching followed by Binary Basefold

The frontend is the shared scalar ring-switching protocol at Binius's tensor profile. Its
original carrier message is followed by the shared product sumcheck and matrix terminal check.
The same packed polynomial and its first oracle then enter the Binary Basefold
opening. That opening's zero-round frontier discards the retained query context while
formatting the evaluation claim; no additional formatting phase is inserted.

Completeness uses exact first-codeword encodings. Round-by-round knowledge soundness
uses unique-radius compatibility, whose functionality follows from encoding injectivity and code
distance. The challenge
errors are the frontend's exact `κ/|L| + 2ℓ'/|L|` and the opening's error function.
`fullReduction_perfectCompleteness_and_rbrKnowledgeSoundness` combines both guarantees
with the total-error bound.
-/

@[expose] public section

noncomputable section
namespace Binius.FRIBinius.RingSwitch
open OracleSpec OracleComp ProtocolSpec Module MvPolynomial
open RingSwitching RingSwitching.Packing Sumcheck.Structured
open scoped NNReal

variable (κ : ℕ) {L : Type} [Field L] [Fintype L] [DecidableEq L] [SampleableType L]
  (K : Type) [Field K] [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)]
  [Algebra K L] (β : Basis (Fin (2 ^ κ)) K L)
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
variable {ℓ ℓ' R ϑ : ℕ} [NeZero ℓ'] [NeZero R] [NeZero ϑ] [Fact (ϑ ∣ ℓ')]
  (h_rate : ℓ' + R < 2 ^ κ) (h_dim : ℓ = ℓ' + κ)

/-- The first-oracle relation of the packed polynomial. -/
abbrev inputInterface := binaryBasefoldInput κ L K β ℓ' R ϑ h_rate

/-- The source query and batching challenge retained until the opening frontier. -/
abbrev Context := (Fin ℓ → L) × (Fin κ → L)

omit [SampleableType L] [DecidableEq K] [NeZero R] in
/-- The first-oracle interface is the general opening interface at the same basis. -/
theorem inputInterface_eq : inputInterface κ K β (ϑ := ϑ) h_rate =
    BinaryBasefold.Opening.abstractInput K β (ϑ := ϑ) (h_rate := h_rate) := rfl

/-- The frontend verifier is defined through the shared prefix protocol. -/
def verifier := TensorPrefix.verifier (biniusProfile κ L K β) h_dim
  (inputInterface κ K β (ϑ := ϑ) h_rate)

/-- The frontend reduction is defined through the shared prefix protocol. -/
def reduction := TensorPrefix.reduction (biniusProfile κ L K β) h_dim
  (inputInterface κ K β (ϑ := ϑ) h_rate)

omit [SampleableType L] [DecidableEq K] [NeZero R] in
/-- The opening receives exactly the frontend's contextual evaluation relation. -/
theorem opening_input_eq :
    (TensorPrefix.commitment (inputInterface κ K β (ϑ := ϑ) h_rate)).evalRelWithContext
        (Context κ (L := L) (ℓ := ℓ)) =
      BinaryBasefold.Opening.contextualInputRelation K β (Context κ (L := L) (ℓ := ℓ))
        (ϑ := ϑ) (h_rate := h_rate) := by
  ext x
  rfl

omit [SampleableType L] [DecidableEq K] [NeZero R] in
/-- Exact encodings identify the frontend's honest endpoint with the opening's strict input. -/
theorem opening_strict_input_eq :
    (TensorPrefix.commitment (inputInterface κ K β (ϑ := ϑ) h_rate).strictView).evalRelWithContext
        (Context κ (L := L) (ℓ := ℓ)) =
      BinaryBasefold.Opening.contextualStrictInputRelation K β (Context κ (L := L) (ℓ := ℓ))
        (ϑ := ϑ) (h_rate := h_rate) := by
  ext x
  rfl

/-- The original carrier wire and product sumcheck followed by the opening wire. -/
abbrev pSpec (γ : ℕ) := TensorPrefix.pSpec (biniusProfile κ L K β) (ℓ' := ℓ') ++ₚ
  ((!p[] : ProtocolSpec 0) ++ₚ BinaryBasefold.fullPSpec K β γ
    (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate))

instance (γ : ℕ) : ∀ j, OracleInterface
    ((pSpec κ K β (ϑ := ϑ) h_rate γ).Message j) :=
  ProtocolSpec.instOracleInterfaceMessageAppend
    (pSpec₁ := TensorPrefix.pSpec (biniusProfile κ L K β) (ℓ' := ℓ'))
    (pSpec₂ := (!p[] : ProtocolSpec 0) ++ₚ BinaryBasefold.fullPSpec K β γ
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate))

instance (γ : ℕ) : ∀ j, SampleableType
    ((pSpec κ K β (ϑ := ϑ) h_rate γ).Challenge j) :=
  ProtocolSpec.instSampleableTypeChallengeAppend
    (pSpec₁ := TensorPrefix.pSpec (biniusProfile κ L K β) (ℓ' := ℓ'))
    (pSpec₂ := (!p[] : ProtocolSpec 0) ++ₚ BinaryBasefold.fullPSpec K β γ
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate))

variable [Fact (β 0 = 1)]

/-- The frontend followed by the concrete opening verifier. -/
def fullVerifier (γ : ℕ) := OracleVerifier.append
  (Oₛ₃ := fun i : Empty => nomatch i)
  (verifier κ K β h_rate h_dim)
  (BinaryBasefold.Opening.contextualVerifier K β (Context κ (L := L) (ℓ := ℓ)) γ
    (ϑ := ϑ) (h_rate := h_rate))

/-- The frontend and opening provers share the same packed-polynomial witness. -/
def fullReduction (γ : ℕ) := OracleReduction.append
  (Oₛ₃ := fun i : Empty => nomatch i)
  (reduction κ K β h_rate h_dim)
  (BinaryBasefold.Opening.contextualReduction K β (Context κ (L := L) (ℓ := ℓ)) γ
    (ϑ := ϑ) (h_rate := h_rate))

/-- Each full-protocol challenge keeps its component's error bound. -/
def fullError (γ : ℕ) : (pSpec κ K β (ϑ := ϑ) h_rate (ℓ' := ℓ') γ).ChallengeIdx → ℝ≥0 :=
  Sum.elim (TensorPrefix.rbrError (biniusProfile κ L K β))
    (BinaryBasefold.Opening.openingError K β γ (ϑ := ϑ) (h_rate := h_rate)) ∘
      ChallengeIdx.sumEquiv.symm

omit [DecidableEq K] [Fact (β 0 = 1)] [Fact (Fintype.card K = 2)] [NeZero R] in
-- Match dependent challenge-index casts between the prefix and general protocol specifications.
set_option backward.isDefEq.respectTransparency false in
/-- The full challenge-error sum is the frontend loss plus the opening's challenge sum. -/
theorem fullError_sum (γ : ℕ) :
    (∑ j, fullError κ K β (ϑ := ϑ) h_rate (ℓ' := ℓ') γ j) =
      (κ : ℝ≥0) / Fintype.card L + (ℓ' : ℝ≥0) * (2 / Fintype.card L) +
        ∑ j, BinaryBasefold.Opening.openingError K β γ (ϑ := ϑ) (h_rate := h_rate) j :=
  RingSwitching.Packing.RingSwitch.append_rbrError_sum
    (M := (biniusProfile κ L K β).A) (PackingData.ofBasis (biniusProfile κ L K β).basis) ℓ'
    (BatchingStrategy.eqFold L κ)
    ((!p[] : ProtocolSpec 0) ++ₚ BinaryBasefold.fullPSpec K β γ
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate))
    (BinaryBasefold.Opening.openingError K β γ (ϑ := ϑ) (h_rate := h_rate))

omit [DecidableEq K] [Fact (β 0 = 1)] in
/-- The challenge sum is bounded by the frontend loss and the opening's closed-form bound. -/
theorem fullError_sum_le (γ : ℕ) :
    (∑ j, fullError κ K β (ϑ := ϑ) h_rate (ℓ' := ℓ') γ j) ≤
      (κ : ℝ≥0) / Fintype.card L + (ℓ' : ℝ≥0) * (2 / Fintype.card L) +
        BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ' R γ := by
  rw [fullError_sum]
  exact add_le_add (le_refl _)
    (BinaryBasefold.Opening.openingError_sum_le_concrete K β γ
      (ϑ := ϑ) (h_rate := h_rate))

omit [DecidableEq K] [Fact (β 0 = 1)] [NeZero R] in
/-- The frontend is round-by-round knowledge sound for first-oracle compatibility. -/
theorem verifier_rbrKnowledgeSoundness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier κ K β h_rate h_dim).toVerifier.rbrKnowledgeSoundness init impl
      (TensorPrefix.relIn (biniusProfile κ L K β) h_dim (inputInterface κ K β (ϑ := ϑ) h_rate))
      ((TensorPrefix.commitment (inputInterface κ K β (ϑ := ϑ) h_rate)).evalRelWithContext
        (Context κ (L := L) (ℓ := ℓ)))
      (TensorPrefix.rbrError (biniusProfile κ L K β)) := by
  apply TensorPrefix.rbrKnowledgeSoundness
  change (BinaryBasefold.Opening.abstractInput K β (ϑ := ϑ) (h_rate := h_rate)).Functional
  exact BinaryBasefold.Opening.abstractInput_functional K β

/-- The full verifier is round-by-round knowledge sound. -/
theorem fullVerifier_rbrKnowledgeSoundness {σ : Type} (γ : ℕ) (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((fullVerifier κ K β h_rate h_dim γ).toVerifier
        (Oₛₒ := fun i : Empty => nomatch i)).rbrKnowledgeSoundness init impl
      (TensorPrefix.relIn (biniusProfile κ L K β) h_dim (inputInterface κ K β (ϑ := ϑ) h_rate))
      acceptRejectOracleRel (fullError κ K β (ϑ := ϑ) h_rate γ) := by
  unfold fullVerifier
  erw [OracleVerifier.append_toVerifier (Oₛ₃ := fun i : Empty => nomatch i)]
  apply Verifier.append_rbrKnowledgeSoundness_of_guarded_first _ _
    (RingSwitching.Packing.RingSwitch.guardedForm
      (PackingData.ofBasis (biniusProfile κ L K β).basis) ℓ'
      (TensorPrefix.layout (biniusProfile κ L K β) h_dim)
      (TensorPrefix.messageEquiv (biniusProfile κ L K β)) (BatchingRule.eqFold L κ)
      (TensorPrefix.commitment (inputInterface κ K β (ϑ := ϑ) h_rate)))
  · exact verifier_rbrKnowledgeSoundness κ K β h_rate h_dim init impl
  · rw [opening_input_eq]
    exact BinaryBasefold.Opening.contextualVerifier_rbrKnowledgeSoundness K β
      (Context κ (L := L) (ℓ := ℓ)) γ init impl

/-- Exact first-codeword encodings give perfect completeness of the full protocol. -/
theorem fullReduction_perfectCompleteness {σ : Type} (γ : ℕ) (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness
      (oracleProof := fullReduction κ K β h_rate h_dim γ)
      (relation := TensorPrefix.relIn (biniusProfile κ L K β) h_dim
        (inputInterface κ K β (ϑ := ϑ) h_rate).strictView) (init := init) (impl := impl) := by
  have hhead : (reduction κ K β h_rate h_dim).perfectCompleteness init impl
      (TensorPrefix.relIn (biniusProfile κ L K β) h_dim
        (inputInterface κ K β (ϑ := ϑ) h_rate).strictView)
      ((TensorPrefix.commitment
        (inputInterface κ K β (ϑ := ϑ) h_rate).strictView).evalRelWithContext
        (Context κ (L := L) (ℓ := ℓ))) := by
    have heq : TensorPrefix.reduction (biniusProfile κ L K β) h_dim
        (inputInterface κ K β (ϑ := ϑ) h_rate).strictView =
        reduction κ K β h_rate h_dim :=
      TensorPrefix.reduction_strictView_eq _ _ _
    rw [← heq]
    exact TensorPrefix.perfectCompleteness _ _ _ init impl
  apply OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (Oₛ₃ := fun i : Empty => nomatch i)
    (reduction κ K β h_rate h_dim)
    (BinaryBasefold.Opening.contextualReduction K β (Context κ (L := L) (ℓ := ℓ)) γ
      (ϑ := ϑ) (h_rate := h_rate))
    (RingSwitching.Packing.RingSwitch.guardedForm
      (PackingData.ofBasis (biniusProfile κ L K β).basis) ℓ'
      (TensorPrefix.layout (biniusProfile κ L K β) h_dim)
      (TensorPrefix.messageEquiv (biniusProfile κ L K β)) (BatchingRule.eqFold L κ)
      (TensorPrefix.commitment (inputInterface κ K β (ϑ := ϑ) h_rate)))
    (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i : Empty => nomatch i)))
    (fun _ => Or.inl (show (RingSwitching.Packing.RingSwitch.reduction
      (PackingData.ofBasis (biniusProfile κ L K β).basis) ℓ'
      (TensorPrefix.layout (biniusProfile κ L K β) h_dim)
      (TensorPrefix.messageEquiv (biniusProfile κ L K β)) (BatchingRule.eqFold L κ)
      (TensorPrefix.commitment (inputInterface κ K β (ϑ := ϑ) h_rate))).prover.OutputIsPure
        from inferInstance))
  · exact hhead
  · intro state
    rw [opening_strict_input_eq]
    exact BinaryBasefold.Opening.contextualReduction_perfectCompleteness K β
      (Context κ (L := L) (ℓ := ℓ)) γ
      (pure state) impl

/-- The prefix reduction followed by Binary Basefold is perfectly complete on exact encodings
and round-by-round knowledge sound at the sum of the frontend and opening errors. -/
theorem fullReduction_perfectCompleteness_and_rbrKnowledgeSoundness
    {σ : Type} (γ : ℕ) (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness
        (oracleProof := fullReduction κ K β h_rate h_dim γ)
        (relation := TensorPrefix.relIn (biniusProfile κ L K β) h_dim
          (inputInterface κ K β (ϑ := ϑ) h_rate).strictView) (init := init) (impl := impl) ∧
      ((fullVerifier κ K β h_rate h_dim γ).toVerifier
          (Oₛₒ := fun i : Empty => nomatch i)).rbrKnowledgeSoundness init impl
        (TensorPrefix.relIn (biniusProfile κ L K β) h_dim
          (inputInterface κ K β (ϑ := ϑ) h_rate))
        acceptRejectOracleRel (fullError κ K β (ϑ := ϑ) h_rate γ) ∧
      (∑ j, fullError κ K β (ϑ := ϑ) h_rate (ℓ' := ℓ') γ j) ≤
        (κ : ℝ≥0) / Fintype.card L + (ℓ' : ℝ≥0) * (2 / Fintype.card L) +
          BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ' R γ :=
  ⟨fullReduction_perfectCompleteness κ K β h_rate h_dim γ init impl,
    fullVerifier_rbrKnowledgeSoundness κ K β h_rate h_dim γ init impl,
    fullError_sum_le κ K β h_rate γ⟩

omit [DecidableEq K] [Fact (β 0 = 1)] [NeZero R] in
/-- The frontend is ordinarily knowledge sound for first-oracle compatibility. -/
theorem verifier_knowledgeSoundness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier κ K β h_rate h_dim).knowledgeSoundness init impl
      (TensorPrefix.relIn (biniusProfile κ L K β) h_dim
        (inputInterface κ K β (ϑ := ϑ) h_rate))
      ((TensorPrefix.commitment (inputInterface κ K β (ϑ := ϑ) h_rate)).evalRelWithContext
        (Context κ (L := L) (ℓ := ℓ)))
      ((κ : ℝ≥0) / Fintype.card L + (ℓ' : ℝ≥0) * (2 / Fintype.card L)) := by
  apply TensorPrefix.knowledgeSoundness
  change (BinaryBasefold.Opening.abstractInput K β (ϑ := ϑ) (h_rate := h_rate)).Functional
  exact BinaryBasefold.Opening.abstractInput_functional K β

/-- The full verifier is ordinarily knowledge sound at the frontend and Binary Basefold errors. -/
theorem fullVerifier_knowledgeSoundness {σ : Type} (γ : ℕ) (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.knowledgeSoundness init impl
      (TensorPrefix.relIn (biniusProfile κ L K β) h_dim
        (inputInterface κ K β (ϑ := ϑ) h_rate))
      (fullVerifier κ K β h_rate h_dim γ)
      ((κ : ℝ≥0) / Fintype.card L + (ℓ' : ℝ≥0) * (2 / Fintype.card L) +
        BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ' R γ) := by
  apply Verifier.knowledgeSoundness_error_mono init impl
    (fullError_sum_le κ K β (ϑ := ϑ) h_rate γ)
  exact Verifier.GuardedForm.knowledgeSoundness_of_rbrKnowledgeSoundness
    (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i : Empty => nomatch i)))
    (fullVerifier_rbrKnowledgeSoundness κ K β h_rate h_dim γ init impl)

/-- The prefix followed by Binary Basefold is perfectly complete on exact encodings and
ordinarily knowledge sound at the frontend loss plus the concrete Binary Basefold error. -/
theorem fullReduction_perfectCompleteness_and_knowledgeSoundness {σ : Type} (γ : ℕ)
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness
        (oracleProof := fullReduction κ K β h_rate h_dim γ)
        (relation := TensorPrefix.relIn (biniusProfile κ L K β) h_dim
          (inputInterface κ K β (ϑ := ϑ) h_rate).strictView) (init := init) (impl := impl) ∧
      OracleProof.knowledgeSoundness init impl
        (TensorPrefix.relIn (biniusProfile κ L K β) h_dim
          (inputInterface κ K β (ϑ := ϑ) h_rate))
        (fullVerifier κ K β h_rate h_dim γ)
        ((κ : ℝ≥0) / Fintype.card L + (ℓ' : ℝ≥0) * (2 / Fintype.card L) +
          BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ' R γ) :=
  ⟨fullReduction_perfectCompleteness κ K β h_rate h_dim γ init impl,
    fullVerifier_knowledgeSoundness κ K β h_rate h_dim γ init impl⟩

end Binius.FRIBinius.RingSwitch
