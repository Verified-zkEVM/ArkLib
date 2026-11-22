/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Opening
import ArkLib.ProofSystem.Binius.FRIBinius.RingSwitch
import ArkLib.ProofSystem.RingSwitching.Packing.RingSwitch
import ArkLib.ProofSystem.RingSwitching.Packing.TensorPrefix

/-!
# Ordinary knowledge soundness through public Binius imports

These clients check the full-protocol completeness and ordinary knowledge-soundness
contracts, including the distinction between exact encodings and unique-radius compatibility.
The packing clients check the generic and tensor-prefix error specializations.
-/

open OracleSpec OracleComp ProtocolSpec
open RingSwitching RingSwitching.Packing
open scoped NNReal

noncomputable section
namespace ArkLibTest.Binius.OrdinaryKnowledgeSoundness

section Packing
variable {B C M : Type} [CommRing B] [CommRing C] [Algebra B C]
  (data : PackingData B) (m : ℕ) (layout : ClaimLayout data m)
  [Algebra data.P C] [IsScalarTower B data.P C]
  (messageEquiv : M ≃ (data.ιP → data.E))
  (bat : BatchingStrategy C data.ιE) (pc : PackedCommitment data.P m)
  [NoZeroDivisors C] [Fintype C] [SampleableType C]

example (hfunctional : pc.Functional) (hinj : Function.Injective (algebraMap data.P C))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (RingSwitch.reduction data m layout messageEquiv bat.toBatchingRule pc).perfectCompleteness
        init impl (Head.relIn data m layout pc)
        (pc.evalRelWithContext (layout.Query × bat.Challenge)) ∧
      (RingSwitch.verifier data m layout messageEquiv bat.toBatchingRule pc).knowledgeSoundness
        init impl (Head.relIn data m layout pc)
        (pc.evalRelWithContext (layout.Query × bat.Challenge))
        (bat.error + (m : ℝ≥0) * (2 / Fintype.card C)) :=
  RingSwitch.perfectCompleteness_and_knowledgeSoundness data m layout messageEquiv bat pc
    hfunctional hinj init impl
end Packing

section TensorPrefix
variable {K L : Type} [CommRing K] [CommRing L] [Algebra K L]
  {κ ℓ ℓ' : ℕ} (P : RingSwitchingProfile K L κ) (h_dim : ℓ = ℓ' + κ)
  [NoZeroDivisors L] [Fintype L] [SampleableType L] (a : AbstractOStmtIn L ℓ')

example (h : a.Functional) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (TensorPrefix.reduction P h_dim a).perfectCompleteness init impl (TensorPrefix.relIn P h_dim a)
        ((TensorPrefix.commitment a).evalRelWithContext ((Fin ℓ → L) × (Fin κ → L))) ∧
      (TensorPrefix.verifier P h_dim a).knowledgeSoundness init impl (TensorPrefix.relIn P h_dim a)
        ((TensorPrefix.commitment a).evalRelWithContext ((Fin ℓ → L) × (Fin κ → L)))
        ((κ : ℝ≥0) / Fintype.card L + (ℓ' : ℝ≥0) * (2 / Fintype.card L)) :=
  TensorPrefix.perfectCompleteness_and_knowledgeSoundness P h_dim a h init impl
end TensorPrefix

section FullBasefold
open Binius.BinaryBasefold Binius.BinaryBasefold.FullBinaryBasefold

variable {r : ℕ} [NeZero r]
  {L : Type} [Field L] [Fintype L] [DecidableEq L] [SampleableType L]
  (K : Type) [Field K] [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)]
  [Algebra K L] (β : Fin r → L) [Fact (LinearIndependent K β)] [Fact (β 0 = 1)]
  {ℓ R ϑ : ℕ} [NeZero ℓ] [NeZero R] [NeZero ϑ] [Fact (ϑ ∣ ℓ)]
  {h_rate : ℓ + R < r} {𝓑 : Fin 2 ↪ L}

omit [Fintype K] in
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩

example (γ : ℕ) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness
        (oracleProof := fullOracleReduction K β γ (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_rate) (𝓑 := 𝓑))
        (relation := strictRoundRelation (multpoly := multiplier) K β (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_rate) (𝓑 := 𝓑) 0) (init := init) (impl := impl) ∧
      OracleProof.knowledgeSoundness init impl
        (roundRelation (multpoly := multiplier) K β (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_rate) (𝓑 := 𝓑) 0)
        (fullOracleVerifier K β γ (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (𝓑 := 𝓑))
        (concreteBinaryBasefoldKnowledgeError L ℓ R γ) :=
  fullOracleReduction_perfectCompleteness_and_knowledgeSoundness K β γ
end FullBasefold

section FullFRIBinius
open Binius.FRIBinius Binius.FRIBinius.RingSwitch

variable (κ : ℕ) {L : Type} [Field L] [Fintype L] [DecidableEq L] [SampleableType L]
  (K : Type) [Field K] [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)]
  [Algebra K L] (β : Module.Basis (Fin (2 ^ κ)) K L) [Fact (β 0 = 1)]
  {ℓ ℓ' R ϑ : ℕ} [NeZero ℓ'] [NeZero R] [NeZero ϑ] [Fact (ϑ ∣ ℓ')]
  (h_rate : ℓ' + R < 2 ^ κ) (h_dim : ℓ = ℓ' + κ)

omit [Fintype K] in
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩

example (γ : ℕ) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness
        (oracleProof := fullReduction κ K β (ϑ := ϑ) h_rate h_dim γ)
        (relation := TensorPrefix.relIn (biniusProfile κ L K β) h_dim
          (inputInterface κ K β (ϑ := ϑ) h_rate).strictView) (init := init) (impl := impl) ∧
      OracleProof.knowledgeSoundness init impl
        (TensorPrefix.relIn (biniusProfile κ L K β) h_dim
          (inputInterface κ K β (ϑ := ϑ) h_rate))
        (fullVerifier κ K β (ϑ := ϑ) h_rate h_dim γ)
        ((κ : ℝ≥0) / Fintype.card L + (ℓ' : ℝ≥0) * (2 / Fintype.card L) +
          Binius.BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ' R γ) :=
  fullReduction_perfectCompleteness_and_knowledgeSoundness κ K β h_rate h_dim γ init impl

example (Context : Type) (γ : ℕ) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.knowledgeSoundness init impl
      (Binius.BinaryBasefold.Opening.contextualInputRelation K β Context
        (ϑ := ϑ) (h_rate := h_rate))
      (Binius.BinaryBasefold.Opening.contextualVerifier K β Context γ
        (ϑ := ϑ) (h_rate := h_rate))
      (Binius.BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ' R γ) :=
  Binius.BinaryBasefold.Opening.contextualVerifier_knowledgeSoundness K β Context γ init impl
end FullFRIBinius

end ArkLibTest.Binius.OrdinaryKnowledgeSoundness

/--
info: 'RingSwitching.Packing.RingSwitch.knowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.Packing.RingSwitch.knowledgeSoundness

/--
info: 'RingSwitching.Packing.TensorPrefix.perfectCompleteness_and_knowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RingSwitching.Packing.TensorPrefix.perfectCompleteness_and_knowledgeSoundness

/--
info: 'Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_knowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_knowledgeSoundness

/--
info: 'Binius.BinaryBasefold.Opening.contextualVerifier_knowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.BinaryBasefold.Opening.contextualVerifier_knowledgeSoundness

/--
info: 'Binius.FRIBinius.RingSwitch.fullVerifier_knowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.RingSwitch.fullVerifier_knowledgeSoundness

/--
info: 'Binius.FRIBinius.RingSwitch.fullReduction_perfectCompleteness_and_knowledgeSoundness'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.RingSwitch.fullReduction_perfectCompleteness_and_knowledgeSoundness
