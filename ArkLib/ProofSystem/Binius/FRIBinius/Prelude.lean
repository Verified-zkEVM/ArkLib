/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Commitment
public import ArkLib.ProofSystem.RingSwitching.Packing.Compatibility

/-!
# FRI-Binius IOPCS Prelude
This module contains the preliminary definitions for the FRI-Binius IOPCS. Hypercube indices
use the canonical least-significant-bit-first order. Relaxed compatibility permits unique-radius
closeness; strict compatibility requires an exact first-codeword encoding. Functionality and
honest coverage certify this oracle relation separately from the later opening protocol.
-/

@[expose] public section

noncomputable section

namespace Binius.FRIBinius

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial
  MvPolynomial TensorProduct Module Sumcheck.Structured
open scoped NNReal

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [Field K]
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) :=
  ⟨CharP.prime_ringChar K⟩
variable [Fintype K] [DecidableEq K]
variable [hF₂ : Fact (Fintype.card K = 2)]
variable [Algebra K L]
variable (β : Basis (Fin (2 ^ κ)) K L)
variable (ℓ ℓ' 𝓡 ϑ γ_repetitions : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]
variable (h_ℓ_add_R_rate : ℓ' + 𝓡 < 2 ^ κ)
variable (h_l : ℓ = ℓ' + κ)
variable [hdiv : Fact (ϑ ∣ ℓ')]

/-- The canonical radix-two enumeration of the Boolean hypercube. -/
def hypercubeEquivFin : (Fin κ → Fin 2) ≃ Fin (2 ^ κ) :=
  finFunctionFinEquiv

/-- The basis reindexed by Boolean-hypercube coordinates. -/
def booleanHypercubeBasis : Basis (Fin κ → Fin 2) K L :=
  β.reindex (e := (hypercubeEquivFin κ).symm)

instance instFactLinearIndependentBasis : Fact (LinearIndependent K ⇑β) := by
  constructor
  exact β.linearIndependent

/-- The Binius ring-switching profile: the tensor-product profile at the Boolean-hypercube
reindexing `booleanHypercubeBasis` of `β`. -/
def biniusProfile : RingSwitching.RingSwitchingProfile K L κ :=
  RingSwitching.tensorProductProfile κ K L (booleanHypercubeBasis κ L K β)

/-- The shared Binary Basefold first-oracle interface at the packed dimension. -/
def binaryBasefoldInput : RingSwitching.AbstractOStmtIn L ℓ' :=
  BinaryBasefold.firstOracleInterface K β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

omit [NeZero κ] [SampleableType L] [DecidableEq K] [NeZero 𝓡] in
/-- Unique-radius compatibility determines the initial committed polynomial. -/
theorem binaryBasefold_initialCompatibility_functional :
    (binaryBasefoldInput κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).Functional :=
  BinaryBasefold.firstOracleInterface_functional K β ϑ

/-- Honest first-codeword oracles cover every packed polynomial. -/
def honestPackedOracle (t : MultilinearPoly L ℓ') :
    ∀ j, (binaryBasefoldInput κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn j :=
  BinaryBasefold.honestInitialOracleStatement K β ϑ
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t

omit [NeZero κ]  [SampleableType L] [DecidableEq K] [NeZero 𝓡] in
/-- Honest families also meet the exact encoding premise used for completeness. -/
theorem honestPackedOracle_strictCompatible (t : MultilinearPoly L ℓ') :
    (binaryBasefoldInput κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).strictInitialCompatibility
      (t, honestPackedOracle κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate t) := by
  classical
  exact BinaryBasefold.firstOracleInterface_strictInitialCompatibility_honest K β ϑ t

end Binius.FRIBinius
