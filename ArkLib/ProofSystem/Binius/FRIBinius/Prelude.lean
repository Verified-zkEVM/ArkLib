/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
import ArkLib.ProofSystem.RingSwitching.BBFSmallFieldIOPCS

/-!
# FRI-Binius IOPCS Prelude
This module contains the preliminary definitions for the FRI-Binius IOPCS.
-/

noncomputable section

namespace Binius.FRIBinius

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial
  MvPolynomial TensorProduct Module
open scoped NNReal

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [h_Fq_char_prime : Fact (Nat.Prime (ringChar K))] [hF₂ : Fact (Fintype.card K = 2)]
variable [Algebra K L]
variable (β : Basis (Fin (2 ^ κ)) K L) [hβ_lin_indep : Fact (LinearIndependent K β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable (ℓ ℓ' 𝓡 ϑ γ_repetitions : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]
variable (h_ℓ_add_R_rate : ℓ' + 𝓡 < 2 ^ κ)
variable (h_l : ℓ = ℓ' + κ)
variable [hdiv : Fact (ϑ ∣ ℓ')]

omit [NeZero κ] in
lemma card_bool_hypercube_eq :
  Fintype.card (Fin κ → Fin 2) = 2 ^ κ := by
  simp only [Fintype.card_pi, Fintype.card_fin, prod_const, card_univ]

def hypercubeEquivFin : (Fin κ → Fin 2) ≃ Fin (2 ^ κ) :=
  Fintype.equivFinOfCardEq (card_bool_hypercube_eq κ)

def booleanHypercubeBasis : Basis (Fin κ → Fin 2) K L :=
  β.reindex (e := (hypercubeEquivFin κ).symm)

instance linearIndependentBooleanHypercubeBasis : Fact (LinearIndependent K ⇑β) := by
  constructor
  exact β.linearIndependent

def BinaryBasefoldAbstractOStmtIn : (RingSwitching.AbstractOStmtIn (L := L) (ℓ' := ℓ')) :=
  Binius.RingSwitching.BBFSmallFieldIOPCS.bbfAbstractOStmtIn (𝔽q := K) (β := β)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)

/-- Non-reducible profile wrapper for the FRI-Binius prelude, mirroring the
`BBFSmallFieldIOPCS.bbfProfile` pattern: kept as a plain (non-`@[reducible]`) `def` so that the
abstract projection `P.A` is used as the discrimination-tree key for instance synthesis, instead
of eagerly unfolding `binaryTowerProfile` to `L ⊗[K] L`. -/
def bbfSumcheckProfile (κ : ℕ) [NeZero κ] (L : Type) [Field L]
    (K : Type) [Field K] [Algebra K L] (β : Basis (Fin κ → Fin 2) K L) :
    RingSwitching.RingSwitchingProfile K L κ :=
  RingSwitching.binaryTowerProfile κ K L β

/-- The `BinaryBasefold.SumcheckMultiplierParam` corresponding to the Ring-Switching
sumcheck multiplier parameter. `BinaryBasefold.SumcheckMultiplierParam` only carries the
`multpoly` field, so we forget the extra `combinator`/`degCombinator` data of the structured
`Sumcheck.Structured.SumcheckMultiplierParam`.

The argument list mirrors `RingSwitching.RingSwitching_SumcheckMultParam` exactly so that call
sites in FRI-Binius can swap the identifier without changing arguments. The `RingSwitchingProfile`
`P` is built from `β` via the non-reducible `bbfSumcheckProfile` wrapper. -/
def RingSwitching_BBFSumcheckMultParam (κ : ℕ) [NeZero κ] (L : Type) [Field L] [Fintype L]
    [DecidableEq L] [CharP L 2] (K : Type) [Field K] [Fintype K] [DecidableEq K] [Algebra K L]
    (β : Basis (Fin κ → Fin 2) K L) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ) :
    Binius.BinaryBasefold.SumcheckMultiplierParam L ℓ'
      (RingSwitching.RingSwitchingBaseContext κ L K ℓ (bbfSumcheckProfile κ L K β)) where
  multpoly := (RingSwitching.RingSwitching_SumcheckMultParam κ L K
    (bbfSumcheckProfile κ L K β) ℓ ℓ' h_l).multpoly

end Binius.FRIBinius
