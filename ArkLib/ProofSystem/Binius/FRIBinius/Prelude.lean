/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.RingSwitching.Prelude
import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec

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
variable (β : Basis (Fin (2 ^ κ)) K L)
variable (ℓ ℓ' 𝓡 ϑ γ_repetitions : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]
variable (h_ℓ_add_R_rate : ℓ' + 𝓡 < 2 ^ κ)
variable (h_l : ℓ = ℓ' + κ)
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ')]

omit [NeZero κ] in
lemma card_bool_hypercube_eq :
  Fintype.card (Fin κ → Fin 2) = 2 ^ κ := by
  simp only [Fintype.card_pi, Fintype.card_fin, prod_const, card_univ]

def hypercubeEquivFin : (Fin κ → Fin 2) ≃ Fin (2 ^ κ) :=
  Fintype.equivFinOfCardEq (card_bool_hypercube_eq κ)

instance booleanHypercubeBasis : Basis (Fin κ → Fin 2) K L :=
  β.reindex (e := (hypercubeEquivFin κ).symm)

instance linearIndependentBooleanHypercubeBasis : Fact (LinearIndependent K ⇑β) := by
  constructor
  exact β.linearIndependent

def BinaryBasefoldAbstractOStmtIn : (RingSwitching.AbstractOStmtIn (L := L) (ℓ' := ℓ')) where
  ιₛᵢ := Fin (BinaryBasefold.toOutCodewordsCount ℓ' ϑ (i:=0))
  OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0
  Oₛᵢ := Binius.BinaryBasefold.instOracleStatementBinaryBasefold K β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (i := 0)
  initialCompatibility := fun ⟨t', oStmt⟩ =>
    -- here t is the ℓ'-variate novel-packed large-field polynomial in K of the original ℓ-variate small-field polynomial in L
    Binius.BinaryBasefold.firstOracleWitnessConsistencyProp K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      t' (f₀ := Binius.BinaryBasefold.getFirstOracle K β oStmt)
  -- Strict relation for completeness: exact first-oracle equality with the oracle
  -- induced by `t'` at frontier 0 (deterministic, computation-style relation).
  strictInitialCompatibility := fun ⟨t', oStmt⟩ =>
    let P₀ : L[X]_(2 ^ ℓ') := polynomialFromNovelCoeffsF₂ K β ℓ' (by omega)
      (fun ω => t'.val.eval (Binius.BinaryBasefold.bitsOfIndex ω))
    let f₀ := Binius.BinaryBasefold.polyToOracleFunc K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
    f₀ = Binius.BinaryBasefold.getFirstOracle K β oStmt
  strictInitialCompatibility_implies_initialCompatibility := by
    intro oStmt t h_compat_strict
    dsimp only [Binius.BinaryBasefold.firstOracleWitnessConsistencyProp]
    dsimp only at h_compat_strict
    rw [← h_compat_strict]
    dsimp only [Binius.BinaryBasefold.pair_UDRClose]
    have h_dist_pos :
        0 < Binius.BinaryBasefold.BBF_CodeDistance K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (0 : Fin (2 ^ κ))) := by
      rw [Binius.BinaryBasefold.BBF_CodeDistance_eq K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (0 : Fin (2 ^ κ))) (h_i := by simp)]
      omega
    simp only [hammingDist_self, mul_zero, h_dist_pos]
  initialCompatibility_unique := fun oStmt t₁ t₂ h₁ h₂ => by
    -- Unique decoding: within the unique decoding radius, the polynomial is unique.
    -- `firstOracleWitnessConsistencyProp` asserts `pair_UDRClose`, which pins down
    -- a unique polynomial via the Berlekamp-Welch algorithm (Algorithm 1 / Theorem 2.2).
    sorry

end Binius.FRIBinius
