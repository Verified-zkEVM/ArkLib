/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.UniformPowerAgreement
/-!
# Nested power agreement

The exact conclusion records the full polynomial identity and the complete common agreement set.
Challenge-composition strategies live with the scalar or interleaved agreement theorem that
supplies their inner contract.
-/

@[expose] public section

noncomputable section
namespace ReedSolomon
open Polynomial
open scoped BigOperators
variable {F : Type*} [Field F] [DecidableEq F] {n m : ℕ}

/-- The exact nested conclusion recovers each original message, its degree, the complete
polynomial identity, and equality of the entire agreement set. -/
def HasExactNestedPowerAgreement (domain : Fin n ↪ F) (ℓ : Fin (m + 1) → ℕ)
    (w : (g : Fin (m + 1)) → Fin (ℓ g + 1) → Fin n → F)
    (k : ℕ) (u v : F) (Q : F[X]) : Prop :=
  ∃ P : (g : Fin (m + 1)) → Fin (ℓ g + 1) → F[X],
    (∀ g j, (P g j).degree < k) ∧
    Q = powerBatchedPolynomial (fun g ↦ powerBatchedPolynomial (P g) u) v ∧
    polynomialAgreementSet domain
      (powerBatchedWord (fun g ↦ powerBatchedWord (w g) u) v) Q =
      Finset.univ.filter (fun i ↦ ∀ g j, (P g j).eval (domain i) = w g j i)

omit [DecidableEq F] in
/-- Under independent uniform sampling, each challenge pair has mass `1 / |F|²`.
This translates the integer exceptional-pair bound into the scalar-budget ratio. -/
theorem nestedPowerAgreement_probability_bound [Fintype F] (bad : Finset (F × F))
    (E : ℕ) (hbad : bad.card ≤ Fintype.card F * E) :
    (bad.card : ℚ) / (Fintype.card F : ℚ) ^ 2 ≤ (E : ℚ) / Fintype.card F := by
  have hq : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hb : (bad.card : ℚ) ≤ (Fintype.card F : ℚ) * E := by exact_mod_cast hbad
  apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
  calc
    (bad.card : ℚ) ≤ (Fintype.card F : ℚ) * E := hb
    _ = (E : ℚ) / Fintype.card F * (Fintype.card F : ℚ) ^ 2 := by
      field_simp

end ReedSolomon
