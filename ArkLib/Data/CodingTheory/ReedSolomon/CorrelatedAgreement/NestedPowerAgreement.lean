/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.UniformPowerAgreement

/-!
# Nested power agreement

The exact conclusion records the full polynomial identity and the complete common agreement set.
Challenge-composition strategies live with the scalar or interleaved agreement theorem that
supplies their inner contract.
-/

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

/-- Exact outer agreement makes every recovered group polynomial at least as close as the
outer candidate. Exact inner agreement can then be applied to those group polynomials. -/
theorem exactNestedPowerAgreement_of_exact (domain : Fin n ↪ F)
    (ℓ : Fin (m + 1) → ℕ)
    (w : (g : Fin (m + 1)) → Fin (ℓ g + 1) → Fin n → F)
    (k L : ℕ) (u v : F) (Q : F[X])
    (hclose : L ≤ (polynomialAgreementSet domain
      (powerBatchedWord (fun g ↦ powerBatchedWord (w g) u) v) Q).card)
    (houter : HasExactPowerAgreement domain (fun g ↦ powerBatchedWord (w g) u)
      (RingHom.id F) k v Q)
    (hinner : ∀ g (R : F[X]), R.degree < k →
      L ≤ (polynomialAgreementSet domain (powerBatchedWord (w g) u) R).card →
      HasExactPowerAgreement domain (w g) (RingHom.id F) k u R) :
    HasExactNestedPowerAgreement domain ℓ w k u v Q := by
  obtain ⟨R, hRdeg, hReq, hRset⟩ := houter
  simp only [Polynomial.map_id] at hReq
  have hRset' : polynomialAgreementSet domain
      (powerBatchedWord (fun g ↦ powerBatchedWord (w g) u) v) Q =
      commonCurveAgreementSet domain (fun g ↦ powerBatchedWord (w g) u) R := by
    simpa [mappedDomain] using hRset
  have hRclose (g) : L ≤
      (polynomialAgreementSet domain (powerBatchedWord (w g) u) (R g)).card := by
    apply hclose.trans
    rw [hRset']
    apply Finset.card_le_card
    intro i hi
    simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [polynomialAgreementSet, hi g]
  choose P hPdeg hPeq hPset using fun g ↦ hinner g (R g) (hRdeg g) (hRclose g)
  refine ⟨P, hPdeg, ?_, ?_⟩
  · simpa only [Polynomial.map_id] using hReq.trans (congrArg
      (fun S ↦ powerBatchedPolynomial S v) (funext fun g ↦ hPeq g))
  · rw [hRset']
    ext i
    simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
    apply forall_congr'
    intro g
    have h := congrArg (fun s : Finset (Fin n) ↦ i ∈ s) (hPset g)
    simpa [polynomialAgreementSet, commonCurveAgreementSet, mappedDomain, powerBatchedWord,
      Finset.mem_filter] using h

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
