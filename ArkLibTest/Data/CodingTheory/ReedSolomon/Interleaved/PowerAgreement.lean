/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreement

/-!
# Interleaved exact power agreement clients

These clients derive the forms with the extra guard `0 < width` (over a finite field and over an
arbitrary field) from the general transfer, compute the interleaved guarantee for a
single received array with no exceptional challenge at every width including zero, and compose
the transfer with nested power agreement, including its probability form.
-/

open Polynomial ReedSolomon CoreDefinitions

namespace InterleavedPowerAgreementTest

-- The form over a finite field with the extra guard `0 < width`.
example {F : Type} [Field F] [Finite F] [DecidableEq F]
    {n k agreement exceptionalCount width ℓ : ℕ} (domain : Fin n ↪ F)
    (hscalar : ∀ values : Fin (ℓ + 1) → Fin n → F,
      UniformExactPowerAgreement domain values k agreement exceptionalCount)
    (_hwidth : 0 < width) (hkAgreement : k ≤ agreement)
    (values : Fin (ℓ + 1) → Fin n → Fin width → F) :
    UniformExactInterleavedPowerAgreement domain values k agreement exceptionalCount :=
  uniformExactInterleavedPowerAgreement_of_scalar domain hscalar hkAgreement values

-- The form over an arbitrary field with the extra guard `0 < width`.
example {F : Type} [Field F] [DecidableEq F]
    {n k agreement exceptionalCount width ℓ : ℕ} (domain : Fin n ↪ F)
    (hscalar : ∀ values : Fin (ℓ + 1) → Fin n → F,
      UniformExactPowerAgreement domain values k agreement exceptionalCount)
    (_hwidth : 0 < width) (hkAgreement : k ≤ agreement)
    (values : Fin (ℓ + 1) → Fin n → Fin width → F) :
    UniformExactInterleavedPowerAgreement domain values k agreement exceptionalCount :=
  uniformExactInterleavedPowerAgreement_of_scalar domain hscalar hkAgreement values

/-- A single received word needs no challenge. -/
theorem uniformExactPowerAgreement_single {F ι : Type} [Field F] [Fintype ι] [DecidableEq F]
    (domain : ι ↪ F) (w : Fin 1 → ι → F) (k L : ℕ) :
    UniformExactPowerAgreement domain w k L 0 := by
  refine ⟨∅, by simp, fun z _ Q hQ _ ↦ ?_⟩
  refine (hasExactPowerAgreement_id_iff _ _ _ _ _).mpr ⟨fun _ ↦ Q, fun _ ↦ hQ, ?_, ?_⟩
  · simp [powerBatchedPolynomial]
  · ext i
    simp [powerBatchedWord]

-- The interleaved guarantee for a single received array, with no exceptional challenge, for every
-- finite row type; `Fin 0` is allowed.
example {F ι : Type} [Field F] [Fintype ι] [DecidableEq F] (domain : ι ↪ F) {k L : ℕ}
    (hk : k ≤ L) (values : Fin 1 → ι → Fin 0 → F) :
    UniformExactInterleavedPowerAgreement domain values k L 0 :=
  uniformExactInterleavedPowerAgreement_of_scalar domain
    (fun w ↦ uniformExactPowerAgreement_single domain w k L) hk values

-- The same guarantee, unfolded at one challenge and one row tuple over `ℚ` with three rows.
example {ι : Type} [Fintype ι] (domain : ι ↪ ℚ) {k L : ℕ} (hk : k ≤ L)
    (values : Fin 1 → ι → Fin 3 → ℚ) (z : ℚ) (Q : Fin 3 → ℚ[X]) (hQ : ∀ j, (Q j).degree < k)
    (hL : L ≤ (interleavedPolynomialAgreementSet domain
      (interleavedPowerBatchedWord values z) Q).card) :
    HasExactInterleavedPowerAgreement domain values k z Q := by
  obtain ⟨bad, hbad, hgood⟩ := uniformExactInterleavedPowerAgreement_of_scalar domain
    (fun w ↦ uniformExactPowerAgreement_single domain w k L) hk values
  have : bad = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hbad)
  exact hgood z (by simp [this]) Q hQ hL

-- Nested power agreement with the inner guarantee supplied by the interleaved transfer.
example {F ι : Type} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {m maxDegree k L innerE outerE : ℕ} (domain : ι ↪ F) (degree : Fin (m + 1) → ℕ)
    (hdegree : ∀ g, degree g ≤ maxDegree)
    (values : (g : Fin (m + 1)) → Fin (degree g + 1) → ι → F) (hk : k ≤ L)
    (hscalar : ∀ w : Fin (maxDegree + 1) → ι → F, UniformExactPowerAgreement domain w k L innerE)
    (houter : ∀ u, UniformExactPowerAgreement domain
      (fun g ↦ powerBatchedWord (values g) u) k L outerE) :
    ∃ bad : Finset (F × F), bad.card ≤ Fintype.card F * (innerE + outerE) ∧
      ∀ u v, (u, v) ∉ bad → ∀ Q : F[X], Q.degree < k →
        L ≤ (polynomialAgreementSet domain
          (powerBatchedWord (fun g ↦ powerBatchedWord (values g) u) v) Q).card →
        HasExactNestedPowerAgreement domain degree values k u v Q :=
  nestedPowerAgreement_sharedInner domain degree hdegree values hk
    (uniformExactInterleavedPowerAgreement_of_scalar domain hscalar hk _) houter

open scoped ProbabilityTheory in
-- The probability form, for one group holding one word: both guarantees have no exceptional
-- challenge, so exact nested agreement fails with probability `0`.
example {F ι : Type} [Field F] [Fintype F] [SampleableType F] [Fintype ι] [DecidableEq F]
    (domain : ι ↪ F) {k L : ℕ} (hk : k ≤ L) (values : (g : Fin (0 + 1)) → Fin (0 + 1) → ι → F) :
    Pr{let p ← $ᵗ (F × F)}[∃ Q : F[X], Q.degree < k ∧
        L ≤ (polynomialAgreementSet domain
          (powerBatchedWord (fun g ↦ powerBatchedWord (values g) p.1) p.2) Q).card ∧
        ¬ HasExactNestedPowerAgreement domain (fun _ ↦ 0) values k p.1 p.2 Q] = 0 := by
  have h := nestedPowerAgreement_probability_le (maxDegree := 0) domain (fun _ ↦ 0)
    (fun _ ↦ le_rfl) values hk
    (uniformExactInterleavedPowerAgreement_of_scalar domain
      (fun w ↦ uniformExactPowerAgreement_single domain w k L) hk _)
    (fun _ ↦ uniformExactPowerAgreement_single domain _ k L)
  simpa using h

-- Padding a group of size two to size three keeps its batched word.
example (z : ℚ) (values : (g : Fin 1) → Fin (1 + 1) → Fin 2 → ℚ) (i : Fin 2) :
    interleavedPowerBatchedWord
        (paddedPowerValues (fun _ ↦ 1) (fun _ ↦ (by decide : 1 ≤ 2)) values) z i 0 =
      values 0 0 i + z * values 0 1 i := by
  rw [interleavedPowerBatchedWord_padded_apply]
  simp [powerBatchedWord, Fin.sum_univ_two]

end InterleavedPowerAgreementTest
