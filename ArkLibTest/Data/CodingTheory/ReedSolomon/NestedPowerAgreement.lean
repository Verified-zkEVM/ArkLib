/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreement

/-! Regression checks for zero-exception singleton composition and the pair-count ratio. -/

open ReedSolomon Polynomial

section
variable {F : Type} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}

-- Both levels have width one: there are no exceptional pairs, for any received word.
example (domain : Fin n ↪ F) (w : Fin (0 + 1) → Fin (0 + 1) → Fin n → F)
    (k L : ℕ) (hkL : k ≤ L) (u v : F) (Q : F[X]) (hQ : Q.degree < k)
    (hclose : L ≤ (polynomialAgreementSet domain
      (powerBatchedWord (fun g ↦ powerBatchedWord (w g) u) v) Q).card) :
    HasExactNestedPowerAgreement domain (fun _ ↦ 0) w k u v Q := by
  let degree : Fin 1 → ℕ := fun _ ↦ 0
  have hdegree (g : Fin 1) : degree g ≤ 0 := by simp [degree]
  let padded : Fin 1 → Fin n → Fin 1 → F := paddedPowerValues degree hdegree w
  have hinner : UniformExactInterleavedPowerAgreement domain
      padded k L 0 :=
    uniformExactInterleavedPowerAgreement_of_scalar
      (ℓ := 0) (width := 1) (exceptionalCount := 0) domain
      (fun values ↦ uniformExactPowerAgreement_singleton domain values k L)
      (by decide) hkL padded
  obtain ⟨bad, hcard, hgood⟩ := nestedPowerAgreement_sharedInner domain
    degree hdegree w hkL hinner
    (fun u ↦ uniformExactPowerAgreement_singleton domain
      (fun g ↦ powerBatchedWord (w g) u) k L)
  have hempty : bad = ∅ := Finset.card_eq_zero.mp (by simpa using hcard)
  exact hgood u v (by simp [hempty]) Q hQ hclose

omit [DecidableEq F] in
example (bad : Finset (F × F)) (E : ℕ) (h : bad.card ≤ Fintype.card F * E) :
    (bad.card : ℚ) / (Fintype.card F : ℚ) ^ 2 ≤ (E : ℚ) / Fintype.card F :=
  nestedPowerAgreement_probability_bound bad E h
end
