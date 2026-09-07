/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.NestedPowerAgreement

/-! Regression checks for zero-exception singleton composition and the pair-count ratio. -/

open ReedSolomon Polynomial

section
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}

-- Both levels have width one: there are no exceptional pairs, for any received word.
example (domain : Fin n ↪ F) (w : Fin (0 + 1) → Fin (0 + 1) → Fin n → F)
    (k L : ℕ) (u v : F) (Q : F[X]) (hQ : Q.degree < k)
    (hclose : L ≤ (polynomialAgreementSet domain
      (powerBatchedWord (fun g ↦ powerBatchedWord (w g) u) v) Q).card) :
    HasExactNestedPowerAgreement domain (fun _ ↦ 0) w k u v Q := by
  obtain ⟨bad, hcard, hgood⟩ := nestedPowerAgreement domain (fun _ ↦ 0) w k L
    (fun _ ↦ 0) 0 (fun g ↦ uniformExactPowerAgreement_singleton domain (w g) k L)
    (fun u ↦ uniformExactPowerAgreement_singleton domain
      (fun g ↦ powerBatchedWord (w g) u) k L)
  have hempty : bad = ∅ := Finset.card_eq_zero.mp (by simpa using hcard)
  exact hgood u v (by simp [hempty]) Q hQ hclose

omit [DecidableEq F] in
example (bad : Finset (F × F)) (E : ℕ) (h : bad.card ≤ Fintype.card F * E) :
    (bad.card : ℚ) / (Fintype.card F : ℚ) ^ 2 ≤ (E : ℚ) / Fintype.card F :=
  nestedPowerAgreement_probability_bound bad E h
end
