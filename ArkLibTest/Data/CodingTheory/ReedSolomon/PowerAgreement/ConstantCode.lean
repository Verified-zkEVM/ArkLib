/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement.ConstantCode

/-!
# Exact power agreement for constant messages

These clients derive the list bound for a batched received word and the threshold-specific forms
of uniform exact power agreement from the general statements, show that `0 < A` is needed in the
list bound, and check on a two-point example over `ℚ` that the exceptional set cannot be empty
and that the count `ℓ * (|ι|.choose 2) / max (A - 1) 1 = 1` is attained.
-/

open Polynomial ReedSolomon

namespace ConstantCodeTest

section General

variable {F : Type*} [Field F] [DecidableEq F]

-- The list bound for the batched word of a received curve, at block length `3` and `A = 2`.
example (domain : Fin 3 ↪ F) (w : Fin 3 → Fin 3 → F) (z : F) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain (powerBatchedWord w z) 1 2) ∧
      list.card ≤ 1 :=
  exists_closePolynomial_finset_one_card_le_div domain (powerBatchedWord w z) (by norm_num)

-- `0 < A` is needed in the list bound: at `A = 0` every constant is in the list, so the list is
-- nonempty while `n / 0 = 0`.
example {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F) :
    ¬ ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received 1 0) ∧ list.card ≤ n / 0 := by
  rintro ⟨list, hlist, hcard⟩
  have h0 : (0 : F[X]) ∈ list := (hlist 0).mpr ⟨by simp, Nat.zero_le _⟩
  simp_all

/-- The form with the two thresholds `A = 1` and `A ≥ 2` joined by a case split, for `0 < A`. -/
theorem uniformExactPowerAgreement_constantCode_ite {ι : Type*} [Fintype ι] {ℓ : ℕ}
    (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) (A : ℕ) (hA : 0 < A) :
    UniformExactPowerAgreement domain w 1 A
      (if A = 1 then ℓ * (Fintype.card ι).choose 2
        else ℓ * (Fintype.card ι).choose 2 / (A - 1)) := by
  split_ifs with hA1
  · subst hA1
    simpa using uniformExactPowerAgreement_constantCode domain w 1
  · exact uniformExactPowerAgreement_constantCode_of_two_le domain w (by omega)

-- The threshold `A = 1`: at most `ℓ * (n.choose 2)` exceptional challenges.
example {n ℓ : ℕ} (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) :
    UniformExactPowerAgreement domain w 1 1 (ℓ * n.choose 2) := by
  simpa using uniformExactPowerAgreement_constantCode domain w 1

-- The threshold `A = 0` has the same count as `A = 1`.
example {n ℓ : ℕ} (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) :
    UniformExactPowerAgreement domain w 1 0 (ℓ * n.choose 2) := by
  simpa using uniformExactPowerAgreement_constantCode domain w 0

-- Block length `3`, two received words, threshold `2`: at most `1 * 3 / 1 = 3` challenges.
example (domain : Fin 3 ↪ F) (w : Fin 2 → Fin 3 → F) :
    UniformExactPowerAgreement domain w 1 2 3 := by
  simpa using uniformExactPowerAgreement_constantCode_of_two_le domain w (le_refl 2)

-- Block length `3`, three received words, threshold `1`: at most `2 * 3 = 6` challenges.
example (domain : Fin 3 ↪ F) (w : Fin 3 → Fin 3 → F) :
    UniformExactPowerAgreement domain w 1 1 6 := by
  simpa using uniformExactPowerAgreement_constantCode domain w 1

end General

section TwoPoints

/-- The evaluation points `0, 1` in `ℚ`. -/
def domain2 : Fin 2 ↪ ℚ :=
  ⟨fun i ↦ ((i : ℕ) : ℚ), fun _ _ h ↦ Fin.ext (Nat.cast_injective (R := ℚ) h)⟩

/-- Two received words with swapped columns `(0, 1)` and `(1, 0)`; their batched values `z` and
`1` collide at `z = 1`. -/
def swapWords : Fin 2 → Fin 2 → ℚ := ![![0, 1], ![1, 0]]

/-- At `z = 1` the constant `1` agrees with the batched word of `swapWords` at both points. -/
theorem polynomialAgreementSet_swapWords_one :
    polynomialAgreementSet domain2 (powerBatchedWord swapWords 1) (C 1) = Finset.univ := by
  ext i
  fin_cases i <;> simp [powerBatchedWord, swapWords]

/-- At `z = 1` the constant `1` has no exact power agreement with `swapWords`, since the two
columns differ. -/
theorem not_hasExactPowerAgreement_swapWords :
    ¬ HasExactPowerAgreement domain2 swapWords (RingHom.id ℚ) 1 1 (C 1) := by
  rw [hasExactPowerAgreement_constant_iff _ _ degree_C_lt, polynomialAgreementSet_swapWords_one]
  intro h
  simpa [swapWords] using h 0 (Finset.mem_univ _) 1 (Finset.mem_univ _) 0

-- The exceptional set cannot be empty.
example : ¬ UniformExactPowerAgreement domain2 swapWords 1 2 0 := by
  rintro ⟨bad, hcard, hbad⟩
  have hempty : bad = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
  refine not_hasExactPowerAgreement_swapWords (hbad 1 (by simp [hempty]) (C 1) degree_C_lt ?_)
  rw [polynomialAgreementSet_swapWords_one]
  simp

-- The general count `1 * (2.choose 2) / max 1 1 = 1` is attained.
example : UniformExactPowerAgreement domain2 swapWords 1 2 1 := by
  simpa using uniformExactPowerAgreement_constantCode domain2 swapWords 2

end TwoPoints

end ConstantCodeTest
