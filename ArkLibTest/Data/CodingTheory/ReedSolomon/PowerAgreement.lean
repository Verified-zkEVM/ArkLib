/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement.ConstantCode
import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement

/-!
# Constant-code power-agreement acceptance tests

A concrete two-point example attains the exceptional-challenge bound for constant messages, and a
sample-interpolated tuple belongs to the finite family.
-/

open Polynomial ReedSolomon

namespace ConstantCodeTest

/-- The evaluation points `0, 1` in `ℚ`. -/
def domain2 : Fin 2 ↪ ℚ :=
  ⟨fun i ↦ ((i : ℕ) : ℚ), fun _ _ h ↦ Fin.ext (Nat.cast_injective (R := ℚ) h)⟩

/-- Two received words with swapped columns `(0, 1)` and `(1, 0)`; their batched values `z` and
`1` collide at `z = 1`. -/
def swapWords : Fin 2 → Fin 2 → ℚ := ![![0, 1], ![1, 0]]

-- The bound is attained: `z = 1` is exceptional, and one exception suffices.
example : ¬ UniformExactPowerAgreement domain2 swapWords 1 2 0 ∧
    UniformExactPowerAgreement domain2 swapWords 1 2 1 := by
  constructor
  · rintro ⟨exceptional, hcard, hagree⟩
    have hempty : exceptional = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    have hfull : polynomialAgreementSet domain2
        (powerBatchedWord swapWords 1) (C 1) = Finset.univ := by
      ext i
      fin_cases i <;> simp [polynomialAgreementSet, powerBatchedWord, swapWords, domain2]
    have hnot : ¬ HasExactPowerAgreement domain2 swapWords (RingHom.id ℚ) 1 1 (C 1) := by
      rw [hasExactPowerAgreement_constant_iff _ _ (by simp : (C (1 : ℚ) : ℚ[X]).degree < 1), hfull]
      intro h
      have hzero := h 0 (by simp) 1 (by simp) 0
      norm_num [swapWords] at hzero
    exact hnot (hagree 1 (by simp [hempty]) (C 1) (by simp) (by rw [hfull]; simp))
  · simpa using uniformExactPowerAgreement_constantCode domain2 swapWords 2

example : UniformExactPowerAgreement domain2 swapWords 2 2 0 :=
  uniformExactPowerAgreement_fullDimension domain2 swapWords

example : ∃ P : Fin 2 → ℚ[X], (∀ t, (P t).degree < 2) ∧
    HasExactPowerAgreement domain2 swapWords (RingHom.id ℚ) 2 0 X := by
  obtain ⟨P, hP, hgood⟩ := exists_exactPower_fullDimension domain2 swapWords
  refine ⟨P, hP, hgood 0 X (by norm_num) ?_⟩
  have hfull : polynomialAgreementSet domain2 (powerBatchedWord swapWords 0) X =
      (Finset.univ : Finset (Fin 2)) := by
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, mem_polynomialAgreementSet, eval_X,
        Finset.mem_univ, iff_true]
      norm_num [powerBatchedWord, swapWords, Fin.sum_univ_succ]
      change (((0 : Fin 2) : ℕ) : ℚ) = 0
      norm_num
    · simp only [Fin.mk_one, Fin.isValue, mem_polynomialAgreementSet, eval_X,
        Finset.mem_univ, iff_true]
      norm_num [powerBatchedWord, swapWords, Fin.sum_univ_succ]
      change (((1 : Fin 2) : ℕ) : ℚ) = 1
      norm_num
  rw [hfull]
  simp

end ConstantCodeTest

namespace InterpolationFamilyTest

open Polynomial ReedSolomon

def domain2 : Fin 2 ↪ ℚ :=
  ⟨fun i ↦ ((i : ℕ) : ℚ), fun _ _ h ↦ Fin.ext (Nat.cast_injective (R := ℚ) h)⟩

def words : Fin 2 → Fin 2 → ℚ := ![![0, 1], ![1, 0]]

noncomputable def tuple : Fin 2 → ℚ[X] := ![0, 1]

example : tuple ∈ polynomialTupleFamily domain2 words 1 ∧
    (polynomialTupleFamily domain2 words 1).card ≤ 2 := by
  have hcommon : commonCurveAgreementSet domain2 words tuple = {0} := by
    ext i
    fin_cases i <;> simp [commonCurveAgreementSet, words, tuple, domain2]
  have hdegree : ∀ t, (tuple t).degree < 1 := by
    intro t
    fin_cases t <;> simp [tuple]
  refine ⟨(mem_polynomialTupleFamily_iff domain2 words tuple 1).2
    ⟨hdegree, by rw [hcommon]; simp⟩, ?_⟩
  simpa using (polynomialTupleFamily_card_le domain2 words 1)

end InterpolationFamilyTest
