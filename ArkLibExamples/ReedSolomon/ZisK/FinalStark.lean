/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLibExamples.ReedSolomon.ZisK.Interpolation
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreement

/-!
# The compressed final STARK: 51 queries with the existing grinding hook

The batching, individual folds, and query checks each meet a 128-bit bound.
These separate phase bounds do not assert a 128-bit bound on their union.
The proof-size calculation changes only the query count and adds no nonce.

The grouped words below include the fixed opening-point weights. The groups follow increasing
outer powers order, reversing the outer Horner traversal; within each group the words
also follow increasing powers order. The theorem applies to arbitrary such words fixed before both
challenges; it does not formalize the implementation’s construction of those words.
-/
open Polynomial ReedSolomon
namespace ArkLibExamples.ReedSolomon.ZisK
open ConcreteFields
noncomputable section

/-- One degree-103 shared-inner bound plus the degree-four outer bound. -/
def batchingCount : ℕ := 4073324287379922825

/-- The shared inner curve is paid once, independently of the five group widths. -/
theorem batchingCount_eq :
    exceptionalCounts 2 + exceptionalCounts 4 = batchingCount := by decide

open Classical in
/-- The two actual powers challenges recover every original message outside one
exceptional set of pairs, constructed from the received words before any candidate. -/
theorem exists_nested_exceptional
    (domain : Fin 524288 ↪ GoldilocksCubic)
    (values : (g : Fin 5) → Fin (innerDegree g + 1) → Fin 524288 → GoldilocksCubic) :
    ∃ exceptional : Finset (GoldilocksCubic × GoldilocksCubic),
      exceptional.card ≤ fieldSize * batchingCount ∧
      ∀ u v, (u, v) ∉ exceptional → ∀ P : GoldilocksCubic[X], P.degree < 32768 →
        124136 ≤ (polynomialAgreementSet domain
          (powerBatchedWord (fun g ↦ powerBatchedWord (values g) u) v) P).card →
        HasExactNestedPowerAgreement domain innerDegree values 32768 u v P := by
  have hdegree (g : Fin 5) : innerDegree g ≤ 103 := by
    fin_cases g <;> decide
  have hscalar (scalarValues : Fin (103 + 1) → Fin 524288 → GoldilocksCubic) :
      UniformExactPowerAgreement domain scalarValues 32768 124136 (exceptionalCounts 2) :=
    exists_exceptional 2 domain scalarValues
  have hi : UniformExactInterleavedPowerAgreement domain
      (paddedPowerValues innerDegree hdegree values) 32768 124136 (exceptionalCounts 2) :=
    uniformExactInterleavedPowerAgreement_of_scalar domain hscalar (by decide) (by decide)
      (paddedPowerValues innerDegree hdegree values)
  have ho (u : GoldilocksCubic) : UniformExactPowerAgreement domain
      (fun g ↦ powerBatchedWord (values g) u) 32768 124136 (exceptionalCounts 4) :=
    exists_exceptional 4 domain (fun g ↦ powerBatchedWord (values g) u)
  obtain ⟨bad, hcard, hgood⟩ := nestedPowerAgreement_sharedInner domain innerDegree hdegree values
    (by decide) hi ho
  refine ⟨bad, ?_, hgood⟩
  rw [fieldSize_eq] at hcard
  simpa only [batchingCount_eq] using hcard

/-- The entire nested batching bound fits its own 128-bit phase, without grinding. -/
theorem batching_at_target :
    (batchingCount : ℚ) / fieldSize ≤ 1 / 2 ^ 128 := by decide +kernel

/-- The constructed pair bound implies the batching phase's uniform-pair error bound. -/
theorem pair_error_at_target (bad : Finset (GoldilocksCubic × GoldilocksCubic))
    (hbad : bad.card ≤ fieldSize * batchingCount) :
    (bad.card : ℚ) / (Fintype.card GoldilocksCubic : ℚ) ^ 2 ≤ 1 / 2 ^ 128 := by
  rw [fieldSize_eq]
  have hc : (bad.card : ℚ) ≤ (fieldSize : ℚ) * batchingCount := by exact_mod_cast hbad
  calc
    (bad.card : ℚ) / (fieldSize : ℚ) ^ 2 ≤
        ((fieldSize : ℚ) * batchingCount) / (fieldSize : ℚ) ^ 2 :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ ≤ 1 / 2 ^ 128 := by decide +kernel

/-- Each folding curve fits its own 128-bit phase. -/
theorem folds_at_target (i : Fin 3) :
    (exceptionalCounts ⟨i.val + 5, by omega⟩ : ℚ) / fieldSize ≤ 1 / 2 ^ 128 := by
  fin_cases i <;> decide +kernel

open Classical in
/-- Each fold constructs a uniform exceptional set whose actual probability meets
its own 128-bit target over the cubic Goldilocks challenge field. -/
theorem exists_fold_at_target (i : Fin 3)
    (domain : Fin (profiles ⟨i.val + 5, by omega⟩).n ↪ GoldilocksCubic)
    (values : Fin ((profiles ⟨i.val + 5, by omega⟩).batchingDegree + 1) →
      Fin (profiles ⟨i.val + 5, by omega⟩).n → GoldilocksCubic) :
    ∃ bad : Finset GoldilocksCubic,
      (bad.card : ℚ) / Fintype.card GoldilocksCubic ≤ 1 / 2 ^ 128 ∧
      ∀ z ∉ bad, ∀ P : GoldilocksCubic[X], P.degree < (profiles ⟨i.val + 5, by omega⟩).k →
        (profiles ⟨i.val + 5, by omega⟩).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id GoldilocksCubic)
          (profiles ⟨i.val + 5, by omega⟩).k z P := by
  obtain ⟨bad, hcard, hgood⟩ := exists_exceptional ⟨i.val + 5, by omega⟩ domain values
  refine ⟨bad, ?_, hgood⟩
  rw [fieldSize_eq]
  apply le_trans _ (folds_at_target i)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hcard

/-- The exact finite agreement threshold permits 51 queries at the existing 22-bit hook. -/
theorem queries_at_target :
    (124136 / 524288 : ℚ) ^ 51 / 2 ^ 22 ≤ 1 / 2 ^ 128 := by decide +kernel

/-- One fewer query misses the target for this exact agreement threshold and grinding hook. -/
theorem fifty_queries_fail :
    (1 / 2 ^ 128 : ℚ) < (124136 / 524288 : ℚ) ^ 50 / 2 ^ 22 := by decide +kernel

/-- The exact squared finite-Johnson comparison underlying the query-only floor. -/
theorem johnson_squared_queries_fail :
    (1 / 2 ^ 256 : ℚ) < (32767 / 524288 : ℚ) ^ 52 / 2 ^ 44 := by
  decide +kernel

/-- Even at the finite Johnson boundary `sqrt ((k - 1) / n)`, 52 queries fail the target
at the same 22-bit hook. Thus the new profile is below the Johnson query-only floor. -/
theorem johnson_queries_fail (a : ℚ) (ha : 0 ≤ a)
    (hj : (32767 / 524288 : ℚ) ≤ a ^ 2) :
    1 / 2 ^ 128 < a ^ 52 / 2 ^ 22 := by
  have hlo : (249 / 1000 : ℚ) < a := by nlinarith
  have hp : (249 / 1000 : ℚ) ^ 52 < a ^ 52 :=
    pow_lt_pow_left₀ hlo (by norm_num) (by decide)
  exact lt_trans (by decide +kernel :
    (1 / 2 ^ 128 : ℚ) < (249 / 1000 : ℚ) ^ 52 / 2 ^ 22)
    (div_lt_div_of_pos_right hp (by norm_num))

/-- With all fixed payload retained, removing three responses saves exactly 11760 bytes. -/
theorem proof_size :
    54 * 3920 + 42352 = (254032 : ℕ) ∧
    51 * 3920 + 42352 = (242272 : ℕ) ∧
    254032 - 242272 = (11760 : ℕ) := by decide

end
end ArkLibExamples.ReedSolomon.ZisK
