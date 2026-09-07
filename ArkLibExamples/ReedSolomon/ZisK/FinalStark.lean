/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLibExamples.ReedSolomon.ZisK.Interpolation
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.NestedPowerAgreement

/-!
# The compressed final STARK: 53 queries with the existing grinding hook

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

/-- Sum of the four positive inner bounds and the outer bound. -/
def batchingCount : ℕ := 5788837775855764804

/-- The singleton contributes zero to the sum of batching exceptions. -/
theorem batchingCount_eq :
    exceptionalCounts 0 + exceptionalCounts 1 + exceptionalCounts 2 +
      exceptionalCounts 3 + exceptionalCounts 4 = batchingCount := by decide

/-- The singleton opening group needs no exceptional challenges. -/
def innerCounts : Fin 5 → ℕ := ![0, exceptionalCounts 3, exceptionalCounts 2,
  exceptionalCounts 1, exceptionalCounts 0]

open Classical in
/-- The two actual powers challenges recover every original message outside one
exceptional set of pairs, constructed from the received words before any candidate. -/
theorem exists_nested_exceptional
    (domain : Fin 524288 ↪ GoldilocksCubic)
    (values : (g : Fin 5) → Fin (innerDegree g + 1) → Fin 524288 → GoldilocksCubic) :
    ∃ exceptional : Finset (GoldilocksCubic × GoldilocksCubic),
      exceptional.card ≤ fieldSize * batchingCount ∧
      ∀ u v, (u, v) ∉ exceptional → ∀ P : GoldilocksCubic[X], P.degree < 32768 →
        131069 ≤ (polynomialAgreementSet domain
          (powerBatchedWord (fun g ↦ powerBatchedWord (values g) u) v) P).card →
        HasExactNestedPowerAgreement domain innerDegree values 32768 u v P := by
  have hi (g : Fin 5) :
      UniformExactPowerAgreement domain (values g) 32768 131069 (innerCounts g) := by
    fin_cases g
    · exact uniformExactPowerAgreement_singleton domain (values 0) 32768 131069
    · exact exists_exceptional 3 domain (values 1)
    · exact exists_exceptional 2 domain (values 2)
    · exact exists_exceptional 1 domain (values 3)
    · exact exists_exceptional 0 domain (values 4)
  have ho (u : GoldilocksCubic) : UniformExactPowerAgreement domain
      (fun g ↦ powerBatchedWord (values g) u) 32768 131069 (exceptionalCounts 4) :=
    exists_exceptional 4 domain (fun g ↦ powerBatchedWord (values g) u)
  obtain ⟨bad, hcard, hgood⟩ := nestedPowerAgreement domain innerDegree values
    32768 131069 innerCounts (exceptionalCounts 4) hi ho
  refine ⟨bad, ?_, hgood⟩
  rw [fieldSize_eq] at hcard
  have hs : (∑ g, innerCounts g) + exceptionalCounts 4 = batchingCount := by
    decide
  simpa only [hs] using hcard

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

/-- The exact finite agreement threshold permits 53 queries at the existing 22-bit hook. -/
theorem queries_at_target :
    (131069 / 524288 : ℚ) ^ 53 / 2 ^ 22 ≤ 1 / 2 ^ 128 := by decide +kernel

/-- At rate `1/16`, every positive-gap implemented Johnson threshold exceeds `1/4`;
53 queries then fail the target at the same 22-bit hook. This concerns that formula,
not all possible Johnson analyses. -/
theorem johnson_queries_fail (a : ℚ) (ha : 1 / 4 < a) :
    1 / 2 ^ 128 < a ^ 53 / 2 ^ 22 := by
  have hp : (1 / 4 : ℚ) ^ 53 < a ^ 53 :=
    pow_lt_pow_left₀ ha (by norm_num) (by decide)
  have heq : (1 / 4 : ℚ) ^ 53 / 2 ^ 22 = 1 / 2 ^ 128 := by norm_num
  rw [← heq]
  exact div_lt_div_of_pos_right hp (by positivity)

/-- With all fixed payload retained, removing one response saves exactly 3920 bytes. -/
theorem proof_size :
    54 * 3920 + 42352 = (254032 : ℕ) ∧
    53 * 3920 + 42352 = (250112 : ℕ) ∧
    254032 - 250112 = (3920 : ℕ) := by decide

end
end ArkLibExamples.ReedSolomon.ZisK
