/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Ideal.CutFamily
import ArkLib.ToMathlib.RingTheory.Ideal.PrincipalCut
import ArkLib.ToMathlib.RingTheory.Ideal.Separator
import Mathlib.RingTheory.Int.Basic

/-!
# Ideal acceptance examples
-/

open Ideal

example : ∃ Q ∈ iteratedRetainedCutFamily {(⊥ : Ideal ℤ)} 1 [2],
    (⊥ : Ideal ℤ) ≤ Q ∧ Q ≤ span {2} := by
  have hprime : (span {(2 : ℤ)}).IsPrime :=
    (span_singleton_prime (by norm_num)).mpr (Int.prime_iff_natAbs_prime.mpr Nat.prime_two)
  have hs : (1 : ℤ) ∉ span {(2 : ℤ)} := by
    rw [mem_span_singleton]
    norm_num
  exact @exists_mem_iteratedRetainedCutFamily_le ℤ inferInstance inferInstance
    {(⊥ : Ideal ℤ)} 1 [2] (⊥ : Ideal ℤ) (span {(2 : ℤ)}) hprime (by simp) bot_le hs (by simp)

example : (⊥ : Ideal ℤ) < span {2} ∧
    ringKrullDim (ℤ ⧸ span {(2 : ℤ)}) + 1 ≤ ringKrullDim (ℤ ⧸ (⊥ : Ideal ℤ)) := by
  have hprime : (span {(2 : ℤ)}).IsPrime :=
    (span_singleton_prime (by norm_num)).mpr (Int.prime_iff_natAbs_prime.mpr Nat.prime_two)
  have hJ : span {(2 : ℤ)} ∈ ((⊥ : Ideal ℤ) ⊔ span {2}).minimalPrimes := by
    rw [bot_sup_eq, minimalPrimes_eq_subsingleton_self]
    rfl
  have h2 : (2 : ℤ) ∉ (⊥ : Ideal ℤ) := by simp
  exact ⟨lt_of_mem_minimalPrimes_sup_span h2 hJ,
    ringKrullDim_quotient_succ_le_of_lt (lt_of_mem_minimalPrimes_sup_span h2 hJ)⟩

example : ∃ s : Fin 2 → ℤ, ∀ i j, s i ∈ ![span {(2 : ℤ)}, span {3}] j ↔ i ≠ j := by
  refine exists_separators_of_pairwise_not_le (fun i ↦ ?_) fun i j hij ↦ ?_
  · fin_cases i
    · exact (span_singleton_prime (by norm_num)).mpr
        (Int.prime_iff_natAbs_prime.mpr Nat.prime_two)
    · exact (span_singleton_prime (by norm_num)).mpr
        (Int.prime_iff_natAbs_prime.mpr Nat.prime_three)
  · fin_cases i <;> fin_cases j <;> simp_all [mem_span_singleton]
