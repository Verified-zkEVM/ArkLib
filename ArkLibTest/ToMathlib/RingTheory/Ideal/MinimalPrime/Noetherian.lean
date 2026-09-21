/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Int.Basic

/-!
# Acceptance client for minimal primes as a finset

The examples use the Noetherian ring `ℤ`. They compute `Ideal.minimalPrimesFinset` and
`Ideal.retainedMinimalPrimes` for the zero ideal and the unit ideal, apply
`Ideal.exists_mem_retainedMinimalPrimes_le` to the ideal `(6)` below the prime `(3)`, and check that
the hypothesis `s ∉ Q` of that theorem cannot be dropped.
-/

namespace MinimalPrimesFinsetCanary

/-- In a domain the zero ideal is prime, so it is its own unique minimal prime. -/
example : (⊥ : Ideal ℤ).minimalPrimesFinset = {⊥} :=
  Ideal.minimalPrimesFinset_of_isPrime ⊥

/-- A nonzero element retains the zero ideal of `ℤ`; zero retains nothing. -/
example :
    (⊥ : Ideal ℤ).retainedMinimalPrimes 2 = {⊥} ∧
      (⊥ : Ideal ℤ).retainedMinimalPrimes 0 = ∅ := by
  refine ⟨?_, Ideal.retainedMinimalPrimes_eq_empty_iff.mpr (Ideal.zero_mem _)⟩
  ext P
  simp only [Ideal.mem_retainedMinimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self,
    Set.mem_singleton_iff, Finset.mem_singleton, and_iff_left_iff_imp]
  rintro rfl
  simp

/-- The unit ideal has no minimal primes. -/
example : (⊤ : Ideal ℤ).minimalPrimesFinset = ∅ :=
  Ideal.minimalPrimesFinset_eq_empty_iff.mpr rfl

/-- The ideal `(6)` lies in the prime `(3)`, which does not contain `2`, so some minimal prime
over `(6)` avoiding `2` lies in `(3)`. -/
example :
    ∃ P ∈ (Ideal.span {(6 : ℤ)}).retainedMinimalPrimes 2, P ≤ Ideal.span {(3 : ℤ)} := by
  have : (Ideal.span {(3 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_three
  refine Ideal.exists_mem_retainedMinimalPrimes_le ?_ ?_
  · rw [Ideal.span_singleton_le_span_singleton]
    norm_num
  · rw [Ideal.mem_span_singleton]
    norm_num

/-- The hypothesis `s ∉ Q` cannot be dropped: for the prime `Q = (3)` and `s = 3`, the only
minimal prime over `(3)` contains `3`, so nothing is retained. -/
example : (Ideal.span {(3 : ℤ)}).retainedMinimalPrimes 3 = ∅ :=
  Ideal.retainedMinimalPrimes_eq_empty_iff.mpr
    (Ideal.le_radical (Ideal.mem_span_singleton_self 3))

/-- Retained minimal primes are minimal primes. -/
example (I : Ideal ℤ) (s : ℤ) (P : Ideal ℤ) (hP : P ∈ I.retainedMinimalPrimes s) :
    P ∈ I.minimalPrimesFinset :=
  Ideal.retainedMinimalPrimes_subset I s hP

end MinimalPrimesFinsetCanary
