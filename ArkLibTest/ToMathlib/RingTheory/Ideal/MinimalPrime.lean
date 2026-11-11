/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Int.Basic

/-!
# Minimal-prime acceptance example
-/

example : ∃ P ∈ (Ideal.span {(6 : ℤ)}).retainedMinimalPrimes 2,
    P ≤ Ideal.span {(3 : ℤ)} := by
  have hprime : (Ideal.span {(3 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_three
  refine Ideal.exists_mem_retainedMinimalPrimes_le ?_ ?_
  · rw [Ideal.span_singleton_le_span_singleton]
    norm_num
  · rw [Ideal.mem_span_singleton]
    norm_num
