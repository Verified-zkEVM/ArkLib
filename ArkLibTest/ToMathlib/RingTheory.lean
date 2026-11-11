/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Nullstellensatz

/-!
# Zero-locus acceptance example
-/

open MvPolynomial

example : ∃ P ∈ (Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}).retainedMinimalPrimes 1,
    (![0] : Fin 1 → ℚ) ∈ zeroLocus ℚ P := by
  have hx : (![0] : Fin 1 → ℚ) ∈
      zeroLocus ℚ (Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}) := by
    simp [zeroLocus_span]
  obtain ⟨P, hP, hxP⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus
    (Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}) (1 : MvPolynomial (Fin 1) ℚ) ![0] hx (by simp)
  exact ⟨P, hP, hxP⟩
