/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.HalfGap.Line
import Mathlib.Data.Fin.VecNotation

open Polynomial Finset ReedSolomon

private def halfGapDomain : Fin 2 ↪ ℚ := ⟨![0, 1], by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all⟩

/-- A half-gap instance with `n = 2`, `k = 1` and `A = 2`. -/
example : ∃ F₀ G₀ : ℚ[X], F₀.degree < 1 ∧ G₀.degree < 1 ∧
    ∃ exceptional : Finset ℚ, exceptional.card ≤ 3 := by
  obtain ⟨F₀, G₀, hF₀, hG₀, exceptional, hcard, -⟩ :=
    exists_exactPair_of_messageDim_add_half_blockLength_le (k := 1) (A := 2)
      halfGapDomain ![0, 1] ![1, 0] (by simp)
  exact ⟨F₀, G₀, hF₀, hG₀, exceptional, by simpa using hcard⟩
