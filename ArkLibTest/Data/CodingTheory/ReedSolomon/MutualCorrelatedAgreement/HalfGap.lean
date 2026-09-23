/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.HalfGap.Line
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation

open Polynomial Finset ReedSolomon

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def halfGapDomain : Fin 2 ↪ ZMod 5 := ⟨![0, 1], by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals simp_all
⟩

/-- A half-gap instance with `n = 2`, `k = 1` and `A = 2`. -/
example : ∃ F₀ G₀ : (ZMod 5)[X], F₀.degree < 1 ∧ G₀.degree < 1 ∧
    ∃ exceptional : Finset (ZMod 5), exceptional.card ≤ 3 ∧
      ∃ z, z ∉ exceptional ∧
        2 ≤ (polynomialAgreementSet halfGapDomain
          (fun i ↦ ![1, 1] i + z * ![0, 0] i) (C 1)).card ∧
        C 1 = F₀ + C z * G₀ ∧
          polynomialAgreementSet halfGapDomain (fun i ↦ ![1, 1] i + z * ![0, 0] i) (C 1) =
            commonPolynomialAgreementSet halfGapDomain ![1, 1] ![0, 0] F₀ G₀ := by
  obtain ⟨F₀, G₀, hF₀, hG₀, exceptional, hcard, hpair⟩ :=
    exists_exactPair_of_messageDim_add_half_blockLength_le (k := 1) (A := 2)
      halfGapDomain ![1, 1] ![0, 0] (by norm_num)
  have hcard' : exceptional.card ≤ 3 := by
    simpa [Fintype.card_fin] using hcard
  have hz : ∃ z, z ∉ exceptional := by
    by_contra hn
    have hsub : (Finset.univ : Finset (ZMod 5)) ⊆ exceptional := by
      intro z _
      by_contra hz
      exact hn ⟨z, hz⟩
    have hle := Finset.card_le_card hsub
    norm_num at hle
    omega
  obtain ⟨z, hz⟩ := hz
  have hagree : polynomialAgreementSet halfGapDomain
      (fun i ↦ ![1, 1] i + z * ![0, 0] i) (C 1) = Finset.univ := by
    ext i
    fin_cases i <;> simp [polynomialAgreementSet, halfGapDomain]
  have hclose : 2 ≤ (polynomialAgreementSet halfGapDomain
      (fun i ↦ ![1, 1] i + z * ![0, 0] i) (C 1)).card := by
    rw [hagree]
    simp
  obtain ⟨hP, hset⟩ := hpair z hz (C 1) (by simp) hclose
  exact ⟨F₀, G₀, hF₀, hG₀, exceptional, hcard', z, hz, hclose, hP, hset⟩
