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

private theorem degree_le_zero_of_degree_lt_one {F : Type*} [Semiring F] (P : F[X])
    (hP : P.degree < 1) : P.degree ≤ 0 := by
  apply (degree_le_iff_coeff_zero P 0).2
  intro m hm
  have hm' : 0 < m := by exact_mod_cast hm
  exact (degree_lt_iff_coeff_zero P 1).mp hP m (Nat.succ_le_iff.mpr hm')

/-- A half-gap instance with `n = 2`, `k = 1` and `A = 2`. -/
example : ∃ F₀ G₀ : ℚ[X], F₀.degree < 1 ∧ G₀.degree < 1 ∧
    ∃ exceptional : Finset ℚ, exceptional.card ≤ 3 ∧ 1 ∈ exceptional ∧
      ∀ z ∉ exceptional, ∀ P : ℚ[X], P.degree < 1 →
        2 ≤ (polynomialAgreementSet halfGapDomain (fun i ↦ ![0, 1] i + z * ![1, 0] i) P).card →
        P = F₀ + C z * G₀ ∧
          polynomialAgreementSet halfGapDomain (fun i ↦ ![0, 1] i + z * ![1, 0] i) P =
            commonPolynomialAgreementSet halfGapDomain ![0, 1] ![1, 0] F₀ G₀ := by
  obtain ⟨F₀, G₀, hF₀, hG₀, exceptional, hcard, hpair⟩ :=
    exists_exactPair_of_messageDim_add_half_blockLength_le (k := 1) (A := 2)
      halfGapDomain ![0, 1] ![1, 0] (by simp)
  refine ⟨F₀, G₀, hF₀, hG₀, exceptional, ?_, ?_, hpair⟩
  · have hcard' := hcard
    rw [Fintype.card_fin] at hcard'
    norm_num at hcard'
    exact hcard'
  by_contra hnot
  have hagree :
      polynomialAgreementSet halfGapDomain (fun i ↦ ![0, 1] i + 1 * ![1, 0] i) (C 1) =
        Finset.univ := by
    ext i
    fin_cases i <;> norm_num [polynomialAgreementSet, halfGapDomain]
  obtain ⟨_, hset⟩ := hpair 1 hnot (C 1) (by simp) (by rw [hagree, card_univ]; decide)
  have h0 : (0 : Fin 2) ∈ commonPolynomialAgreementSet halfGapDomain ![0, 1] ![1, 0] F₀ G₀ := by
    rw [← hset, hagree]
    simp
  have h1 : (1 : Fin 2) ∈ commonPolynomialAgreementSet halfGapDomain ![0, 1] ![1, 0] F₀ G₀ := by
    rw [← hset, hagree]
    simp
  have hF0 := (mem_commonPolynomialAgreementSet ..).mp h0
  have hF1 := (mem_commonPolynomialAgreementSet ..).mp h1
  have hFpoly : F₀ = C (F₀.coeff 0) := by
    exact eq_C_of_degree_le_zero (degree_le_zero_of_degree_lt_one F₀ hF₀)
  have hFconstant' : F₀.eval 0 = F₀.eval 1 := by
    rw [hFpoly]
    simp
  have hF0' : F₀.eval 0 = 0 ∧ G₀.eval 0 = 1 := by
    rcases hF0 with ⟨hFzero, hGzero⟩
    change F₀.eval 0 = 0 at hFzero
    change G₀.eval 0 = 1 at hGzero
    exact ⟨hFzero, hGzero⟩
  have hF1' : F₀.eval 1 = 1 ∧ G₀.eval 1 = 0 := by
    rcases hF1 with ⟨hFone, hGone⟩
    change F₀.eval 1 = 1 at hFone
    change G₀.eval 1 = 0 at hGone
    exact ⟨hFone, hGone⟩
  rcases hF0' with ⟨hFzero, _⟩
  rcases hF1' with ⟨hFone, _⟩
  rw [hFzero, hFone] at hFconstant'
  norm_num at hFconstant'
