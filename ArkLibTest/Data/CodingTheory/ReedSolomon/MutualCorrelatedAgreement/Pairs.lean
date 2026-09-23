/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Pairs.ExceptionalSet
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Pairs.Family
import Mathlib.Data.Fin.VecNotation

open Polynomial ReedSolomon

private def pairDomain : Fin 2 ↪ ℚ :=
  ⟨fun i ↦ ((i : ℕ) : ℚ), fun _ _ h ↦ Fin.ext (Nat.cast_injective (R := ℚ) h)⟩

example : correlatedPairFamily pairDomain ![1, 2] ![1, 1] 2 = {(X + 1, C 1)} := by
  have hmem : (X + 1, C 1) ∈ correlatedPairFamily pairDomain ![1, 2] ![1, 1] 2 := by
    refine mem_correlatedPairFamily_of_commonAgreement pairDomain _ _ _ _ ?_ ?_ ?_
    · rw [← C_1, degree_X_add_C]
      norm_num
    · exact (degree_C_le).trans_lt (by norm_num)
    · have hcommon :
        commonPolynomialAgreementSet pairDomain ![1, 2] ![1, 1] (X + 1) (C 1) = Finset.univ := by
        ext i
        fin_cases i
        · norm_num [commonPolynomialAgreementSet, pairDomain]
          change (0 : ℚ) = 0
          rfl
        · norm_num [commonPolynomialAgreementSet, pairDomain]
          change (1 : ℚ) + 1 = 2
          norm_num
      rw [hcommon, Finset.card_univ, Fintype.card_fin]
  have hcard := correlatedPairFamily_card_le pairDomain ![1, 2] ![1, 1] 2
  simp only [Fintype.card_fin, Nat.choose_self] at hcard
  exact (Finset.card_le_one_iff_subset_singleton.mp hcard).elim fun p hp ↦ by
    rw [Finset.subset_singleton_iff] at hp
    rcases hp with hp | hp
    · simp [hp] at hmem
    · rw [hp, Finset.singleton_inj.mpr (Finset.mem_singleton.mp (hp ▸ hmem)).symm]

/-- The threshold bound is zero for a pair agreeing on both coordinates. -/
example : ∃ exceptional : Finset ℚ, exceptional.card ≤ 0 ∧
    ∀ pair ∈ ({(X + 1, C 1)} : Finset (ℚ[X] × ℚ[X])), ∀ z ∉ exceptional,
      polynomialAgreementSet (pairDomain.trans ⟨RingHom.id ℚ, (RingHom.id ℚ).injective⟩)
          (fun i ↦ RingHom.id ℚ (![1, 2] i) + z * RingHom.id ℚ (![1, 1] i))
          (correlatedPairSpecialization (RingHom.id ℚ) z pair) =
        commonPolynomialAgreementSet pairDomain ![1, 2] ![1, 1] pair.1 pair.2 := by
  have h := exists_exceptional_correlatedPairFamily (L := 2) pairDomain ![1, 2] ![1, 1]
    (RingHom.id ℚ) {(X + 1, C 1)} (by
      intro pair hpair
      rw [Finset.mem_singleton.mp hpair]
      have hcommon :
          commonPolynomialAgreementSet pairDomain ![1, 2] ![1, 1] (X + 1) (C 1) = Finset.univ := by
        ext i
        fin_cases i
        · norm_num [commonPolynomialAgreementSet, pairDomain]
          change (0 : ℚ) = 0
          rfl
        · norm_num [commonPolynomialAgreementSet, pairDomain]
          change (1 : ℚ) + 1 = 2
          norm_num
      rw [hcommon, Finset.card_univ, Fintype.card_fin])
  simpa using h

example : ∃ z : ℚ, z ∉ ({0, 1} : Finset ℚ) ∧
    Set.InjOn (correlatedPairSpecialization (RingHom.id ℚ) z)
      ↑({(0, 0), (0, C 1), (C 1, 0), (C 1, C 1)} : Finset (ℚ[X] × ℚ[X])) :=
  exists_correlatedPairSpecialization_injOn_avoiding _ _ _
