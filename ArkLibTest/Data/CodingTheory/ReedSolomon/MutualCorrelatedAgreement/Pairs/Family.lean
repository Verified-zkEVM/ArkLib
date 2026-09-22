/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Pairs.Family
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance tests for correlated pair families

On the domain `0, 1` in `ℚ` with `f = (1, 2)` and `g = (1, 1)`, the family at `k = 2` is exactly
`{(X + 1, 1)}`: the pair agrees everywhere, and the family has at most `choose 2 2 = 1` element.
At `k = 3` the family is empty. Over `ZMod 2`, no challenge separates the four constant pairs,
so the hypothesis `Infinite E` is needed.
-/

open Polynomial

namespace ReedSolomon.PairFamilyTest

/-- The domain `0, 1` in `ℚ`. -/
def dom : Fin 2 ↪ ℚ := ⟨![0, 1], by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all⟩

@[simp] lemma dom_apply (i : Fin 2) : dom i = ![0, 1] i := rfl

/-- The family at `k = 2` is the single interpolant pair `(X + 1, 1)`. -/
example : correlatedPairFamily dom ![1, 2] ![1, 1] 2 = {(X + 1, C 1)} := by
  have hmem : (X + 1, C 1) ∈ correlatedPairFamily dom ![1, 2] ![1, 1] 2 := by
    refine mem_correlatedPairFamily_of_commonAgreement dom _ _ _ _ ?_ ?_ ?_
    · rw [← C_1, degree_X_add_C]
      norm_num
    · exact (degree_C_le).trans_lt (by norm_num)
    · have : commonPolynomialAgreementSet dom ![1, 2] ![1, 1] (X + 1) (C 1) = Finset.univ := by
        ext i
        fin_cases i <;> norm_num [commonPolynomialAgreementSet]
      rw [this, Finset.card_univ, Fintype.card_fin]
  have hcard := correlatedPairFamily_card_le dom ![1, 2] ![1, 1] 2
  simp only [Fintype.card_fin, Nat.choose_self] at hcard
  exact (Finset.card_le_one_iff_subset_singleton.mp hcard).elim fun p hp ↦ by
    rw [Finset.subset_singleton_iff] at hp
    rcases hp with hp | hp
    · simp [hp] at hmem
    · rw [hp, Finset.singleton_inj.mpr (Finset.mem_singleton.mp (hp ▸ hmem)).symm]

/-- The family is empty when `k` exceeds the number of coordinates. -/
example (f g : Fin 2 → ℚ) : correlatedPairFamily dom f g 3 = ∅ := by
  have := correlatedPairFamily_card_le dom f g 3
  simpa using this

/-- `Infinite E` is needed in `exists_correlatedPairSpecialization_injOn_avoiding`: over `ZMod 2`,
every challenge identifies two of the four constant pairs. -/
example : ¬ ∃ z : ZMod 2, Set.InjOn (correlatedPairSpecialization (RingHom.id (ZMod 2)) z)
    ↑({(0, 0), (0, C 1), (C 1, 0), (C 1, C 1)} : Finset ((ZMod 2)[X] × (ZMod 2)[X])) := by
  rintro ⟨z, hz⟩
  fin_cases z
  · have h := hz (by simp) (by simp) (show correlatedPairSpecialization (RingHom.id _) 0
      ((0 : (ZMod 2)[X]), C 1) = correlatedPairSpecialization (RingHom.id _) 0 (0, 0) by
        simp [correlatedPairSpecialization])
    simp at h
  · have h := hz (by simp) (by simp) (show correlatedPairSpecialization (RingHom.id _) 1
      ((0 : (ZMod 2)[X]), C 1) = correlatedPairSpecialization (RingHom.id _) 1 (C 1, 0) by
        simp [correlatedPairSpecialization])
    simp at h

/-- Over `ℚ`, the four constant pairs are separated by a challenge outside `{0, 1}`. -/
example : ∃ z : ℚ, z ∉ ({0, 1} : Finset ℚ) ∧
    Set.InjOn (correlatedPairSpecialization (RingHom.id ℚ) z)
      ↑({(0, 0), (0, C 1), (C 1, 0), (C 1, C 1)} : Finset (ℚ[X] × ℚ[X])) :=
  exists_correlatedPairSpecialization_injOn_avoiding _ _ _

end ReedSolomon.PairFamilyTest
