/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Pairs.ExceptionalSet
import Mathlib.Data.Fin.VecNotation

/-!
# Acceptance tests for the family exceptional set

On the domain `0, 1` in `ℚ` with `f = (1, 2)` and `g = (1, 1)`, the family `{(0, 1)}` has second
polynomial `1`, which agrees with `g` everywhere. The disagreement count is `0`, so the exceptional
set is empty and the agreement identity holds for every challenge. With the threshold version and
the family `{(X + 1, 1)}` of full common agreement, the bound `#pairs * (2 - 2)` is also `0`.
-/

open Polynomial

namespace ReedSolomon.PairExceptionalSetTest

/-- The domain `0, 1` in `ℚ`. -/
def dom : Fin 2 ↪ ℚ := ⟨![0, 1], by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all⟩

@[simp] lemma dom_apply (i : Fin 2) : dom i = ![0, 1] i := rfl

/-- A zero disagreement count forces an empty exceptional set, so the identity holds at every
challenge. -/
example (z : ℚ) :
    polynomialAgreementSet (dom.trans ⟨RingHom.id ℚ, (RingHom.id ℚ).injective⟩)
        (fun i ↦ RingHom.id ℚ (![1, 2] i) + z * RingHom.id ℚ (![1, 1] i))
        (correlatedPairSpecialization (RingHom.id ℚ) z (0, C 1)) =
      commonPolynomialAgreementSet dom ![1, 2] ![1, 1] 0 (C 1) := by
  obtain ⟨exceptional, hcard, h⟩ := exists_exceptional_correlatedPairFamily_le_sum dom ![1, 2]
    ![1, 1] (RingHom.id ℚ) {((0 : ℚ[X]), C 1)}
  have hg : polynomialAgreementSet dom ![1, 1] (C 1) = Finset.univ := by
    ext i
    fin_cases i <;> simp [polynomialAgreementSet]
  simp only [Finset.sum_singleton, hg, Finset.card_univ, Fintype.card_fin, Nat.sub_self,
    nonpos_iff_eq_zero, Finset.card_eq_zero] at hcard
  exact h _ (Finset.mem_singleton_self _) z (by simp [hcard])

/-- The threshold version at `L = 2` on a family with full common agreement gives the bound `0`. -/
example : ∃ exceptional : Finset ℚ, exceptional.card ≤ 0 ∧
    ∀ pair ∈ ({(X + 1, C 1)} : Finset (ℚ[X] × ℚ[X])), ∀ z ∉ exceptional,
      polynomialAgreementSet (dom.trans ⟨RingHom.id ℚ, (RingHom.id ℚ).injective⟩)
          (fun i ↦ RingHom.id ℚ (![1, 2] i) + z * RingHom.id ℚ (![1, 1] i))
          (correlatedPairSpecialization (RingHom.id ℚ) z pair) =
        commonPolynomialAgreementSet dom ![1, 2] ![1, 1] pair.1 pair.2 := by
  have h := exists_exceptional_correlatedPairFamily (L := 2) dom ![1, 2] ![1, 1] (RingHom.id ℚ)
    {(X + 1, C 1)} (by
      intro pair hpair
      rw [Finset.mem_singleton.mp hpair]
      have : commonPolynomialAgreementSet dom ![1, 2] ![1, 1] (X + 1) (C 1) = Finset.univ := by
        ext i
        fin_cases i <;> norm_num [commonPolynomialAgreementSet]
      rw [this, Finset.card_univ, Fintype.card_fin])
  simpa using h

end ReedSolomon.PairExceptionalSetTest
