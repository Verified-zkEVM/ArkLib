/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.Uniform
import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.SharpListBound
/-!
# Uniform first-order lists at capacity gap 6/25

The fixed support `(m,M,μ) = (12,4,22)` and height `851` give an exact list
with at most `13623 n` candidates. The `k = 1` branch uses elementary agreement
incidence and requires no characteristic condition. The other branch retains its
original characteristic guard. Mutual correlated agreement is proved separately.
-/

namespace ReedSolomon

open Polynomial HiddenDerivative
open scoped BigOperators

universe u

open Classical in
private theorem mem_closePolynomialSet_iff_isAgreementSolution
    {F : Type*} [Field F] [DecidableEq F] {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (P : F[X]) :
    P ∈ closePolynomialSet domain received k A ↔
      IsAgreementSolution domain received k A P := by
  unfold closePolynomialSet IsAgreementSolution
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    convert h.2 using 1
    congr 1
    ext i
    simp [polynomialAgreementSet]
  · intro h
    refine ⟨h.1, ?_⟩
    convert h.2 using 1
    congr 1
    ext i
    simp [polynomialAgreementSet]

private theorem uniformFirstOrder_listWeight_eq (k : ℕ) :
    firstOrderListWeight k 22 4 = 3208 * k + 253 := by
  norm_num [firstOrderListWeight]
  ring

private theorem uniformFirstOrder_listRatio_le (n k A : ℕ)
    (hn : 2 ≤ n) (_hk : 2 ≤ k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A) :
    ((n * firstOrderListWeight k 22 4 : ℕ) : ℚ) / (A - k + 1 : ℕ) ≤
      13623 * n := by
  have hkA : k ≤ A := by exact_mod_cast (show (k : ℝ) ≤ A by linarith)
  have hden : (0 : ℚ) < (A - k + 1 : ℕ) := by positivity
  apply (div_le_iff₀ hden).2
  rw [uniformFirstOrder_listWeight_eq]
  push_cast [Nat.cast_sub hkA]
  have hkn : k ≤ n := hkA.trans hAn
  have hrate : (25 : ℚ) * k ≤ 19 * n := by
    have hAnR : (A : ℝ) ≤ n := by exact_mod_cast hAn
    exact_mod_cast (show (25 : ℝ) * k ≤ 19 * n by nlinarith)
  have hgapQ : (6 : ℚ) * n ≤ 25 * ((A : ℚ) - k) := by
    exact_mod_cast (show (6 : ℝ) * n ≤ 25 * ((A : ℝ) - k) by nlinarith)
  have hnQ : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hnposQ : (0 : ℚ) < n := by positivity
  calc
    (n : ℚ) * (3208 * k + 253) ≤
        n * (13623 * ((A : ℚ) - k + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hnposQ.le
          nlinarith
    _ = 13623 * n * ((A : ℚ) - k + 1) := by ring

/-- The actual height-851 shifted certificate bounds the complete close-polynomial list for
every message dimension `k >= 2`.  The returned finite set is extensionally exact. -/
private theorem exists_uniformFirstOrder_list_of_two_le
    {F : Type u} [Field F] [DecidableEq F]
    (n k A : ℕ) (domain : Fin n ↪ F) (received : Fin n → F)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A)
    (hchar : ringChar F = 0 ∨ max (k - 1) 22 < ringChar F) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received k A) ∧
      list.card ≤ 13623 * n := by
  classical
  let D := max (k - 1) 2
  have hgapNat : 25 * k + 6 * n ≤ 25 * A := by
    exact_mod_cast (show (25 : ℝ) * k + 6 * n ≤ 25 * A by nlinarith)
  obtain ⟨hD, hbudget, hkD, hheight⟩ :=
    uniformFirstOrder_parameters n k A hn hk hAn hgapNat
  have hkA : k ≤ A := by exact_mod_cast (show (k : ℝ) ≤ A by linarith)
  have hfin := closePolynomialSet_finite domain received hkA
  let list := hfin.toFinset
  have hlist : ∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received k A := by
    intro P
    exact hfin.mem_toFinset
  have hsolutions : ∀ P ∈ list, IsAgreementSolution domain received k A P := by
    intro P hP
    exact (mem_closePolynomialSet_iff_isAgreementSolution domain received P).mp
      (hfin.mem_toFinset.mp hP)
  have hcard := finite_firstOrder_list_bound_of_heightSlotCount_sharp
    (F := F) (by omega) hbudget hkD domain received hheight (by omega) (le_refl k)
      (hkA.trans hAn) (by omega) hkA hAn hchar list hsolutions
  refine ⟨list, hlist, ?_⟩
  exact_mod_cast hcard.trans (uniformFirstOrder_listRatio_le n k A hn hk hAn hgap)

/-- The complete close-polynomial set at gap `6/25` is represented by an exact finite list of
cardinality at most `13623 n`, including the constant-message edge case. -/
theorem exists_uniformFirstOrder_list
    {F : Type u} [Field F] [DecidableEq F]
    (n k A : ℕ) (domain : Fin n ↪ F) (received : Fin n → F)
    (hn : 2 ≤ n) (hk : 0 < k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A)
    (hchar : 2 ≤ k → ringChar F = 0 ∨ max (k - 1) 22 < ringChar F) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received k A) ∧
      list.card ≤ 13623 * n := by
  by_cases hkTwo : 2 ≤ k
  · exact exists_uniformFirstOrder_list_of_two_le n k A domain received
      hn hkTwo hAn hgap (hchar hkTwo)
  · have hkOne : k = 1 := by omega
    subst k
    have hOneA : 1 ≤ A := by exact_mod_cast (show (1 : ℝ) ≤ A by linarith)
    obtain ⟨list, hlist, hincidence⟩ :=
      exists_closePolynomial_finset_with_incidence_bound domain received hOneA
    refine ⟨list, hlist, ?_⟩
    norm_num at hincidence
    calc
      list.card ≤ list.card * A := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ n := hincidence
      _ ≤ 13623 * n := by omega

end ReedSolomon
