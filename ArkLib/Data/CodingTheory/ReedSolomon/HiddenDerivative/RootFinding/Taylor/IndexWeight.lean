/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Support
public import ArkLib.ToMathlib.MvPolynomial.SupportWeightOffset

/-!
# Coefficient-index weight in a Taylor residual

In the `j`th universal Hasse jet, a coefficient `c_l` occurs with Taylor exponent `l-j`.
Thus its index `l` exceeds its Taylor order by exactly `j`. Multiplying jets adds these
excesses. For a first-order equation, the excess of a source monomial is precisely its
degree in the derivative variable. This is the additional support bound that keeps that
degree separate in the rational Taylor lift.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [CommSemiring F]

/-- The coefficient index of a monomial in the `j`th jet is its Taylor order plus `j`. -/
theorem universalTaylorJet_indexWeight (K j : ℕ) :
    SupportWeightOffset
      (Finsupp.weight (fun i : Option (Fin K) ↦ i.elim 0 Fin.val))
      (Finsupp.applyAddHom none) j (universalTaylorJet (F := F) K j) := by
  classical
  apply SupportWeightOffset.sum
  intro l hl
  apply SupportWeightOffset.monomial
  have hj := (Finset.mem_filter.mp hl).2
  simp only [map_add, Finsupp.weight_single, one_smul, Option.elim_some,
    Option.elim_none, smul_zero, add_zero, Finsupp.applyAddHom_apply,
    Finsupp.single_apply, Option.some_ne_none, ↓reduceIte, zero_add]
  omega

/-- Substitution charges each source jet its index, rather than charging all jets equally. -/
theorem universalTaylorResidual_indexWeight {r : ℕ} (K : ℕ) (center : F)
    (Q : MvPolynomial (Option (Fin (r + 1))) F) :
    SupportWeightOffset
      (Finsupp.weight (fun i : Option (Fin K) ↦ i.elim 0 Fin.val))
      (Finsupp.applyAddHom none)
      (Q.weightedTotalDegree (fun i ↦ i.elim 0 Fin.val))
      (universalTaylorResidual K center Q) := by
  apply supportWeightOffset_aeval
  intro i
  cases i with
  | none =>
    apply SupportWeightOffset.add
    · exact SupportWeightOffset.C center
    · apply SupportWeightOffset.monomial
      simp [Finsupp.weight_single]
  | some j => exact universalTaylorJet_indexWeight K j.val

/-- A monomial in residual coefficient `h` has coefficient-index weight at most `h` plus
the source jet-index degree. In order one, the latter is the derivative-variable degree. -/
theorem indexWeight_le_of_mem_universalTaylorResidual_coeff {r : ℕ}
    (K : ℕ) (center : F) (Q : MvPolynomial (Option (Fin (r + 1))) F)
    (h : ℕ) (m : Fin K →₀ ℕ)
    (hm : m ∈ ((optionEquivLeft F (Fin K)
      (universalTaylorResidual K center Q)).coeff h).support) :
    Finsupp.weight Fin.val m ≤ h + Q.weightedTotalDegree (fun i ↦ i.elim 0 Fin.val) := by
  have hbound := universalTaylorResidual_indexWeight K center Q (m.optionElim h)
    ((mem_support_coeff_optionEquivLeft F).mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_option_index] at hbound
  · simpa [Finsupp.weight_apply] using hbound
  · intro i
    simp
  · intro i c d
    exact add_smul c d _

/-- For two jets, index weight is exactly degree in the first derivative. -/
theorem firstOrder_jetIndexDegree (Q : MvPolynomial (Option (Fin 2)) F) :
    Q.weightedTotalDegree (fun i ↦ i.elim 0 Fin.val) = Q.degreeOf (some 1) := by
  have hw : (fun i : Option (Fin 2) ↦ i.elim 0 Fin.val) = Pi.single (some 1) 1 := by
    funext i
    cases i with
    | none => simp
    | some j => fin_cases j <;> simp
  rw [hw, weightedTotalDegree_piSingle]

end

end ReedSolomon.HiddenDerivative
