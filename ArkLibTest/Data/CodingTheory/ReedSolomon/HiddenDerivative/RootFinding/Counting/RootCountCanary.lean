/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.ExtensionRootCount
import Mathlib.Algebra.Field.ZMod
/-!
# Canaries for the differential root bound

The main canary uses `Y₀(Y₀-1)`: it has two visibly distinct constant solutions, so the capstone
cannot be exercised only on empty or singleton solution types.  A separate characteristic-two
calculation hits equality in the cubic extension's half-field estimate `2|F|² ≤ |F|³`.
-/

namespace ReedSolomon.HiddenDerivative.RootCountCanary

open PolynomialDifferential

noncomputable section

open Polynomial

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def binaryConstantEquation : DifferentialPolynomial (ZMod 5) 0 :=
  let Y := MvPolynomial.X (some (0 : Fin 1))
  Y * (Y - 1)

private def zeroSolution : BoundedSolution binaryConstantEquation 4 :=
  ⟨⟨0, by simp⟩, by simp [binaryConstantEquation, differentialSpecialization]⟩

private def oneSolution : BoundedSolution binaryConstantEquation 4 :=
  ⟨⟨1, Polynomial.mem_degreeLT.mpr (by simp)⟩,
    by simp [binaryConstantEquation, differentialSpecialization]⟩

private def binarySolutionEmbedding : Bool ↪ BoundedSolution binaryConstantEquation 4 where
  toFun flag := if flag then oneSolution else zeroSolution
  inj' := by
    intro left right heq
    cases left <;> cases right
    · rfl
    · exfalso
      have hcoeff := congrArg (fun solution ↦ solution.polynomial.coeff 0) heq
      change (0 : (ZMod 5)[X]).coeff 0 = (1 : (ZMod 5)[X]).coeff 0 at hcoeff
      norm_num at hcoeff
    · exfalso
      have hcoeff := congrArg (fun solution ↦ solution.polynomial.coeff 0) heq
      change (1 : (ZMod 5)[X]).coeff 0 = (0 : (ZMod 5)[X]).coeff 0 at hcoeff
      norm_num at hcoeff
    · rfl

private theorem binaryConstantEquation_ne_zero : binaryConstantEquation ≠ 0 := by
  let Y : DifferentialPolynomial (ZMod 5) 0 := MvPolynomial.X (some (0 : Fin 1))
  have hY : Y ≠ 0 := MvPolynomial.X_ne_zero _
  have hYsub : Y - 1 ≠ 0 := by
    intro hzero
    have heval := congrArg (MvPolynomial.eval fun _ ↦ (0 : ZMod 5)) hzero
    norm_num [Y] at heval
  exact mul_ne_zero hY hYsub

private theorem binaryConstantEquation_belowCharacteristic :
    IsBelowCharacteristic 4 binaryConstantEquation := by
  constructor
  · norm_num [ZMod.ringChar_zmod_n]
  · intro s
    fin_cases s
    let Y : DifferentialPolynomial (ZMod 5) 0 := MvPolynomial.X (some (0 : Fin 1))
    calc
      jetDegree binaryConstantEquation 0 = MvPolynomial.degreeOf (some 0) (Y * (Y - 1)) := rfl
      _ ≤ MvPolynomial.degreeOf (some 0) Y + MvPolynomial.degreeOf (some 0) (Y - 1) :=
        MvPolynomial.degreeOf_mul_le _ _ _
      _ ≤ 1 + 1 := by
        gcongr
        · simp [Y]
        · exact (MvPolynomial.degreeOf_sub_le _ _ _).trans (by simp [Y])
      _ < ringChar (ZMod 5) := by norm_num [ZMod.ringChar_zmod_n]

private theorem binaryConstantEquation_weightedDegree :
    differentialWeightedDegree 4 binaryConstantEquation ≤ Nat.card (ZMod 5) ^ 2 := by
  let Y : DifferentialPolynomial (ZMod 5) 0 := MvPolynomial.X (some (0 : Fin 1))
  have hY : Y.weightedTotalDegree (differentialWeight 4) = 4 := by
    rw [show Y = MvPolynomial.monomial (Finsupp.single (some 0) 1) 1 by
      simp [Y, ← MvPolynomial.C_mul_X_eq_monomial]]
    rw [MvPolynomial.weightedTotalDegree_monomial _ _ _ one_ne_zero]
    simp [Finsupp.weight, differentialWeight]
  have hYsub : (Y - 1).weightedTotalDegree (differentialWeight 4) ≤ 4 := by
    unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro exponent hexponent
    rcases Finset.mem_union.mp (MvPolynomial.support_sub _ Y 1 hexponent) with hYexp | hone
    · simp only [Y, MvPolynomial.support_X, Finset.mem_singleton] at hYexp
      rw [hYexp]
      simp [Finsupp.weight, differentialWeight]
    · simp only [MvPolynomial.support_one, Finset.mem_singleton] at hone
      rw [hone]
      simp [Finsupp.weight]
  calc
    differentialWeightedDegree 4 binaryConstantEquation =
        (Y * (Y - 1)).weightedTotalDegree (differentialWeight 4) := rfl
    _ ≤ Y.weightedTotalDegree (differentialWeight 4) +
        (Y - 1).weightedTotalDegree (differentialWeight 4) :=
      MvPolynomial.weightedTotalDegree_mul_le _ _ _
    _ ≤ 4 + 4 := by omega
    _ ≤ Nat.card (ZMod 5) ^ 2 := by norm_num [Nat.card_zmod]

/-- The concrete equation has at least two solutions and is bounded by the fixed-exponent
capstone.  The lower bound independently prevents the example from collapsing to an empty or
singleton solution family. -/
example : 2 ≤ Nat.card (BoundedSolution binaryConstantEquation 4) ∧
    Nat.card (BoundedSolution binaryConstantEquation 4) ≤ 50 := by
  constructor
  · simpa using Nat.card_le_card_of_injective binarySolutionEmbedding
      binarySolutionEmbedding.injective
  · have hbound := natCard_boundedSolution_le_extension_pow_of_weightedDegree
      (D := 4) binaryConstantEquation 3 25 (by norm_num)
      binaryConstantEquation_ne_zero binaryConstantEquation_belowCharacteristic
      (by simpa [Nat.card_zmod] using binaryConstantEquation_weightedDegree)
      (by norm_num [Nat.card_zmod])
    norm_num [Nat.card_zmod] at hbound ⊢
    exact hbound

private def terminalEquation : DifferentialPolynomial (ZMod 5) 0 :=
  MvPolynomial.X none

private theorem terminalEquation_isEmpty : IsEmpty (BoundedSolution terminalEquation 4) := by
  apply isEmpty_boundedSolution_of_highestActiveJet_eq_none terminalEquation
  · simp [terminalEquation]
  · rw [highestActiveJet_eq_none_iff]
    intro s
    fin_cases s
    rw [DependsOnJet, jetDegree, terminalEquation,
      MvPolynomial.degreeOf_X_of_ne (by simp)]
    simp

/-- The capstone includes the terminal recursion branch: a nonzero equation with no active jet
has no bounded roots and does not require a fabricated highest-active-jet witness. -/
example : Nat.card (BoundedSolution terminalEquation 4) = 0 ∧
    Nat.card (BoundedSolution terminalEquation 4) ≤ 50 := by
  constructor
  · let _ := Fintype.ofFinite (BoundedSolution terminalEquation 4)
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
    exact terminalEquation_isEmpty
  · have hbound := natCard_boundedSolution_le_extension_pow_of_weightedDegree
      (D := 4) terminalEquation 3 25 (by norm_num)
      (by simp [terminalEquation])
      (by
        constructor
        · norm_num [ZMod.ringChar_zmod_n]
        · intro s
          fin_cases s
          rw [jetDegree, terminalEquation, MvPolynomial.degreeOf_X_of_ne (by simp)]
          norm_num [ZMod.ringChar_zmod_n])
      (by
        rw [differentialWeightedDegree, terminalEquation]
        unfold MvPolynomial.weightedTotalDegree
        rw [MvPolynomial.support_X]
        norm_num [Finsupp.weight, differentialWeight, Nat.card_zmod])
      (by norm_num [Nat.card_zmod])
    norm_num [Nat.card_zmod] at hbound ⊢
    exact hbound

/-- Over the two-element field, the half-field inequality used by the cubic extension is exact. -/
example : 2 * Nat.card (ZMod 2) ^ 2 = Nat.card (ZMod 2) ^ 3 := by
  norm_num [Nat.card_zmod]

end
end ReedSolomon.HiddenDerivative.RootCountCanary
