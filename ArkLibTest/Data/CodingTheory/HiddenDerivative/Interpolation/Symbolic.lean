/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ChallengeDegree
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ConstraintMatrix
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveHeight
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.LocalRank
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.SourceColumn
import Mathlib.Data.ZMod.Basic

/-!
# Symbolic interpolation acceptance cases

Concrete coefficient-degree, matrix-entry, height-transfer, translation, and source-column cases.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped Polynomial

example : ((unscaledLocalSubstitution 0 (Polynomial.C (0 : ℚ)) Polynomial.X
    (SourceColumn.polynomial (R := ℚ[X]) ⟨0, 2, ![]⟩)).coeff 0).natDegree ≤ 2 := by
  simpa using SourceColumn.natDegree_coeff_unscaledLocalSubstitution_le 1 (0 : ℚ)
    (by compute_degree) (⟨0, 2, ![]⟩ : SourceColumn 0) 0

private noncomputable def matrixRowE : Fin 1 × LowContactIndex 0 1 :=
  (0, ⟨Finsupp.single (localE 0) 2, by simp [localContactOrder_eq, localT, localAux]⟩)

private def matrixColumnY : Fin 1 → SourceColumn 0 := fun _ => ⟨0, 1, ![]⟩

private def matrixRowZero : Fin 1 × LowContactIndex 0 1 :=
  (0, ⟨0, by simp [localContactOrder]⟩)

example :
    localConstraintMatrix 1 (fun _ : Fin 1 => (0 : ℚ)) (fun _ => 1)
        matrixColumnY matrixRowZero 0 =
      (localConstraintAt 1 0 1 (matrixColumnY 0).polynomial).coeff 0 :=
  localConstraintMatrix_apply_eq_localConstraintAt_coeff 1 (fun _ : Fin 1 => 0) (fun _ => 1)
    matrixColumnY matrixRowZero 0

example : localConstraintMatrix 1 (fun _ : Fin 1 => (0 : ℚ)) (fun _ => 0)
    matrixColumnY matrixRowE 0 = 0 :=
  localConstraintMatrix_eq_zero_of_lt 1 _ _ matrixColumnY matrixRowE 0
    (by simp [matrixColumnY, matrixRowE, Finsupp.weight_single, localJetDegreeWeight, localAux])

example :
    1 * (curveInterpolationHeight 3 4 + 1) <
      ∑ i ∈ ({0, 1} : Finset (Fin 2)),
        ![1, 2] i * (curveInterpolationHeight 3 4 + 1 - 3 * ![0, 2] i) :=
  curveInterpolationHeight_preserves_certificate _ ![1, 2] ![0, 2] 1 4 3 (by decide)

private theorem XMemWeightedSupport :
    (X none : DifferentialPolynomial ℚ 1) ∈ weightedSupportSpace ℚ 1 1 0 2 Nat.one_pos := by
  rw [mem_weightedSupportSpace_iff, support_X]
  intro u hu
  obtain rfl := Finset.mem_singleton.mp hu
  simp [WeightedSupportEligible, fullHigherJetWeight, totalJetDegree, Finsupp.weight_single,
    jetHigherWeight, jetDegreeWeight]

example :
    (weightedSupportPointTranslation (W := 0) (L := 2) Nat.one_pos (0 : ℚ) 0
        ⟨X none, XMemWeightedSupport⟩ : DifferentialPolynomial ℚ 1) = C 0 + X none := by
  simp

private def sourceColumns : Fin 2 → SourceColumn 1 := ![⟨0, 1, ![0]⟩, ⟨1, 0, ![0]⟩]

private theorem sourceColumnsInjective : Function.Injective sourceColumns := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [sourceColumns]

example :
    (SourceColumn.interpolant sourceColumns ![(5 : ℚ), 7]).coeff (sourceColumns 1).exponent = 7 :=
  SourceColumn.coeff_interpolant sourceColumnsInjective _ 1

example : MvPolynomial.map (Int.castRingHom (ZMod 2))
    (SourceColumn.interpolant sourceColumns ![(2 : ℤ), 3]) ≠ 0 := by
  refine SourceColumn.map_interpolant_ne_zero sourceColumnsInjective _ fun h => ?_
  have h1 : ((3 : ℤ) : ZMod 2) = 0 := by simpa using congrFun h 1
  exact absurd h1 (by decide)
