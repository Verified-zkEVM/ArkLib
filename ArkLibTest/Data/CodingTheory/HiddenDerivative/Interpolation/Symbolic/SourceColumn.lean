/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.SourceColumn
import Mathlib.Data.ZMod.Basic

/-!
# Source column acceptance tests

The column `X² Y₀ Y₁³` at `d = 1` has total jet degree `4` and is the source monomial with those
exponents. For the distinct columns `Y₀` and `X`, the interpolant with coefficients `5, 7` has
coefficient `7` at `X`. With a repeated column the coefficients `1, -1` cancel, so injectivity is
needed. Reducing the coefficients `2, 3` modulo `2` leaves a nonzero interpolant.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

namespace SourceColumnTest

/-- The column `X² Y₀ Y₁³` at `d = 1`. -/
def c₀ : SourceColumn 1 := ⟨2, 1, ![3]⟩

/-- `X² Y₀ Y₁³` has total jet degree `1 + 3`. -/
example : totalJetDegree c₀.exponent = 4 := by
  simp [c₀]

/-- The monomial of `c₀` is the source monomial `X² Y₀ Y₁³`. -/
example : (c₀.polynomial : DifferentialPolynomial ℚ 1) = sourceMonomial 2 1 ![3] :=
  SourceColumn.polynomial_eq_sourceMonomial c₀

/-- The columns `Y₀` and `X` at `d = 1`. -/
def columns₀ : Fin 2 → SourceColumn 1 := ![⟨0, 1, ![0]⟩, ⟨1, 0, ![0]⟩]

/-- The two columns are distinct. -/
theorem columns₀_injective : Function.Injective columns₀ := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [columns₀]

/-- The coefficient of `5 Y₀ + 7 X` at `X` is `7`. -/
example : (SourceColumn.interpolant columns₀ ![(5 : ℚ), 7]).coeff (columns₀ 1).exponent = 7 :=
  SourceColumn.coeff_interpolant columns₀_injective _ 1

/-- Injectivity is needed: with the column `c₀` repeated, the coefficients `1, -1` cancel. -/
example : (SourceColumn.interpolant (fun _ : Fin 2 => c₀) ![(1 : ℚ), -1]).coeff c₀.exponent ≠
    (![(1 : ℚ), -1] : Fin 2 → ℚ) 0 := by
  simp [SourceColumn.interpolant, Fin.sum_univ_two]

/-- Reducing `2 Y₀ + 3 X` modulo `2` leaves the nonzero `X`. -/
example : MvPolynomial.map (Int.castRingHom (ZMod 2))
    (SourceColumn.interpolant columns₀ ![(2 : ℤ), 3]) ≠ 0 := by
  refine SourceColumn.map_interpolant_ne_zero columns₀_injective _ fun h => ?_
  have h1 : ((3 : ℤ) : ZMod 2) = 0 := by simpa using congrFun h 1
  exact absurd h1 (by decide)

end SourceColumnTest
