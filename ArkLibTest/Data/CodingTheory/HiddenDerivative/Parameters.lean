/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.ExactCharacteristicBudget
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FreeOrder
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RankRounding
import Mathlib.Data.ZMod.Basic

open PolynomialDifferential ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.InterpolationRounding

example :
    exactInterpolationJetDegreeFloorAt 3 2 2 (0 : Fin 2) ≤
      exactInterpolationJetDegreeFloor 3 2 1 2 :=
  exactInterpolationJetDegreeFloorAt_le (D := 3) (A := 2) (d := 1) (m := 2)
    (by norm_num) 0

/-- A nonzero monomial in the exact interpolation space has jet degree below the characteristic. -/
example :
    jetDegree
        (MvPolynomial.monomial (Finsupp.single (some (0 : Fin 1)) 1) (1 : ZMod 5)) 0 ≤ 1 ∧
      jetDegree
        (MvPolynomial.monomial (Finsupp.single (some (0 : Fin 1)) 1) (1 : ZMod 5)) 0 <
          ringChar (ZMod 5) := by
  let u : JetVariable 0 →₀ ℕ := Finsupp.single (some (0 : Fin 1)) 1
  let Q : DifferentialPolynomial (ZMod 5) 0 := MvPolynomial.monomial u 1
  have hQ : Q ∈ exactInterpolationSpace (ZMod 5) 1 1 0 2 1 0 (by omega) := by
    dsimp [Q]
    rw [monomial_mem_exactInterpolationSpace]
    left
    norm_num [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight,
      jetFirstWeight, jetHigherWeight, differentialWeight, Finsupp.weight, u]
  have hfloor : exactInterpolationJetDegreeFloor 1 1 0 2 < ringChar (ZMod 5) := by
    rw [ZMod.ringChar_zmod_n 5]
    norm_num [exactInterpolationJetDegreeFloor]
  have hcoord := jetDegree_le_exactInterpolationJetDegreeFloorAt_of_mem_exactInterpolationSpace
    Q hQ (0 : Fin 1)
  have hchar := jetDegree_lt_ringChar_of_mem_exactInterpolationSpace Q hQ hfloor (0 : Fin 1)
  constructor
  · simpa [Q, u, exactInterpolationJetDegreeFloorAt] using hcoord
  · exact hchar

/-- The free-order rectangular slack theorem at `ε = θ = 1/2`, `d = 1`, and `n = 8`. -/
example :
    interpolationBoxWidth (1 / 2) 1 ≤ ReedSolomon.HiddenDerivative.multiplicity 1 ∧
      higherJetDegreeBudget (1 / 2) 1 + 2 * interpolationBoxWidth (1 / 2) 1 ≤
        interpolationDegreeBudget 1 (1 / 2) (1 / 2) 8 ∧
      (ambientDimension (1 / 2) (1 / 2) 8 - 1) *
          (higherJetDegreeBudget (1 / 2) 1 + 3 * interpolationBoxWidth (1 / 2) 1) ≤
        ReedSolomon.HiddenDerivative.multiplicity 1 * agreementThreshold (1 / 2) 8 := by
  exact freeGlobalDimensionSlacks (ε := 1 / 2) (θ := 1 / 2) (d := 1) (n := 8)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [ambientDimension])

/-- The rounded-rank interval at `a = H = 1`, `d = 2`, and `m = 2`. -/
example :
    1 / 2 ≤ ((2 - 1 : ℕ) : ℝ) * 2 / Nat.floor ((1 : ℝ) * (2 : ℕ) * 2 / 1) ∧
      ((2 - 1 : ℕ) : ℝ) * 2 / Nat.floor ((1 : ℝ) * (2 : ℕ) * 2 / 1) ≤ 1 := by
  have h := kappa_interval 1 1 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  norm_num at h ⊢

/-- The prescribed multiplicity and rounded rank at `a = H = 1`, `d = 1000`. -/
example :
    ⌈100 * ((1000 : ℕ) : ℝ) ^ 2 * 1⌉₊ = 10 ^ 8 ∧
      ((1000 - 1 : ℕ) : ℝ) * ⌈100 * ((1000 : ℕ) : ℝ) ^ 2 * 1⌉₊ /
          ⌊(1 : ℝ) * (1000 : ℕ) * ⌈100 * ((1000 : ℕ) : ℝ) ^ 2 * 1⌉₊ / 1⌋₊ ≤ 1 / 1 := by
  obtain ⟨-, -, -, -, hhi, -⟩ := prescribed_kappa_bounds 1 1 1000 le_rfl one_pos le_rfl
  refine ⟨?_, hhi⟩
  rw [Nat.ceil_eq_iff (by norm_num)]
  norm_num
