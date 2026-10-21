/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.ExactCharacteristicBudget
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FreeOrder
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RankRounding
import Mathlib.Data.ZMod.Basic

/-!
# Hidden-derivative parameter acceptance tests

Concrete checks for characteristic budgets, free-order bounds, and rank rounding.
-/

open PolynomialDifferential ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.InterpolationRounding

example :
    exactInterpolationJetDegreeFloorAt 3 2 2 (0 : Fin 2) ≤
      exactInterpolationJetDegreeFloor 3 2 1 2 :=
  exactInterpolationJetDegreeFloorAt_le (D := 3) (A := 2) (d := 1) (m := 2)
    (by norm_num) 0

/-- A prescribed nonconstant interpolation monomial obeys both jet-degree bounds. -/
example :
    let u : JetVariable 0 →₀ ℕ := Finsupp.single (some (0 : Fin 1)) 1
    let i : ExactInterpolationIndex 1 1 0 2 1 0 (by omega) := ⟨u, by
      rw [mem_exactInterpolationExponents]
      norm_num [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight,
        jetFirstWeight, jetHigherWeight, differentialWeight, Finsupp.weight, u]
    ⟩
    let c : ExactInterpolationCoefficients (ZMod 5) 1 1 0 2 1 0 (by omega) :=
      Finsupp.single i 1
    jetDegree (exactInterpolationPolynomial (by omega) c : DifferentialPolynomial (ZMod 5) 0)
        (0 : Fin 1) ≤ exactInterpolationJetDegreeFloorAt 1 1 2 (0 : Fin 1) ∧
      jetDegree (exactInterpolationPolynomial (by omega) c : DifferentialPolynomial (ZMod 5) 0)
        (0 : Fin 1) < ringChar (ZMod 5) := by
  dsimp only
  constructor
  · exact jetDegree_exactInterpolationPolynomial_le_floorAt _ _
  · have hfloor : exactInterpolationJetDegreeFloor 1 1 0 2 < ringChar (ZMod 5) := by
      rw [ZMod.ringChar_zmod_n 5]
      norm_num [exactInterpolationJetDegreeFloor]
    exact jetDegree_exactInterpolationPolynomial_lt_ringChar _ hfloor _

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

/-- The free-order rectangular slack theorem at `ε = θ = 1/2`, `d = 4`, and `n = 64`. -/
example :
    interpolationBoxWidth (1 / 2) 4 ≤ ReedSolomon.HiddenDerivative.multiplicity 4 ∧
      higherJetDegreeBudget (1 / 2) 4 + 2 * interpolationBoxWidth (1 / 2) 4 ≤
        interpolationDegreeBudget 4 (1 / 2) (1 / 2) 64 ∧
      (ambientDimension (1 / 2) (1 / 2) 64 - 1) *
          (higherJetDegreeBudget (1 / 2) 4 + 3 * interpolationBoxWidth (1 / 2) 4) ≤
        ReedSolomon.HiddenDerivative.multiplicity 4 * agreementThreshold (1 / 2) 64 := by
  exact freeGlobalDimensionSlacks (ε := 1 / 2) (θ := 1 / 2) (d := 4) (n := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [ambientDimension])

/-- Concrete large-order thresholds at fixed positive free-order parameters. -/
example :
    (∃ D : ℕ, ∀ d : ℕ, D ≤ d → 1 ≤ (1 : ℝ) *
      (ReedSolomon.HiddenDerivative.multiplicity d : ℝ) / 16) ∧
    (∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      2 ≤ d ∧ 2 ≤ (1 / 2 : ℝ) *
        (ReedSolomon.HiddenDerivative.multiplicity d : ℝ) / 16 ∧
        1 < ((1 / 2 : ℝ) ^ 3 / 262144) * ((1 - 1 / 2) * (1 / 2) / 2) *
          (d : ℝ) ^ rankSavingExponent (1 / 2)) := by
  refine ⟨exists_orderThreshold_for_boxWidth (θ := 1) (c := 1) (by norm_num), ?_⟩
  exact exists_freeOrderElementaryThreshold (ε := 1 / 2) (θ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)

/-- A concrete threshold witness also yields the rounded-rate comparison at block length 12. -/
example :
    ∃ d : ℕ,
      1 < ((1 / 2 : ℝ) ^ 3 / 262144) * ((1 - 1 / 2) * (1 / 2) / 2) *
        (d : ℝ) ^ rankSavingExponent (1 / 2) ∧
      1 < ((1 / 2 : ℝ) ^ 3 / 262144) *
        (((ambientDimension (1 / 2) (1 / 2) 12 - 1 : ℕ) : ℝ) / 12) *
          (d : ℝ) ^ rankSavingExponent (1 / 2) := by
  obtain ⟨d₀, hd₀⟩ := exists_freeOrderRankThreshold (ε := 1 / 2) (θ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨d₀, hd₀ d₀ le_rfl, ?_⟩
  exact freeOrder_rank_comparison (ε := 1 / 2) (θ := 1 / 2) (d := d₀) (n := 12)
    (by norm_num) (by norm_num [ambientDimension]) (hd₀ d₀ le_rfl)

/-- At the same block length, the rounded rate is at least half the source rate. -/
example :
    (1 - (1 / 2 : ℝ)) * (1 / 2) / 2 ≤
      ((ambientDimension (1 / 2) (1 / 2) 12 - 1 : ℕ) : ℝ) / 12 := by
  exact half_rate_le_ambientDimension_sub_one_div (ε := 1 / 2) (θ := 1 / 2)
    (n := 12) (by norm_num [ambientDimension])

/-- The sharper floor interval and the order-normalized interval both hold at `a = H = 1`. -/
example :
    let R := (1 : ℝ) * 2 * 4 / 1
    let κ := ((2 - 1 : ℕ) : ℝ) * 4 / Nat.floor R
    1 / 2 ≤ κ ∧ κ ≤ (1 : ℝ) / 1 * (1 - 1 / 2) * (1 + 2 / R) ∧
      (1 - 1 / 2) * ((1 : ℝ) / 1) ≤ κ ∧ κ ≤ (1 : ℝ) / 1 := by
  have hfloor := kappa_floor_bounds 1 1 2 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hinterval := kappa_interval 1 1 2 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at hfloor hinterval ⊢

/-- Positive concrete multiplicity exercises the binomial, rank, and reciprocal error bounds. -/
example :
    (1 : ℝ) * (1 + (Nat.choose 2 2 : ℝ) / 4) ≤ 1 + 1 / (2 * 1) ∧
      (2 : ℝ) * 1 / 4 ≤ 1 / (1 * 2) ∧
      1 / (1 : ℝ) ^ 2 + 2 / (4 * 1) ≤ (1 + 1 / 2) / 1 ^ 2 * (1 / 1 ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using kappa_exponent_le 1 1 1 1 2 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · simpa using kappa_multiplicity_error_le 1 1 1 2 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · simpa using kappa_reciprocal_factor_le 1 1 2 4 1 (1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The prescribed multiplicity and rounded rank at `a = H = 1`, `d = 1000`. -/
example :
    ⌈100 * ((1000 : ℕ) : ℝ) ^ 2 * 1⌉₊ = 10 ^ 8 ∧
      ((1000 - 1 : ℕ) : ℝ) * ⌈100 * ((1000 : ℕ) : ℝ) ^ 2 * 1⌉₊ /
          ⌊(1 : ℝ) * (1000 : ℕ) * ⌈100 * ((1000 : ℕ) : ℝ) ^ 2 * 1⌉₊ / 1⌋₊ ≤
        1 / 1 := by
  obtain ⟨-, -, -, -, hhi, -⟩ := prescribed_kappa_bounds 1 1 1000 le_rfl one_pos le_rfl
  refine ⟨?_, hhi⟩
  rw [Nat.ceil_eq_iff (by norm_num)]
  norm_num
