/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedSupport

/-!
# Weighted-support symbolic interpolation acceptance tests

The exponent map has a coordinate inverse, and finite support enumeration stays inside the
eligible set. A fixed margin with no received points gives a nonzero primitive coefficient vector;
when the local constraint order is zero, its coefficients are constant. The numeric height bound
holds at zero column count, and fails when the positive-height hypothesis is removed.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped Polynomial Matrix

/-- Every exponent vector is recovered by `SourceColumn.ofExponent`. -/
example (u : JetVariable 2 →₀ ℕ) : (SourceColumn.ofExponent u).exponent = u := by simp

/-- The enumerated columns are all eligible for a small weighted support. -/
example (j : Fin (Fintype.card
    (↥(weightedSupportExponents 1 1 0 2 Nat.one_pos)))) :
    WeightedSupportEligible 1 1 0 2
      (weightedSupportColumns (d := 1) (W := 0) (L := 2) Nat.one_pos j).exponent :=
  weightedSupportColumns_eligible (d := 1) (D := 1) (W := 0) (L := 2) Nat.one_pos j

/-- Under the cutoff `L = D * m * (1 + g)` with `g = 1`, the `Y₀` exponent is at most `1`. -/
example {u : JetVariable 1 →₀ ℕ}
    (hu : WeightedSupportEligible 1 1 0 2 u) : u (some 0) ≤ 1 := by
  have hu' : WeightedSupportEligible 1 1 0
      ((↑(1 : ℕ) : ℝ) * (↑(1 : ℕ) : ℝ) * (1 + (1 : ℝ))) u := by
    convert hu using 1
    norm_num
  exact y₀_le_two_mul_sub_one_of_eligible (d := 1) (D := 1) (m := 1) (W := 0) (g := 1)
    Nat.one_pos (by norm_num) Nat.one_pos hu'

/-- The full received-line matrix rank is bounded by the sum of the pointwise local ranks. -/
example (centers f g : Fin 1 → ℚ) :
    ((localConstraintMatrix 1 (fun i => Polynomial.C (centers i))
      (fun i => receivedLine (f i) (g i))
      (weightedSupportColumns (d := 1) (W := 0) (L := 2) Nat.one_pos)).map
        (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤
      1 * Module.finrank ℚ (LinearMap.range
        (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
          Nat.one_pos 0 0)) := by
  exact receivedLine_matrix_rank_le_base_actual (F := ℚ) (d := 1) (D := 1) (W := 0)
    (L := 2) (m := 1) Nat.one_pos centers f g _
    (weightedSupportColumns_eligible (d := 1) (D := 1) (W := 0) (L := 2) Nat.one_pos)

/-- At zero local order and with no points, the source-shaped specialization yields a primitive
interpolant with constant coefficient polynomials. -/
example :
    let N := Fintype.card (↥(weightedSupportExponents 1 1 0 2 Nat.one_pos))
    let columns := weightedSupportColumns (d := 1) (W := 0) (L := 2) Nat.one_pos
    ∃ v : Fin N → ℚ[X],
      v ≠ 0 ∧
        (∀ j, (v j).natDegree = 0) ∧
        Ideal.span (Set.range v) = ⊤ ∧
        (∀ {E : Type*} [Field E] (ι : ℚ →+* E) (z : E),
          MvPolynomial.map (Polynomial.eval₂RingHom ι z)
            (SourceColumn.interpolant columns v) ≠ 0) ∧
        ∀ i, SatisfiesLocalConstraints 0 (Polynomial.C (Fin.elim0 i))
          (receivedLine (Fin.elim0 i) (Fin.elim0 i)) (SourceColumn.interpolant columns v) := by
  have hzero : (0 : JetVariable 1 →₀ ℕ) ∈ weightedSupportExponents 1 1 0 2 Nat.one_pos := by
    simp [WeightedSupportEligible, fullHigherJetWeight, totalJetDegree]
  have hdim : 0 < Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 2 Nat.one_pos) := by
    rw [finrank_weightedSupportSpace_eq_card]
    exact Finset.card_pos.mpr ⟨0, hzero⟩
  have hzeroMap : weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 0
      Nat.one_pos (0 : ℚ) 0 = 0 := by
    ext Q e
    simp [weightedSupportLocalConstraint, localConstraintAt, projectLowContact]
  have hrank : Module.finrank ℚ (LinearMap.range
      (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 0
        Nat.one_pos 0 0)) = 0 := by
    rw [hzeroMap, LinearMap.range_zero]
    simp
  have hy₀ : ∀ u, WeightedSupportEligible 1 1 0 2 u → u (some 0) ≤ 1 := by
    intro u hu
    have hu' : WeightedSupportEligible 1 1 0
        ((↑(1 : ℕ) : ℝ) * (↑(1 : ℕ) : ℝ) * (1 + (1 : ℝ))) u := by
      convert hu using 1
      norm_num
    exact y₀_le_two_mul_sub_one_of_eligible (d := 1) (D := 1) (m := 1) (W := 0) (g := 1)
      Nat.one_pos (by norm_num) Nat.one_pos hu'
  exact exists_constant_interpolant_of_zero_rank (F := ℚ) (d := 1) (D := 1) (m := 0)
    (W := 0) (L := 2) (n := 0) (ν := 1) Nat.one_pos (by norm_num)
    Fin.elim0 Fin.elim0 Fin.elim0 hy₀ hrank hdim

/-- The height estimate holds at zero column count. -/
example : (((0 * 1 / (1 - 0) : ℕ) : ℝ) < 12 * (↑(1 : ℕ) : ℝ)) := by
  have hmargin : (543 / 500 : ℝ) * (0 : ℕ) < (1 : ℕ) := by norm_num
  exact noBand_kernel_height_lt 1 0 1 Nat.one_pos hmargin

/-- With `ν = 0`, the strict height conclusion fails, showing why positivity is required. -/
example : ¬ (((0 * 0 / (1 - 0) : ℕ) : ℝ) < 12 * 0) := by norm_num
