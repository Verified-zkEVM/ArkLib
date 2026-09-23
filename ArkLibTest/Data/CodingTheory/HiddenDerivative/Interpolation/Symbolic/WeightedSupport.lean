/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedSupport

/-!
# Weighted-support symbolic interpolation acceptance tests

The exponent map has a coordinate inverse, and finite support enumeration stays inside the
eligible set. A concrete one-point instance has enough support dimension for the fixed-margin
theorem to produce a primitive interpolant satisfying order-one constraints. A zero-point case
checks constant coefficients, while height examples exercise the bound and its positive-height
hypothesis.
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

/-- The local constraint rank in the concrete order-one instance is at most two. -/
private theorem onePointLocalRank_le_two :
    Module.finrank ℚ (LinearMap.range
      (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
        Nat.one_pos 0 0)) ≤ 2 := by
  calc
    _ ≤ localResidualCoordinateBudget 1 1 0 ⌈(2 : ℝ) / 1⌉₊ := by
      simpa using (finrank_weightedSupportLocalConstraint_le (F := ℚ) (d := 1) (D := 1)
        (W := 0) (L := 2) (m := 1) (by norm_num) Nat.one_pos (0 : ℚ) 0)
    _ ≤ 2 := by
      norm_num [localResidualCoordinateBudget, contactThreshold, Finset.natWeightedSimplex]

/-- The small weighted support contains three distinct eligible exponents. -/
private theorem onePointSupportDimension_ge_three :
    3 ≤ Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 2 Nat.one_pos) := by
  rw [finrank_weightedSupportSpace_eq_card]
  have hzero : (0 : JetVariable 1 →₀ ℕ) ∈ weightedSupportExponents 1 1 0 2 Nat.one_pos := by
    simp [WeightedSupportEligible, fullHigherJetWeight, totalJetDegree]
  have hx : Finsupp.single none 1 ∈ weightedSupportExponents 1 1 0 2 Nat.one_pos := by
    simp [WeightedSupportEligible, fullHigherJetWeight, jetHigherWeight,
      totalJetDegree, jetDegreeWeight, Finsupp.weight_single]
  have hy : Finsupp.single (some 0) 1 ∈ weightedSupportExponents 1 1 0 2 Nat.one_pos := by
    simp [WeightedSupportEligible, fullHigherJetWeight, jetHigherWeight,
      totalJetDegree, jetDegreeWeight, Finsupp.weight_single]
  have hzeroX : (0 : JetVariable 1 →₀ ℕ) ≠ Finsupp.single none 1 := by
    intro h
    have he := congrArg (fun u : JetVariable 1 →₀ ℕ => u none) h
    simp only [Finsupp.zero_apply, Finsupp.single_apply] at he
    norm_num at he
  have hzeroY : (0 : JetVariable 1 →₀ ℕ) ≠ Finsupp.single (some 0) 1 := by
    intro h
    have he := congrArg (fun u : JetVariable 1 →₀ ℕ => u (some 0)) h
    simp only [Finsupp.zero_apply, Finsupp.single_apply] at he
    norm_num at he
  have hxy : (Finsupp.single none 1 : JetVariable 1 →₀ ℕ) ≠
      Finsupp.single (some 0) 1 := by
    intro h
    have := congrArg (fun u : JetVariable 1 →₀ ℕ => u none) h
    simp at this
  have hsubset :
      ({0, Finsupp.single none 1, Finsupp.single (some 0) 1} :
        Finset (JetVariable 1 →₀ ℕ)) ⊆
        weightedSupportExponents 1 1 0 2 Nat.one_pos := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact hzero
    · exact hx
    · exact hy
  calc
    3 = ({0, Finsupp.single none 1, Finsupp.single (some 0) 1} :
        Finset (JetVariable 1 →₀ ℕ)).card :=
      (Finset.card_triple_eq_three_iff.mpr ⟨hzeroX, hzeroY, hxy⟩).symm
    _ ≤ (weightedSupportExponents 1 1 0 2 Nat.one_pos).card := Finset.card_le_card hsubset

/-- The one-point received-line matrix has a concrete rank bound of two. -/
example :
    ((localConstraintMatrix 1 (fun _ : Fin 1 => Polynomial.C (0 : ℚ))
      (fun _ => receivedLine (0 : ℚ) 0)
      (weightedSupportColumns (d := 1) (W := 0) (L := 2) Nat.one_pos)).map
        (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤
      2 := by
  let centers : Fin 1 → ℚ := fun _ => 0
  let f : Fin 1 → ℚ := fun _ => 0
  let g : Fin 1 → ℚ := fun _ => 0
  calc
    _ ≤ 1 * Module.finrank ℚ (LinearMap.range
        (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
          Nat.one_pos 0 0)) := by
      exact receivedLine_matrix_rank_le_base_actual (F := ℚ) (d := 1) (D := 1) (W := 0)
        (L := 2) (m := 1) Nat.one_pos centers f g _
        (weightedSupportColumns_eligible (d := 1) (D := 1) (W := 0) (L := 2) Nat.one_pos)
    _ ≤ 2 := by simpa using onePointLocalRank_le_two

/-- One received point and order-one constraints yield a primitive interpolant of height below
twelve and coefficient-polynomial degree at most two. -/
example :
    let N := Fintype.card (↥(weightedSupportExponents 1 1 0 2 Nat.one_pos))
    let columns := weightedSupportColumns (d := 1) (W := 0) (L := 2) Nat.one_pos
    ∃ v : Fin N → ℚ[X],
      v ≠ 0 ∧
        localConstraintMatrix 1 (fun _ : Fin 1 => Polynomial.C (0 : ℚ))
          (fun _ => receivedLine (0 : ℚ) 0) columns *ᵥ v = 0 ∧
        (∀ j, (v j).natDegree ≤ 2) ∧
        (∀ j, ((v j).natDegree : ℝ) < 12) ∧
        Ideal.span (Set.range v) = ⊤ ∧
        (∀ {E : Type*} [Field E] (ι : ℚ →+* E) (z : E),
          MvPolynomial.map (Polynomial.eval₂RingHom ι z)
            (SourceColumn.interpolant columns v) ≠ 0) ∧
        SatisfiesLocalConstraints 1 (Polynomial.C (0 : ℚ)) (receivedLine (0 : ℚ) 0)
          (SourceColumn.interpolant columns v) := by
  dsimp only
  let columns := weightedSupportColumns (d := 1) (W := 0) (L := 2) Nat.one_pos
  let N := Fintype.card (↥(weightedSupportExponents 1 1 0 2 Nat.one_pos))
  have hy₀ : ∀ u, WeightedSupportEligible 1 1 0 2 u → u (some 0) ≤ 1 := by
    intro u hu
    have htotal : totalJetDegree u ≤ 1 :=
      totalJetDegree_le_pred_of_weightedSupportEligible (D := 1) (d := 1) (W := 0)
        (L := 2) (t := 2) Nat.one_pos (by norm_num) hu
    have hcoordinate : u (some 0) ≤ totalJetDegree u := by
      rw [totalJetDegree_eq_sum]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (u (some j))) (Finset.mem_univ 0)
    exact hcoordinate.trans htotal
  have hmargin : (543 / 500 : ℝ) * 1 *
      Module.finrank ℚ (LinearMap.range
        (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
          Nat.one_pos 0 0)) <
        Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 2 Nat.one_pos) := by
    have hrank := onePointLocalRank_le_two
    have hdimension := onePointSupportDimension_ge_three
    have hrankReal :
        (Module.finrank ℚ (LinearMap.range
          (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
            Nat.one_pos 0 0)) : ℝ) ≤ 2 := by
      exact_mod_cast hrank
    have hdimensionReal : (3 : ℝ) ≤
        Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 2 Nat.one_pos) := by
      exact_mod_cast hdimension
    have hmarginReal :
        (543 / 500 : ℝ) *
          (Module.finrank ℚ (LinearMap.range
            (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
              Nat.one_pos 0 0)) : ℝ) <
          Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 2 Nat.one_pos) := by
      calc
        _ ≤ (543 / 500 : ℝ) * 2 :=
          mul_le_mul_of_nonneg_left hrankReal (by norm_num)
        _ < 3 := by norm_num
        _ ≤ _ := hdimensionReal
    simpa using hmarginReal
  obtain ⟨v, hv, hkernel, hdegree, hheight, hprimitive, hnozero, hconstraints, _⟩ :=
    exists_symbolic_weightedSupport_interpolant_of_fixed_margin (F := ℚ) (d := 1) (D := 1)
      (W := 0) (L := 2) (m := 1) (n := 1) (ν := 1) Nat.one_pos Nat.one_pos
      (fun _ => 0) (fun _ => 0) (fun _ => 0) hy₀ (by simpa using hmargin)
  refine ⟨v, hv, hkernel, ?_, ?_, hprimitive, ⟨hnozero, hconstraints 0⟩⟩
  · intro j
    calc
      (v j).natDegree ≤
          1 * Module.finrank ℚ (LinearMap.range
            (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
              Nat.one_pos 0 0)) * 1 /
            (N - 1 * Module.finrank ℚ (LinearMap.range
              (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
                Nat.one_pos 0 0))) := by
        simpa [N] using hdegree j
      _ ≤ 1 * Module.finrank ℚ (LinearMap.range
          (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
            Nat.one_pos 0 0)) * 1 := Nat.div_le_self _ _
      _ ≤ 2 := by simpa using onePointLocalRank_le_two
  · intro j
    simpa using hheight j

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
  exact kernel_height_lt_twelve_mul_of_margin 1 0 1 Nat.one_pos hmargin

/-- With `ν = 0`, the strict height conclusion fails, showing why positivity is required. -/
example : ¬ (((0 * 0 / (1 - 0) : ℕ) : ℝ) < 12 * 0) := by norm_num
