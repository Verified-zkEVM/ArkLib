/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.Certificate

/-!
# Symbolic interpolation acceptance tests

Concrete one-point instances exercise certificate construction, the curve rank bound, and
primitive interpolation under order-one local constraints.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped Polynomial Matrix

namespace SymbolicInterpolationTest

private def onePointEmbedding : Fin 1 ↪ ℚ where
  toFun := fun _ => 0
  inj' := by
    intro i j _
    exact Subsingleton.elim _ _

/-- The local constraint rank in the concrete order-one instance is at most two. -/
private theorem onePointLocalRank_le_two {F : Type*} [Field F] :
    Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := 1) (W := 0) (L := 2) 1
        Nat.one_pos 0 0)) ≤ 2 := by
  calc
    _ ≤ localResidualCoordinateBudget 1 1 0 ⌈(2 : ℝ) / 1⌉₊ := by
      simpa using (finrank_weightedSupportLocalConstraint_le (F := F) (d := 1) (D := 1)
        (W := 0) (L := 2) (m := 1) (by norm_num) Nat.one_pos (0 : F) 0)
    _ ≤ 2 := by
      norm_num [localResidualCoordinateBudget, contactThreshold, Finset.natWeightedSimplex]

/-- The weighted support contains three distinct eligible exponents. -/
private theorem onePointSupportDimension_ge_three {F : Type*} [Field F] :
    3 ≤ Module.finrank F (weightedSupportSpace F 1 1 0 2 Nat.one_pos) := by
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
    have he := congrArg (fun u : JetVariable 1 →₀ ℕ => u none) h
    simp at he
  have hsubset : ({0, Finsupp.single none 1, Finsupp.single (some 0) 1} :
      Finset (JetVariable 1 →₀ ℕ)) ⊆ weightedSupportExponents 1 1 0 2 Nat.one_pos := by
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

private theorem onePointStrictMargin {F : Type*} [Field F] :
    (543 / 500 : ℝ) * 1 * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := 1) (W := 0) (L := 2) 1
        Nat.one_pos 0 0)) < Module.finrank F (weightedSupportSpace F 1 1 0 2 Nat.one_pos) := by
  have hrank := onePointLocalRank_le_two (F := F)
  have hdimension := onePointSupportDimension_ge_three (F := F)
  have hrankReal : (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := 1) (W := 0) (L := 2) 1
        Nat.one_pos 0 0)) : ℝ) ≤ 2 := by
    exact_mod_cast hrank
  have hdimensionReal : (3 : ℝ) ≤
      Module.finrank F (weightedSupportSpace F 1 1 0 2 Nat.one_pos) := by
    exact_mod_cast hdimension
  calc
    _ ≤ (543 / 500 : ℝ) * 1 * 2 := by nlinarith [hrankReal]
    _ < 3 := by norm_num
    _ ≤ _ := hdimensionReal

/-- The fixed-margin construction produces a certificate at one received point. -/
example : Nonempty (WeightedSupportCertificate ℚ 2 1 1 1 11 onePointEmbedding
    (fun _ => 0) (fun _ => 0)) := by
  have hmargin := onePointStrictMargin (F := ℚ)
  exact exists_weightedSupport_certificate_of_fixed_margin (F := ℚ) (D := 1) (d := 1)
    (W := 0) (m := 1) (A := 2) (k := 1) (g₀ := 1) Nat.one_pos (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) onePointEmbedding
    (fun _ => 0) (fun _ => 0) (by
      have hcut : ((1 : ℕ) : ℝ) * (1 : ℕ) * (1 + (1 : ℝ)) = 2 := by norm_num
      convert hmargin using 1
      all_goals rw [hcut] <;> norm_num [Fintype.card_fin])

/-- The one-point received-line curve matrix has rank at most two. -/
example :
    ((localConstraintMatrix 1 (fun _ : Fin 1 => Polynomial.C (0 : ℚ))
      (fun _ => receivedLine (0 : ℚ) 0)
      (weightedSupportColumns (d := 1) (W := 0) (L := 2) Nat.one_pos)).map
        (algebraMap ℚ[X] (RatFunc ℚ))).rank ≤ 2 := by
  let centers : Fin 1 → ℚ := fun _ => 0
  let received : Fin 1 → ℚ[X] := fun _ => receivedLine 0 0
  let columns := weightedSupportColumns (d := 1) (W := 0) (L := 2) Nat.one_pos
  have hband := weightedSupportColumns_eligible (d := 1) (D := 1) (W := 0) (L := 2)
    Nat.one_pos
  calc
    _ ≤ Fintype.card (Fin 1) * Module.finrank ℚ (LinearMap.range
        (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
          Nat.one_pos 0 0)) := by
      exact localConstraintMatrix_rank_le_weightedSupport (F := ℚ) (d := 1) (D := 1)
        (W := 0) (L := 2) (m := 1) Nat.one_pos centers received columns hband
    _ ≤ 2 := by simpa using onePointLocalRank_le_two

/-- One received point admits a nonzero primitive interpolant satisfying its local constraints. -/
example :
    let N := Fintype.card (↥(weightedSupportExponents 1 1 0 2 Nat.one_pos))
    let centers : Fin 1 → ℚ := fun _ => 0
    let polynomialCenters : Fin 1 → ℚ[X] := fun i => Polynomial.C (centers i)
    let received : Fin 1 → ℚ[X] := fun _ => receivedLine 0 0
    let columns := weightedSupportColumns (d := 1) (W := 0) (L := 2) Nat.one_pos
    ∃ v : Fin N → ℚ[X], v ≠ 0 ∧
      localConstraintMatrix 1 polynomialCenters received columns *ᵥ v = 0 ∧
      Ideal.span (Set.range v) = ⊤ ∧
      SatisfiesLocalConstraints 1 (Polynomial.C (0 : ℚ)) (receivedLine 0 0)
        (SourceColumn.interpolant columns v) := by
  dsimp only
  let centers : Fin 1 → ℚ := fun _ => 0
  let polynomialCenters : Fin 1 → ℚ[X] := fun i => Polynomial.C (centers i)
  let received : Fin 1 → ℚ[X] := fun _ => receivedLine 0 0
  let columns := weightedSupportColumns (d := 1) (W := 0) (L := 2) Nat.one_pos
  let N := Fintype.card (↥(weightedSupportExponents 1 1 0 2 Nat.one_pos))
  have hband : ∀ j, WeightedSupportEligible 1 1 0 2 (columns j).exponent :=
    weightedSupportColumns_eligible (d := 1) (D := 1) (W := 0) (L := 2) Nat.one_pos
  have hcolumns : Function.Injective columns :=
    weightedSupportColumns_injective (d := 1) (D := 1) (W := 0) (L := 2) Nat.one_pos
  have hy₀ : ∀ j, (columns j).y₀ ≤ 1 := by
    intro j
    have hband' : WeightedSupportEligible 1 1 0
        (((1 : ℕ) : ℝ) * (1 : ℕ) * (1 + (1 : ℝ))) (columns j).exponent := by
      have hcut : ((1 : ℕ) : ℝ) * (1 : ℕ) * (1 + (1 : ℝ)) = 2 := by norm_num
      simpa only [hcut] using hband j
    have h := y₀_le_two_mul_sub_one_of_eligible (d := 1) (D := 1) (m := 1) (W := 0)
      (g := 1) Nat.one_pos (by norm_num) Nat.one_pos hband'
    simpa using h
  have hdim : 3 ≤ N := by
    have hdim' := onePointSupportDimension_ge_three (F := ℚ)
    rw [finrank_weightedSupportSpace_eq_card] at hdim'
    simpa [N, Fintype.card_coe] using hdim'
  have hmargin : Fintype.card (Fin 1) * Module.finrank ℚ (LinearMap.range
      (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
        Nat.one_pos 0 0)) < Fintype.card (Fin N) := by
    have hrank := onePointLocalRank_le_two (F := ℚ)
    have hlt : Module.finrank ℚ (LinearMap.range
        (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := 2) 1
          Nat.one_pos 0 0)) < N := by omega
    simpa [Fintype.card_fin] using hlt
  obtain ⟨v, hv, _, hspan, _, hconstraints⟩ :=
    exists_primitive_weightedSupport_interpolant.{0, 0, 0, 0}
      (F := ℚ) (d := 1) (D := 1) (W := 0)
      (L := 2) (m := 1) (ι := Fin 1) (κ := Fin N) Nat.one_pos 1 1 centers received
      (fun _ => natDegree_receivedLine_le 0 0) columns hcolumns hy₀ hband hmargin
  exact ⟨v, hv,
    (localConstraintMatrix_mulVec_eq_zero_iff 1 polynomialCenters received columns v).mpr
      hconstraints,
    hspan, hconstraints 0⟩

end SymbolicInterpolationTest
