/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Space

/-!
# Rectangular interpolation space acceptance tests

Counts of good higher-jet exponents, including the source statement at `C = W` and an exponent
removed by a degree cap `C < W`; the source-shaped comparison with the exact space at `K = D + 1`;
and an exponent showing that the comparison needs `D < K`.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- Source shape (`goodHigherExponents_self_eq_weighted_count`): at `C = W` the good exponents
are counted by the weighted simplex. -/
example (d W : ℕ) : (goodHigherExponents d W W).card = weightedHigherJetCount d W :=
  card_goodHigherExponents_of_le le_rfl

/-- For `d = 3`, `W = 2`, and any `C ≥ 2`: the exponents `1, Y₂, Y₂², Y₃`. -/
example : (goodHigherExponents 3 2 5).card = 4 := by
  rw [card_goodHigherExponents_of_le (by norm_num)]
  decide

/-- For `C < W` the degree cap removes exponents: `Y₂²` has weight `2 ≤ W` but degree `2 > C`. -/
example : higherJetWeight (Finsupp.single 0 2 : HigherJetExponent 3) = 2 ∧
    (Finsupp.single 0 2 : HigherJetExponent 3) ∉ goodHigherExponents 3 2 1 := by
  refine ⟨by simp [higherJetWeight, Finsupp.weight_single], ?_⟩
  rw [mem_goodHigherExponents, GoodHigherExponent, higherJetDegree, Finsupp.degree_single]
  omega

/-- `Y₁` has higher-jet weight `0` but derivative-order weight `1`. -/
example : fullHigherJetWeight (Finsupp.single (some 1 : JetVariable 1) 1) = 0 ∧
    fullDerivativeJetWeight (Finsupp.single (some 1 : JetVariable 1) 1) = 1 := by
  simp [fullHigherJetWeight, fullDerivativeJetWeight, Finsupp.weight_single, jetHigherWeight,
    jetDerivativeWeight]

/-- Source shape: at `K = D + 1` the rectangular space lies in the exact space. -/
example {F : Type*} [Field F] {d D m A B W C : ℕ} (hdD : d < D) :
    interpolationSpace F d m A (D + 1) B W C ≤ exactInterpolationSpace F D A d m m W hdD :=
  interpolationSpace_le_exactInterpolationSpace hdD (Nat.lt_succ_self D)

/-- Source shape of the dimension comparison. -/
example {F : Type*} [Field F] {d D m A B W C : ℕ} (hdD : d < D) :
    Module.finrank F (interpolationSpace F d m A (D + 1) B W C) ≤
      Module.finrank F (exactInterpolationSpace F D A d m m W hdD) :=
  finrank_interpolationSpace_le_exactInterpolationSpace F hdD (Nat.lt_succ_self D)

/-- The comparison needs `D < K`: at `d = 0`, `K = D = 1`, `m = A = 1`, the exponent `Y₀` is
globally eligible but has specialization weight `1 = m A`. -/
example : GlobalEligibleExponent 0 1 1 1 1 0 0 (Finsupp.single (some 0) 1) ∧
    ¬ExactInterpolationEligibleExponent 1 1 0 1 1 0 (Finsupp.single (some 0) 1) := by
  simp [GlobalEligibleExponent, ExactInterpolationEligibleExponent, firstJetExponent,
    totalJetDegree, fullHigherJetWeight, fullHigherJetDegree, Finsupp.weight_single,
    jetFirstWeight, jetDegreeWeight, jetHigherWeight, jetHigherDegreeWeight]
