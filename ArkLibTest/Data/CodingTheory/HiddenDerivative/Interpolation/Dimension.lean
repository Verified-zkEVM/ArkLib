/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Dimension

/-!
# Interpolation dimension acceptance tests

Exact dimensions computed by `finrank_exactInterpolationSpace_eq_exactInterpolationDimensionCount`,
a case at `d = 0` where the count formula is wrong, the cardinality form of the dimension count,
the rectangular lower bound on the number of eligible exponents with one side length `H`, a
concrete lower bound, and a case at `d = 0` where the rectangular bound fails.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-! ### Coordinates -/

/-- The coordinates of `X² Y₀ Y₂³` for `d = 2`. -/
example : jetExponentCoordinatesEquiv (d := 2) (by norm_num)
    (Finsupp.single none 2 + Finsupp.single (some 0) 1 + Finsupp.single (some 2) 3) =
      (2, 1, 0, fun _ => 3) := by
  rw [jetExponentCoordinatesEquiv_apply]
  ext <;> simp

/-! ### The exact dimension -/

/-- `D = 2`, `A = 2`, `d = 1`, `m = 1`, `M = 1`, `W = 0`: the eligible monomials are `1`, `X`, and
`Y₁`, of specialization weights `0`, `1`, `1 < 2`. -/
example : Module.finrank ℚ (exactInterpolationSpace ℚ 2 2 1 1 1 0 (by norm_num)) = 3 := by
  rw [finrank_exactInterpolationSpace_eq_exactInterpolationDimensionCount ℚ (by norm_num)]
  decide

/-- `D = 3`, `A = 3`, `d = 2`, `m = 1`, `M = 1`, `W = 1`: the monomials `1, X, X², Y₁, Y₂, X Y₂`
of specialization weight below `3`. -/
example : Module.finrank ℚ (exactInterpolationSpace ℚ 3 3 2 1 1 1 (by norm_num)) = 6 := by
  rw [finrank_exactInterpolationSpace_eq_exactInterpolationDimensionCount ℚ (by norm_num)]
  decide

/-- For `0 < d < D` the number of eligible exact exponents is
`exactInterpolationDimensionCount D A d m M W`. -/
example {D A d m M W : ℕ} (hd : 0 < d) (hdD : d < D) :
    (exactInterpolationExponents D A d m M W hdD).card =
      exactInterpolationDimensionCount D A d m M W :=
  card_exactInterpolationExponents hd hdD

/-- At `d = 0`, `D = 1`, `m = A = 1`, `M = 1`, `W = 0` only the exponent `0` is eligible, since
`X` and `Y₀` both have specialization weight `1`. The count formula gives `2`, because it sums over
the `Y₁` exponents `b₁ ∈ {0, 1}` although `Y₁` does not exist: `card_exactInterpolationExponents`
needs `0 < d`. -/
example : (exactInterpolationExponents 1 1 0 1 1 0 (by norm_num)).card = 1 ∧
    exactInterpolationDimensionCount 1 1 0 1 1 0 = 2 := by
  refine ⟨?_, by decide⟩
  rw [Finset.card_eq_one]
  refine ⟨0, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun u hu => ?_⟩⟩
  · rw [mem_exactInterpolationExponents]
    simp [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight]
  · rw [mem_exactInterpolationExponents] at hu
    have hw := hu.2.2
    rw [weight_differentialWeight_eq, Fin.sum_univ_one] at hw
    ext v
    rcases v with _ | j
    · simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    · rw [Fin.fin_one_eq_zero j]
      simp only [Fin.val_zero, Nat.sub_zero, one_mul, Finsupp.coe_zero, Pi.zero_apply] at hw ⊢
      omega

/-! ### The rectangular lower bound -/

/-- The rectangular lower bound on the number of globally eligible exponents, with one side
length `H`. -/
example {d m A K B W C H : ℕ} (hd : 1 ≤ d) (hH : H ≤ m) (hdegree : C + 2 * H ≤ B)
    (hweighted : (K - 1) * (C + 3 * H) ≤ m * A) :
    (goodHigherExponents d W C).card * (K - 1) * H ^ 3 ≤
      (globalEligibleExponents d m A K B W C).card := by
  rw [← finrank_interpolationSpace_eq_card ℚ]
  exact finrank_interpolationSpace_lowerBound ℚ hd hH hdegree hweighted

/-- For `d = 2`, `W = C = 1` there are two good higher-jet exponents, `1` and `Y₂`. With `K = 3`,
`H = 2`, `m = 2`, `B = 5`, `A = 7`, the rectangular bound gives `2 * 2 * 2³ = 32`. -/
example : 32 ≤ Module.finrank ℚ (interpolationSpace ℚ 2 2 7 3 5 1 1) := by
  have h := finrank_interpolationSpace_lowerBound ℚ (d := 2) (m := 2) (A := 7) (K := 3) (B := 5)
    (W := 1) (C := 1) (H := 2) (by norm_num) le_rfl (by norm_num) (by norm_num)
  rw [card_goodHigherExponents_of_le le_rfl] at h
  exact le_of_eq_of_le (by decide) h

/-- Unequal sides: `N = 6` values of the `X` exponent with `H₀ = H₁ = 1`, at `d = 1`,
`m = 1`, `A = 6`, `K = 1`, `B = 2`, `W = C = 0`. -/
example : 6 ≤ Module.finrank ℚ (interpolationSpace ℚ 1 1 6 1 2 0 0) := by
  have h := le_finrank_interpolationSpace ℚ (d := 1) (m := 1) (A := 6) (K := 1) (B := 2) (W := 0)
    (C := 0) (N := 6) (H₀ := 1) (H₁ := 1) (by norm_num) le_rfl (by norm_num) (by norm_num)
  rw [card_goodHigherExponents_of_le le_rfl] at h
  exact le_of_eq_of_le (by decide) h

/-- At `d = 0` the rectangular bound fails. With `K = 2`, `H = 5`, `m = 5`, `A = 3`, `B = 10`,
`W = C = 0` the hypotheses `H ≤ m`, `C + 2H ≤ B`, `(K - 1)(C + 3H) ≤ m A` hold and the bound
would be `5³ = 125`, but the eligible exponents `X^x Y₀^b` have `b ≤ 10` and `x + b < 15`, and
there are only `110` of them. So `finrank_interpolationSpace_lowerBound` needs `0 < d`. -/
example : ¬ (goodHigherExponents 0 0 0).card * (2 - 1) * 5 ^ 3 ≤
    (globalEligibleExponents 0 5 3 2 10 0 0).card := by
  rw [card_goodHigherExponents_of_le le_rfl]
  have hcard : (globalEligibleExponents 0 5 3 2 10 0 0).card ≤
      ((Finset.range 15 ×ˢ Finset.range 11).filter fun p : ℕ × ℕ => p.1 + p.2 < 15).card := by
    refine Finset.card_le_card_of_injOn (fun u => (u none, u (some 0))) ?_ ?_
    · intro u hu
      rw [Finset.mem_coe, mem_globalEligibleExponents] at hu
      obtain ⟨-, htot, hx, -, -⟩ := hu
      rw [totalJetDegree_eq_sum, Fin.sum_univ_one] at htot hx
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq]
      omega
    · intro u _ v _ h
      simp only [Prod.mk.injEq] at h
      ext w
      rcases w with _ | j
      · exact h.1
      · rw [Fin.fin_one_eq_zero j]
        exact h.2
  have h110 : ((Finset.range 15 ×ˢ Finset.range 11).filter
      fun p : ℕ × ℕ => p.1 + p.2 < 15).card = 110 := by decide
  have hone : weightedHigherJetCount 0 0 = 1 := by decide
  omega
