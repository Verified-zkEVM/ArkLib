/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.UniformRate
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.PairwiseJohnson
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.MathematicalUniform

/-!
# Mathematical uniform Reed–Solomon list bounds near capacity

For a capacity gap `0 < δ < 6/25`, the mathematical uniform recipe takes

* `d = ⌈exp (3/(2δ))⌉₊`, the derivative order;
* `m = ⌈300 d² log(6d)⌉₊`, the interpolation multiplicity;
* `ν = ⌈m/δ²⌉₊ - 1`, the jet cap; and
* `max (ν + 1) ⌈4ν/δ²⌉₊`, the length threshold.

For distinct evaluation points and any received word, the complete list of degree-`< k`
polynomials agreeing in at least `A ≥ k + δ n` positions is finite and has at most `C n^d`
members, where `C = max (ν² (2ν/δ)^d) (4/(3δ))`. The field may be infinite, and its
characteristic need only be zero or exceed `k - 1`: when it does not also exceed `ν`, the message
dimension is at most `ν` and the pairwise Johnson bound gives at most `4/(3δ)` members.

## Main statements

* `ReedSolomon.mathematicalUniformRatePartition_close_list_bound`: the bound `ν² (2ν/δ)^d n^d`
  when the characteristic is zero or exceeds `max (k - 1) ν`.
* `ReedSolomon.mathematicalUniformListConstant`: the coefficient `C`.
* `ReedSolomon.mathematicalUniform_capacity_list_bound`: the bound `C n^d` when the
  characteristic is zero or exceeds `k - 1`.

## References

* [DKTZ26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open HiddenDerivative HiddenDerivative.RatePartition

universe u

open Classical in
/-- **Mathematical uniform list bound.** For `0 < δ < 6/25`, length at least
`uniformMathematicalLength δ`, `0 < k` and `k + δ n ≤ A ≤ n`, the complete list of degree-`< k`
polynomials agreeing with the received word on at least `A` points is finite and has at most
`ν² (2ν/δ)^d n^d` members, where `ν` is the mathematical jet cap and `d` the uniform derivative
order. The characteristic must be zero or exceed `max (k - 1) ν`. -/
theorem mathematicalUniformRatePartition_close_list_bound {F : Type u} [Field F]
    {δ : ℝ} {n k A : ℕ} (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformMathematicalLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ max (k - 1) (uniformMathematicalJetBound δ) < ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (uniformMathematicalJetBound δ : ℝ) ^ 2 *
          (2 * uniformMathematicalJetBound δ / δ) ^ uniformDerivativeOrder δ *
          n ^ uniformDerivativeOrder δ := by
  classical
  obtain ⟨e⟩ := exists_mathematicalRatePartitionEnvelope hδ hδsmall hn hk hgap hAn
  have hd := uniformDerivativeOrder_ge_519 hδ hδsmall
  have hδone : δ < 1 := by linarith
  have hm : 0 < uniformMathematicalMultiplicity δ :=
    lt_of_lt_of_le (by omega) (add_two_le_closedMultiplicity (by norm_num)
      (by omega : 1 ≤ uniformDerivativeOrder δ))
  obtain ⟨_, _, hν, _⟩ := uniformMathematical_integer_guards hδ hδone hm hn
  have hscale : (1 : ℝ) < 300 * (uniformDerivativeOrder δ : ℝ) ^ 3 := by
    have hd' : (519 : ℝ) ≤ uniformDerivativeOrder δ := by exact_mod_cast hd
    nlinarith [sq_nonneg (uniformDerivativeOrder δ : ℝ)]
  obtain ⟨cert⟩ := e.exists_curve_certificate (scale := 300) hδ hδone (by omega) hscale hAn
    domain (fun i ↦ Polynomial.C (received i)) (fun _ ↦ by simp)
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := by nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg n)]
    exact_mod_cast h
  let K := max k (uniformDerivativeOrder δ + 1)
  have hKn : K ≤ n := max_le (hkA.trans hAn) (by have := e.order_le; have := e.ambient_le; omega)
  have hdν := uniformDerivativeOrder_le_mathematicalJetBound hδ hδsmall
  have hchar' : ringChar F = 0 ∨ max (K - 1) (uniformMathematicalJetBound δ) < ringChar F := by
    refine hchar.imp_right fun hc ↦ ?_
    have hkchar := (Nat.le_max_left _ _).trans_lt hc
    have hνchar := (Nat.le_max_right _ _).trans_lt hc
    dsimp only [K]
    omega
  exact close_list_bound_of_curve_certificate_of_jetCharacteristic domain received cert hk
    (Nat.le_max_left _ _) (Nat.lt_succ_self _ |>.trans_le (Nat.le_max_right _ _)) hKn hkA hAn
    hν hδ hgap hchar'

/-- The list coefficient `max (ν² (2ν/δ)^d) (4/(3δ))`, where `ν` is the mathematical jet cap and
`d` the uniform derivative order at gap `δ`, and `4/(3δ)` is the pairwise Johnson bound. -/
def mathematicalUniformListConstant (δ : ℝ) : ℝ :=
  max
    ((uniformMathematicalJetBound δ : ℝ) ^ 2 *
      (2 * uniformMathematicalJetBound δ / δ) ^ uniformDerivativeOrder δ)
    (4 / (3 * δ))

open Classical in
/-- **Mathematical uniform capacity list bound.** For `0 < δ < 6/25`, length at least
`uniformMathematicalCapacityLength δ`, `0 < k` and `k + δ n ≤ A ≤ n`, the complete list of
degree-`< k` polynomials agreeing with the received word on at least `A` points is finite and has
at most `mathematicalUniformListConstant δ * n^d` members, where `d` is the uniform derivative
order. The field may be infinite; its characteristic must be zero or exceed `k - 1`. -/
theorem mathematicalUniform_capacity_list_bound
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (n k A : ℕ) (hn : uniformMathematicalCapacityLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n)
    {F : Type*} [Field F] (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ k - 1 < ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        mathematicalUniformListConstant δ * n ^ uniformDerivativeOrder δ := by
  have hnBase : uniformMathematicalLength δ ≤ n := (le_max_left _ _).trans hn
  have hnJohnson : ⌈(4 : ℝ) * uniformMathematicalJetBound δ / δ ^ 2⌉₊ ≤ n :=
    (le_max_right _ _).trans hn
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ uniformDerivativeOrder δ := by
    have hkA : (k : ℝ) ≤ A := hgap.trans' (le_add_of_nonneg_right (by positivity))
    have hkn : k ≤ n := by exact_mod_cast hkA.trans (by exact_mod_cast hAn : (A : ℝ) ≤ n)
    exact one_le_pow₀ (by exact_mod_cast hk.trans_le hkn)
  by_cases hsupport :
      ringChar F = 0 ∨ max (k - 1) (uniformMathematicalJetBound δ) < ringChar F
  · obtain ⟨hfinite, hcard⟩ := mathematicalUniformRatePartition_close_list_bound
      hδ hδsmall hnBase hk hgap hAn domain received hsupport
    exact ⟨hfinite, hcard.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩
  · have hdegreeChar := hchar.resolve_left fun hzero ↦ hsupport (Or.inl hzero)
    have hkJet : k ≤ uniformMathematicalJetBound δ := by
      by_contra hjet
      exact hsupport (Or.inr (max_lt hdegreeChar (by omega)))
    have hscale : 4 * ((k : ℝ) - 1) ≤ δ ^ 2 * n := by
      have hjet : (4 : ℝ) * uniformMathematicalJetBound δ / δ ^ 2 ≤ n :=
        (Nat.le_ceil _).trans (by exact_mod_cast hnJohnson)
      have hkJetR : (k : ℝ) ≤ uniformMathematicalJetBound δ := by exact_mod_cast hkJet
      have := (div_le_iff₀ (sq_pos_of_pos hδ)).mp hjet
      nlinarith
    obtain ⟨hfinite, hcard⟩ := closePolynomialSet_finite_and_ncard_le_pairwiseJohnson_of_gap
      domain received hδ hk hscale hgap
    refine ⟨hfinite, hcard.trans ?_⟩
    calc
      4 / (3 * δ) ≤ mathematicalUniformListConstant δ := le_max_right _ _
      _ ≤ mathematicalUniformListConstant δ * n ^ uniformDerivativeOrder δ :=
        le_mul_of_one_le_right ((by positivity : (0 : ℝ) ≤ 4 / (3 * δ)).trans
          (le_max_right _ _)) hpow

end ReedSolomon
