/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.WeightedDegree

/-!
# Weighted-degree acceptance tests

These examples distinguish supplied nonuniform weights from total degree and exercise a
nonuniform substitution with unequal exponents. The partial-derivative examples check that the
saving is the differentiated variable's weight, including weight zero, and the univariate
substitution example uses a zero-weight constant substitution.
-/

open MvPolynomial

example :
    let w : Fin 2 → ℕ := ![1, 2]
    (X 0 ^ 2 + X 1 : MvPolynomial (Fin 2) ℤ) ∈ restrictWeightedDegree w 2 ∧
      (X 1 ^ 2 : MvPolynomial (Fin 2) ℤ) ∉ restrictWeightedDegree w 2 := by
  dsimp
  constructor
  · apply (restrictWeightedDegree (R := ℤ) ![1, 2] 2).add_mem
    · simpa using pow_mem_restrictWeightedDegree
        (X_mem_restrictWeightedDegree (R := ℤ) ![1, 2] 1 0 (by decide)) 2
    · exact X_mem_restrictWeightedDegree ![1, 2] 2 1 (by decide)
  · rw [X_pow_eq_monomial, monomial_mem_restrictWeightedDegree]
    norm_num [Finsupp.weight_single]

example :
    let v : Bool → ℕ := fun b => bif b then 5 else 2
    let f : Bool → MvPolynomial Bool ℕ := fun b =>
      bif b then X true ^ 2 else X false ^ 3
    let p : MvPolynomial Bool ℕ := X false * X true
    weightedTotalDegree v (bind₁ f p) = 16 ∧
      ¬weightedTotalDegree v (bind₁ f p) ≤ 15 := by
  dsimp only
  have hbind :
      bind₁ (fun b : Bool => bif b then X true ^ 2 else X false ^ 3)
          (X false * X true : MvPolynomial Bool ℕ) =
        monomial (Finsupp.single false 3 + Finsupp.single true 2) 1 := by
    simp [X_pow_eq_monomial]
  constructor <;>
    rw [hbind, weightedTotalDegree_monomial _ _ _ one_ne_zero, map_add,
      Finsupp.weight_single, Finsupp.weight_single] <;>
    norm_num

/-- Differentiating in a weight-two variable saves exactly two: `∂₁(X₀X₁²) = 2X₀X₁` has weight
`1 + 2 = 3 = 5 - 2` for weights `![1, 2]`. -/
example :
    let w : Fin 2 → ℕ := ![1, 2]
    let p : MvPolynomial (Fin 2) ℚ := monomial (Finsupp.single 0 1 + Finsupp.single 1 2) 1
    weightedTotalDegree w p = 5 ∧ weightedTotalDegree w (pderiv 1 p) = 3 ∧
      weightedTotalDegree w (pderiv 1 p) ≤ weightedTotalDegree w p - w 1 := by
  dsimp only
  refine ⟨?_, ?_, weightedTotalDegree_pderiv_le_sub _ 1 _⟩
  · rw [weightedTotalDegree_monomial _ _ _ one_ne_zero, map_add, Finsupp.weight_single,
      Finsupp.weight_single]
    norm_num
  · have hexp : Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 2 - Finsupp.single 1 1 =
        Finsupp.single 0 1 + Finsupp.single 1 1 := by
      ext j
      fin_cases j <;> simp
    rw [pderiv_monomial, hexp, weightedTotalDegree_monomial _ _ _ (by norm_num), map_add,
      Finsupp.weight_single, Finsupp.weight_single]
    norm_num

/-- Differentiating in a weight-zero variable saves nothing: for weights `![0, 1]`,
`∂₀(X₀²X₁) = 2X₀X₁` keeps weighted total degree `1`. -/
example :
    let w : Fin 2 → ℕ := ![0, 1]
    let p : MvPolynomial (Fin 2) ℚ := monomial (Finsupp.single 0 2 + Finsupp.single 1 1) 1
    weightedTotalDegree w (pderiv 0 p) = weightedTotalDegree w p - w 0 ∧
      weightedTotalDegree w p = 1 := by
  dsimp only
  have hp : weightedTotalDegree ![0, 1]
      (monomial (Finsupp.single 0 2 + Finsupp.single 1 1) (1 : ℚ)) = 1 := by
    rw [weightedTotalDegree_monomial _ _ _ one_ne_zero, map_add, Finsupp.weight_single,
      Finsupp.weight_single]
    norm_num
  have hexp : Finsupp.single (0 : Fin 2) 2 + Finsupp.single 1 1 - Finsupp.single 0 1 =
      Finsupp.single 0 1 + Finsupp.single 1 1 := by
    ext j
    fin_cases j <;> simp
  refine ⟨?_, hp⟩
  rw [hp, pderiv_monomial, hexp, weightedTotalDegree_monomial _ _ _ (by norm_num), map_add,
    Finsupp.weight_single, Finsupp.weight_single]
  norm_num

/-- Substituting the constant `3` (weight `0`) and `Y²` (weight `2`) into `X₀⁵X₁`: the univariate
degree is bounded by the weighted total degree `2`, far below the total degree `6`, and the bound
is attained. -/
example :
    let f : Fin 2 → Polynomial ℚ := ![Polynomial.C 3, Polynomial.X ^ 2]
    let p : MvPolynomial (Fin 2) ℚ := X 0 ^ 5 * X 1
    (aeval f p).natDegree ≤ 2 ∧ (aeval f p).natDegree = 2 ∧ p.totalDegree = 6 := by
  dsimp only
  have heval : aeval ![Polynomial.C (3 : ℚ), Polynomial.X ^ 2] (X 0 ^ 5 * X 1 :
      MvPolynomial (Fin 2) ℚ) = Polynomial.C 243 * Polynomial.X ^ 2 := by
    simp only [map_mul, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← Polynomial.C_pow]
    norm_num
  have hmon : (X 0 ^ 5 * X 1 : MvPolynomial (Fin 2) ℚ) =
      monomial (Finsupp.single 0 5 + Finsupp.single 1 1) 1 := by
    rw [X_pow_eq_monomial, X, monomial_mul_monomial, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · refine (natDegree_aeval_le_weightedTotalDegree_of_le ![0, 2] _ _ fun i => ?_).trans ?_
    · fin_cases i
      · simp
      · simp
    · rw [hmon, weightedTotalDegree_monomial _ _ _ one_ne_zero, map_add, Finsupp.weight_single,
        Finsupp.weight_single]
      norm_num
  · rw [heval, Polynomial.natDegree_C_mul_X_pow 2 243 (by norm_num)]
  · rw [← weightedTotalDegree_one, hmon, weightedTotalDegree_monomial _ _ _ one_ne_zero, map_add,
      Finsupp.weight_single, Finsupp.weight_single]
    norm_num
