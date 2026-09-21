/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.WeightedDegree

/-!
# Weighted-degree acceptance tests

These examples distinguish supplied nonuniform weights from total degree and exercise a
nonuniform substitution with unequal exponents.
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
