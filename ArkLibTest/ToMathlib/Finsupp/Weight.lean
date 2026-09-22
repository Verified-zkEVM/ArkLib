/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Finsupp.Weight
import Mathlib.Algebra.BigOperators.Fin

/-!
# Weight comparison acceptance tests

* For the weight `(2, 3)` and the exponent `(4, 1)` of weight `11`, the term of the first variable
  is `8 ≤ 11` and the term of the second is `3 ≤ 11`.
* The bound is attained by an exponent supported on one variable.
-/

/-- Both single-variable terms of the exponent `(4, 1)` are at most its weight `11`. -/
example : (Finsupp.equivFunOnFinite.symm ![4, 1] : Fin 2 →₀ ℕ) 0 • (![2, 3] : Fin 2 → ℕ) 0 ≤
      (Finsupp.equivFunOnFinite.symm ![4, 1]).weight ![2, 3] ∧
    (Finsupp.equivFunOnFinite.symm ![4, 1] : Fin 2 →₀ ℕ) 1 • (![2, 3] : Fin 2 → ℕ) 1 ≤
      (Finsupp.equivFunOnFinite.symm ![4, 1]).weight ![2, 3] :=
  ⟨Finsupp.apply_smul_le_weight _ _ 0, Finsupp.apply_smul_le_weight _ _ 1⟩

/-- The weight `(4, 1)` against `(2, 3)` is `11`, so the two terms are `8` and `3`. -/
example : (Finsupp.equivFunOnFinite.symm ![4, 1] : Fin 2 →₀ ℕ).weight ![2, 3] = 11 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_two]

/-- For an exponent supported on one variable the bound is an equality. -/
example : (Finsupp.single (0 : Fin 2) 4).weight ![2, 3] =
    (Finsupp.single (0 : Fin 2) 4) 0 • (![2, 3] : Fin 2 → ℕ) 0 := by
  simp [Finsupp.weight_single]
