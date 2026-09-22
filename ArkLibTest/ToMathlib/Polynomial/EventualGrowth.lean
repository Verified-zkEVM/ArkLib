/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.EventualGrowth

/-!
# Acceptance tests for polynomials compared on large natural numbers

The examples evaluate a backward difference and read off its top coefficient. Over `ZMod 4` that
coefficient vanishes for a nonzero step, and over `ZMod 2` the polynomials `X ^ 2` and `X` agree
at every natural number, so characteristic zero is needed in both places. The comparison lemma
needs the nonnegativity of the smaller polynomial. The source-shaped `ℚ` statements, including
the disjunction with `Q = 0`, are derived from the general ones.
-/

open Polynomial Filter

namespace EventualGrowthTest

/-- `X ^ 2 - (X - 3) ^ 2 = 6 X - 9`, which is `21` at `5`. -/
example : (backwardDifference (3 : ℤ) (X ^ 2)).eval 5 = 21 := by
  norm_num [eval_backwardDifference]

/-- The top coefficient of `X ^ 2 - (X - b) ^ 2` is `b * 2 * 1`. -/
example (b : ℤ) : (backwardDifference b (X ^ 2 : ℤ[X])).coeff 1 = b * 2 := by
  have h := coeff_backwardDifference_natDegree_sub_one b (X ^ 2 : ℤ[X])
  rw [natDegree_X_pow, leadingCoeff_X_pow] at h
  simpa using h

/-- In `natDegree_backwardDifference_eq_and_leadingCoeff`, a nonzero step and a nonconstant
polynomial do not suffice outside characteristic zero: over `ZMod 4`, `X ^ 2 - (X - 2) ^ 2` is
`4 X - 4 = 0`, because the top coefficient `2 * 2 * 1` vanishes. -/
example : backwardDifference (2 : ZMod 4) (X ^ 2) = 0 := by
  rw [backwardDifference, taylor_apply]
  simp only [pow_two, mul_comp, X_comp]
  have h1 : (C (-2) : (ZMod 4)[X]) + C (-2) = 0 := by
    rw [← C_add, show (-2 : ZMod 4) + -2 = 0 by decide, map_zero]
  have h2 : (C (-2) : (ZMod 4)[X]) * C (-2) = 0 := by
    rw [← C_mul, show (-2 : ZMod 4) * -2 = 0 by decide, map_zero]
  linear_combination (-X) * h1 - h2

/-- Characteristic zero is needed in `eq_of_eventually_eval_natCast_eq`: over `ZMod 2` the
polynomials `X ^ 2` and `X` agree at every natural number but are different. -/
example : (∀ N : ℕ, (X ^ 2 : (ZMod 2)[X]).eval (N : ZMod 2) = (X : (ZMod 2)[X]).eval (N : ZMod 2))
    ∧ (X ^ 2 : (ZMod 2)[X]) ≠ X := by
  have hsq : ∀ x : ZMod 2, x ^ 2 = x := by decide
  refine ⟨fun N ↦ by simp [hsq], fun h ↦ ?_⟩
  have := congrArg natDegree h
  rw [natDegree_X_pow, natDegree_X] at this
  exact absurd this (by norm_num)

/-- The source statement over `ℚ`: agreement on a tail of `ℕ` gives equality. -/
example {P Q : ℚ[X]} {N₀ : ℕ} (h : ∀ N ≥ N₀, P.eval (N : ℚ) = Q.eval (N : ℚ)) : P = Q :=
  eq_of_eventually_eval_natCast_eq h

/-- The nonnegativity hypothesis of `natDegree_le_of_eventually_eval_natCast_le` is needed:
`-X ^ 2` lies below `0` everywhere, yet has the larger natural degree. -/
example : (∀ x : ℚ, (-X ^ 2 : ℚ[X]).eval x ≤ (0 : ℚ[X]).eval x) ∧
    ¬(-X ^ 2 : ℚ[X]).natDegree ≤ (0 : ℚ[X]).natDegree := by
  refine ⟨fun x ↦ by simp [sq_nonneg], ?_⟩
  rw [natDegree_neg, natDegree_X_pow, natDegree_zero]
  norm_num

/-- The source's comparison statement over `ℚ`, which assumed `Q ≠ 0`. -/
example {Q R : ℚ[X]} (_hQ : Q ≠ 0) (hQnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ Q.eval (N : ℚ))
    (hle : ∀ᶠ N : ℕ in atTop, Q.eval (N : ℚ) ≤ R.eval (N : ℚ)) :
    Q.natDegree ≤ R.natDegree ∧
      (Q.natDegree = R.natDegree → Q.leadingCoeff ≤ R.leadingCoeff) :=
  natDegree_le_of_eventually_eval_natCast_le hQnonneg hle

/-- The source's degree statement for a backward difference with a positive natural step. -/
example {b : ℕ} (hb : 0 < b) {P : ℚ[X]} (hd : 0 < P.natDegree) :
    (backwardDifference (b : ℚ) P).natDegree = P.natDegree - 1 ∧
      (backwardDifference (b : ℚ) P).leadingCoeff = (b : ℚ) * P.natDegree * P.leadingCoeff :=
  natDegree_backwardDifference_eq_and_leadingCoeff_of_ne_zero (Nat.cast_ne_zero.mpr hb.ne') hd

/-- The polynomial half of the source's principal-cut statement, in its disjunctive form. -/
example {b : ℕ} {P Q : ℚ[X]} (hQ : ∀ᶠ N : ℕ in atTop, 0 ≤ Q.eval (N : ℚ))
    (hle : ∀ᶠ N : ℕ in atTop, Q.eval (N : ℚ) ≤ (backwardDifference (b : ℚ) P).eval (N : ℚ)) :
    Q = 0 ∨ Q.natDegree ≤ P.natDegree - 1 ∧
      Q.coeff (P.natDegree - 1) ≤ (b : ℚ) * P.natDegree * P.leadingCoeff :=
  Or.inr (natDegree_le_and_coeff_le_of_eventually_eval_natCast_le_backwardDifference hQ hle)

end EventualGrowthTest
