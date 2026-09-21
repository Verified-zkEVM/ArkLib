/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.ClearedSubstitution
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for cleared substitutions

For `Q = X 0 ^ 2` over `ℚ`, common denominator `S = 3`, numerator `N = 5`, and denominator
exponent `d = 1`, the cleared numerator with budget `H = 3` is `5 ^ 2 * 3 = 75`, which is
`3 ^ 3 * (5 / 3) ^ 2`. With budget `H = 1`, below the weight `2` of the monomial, the numerator is
`25`, while `3 ^ 1 * (5 / 3) ^ 2 = 25 / 3`; so the budget hypothesis of
`MvPolynomial.map_clearedSubstitution` cannot be dropped.
-/

open MvPolynomial

/-- The test polynomial `X 0 ^ 2` in one variable. -/
private noncomputable abbrev squareQ : MvPolynomial (Fin 1) ℚ := X 0 ^ 2

private theorem support_squareQ : squareQ.support = {Finsupp.single 0 2} := by
  rw [squareQ, X_pow_eq_monomial, support_monomial]
  simp

private theorem clearedSubstitution_squareQ (H : ℕ) :
    clearedSubstitution (RingHom.id ℚ) 3 (fun _ ↦ 5) (fun _ ↦ 1) H squareQ =
      25 * 3 ^ (H - 2) := by
  simp [clearedSubstitution, squareQ, X_pow_eq_monomial,
    Finsupp.weight_single]
  norm_num

/-- Within budget, the cleared numerator is `3 ^ 3 * Q(5 / 3) = 75`. -/
example :
    clearedSubstitution (RingHom.id ℚ) 3 (fun _ ↦ 5) (fun _ ↦ 1) 3 squareQ = 75 ∧
      (RingHom.id ℚ) (clearedSubstitution (RingHom.id ℚ) 3 (fun _ ↦ 5) (fun _ ↦ 1) 3 squareQ) =
        3 ^ 3 * eval₂ (RingHom.id ℚ) (fun _ ↦ 5 / 3 ^ 1) squareQ := by
  refine ⟨by rw [clearedSubstitution_squareQ]; norm_num, ?_⟩
  have h := map_clearedSubstitution (RingHom.id ℚ) (RingHom.id ℚ) 3 (by norm_num)
    (fun _ ↦ 5) (fun _ ↦ 1) 3 squareQ (by simp [support_squareQ, Finsupp.weight_single])
  simpa using h

/-- Over budget, the identity of `map_clearedSubstitution` fails: `25 ≠ 3 * (5 / 3) ^ 2`. -/
example :
    clearedSubstitution (RingHom.id ℚ) 3 (fun _ ↦ 5) (fun _ ↦ 1) 1 squareQ ≠
      3 ^ 1 * eval₂ (RingHom.id ℚ) (fun _ ↦ (5 : ℚ) / 3 ^ 1) squareQ := by
  rw [clearedSubstitution_squareQ]
  simp [squareQ]
  norm_num

/-- The total-degree bound: with `S = X 0` of degree `1`, `N = X 0 ^ 2` of degree `1 * 1 + 1`,
and `d = 1`, the cleared numerator of `X 0 ^ 2` with budget `2` has total degree at most
`2 * 1 + 2 = 4`. -/
example :
    (clearedSubstitution C (X 0 : MvPolynomial (Fin 1) ℚ) (fun _ ↦ X 0 ^ 2) (fun _ ↦ 1) 2
      squareQ).totalDegree ≤ 4 := by
  have h := totalDegree_clearedSubstitution (X 0 : MvPolynomial (Fin 1) ℚ) (fun _ ↦ X 0 ^ 2)
    (fun _ ↦ 1) 2 1 2 squareQ (by simp) (fun _ ↦ by simp [totalDegree_X_pow])
    (by simp [support_squareQ, Finsupp.weight_single])
    (by simp [squareQ, totalDegree_X_pow])
  simpa using h
