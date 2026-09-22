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

For the rescaled comparisons, the examples compute the degree of a composite with an affine
polynomial, show that `c ≠ 0` is needed there and that the lower polynomial must be eventually
nonnegative in the sandwich, and derive the source's rescaled, affine and sandwich statements,
with their `≠ 0` and positivity hypotheses, from the general ones.

For the coefficient comparisons in a degree `d` at least the natural degree, `X - 1` and `1 - X`
show that the degree bounds are needed, and `taylor 3 (X ^ 2)` shows that a Taylor shift keeps
the coefficients in degrees at least the natural degree but changes the one in degree `1`.
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

/-- `(X ^ 2).comp (3 X + 1) = 9 X ^ 2 + 6 X + 1` has natural degree `2`. -/
example : ((X ^ 2 : ℚ[X]).comp (C 3 * X + C 1)).natDegree = 2 := by
  rw [natDegree_comp_C_mul_X_add_C _ (by norm_num), natDegree_X_pow]

/-- The hypothesis `c ≠ 0` of `natDegree_comp_C_mul_X_add_C` is needed: composing `X ^ 2` with the
constant `C 0 * X + C 1` gives the constant `1`. -/
example : ((X ^ 2 : ℚ[X]).comp (C 0 * X + C 1)).natDegree = 0 := by
  simp

/-- Without positivity of `m`: a polynomial eventually between `0` and `0 * P (c * N + d)` is
constant. -/
example {P Q : ℚ[X]} {c d : ℚ} (hQ : ∀ᶠ N : ℕ in atTop, 0 ≤ Q.eval (N : ℚ))
    (hle : ∀ᶠ N : ℕ in atTop, Q.eval (N : ℚ) ≤ 0 * P.eval (c * N + d)) : Q.natDegree = 0 := by
  have := natDegree_le_of_eventually_eval_natCast_le_mul_eval_comp (P := P) (m := 0) (S := C 0)
    hQ (hle.mono fun N hN ↦ by simpa using hN)
  simpa using this

/-- The nonnegativity of the lower polynomial is needed in the sandwich: `P = -X` lies below
`Q = 0`, which lies below `-1 * P N`, but the natural degrees are `0` and `1`. -/
example : (∀ x : ℚ, (-X : ℚ[X]).eval x ≤ (0 : ℚ[X]).eval x ∨ x < 0) ∧
    (∀ x : ℚ, (0 : ℚ[X]).eval x ≤ -1 * (-X : ℚ[X]).eval (1 * x + 0) ∨ x < 0) ∧
    (0 : ℚ[X]).natDegree ≠ (-X : ℚ[X]).natDegree := by
  refine ⟨fun x ↦ ?_, fun x ↦ ?_, by simp⟩ <;>
  · rcases le_or_gt 0 x with hx | hx
    · left; simpa using hx
    · right; exact hx

/-- The source's `natDegree_comp_C_mul_X` over `ℚ`. -/
example (P : ℚ[X]) {c : ℚ} (hc : c ≠ 0) : (P.comp (C c * X)).natDegree = P.natDegree := by
  simpa using natDegree_comp_C_mul_X_add_C P hc 0

/-- The source's rescaled comparison, with its hypotheses `Q ≠ 0` and `0 < c`. -/
example {P Q : ℚ[X]} (_hQ : Q ≠ 0) {c : ℕ} (_hc : 0 < c)
    (hQnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ Q.eval (N : ℚ))
    (hle : ∀ᶠ N : ℕ in atTop, Q.eval (N : ℚ) ≤ P.eval ((c * N : ℕ) : ℚ)) :
    Q.natDegree ≤ P.natDegree :=
  natDegree_le_of_eventually_eval_natCast_le_mul_eval_affine (m := 1) (c := c) (d := 0) hQnonneg
    (hle.mono fun N hN ↦ by simpa using hN)

/-- The source's affine comparison with natural constants `m, c > 0` and `d`. -/
example {P Q : ℚ[X]} (_hQ : Q ≠ 0) {m c d : ℕ} (_hm : 0 < m) (_hc : 0 < c)
    (hQnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ Q.eval (N : ℚ))
    (hle : ∀ᶠ N : ℕ in atTop, Q.eval (N : ℚ) ≤ (m : ℚ) * P.eval ((c * N + d : ℕ) : ℚ)) :
    Q.natDegree ≤ P.natDegree :=
  natDegree_le_of_eventually_eval_natCast_le_mul_eval_affine (m := m) (c := c) (d := d) hQnonneg
    (hle.mono fun N hN ↦ by simpa using hN)

/-- The source's sandwich, with its redundant hypotheses `P ≠ 0`, `Q ≠ 0`, `0 < c` and eventual
nonnegativity of `Q`. -/
example {P Q : ℚ[X]} (_hP : P ≠ 0) (_hQ : Q ≠ 0) {c : ℕ} (_hc : 0 < c)
    (hPnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ P.eval (N : ℚ))
    (_hQnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ Q.eval (N : ℚ))
    (hlower : ∀ᶠ N : ℕ in atTop, P.eval (N : ℚ) ≤ Q.eval (N : ℚ))
    (hupper : ∀ᶠ N : ℕ in atTop, Q.eval (N : ℚ) ≤ P.eval ((c * N : ℕ) : ℚ)) :
    Q.natDegree = P.natDegree :=
  natDegree_eq_of_eventually_eval_natCast_le_of_le_mul_eval_affine (m := 1) (c := c) (d := 0)
    hPnonneg hlower (hupper.mono fun N hN ↦ by simpa using hN)

/-! ### Coefficients in a degree at least the natural degree -/

/-- `X - 1` is nonnegative at every positive natural number, but its coefficient in degree `0`,
below its natural degree `1`, is `-1`. So the degree bound in
`coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg` is needed. -/
example : (∀ᶠ N : ℕ in atTop, (0 : ℚ) ≤ (X - 1 : ℚ[X]).eval (N : ℚ)) ∧
    (X - 1 : ℚ[X]).coeff 0 < 0 := by
  refine ⟨(eventually_ge_atTop 1).mono fun N hN ↦ ?_, by simp⟩
  have : (1 : ℚ) ≤ N := by exact_mod_cast hN
  simp only [eval_sub, eval_X, eval_one]
  linarith

/-- In degree `1`, the natural degree of `X - 1`, the nonnegativity lemma gives `0 ≤ 1`. -/
example : (0 : ℚ) ≤ (X - 1 : ℚ[X]).coeff 1 :=
  coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg
    (by compute_degree!) ((eventually_ge_atTop 1).mono fun N hN ↦ by
      have : (1 : ℚ) ≤ N := by exact_mod_cast hN
      simp only [eval_sub, eval_X, eval_one]
      linarith)

/-- The degree bound on the smaller polynomial in
`coeff_le_of_natDegree_le_of_eventually_eval_natCast_le` is needed: `1 - X ≤ 0` at every
positive natural number, but in degree `0` the coefficients are `1 > 0`. -/
example : (∀ᶠ N : ℕ in atTop, (1 - X : ℚ[X]).eval (N : ℚ) ≤ (0 : ℚ[X]).eval (N : ℚ)) ∧
    (0 : ℚ[X]).coeff 0 < (1 - X : ℚ[X]).coeff 0 := by
  refine ⟨(eventually_ge_atTop 1).mono fun N hN ↦ ?_, by simp⟩
  have : (1 : ℚ) ≤ N := by exact_mod_cast hN
  simp only [eval_sub, eval_X, eval_one, eval_zero]
  linarith

/-- A Taylor shift keeps the coefficients in degrees at least the natural degree: for
`taylor 3 (X ^ 2) = (X + 3) ^ 2` the coefficient in degree `2` is `1` and in degree `5` it is
`0`. -/
example : (taylor (3 : ℚ) (X ^ 2)).coeff 2 = 1 ∧ (taylor (3 : ℚ) (X ^ 2)).coeff 5 = 0 := by
  constructor
  · rw [coeff_taylor_of_natDegree_le _ (natDegree_X_pow_le 2), coeff_X_pow_self]
  · rw [coeff_taylor_of_natDegree_le _ ((natDegree_X_pow_le 2).trans (by norm_num)),
      coeff_X_pow]
    norm_num

/-- Below the natural degree the Taylor shift changes coefficients: the coefficient of
`(X + 3) ^ 2` in degree `1` is `6`, while that of `X ^ 2` is `0`. -/
example : (taylor (3 : ℚ) (X ^ 2)).coeff 1 = 6 ∧ (X ^ 2 : ℚ[X]).coeff 1 = 0 := by
  constructor
  · rw [taylor_coeff_one]
    simp only [derivative_X_pow, eval_mul, eval_C, eval_pow, eval_X]
    norm_num
  · rw [coeff_X_pow]
    norm_num

/-- The source's `ℚ` forms of the coefficient lemmas. -/
example {P Q : ℚ[X]} {d : ℕ} (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (hnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ P.eval (N : ℚ))
    (hle : ∀ᶠ N : ℕ in atTop, P.eval (N : ℚ) ≤ Q.eval (N : ℚ)) (a : ℚ) :
    0 ≤ P.coeff d ∧ P.coeff d ≤ Q.coeff d ∧ (taylor a P).coeff d = P.coeff d :=
  ⟨coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg hP hnonneg,
    coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hP hQ hle,
    coeff_taylor_of_natDegree_le a hP⟩

end EventualGrowthTest
