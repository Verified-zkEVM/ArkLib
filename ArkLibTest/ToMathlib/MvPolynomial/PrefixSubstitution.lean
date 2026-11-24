/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.ToMathlib.MvPolynomial.PrefixSubstitution
import Mathlib.Data.Fin.VecNotation

/-!
# Prefix substitution acceptance tests

The polynomial `X 0 * X 1` vanishes at the point `(1, 0)`. Substituting at the variables `< 1`
leaves `X 1`, and substituting at the variables `≤ 1` gives `0`, so `1` is the variable at which
the substitutions first vanish.
-/

open MvPolynomial

example : aeval (fun j : Fin 2 ↦ if j < 1 then C ((![1, 0] : Fin 2 → ℤ) j) else X j)
      (X 0 * X 1 : MvPolynomial (Fin 2) ℤ) = X 1 ∧
    aeval (fun j : Fin 2 ↦ if j ≤ 1 then C ((![1, 0] : Fin 2 → ℤ) j) else X j)
      (X 0 * X 1 : MvPolynomial (Fin 2) ℤ) = 0 := by
  simp

/-- For `X 0 * X 1` at `(1, 0)`, the variable given by
`exists_aeval_ite_lt_ne_zero_and_aeval_ite_le_eq_zero` is `1`: at `0` the substitution at the
variables `≤ 0` leaves `X 1 ≠ 0`. -/
example : ∃ i : Fin 2, i = 1 ∧
    aeval (fun j ↦ if j < i then C ((![1, 0] : Fin 2 → ℤ) j) else X j)
      (X 0 * X 1 : MvPolynomial (Fin 2) ℤ) ≠ 0 := by
  obtain ⟨i, hlt, hle⟩ := exists_aeval_ite_lt_ne_zero_and_aeval_ite_le_eq_zero
    (x := (![1, 0] : Fin 2 → ℤ)) (mul_ne_zero (X_ne_zero 0) (X_ne_zero 1)) (by simp)
  refine ⟨i, ?_, hlt⟩
  fin_cases i
  · simp [X_ne_zero] at hle
  · rfl
