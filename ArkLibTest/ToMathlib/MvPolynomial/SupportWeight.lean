/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.SupportWeight
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for support-weight subalgebras and the denominator budget

The examples compute a sharp instance of `Finsupp.weight_two_mul_sub_one_le`, show that its
support hypothesis cannot be dropped, derive the special case on `Fin (r + h)`, and check
membership in `supportWeightLE` for a polynomial and its coefficient in a distinguished variable.
-/

open MvPolynomial

/-! ### Denominator budget -/

/-- The exponent vector `e₁ + e₂` on `Fin 3`. -/
private noncomputable abbrev e₁₂ : Fin 3 →₀ ℕ := Finsupp.single 1 1 + Finsupp.single 2 1

/-- With `t i = i`, `h = 3`, and `m = e₁ + e₂`, the budget `2 * h - 2 = 4` is attained. -/
example :
    Finsupp.weight (fun i : Fin 3 ↦ 2 * i.val - 1) e₁₂ = 4 ∧
      Finsupp.weight (fun i : Fin 3 ↦ 2 * i.val - 1) e₁₂ ≤ 2 * 3 - 2 := by
  refine ⟨by simp [Finsupp.weight_single], ?_⟩
  refine Finsupp.weight_two_mul_sub_one_le (fun i : Fin 3 ↦ i.val) _ ?_ ?_
  · simp [Finsupp.weight_single]
  · intro i _
    omega

/-- The support hypothesis `t i ≤ h - 1` is necessary: with `t 2 = h = 2` and `m = e₂`, the
weight hypothesis holds but the denominator weight is `3 > 2 * 2 - 2`. -/
example :
    Finsupp.weight (fun i : Fin 3 ↦ i.val) (Finsupp.single (2 : Fin 3) 1) ≤ 2 ∧
      ¬ Finsupp.weight (fun i : Fin 3 ↦ 2 * i.val - 1) (Finsupp.single (2 : Fin 3) 1) ≤
        2 * 2 - 2 := by
  simp [Finsupp.weight_single]

/-- The special case on `Fin (r + h)` with `0 < h` follows from the general budget with
`t l = l - r`. -/
example {r h : ℕ} (_hh : 0 < h) (m : Fin (r + h) →₀ ℕ)
    (hm : Finsupp.weight (fun l : Fin (r + h) ↦ l.val - r) m ≤ h) :
    Finsupp.weight (fun l : Fin (r + h) ↦ 2 * (l.val - r) - 1) m ≤ 2 * h - 2 :=
  Finsupp.weight_two_mul_sub_one_le (fun l : Fin (r + h) ↦ l.val - r) m hm
    (fun l _ ↦ by omega)

/-- At `h = 0` the general budget still applies: every coordinate has `t l = 0`. -/
example {r : ℕ} (m : Fin r →₀ ℕ) :
    Finsupp.weight (fun l : Fin r ↦ 2 * (l.val - r) - 1) m ≤ 2 * 0 - 2 := by
  refine Finsupp.weight_two_mul_sub_one_le (fun l : Fin r ↦ l.val - r) m ?_ (fun l _ ↦ by omega)
  simp [Finsupp.weight_apply]

/-! ### Support-weight subalgebras -/

/-- The weight that ignores `none` and gives `some 0` weight one. -/
private noncomputable abbrev coefficientWeight : (Option (Fin 1) →₀ ℕ) →+ ℕ :=
  Finsupp.weight (fun i : Option (Fin 1) ↦ i.elim 0 (fun _ ↦ 1))

/-- `c ξ` satisfies `weight ≤ exponent of ξ`, but `c` alone does not. -/
example :
    (X (some 0) * X none : MvPolynomial (Option (Fin 1)) ℚ) ∈
        supportWeightLE coefficientWeight (Finsupp.applyAddHom none) ∧
      (X (some 0) : MvPolynomial (Option (Fin 1)) ℚ) ∉
        supportWeightLE coefficientWeight (Finsupp.applyAddHom none) := by
  constructor
  · rw [X, X, monomial_mul_monomial, one_mul]
    exact monomial_mem_supportWeightLE _ _ _ _ (by simp [Finsupp.weight_single])
  · rw [mem_supportWeightLE]
    simp [support_X, Finsupp.weight_single]
