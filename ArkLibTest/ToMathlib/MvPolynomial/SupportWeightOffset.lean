/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.SupportWeightOffset
import ArkLib.Data.MvPolynomial.WeightedDegree

/-!
# Acceptance tests for support weights with an allowance

The weights are the exponent of `X 0` (first weight) and of `X 1` (second weight) on `Fin 2`. The
examples compute a sharp allowance for a monomial, show that allowances of a product cannot be
smaller than the sum, compute the allowance of a substitution, and recover
`aeval_mem_supportWeightLE` from `supportWeightOffset_aeval` at the zero weight.
-/

open MvPolynomial

/-- The first weight: the exponent of `X 0`. -/
private noncomputable abbrev a₀ : (Fin 2 →₀ ℕ) →+ ℕ := Finsupp.applyAddHom 0

/-- The second weight: the exponent of `X 1`. -/
private noncomputable abbrev b₁ : (Fin 2 →₀ ℕ) →+ ℕ := Finsupp.applyAddHom 1

/-- The exponent vector of `X 0 ^ 3 * X 1`. -/
private noncomputable abbrev m₃₁ : Fin 2 →₀ ℕ := Finsupp.single 0 3 + Finsupp.single 1 1

/-- `X 0 ^ 3 * X 1` has allowance `2` and not `1`, since `3 ≤ 1 + 2` and `3 > 1 + 1`. -/
example :
    SupportWeightOffset a₀ b₁ 2 (monomial m₃₁ (1 : ℚ)) ∧
      ¬ SupportWeightOffset a₀ b₁ 1 (monomial m₃₁ (1 : ℚ)) := by
  refine ⟨SupportWeightOffset.monomial _ _ (by simp [m₃₁]), fun h ↦ ?_⟩
  have := h m₃₁ (by simp)
  simp [m₃₁] at this

/-- `X 0` has allowance `1`, so `X 0 ^ 2` has allowance `2 * 1` by `pow`, and that allowance is
attained: the square does not have allowance `1`. -/
example :
    SupportWeightOffset a₀ b₁ (2 * 1) (X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) ∧
      ¬ SupportWeightOffset a₀ b₁ 1 (X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) := by
  have hX : SupportWeightOffset a₀ b₁ 1 (X 0 : MvPolynomial (Fin 2) ℚ) :=
    SupportWeightOffset.monomial _ _ (by simp)
  refine ⟨hX.pow 2, fun h ↦ ?_⟩
  rw [X_pow_eq_monomial] at h
  have := h (Finsupp.single 0 2) (by simp)
  simp at this

/-- Substituting `X 0` (allowance `1`) and `X 1` (allowance `0`) into `Y 0 ^ 3 * Y 1` gives
allowance equal to the weighted degree `3 * 1 + 1 * 0 = 3`. -/
example :
    SupportWeightOffset a₀ b₁ 3
      (aeval (fun i : Fin 2 ↦ (X i : MvPolynomial (Fin 2) ℚ)) (monomial m₃₁ (1 : ℚ))) := by
  have h := supportWeightOffset_aeval a₀ b₁ (fun i : Fin 2 ↦ if i = 0 then 1 else 0)
    (fun i : Fin 2 ↦ (X i : MvPolynomial (Fin 2) ℚ)) (fun i ↦ by
      fin_cases i
      · exact SupportWeightOffset.monomial _ _ (by simp)
      · exact SupportWeightOffset.monomial _ _ (by simp)) (monomial m₃₁ (1 : ℚ))
  rw [weightedTotalDegree_monomial _ _ _ one_ne_zero] at h
  convert h using 1
  rw [m₃₁, map_add]
  simp [Finsupp.weight_single]

/-- At the zero weight, `supportWeightOffset_aeval` recovers `aeval_mem_supportWeightLE`. -/
example {R σ τ : Type*} [CommSemiring R] (a b : (τ →₀ ℕ) →+ ℕ)
    (v : σ → MvPolynomial τ R) (hv : ∀ i, v i ∈ supportWeightLE a b) (p : MvPolynomial σ R) :
    aeval v p ∈ supportWeightLE a b := by
  rw [← supportWeightOffset_zero_iff]
  have h := supportWeightOffset_aeval a b (fun _ ↦ 0) v
    (fun i ↦ supportWeightOffset_zero_iff.mpr (hv i)) p
  refine h.mono (le_of_eq ?_)
  simp [weightedTotalDegree, Finsupp.weight_apply]
