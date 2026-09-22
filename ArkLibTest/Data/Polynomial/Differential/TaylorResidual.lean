/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.TaylorResidual
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for universal Taylor residuals

The examples derive the separant-denominator budget on a chart of length exactly `r + h` with
`0 < h`, compute the residual of the first-order equation `Q = Y₁` on a chart of length `3`, and
use it to show that the chart-length hypothesis of
`denominator_weight_le_of_mem_universalTaylorResidual_coeff` cannot be dropped. They also
specialize the residual of `Q = Y₀` at an explicit coefficient prefix, and reduce a residual
over `ℤ` modulo `2`.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-- The special case of a chart of length exactly `r + h` with `0 < h`: every monomial of
the coefficient of `ξ ^ h` has denominator weight at most `2h - 2`. -/
example {F : Type*} [CommSemiring F] {r h : ℕ} (_hh : 0 < h) (center : F)
    (Q : DifferentialPolynomial F r) (m : Fin (r + h) →₀ ℕ)
    (hm : m ∈ ((optionEquivLeft F (Fin (r + h))
      (universalTaylorResidual (r + h) center Q)).coeff h).support) :
    Finsupp.weight (fun l : Fin (r + h) ↦ 2 * (l.val - r) - 1) m ≤ 2 * h - 2 :=
  denominator_weight_le_of_mem_universalTaylorResidual_coeff le_rfl center Q m hm

/-- The first-order equation `Q = Y₁`. -/
private abbrev firstJet : DifferentialPolynomial ℚ 1 := X (some 1)

/-- On a chart of length `3`, the coefficient of `ξ` in the residual of `Y₁` is `2 c₂`: the first
derivative of `c₀ + c₁ ξ + c₂ ξ ^ 2` is `c₁ + 2 c₂ ξ`. -/
private theorem firstJet_residual_coeff_one :
    (optionEquivLeft ℚ (Fin 3) (universalTaylorResidual 3 0 firstJet)).coeff 1 =
      C 2 * X 2 := by
  have hres : universalTaylorResidual 3 (0 : ℚ) firstJet = universalTaylorJet 3 1 := by
    simp [universalTaylorResidual, firstJet]
  rw [hres, optionEquivLeft_universalTaylorJet, Polynomial.hasseDeriv_coeff]
  simp [Fin.sum_univ_three, Polynomial.coeff_monomial]
  rfl

/-- The chart-length hypothesis `K ≤ r + h` is necessary. With `r = h = 1` and chart length
`3 = r + h + 1`, the monomial `c₂` occurs in the coefficient of `ξ`, and its denominator weight
`2 * (2 - 1) - 1 = 1` exceeds `2 * 1 - 2 = 0`. The Taylor-weight bound still holds. -/
example :
    Finsupp.single (2 : Fin 3) 1 ∈
        ((optionEquivLeft ℚ (Fin 3) (universalTaylorResidual 3 0 firstJet)).coeff 1).support ∧
      Finsupp.weight (fun l : Fin 3 ↦ l.val - 1) (Finsupp.single (2 : Fin 3) 1) ≤ 1 ∧
      ¬ Finsupp.weight (fun l : Fin 3 ↦ 2 * (l.val - 1) - 1) (Finsupp.single (2 : Fin 3) 1) ≤
        2 * 1 - 2 := by
  refine ⟨?_, by simp [Finsupp.weight_single], by simp [Finsupp.weight_single]⟩
  rw [firstJet_residual_coeff_one, mem_support_iff, X, C_mul_monomial, coeff_monomial]
  norm_num

/-- Specializing the residual of `Q = Y₀` at a prefix recovers the prefix's Taylor coefficients:
the coefficient of `ξ ^ h` evaluates to `c h` when `h < K`. -/
example (center : ℚ) (c : ℕ → ℚ) (K h : ℕ) (hh : h < K) :
    aeval (fun i : Fin K ↦ c i.val)
        ((optionEquivLeft ℚ (Fin K)
          (universalTaylorResidual K center (X (some 0) : DifferentialPolynomial ℚ 0))).coeff h) =
      c h := by
  rw [aeval_universalTaylorResidual_coeff, differentialSpecialization_jet]
  simp [Polynomial.coeff_taylor_centeredCoefficientPrefix, hh]

/-- Reducing coefficients modulo `2` commutes with the residual: the residual of `2 Y₁` over `ℤ`
reduces to the residual of `0`, which is `0`. -/
example (K : ℕ) :
    map (Int.castRingHom (ZMod 2))
        (universalTaylorResidual K 1 (2 * X (some 1) : DifferentialPolynomial ℤ 1)) = 0 := by
  rw [map_universalTaylorResidual]
  have h2 : map (Int.castRingHom (ZMod 2)) (2 * X (some 1) : DifferentialPolynomial ℤ 1) = 0 := by
    rw [map_mul, map_ofNat, map_X, show (2 : DifferentialPolynomial (ZMod 2) 1) = C 2 from rfl,
      show (2 : ZMod 2) = 0 from rfl, C_0, zero_mul]
  simp [h2, universalTaylorResidual]

end

end PolynomialDifferential
