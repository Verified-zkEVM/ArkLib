/- Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, František Silváši
-/
import Mathlib.Algebra.Field.Rat
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.Module.LinearMap.Defs

import ArkLib.Data.CodingTheory.Basic

namespace JohnsonBound

private def f (x : ℚ) : ℚ := x^2 - x

private lemma f_convex {x₁ x₂ : ℚ} {α₁ α₂ : ℚ}
  (h_noneg_1 : 0 ≤ α₁)
  (h_noneg_2 : 0 ≤ α₂)
  (h_conv : α₁ + α₂ = 1)
  :
  f (α₁ * x₁ + α₂ * x₂) ≤ α₁ * f x₁ + α₂ * f x₂ := by
  unfold f
  obtain ⟨rfl⟩ := show α₂ = 1 - α₁ by rw [←h_conv]; simp
  suffices 0 ≤ α₁ * (1 - α₁) * (x₁ - x₂) ^ 2 by linarith
  exact mul_nonneg (mul_nonneg h_noneg_1 h_noneg_2) (sq_nonneg _)

def choose_2 (x : ℚ) : ℚ := x * (x-1)/2

private lemma choose_2_eq_half_f :
  choose_2 = (1/2) * f := by
  ext x
  simp [choose_2, f]
  ring

@[simp]
theorem choose_2_convex : ConvexOn ℚ Set.univ choose_2 := by
  rw [choose_2_eq_half_f]
  refine ⟨convex_univ, fun x₁ _ x₂ _ α₁ α₂ hα₁ hα₂ h ↦ ?p₁⟩
  have := f_convex (x₁ := x₁) (x₂ := x₂) hα₁ hα₂ h
  field_simp
  sorry --linarith

end JohnsonBound
