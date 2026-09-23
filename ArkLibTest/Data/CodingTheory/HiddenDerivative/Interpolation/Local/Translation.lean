/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Translation

/-!
# Point translation acceptance tests

* Translating `Y₀ - X` by `(c, r)` gives `Y₀ - X + (r - c)`.
* The statements at the zero point: the unscaled substitution at `(c, r)` is the
  substitution at `(0, 0)` after translation, and translation by `(-c, -r)` undoes translation by
  `(c, r)`.
* The nonnegativity hypothesis on the weight of `X` is needed: with weight `-1` on `X` and `0`
  elsewhere, `X` has weight at most `-1` but its translate `1 + X` does not.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- Translating `Y₀ - X` by `(c, r)` adds `r - c`. -/
example (c r : ℚ) :
    globalPointTranslation (d := 2) c r (X (some 0) - X none) =
      X (some 0) - X none + C (r - c) := by
  simp only [map_sub, globalPointTranslation_X, globalPointTranslation_Y_zero, map_sub]
  ring

/-- The unscaled substitution at `(0, 0)` after translation by `(c, r)` is the unscaled
substitution at `(c, r)`. -/
example (d : ℕ) (c r : ℤ) :
    (unscaledLocalSubstitution d 0 0).comp (globalPointTranslation c r) =
      unscaledLocalSubstitution d c r := by
  rw [unscaledLocalSubstitution_comp_globalPointTranslation, add_zero, add_zero]

/-- Translation by `(-c, -r)` after translation by `(c, r)` fixes a concrete polynomial. -/
example (c r : ℤ) :
    globalPointTranslation (d := 1) (-c) (-r)
        (globalPointTranslation c r (X none * X (some 0) + X (some 1))) =
      X none * X (some 0) + X (some 1) := by
  rw [← AlgHom.comp_apply, globalPointTranslation_neg_comp, AlgHom.id_apply]

/-- The nonnegativity hypothesis on the weight of `X` cannot be dropped. -/
example :
    ∃ (w : JetVariable 0 → ℤ) (Q : DifferentialPolynomial ℚ 0),
      Q ∈ restrictWeightAtMost (R := ℚ) w (-1) ∧
        globalPointTranslation 1 0 Q ∉ restrictWeightAtMost (R := ℚ) w (-1) := by
  refine ⟨fun v => Option.elim v (-1) fun _ => 0, X none,
    X_mem_restrictWeightAtMost _ _ le_rfl, ?_⟩
  rw [globalPointTranslation_X, mem_restrictWeightAtMost]
  intro h
  have h0 := h 0 (by simp [mem_support_iff, coeff_X])
  simp at h0
