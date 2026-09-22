/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.NormalizedSubstitution

/-!
# Normalized substitution acceptance tests

At `d = 1` the normalized substitution sends `Y₀ - received` to `T Y₁ + T² E`, while the unscaled
substitution sends it to `T Y₁ + T E`; normalization carries the second to the first. At
`d = 0` the rescaling `E ↦ T⁰ E` is the identity on `E`, so the two substitutions agree. The
statements are checked over `ℤ`.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- At `d = 1`, the normalized image of `Y₀ - received` is `T Y₁ + T² E`. -/
example (center received : ℤ) :
    normalizedLocalSubstitution 1 center received (X (some 0) - C received) =
      X (localT 1) * X (localY 0) + X (localT 1) ^ 2 * X (localE 1) := by
  simp [localCorrection]
  ring

/-- The same image computed through `normalizeError` and the unscaled substitution. -/
example (center received : ℤ) :
    normalizeError 1 (unscaledLocalSubstitution 1 center received (X (some 0) - C received)) =
      X (localT 1) * X (localY 0) + X (localT 1) ^ 2 * X (localE 1) := by
  rw [← AlgHom.comp_apply, ← normalizedLocalSubstitution_eq_normalize_comp_unscaled]
  simp [localCorrection]
  ring

/-- At `d = 0` normalization fixes `E`, so the normalized and unscaled substitutions agree. -/
example (center received : ℤ) :
    normalizedLocalSubstitution 0 center received =
      unscaledLocalSubstitution 0 center received := by
  have h : normalizeError (R := ℤ) 0 = AlgHom.id ℤ _ := by
    refine MvPolynomial.algHom_ext fun v => ?_
    rcases v with _ | _ | j
    · exact normalizeError_T 0
    · have hE := normalizeError_E (R := ℤ) 0
      rwa [pow_zero, one_mul] at hE
    · exact j.elim0
  rw [normalizedLocalSubstitution_eq_normalize_comp_unscaled, h, AlgHom.id_comp]
