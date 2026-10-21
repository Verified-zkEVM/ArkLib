/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.NormalizedSubstitution

/-!
# Normalized substitution acceptance test

At `d = 1`, the normalized and composed substitutions agree on a concrete input polynomial.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- The composition identity at `d = 1`, `center = 2`, and `received = 3`. -/
example :
    normalizedLocalSubstitution 1 (2 : ℤ) 3 (X (some 0) - C (3 : ℤ)) =
      (normalizeError 1).comp (unscaledLocalSubstitution 1 (2 : ℤ) 3)
        (X (some 0) - C (3 : ℤ)) := by
  exact congrArg (fun σ => σ (X (some 0) - C (3 : ℤ)))
    (normalizedLocalSubstitution_eq_normalize_comp_unscaled 1 2 3)
