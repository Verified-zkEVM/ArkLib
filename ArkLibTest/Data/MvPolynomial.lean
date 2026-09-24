/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.WeightedDegree

/-!
# Acceptance tests for multivariate polynomial degrees

This example checks a separate-variable degree against a positive weighted total degree.
-/

open MvPolynomial

/-- The degree in `X₁` of `X₀² X₁³` is bounded by its `![1, 2]`-weighted degree. -/
example :
    let p : MvPolynomial (Fin 2) ℚ := X 0 ^ 2 * X 1 ^ 3
    degreeOf (1 : Fin 2) p ≤
      weightedTotalDegree (fun i : Fin 2 ↦ if i = 0 then 1 else 2) p := by
  dsimp
  exact degreeOf_le_weightedTotalDegree (fun i : Fin 2 ↦ if i = 0 then 1 else 2) 1
    (by decide) _
