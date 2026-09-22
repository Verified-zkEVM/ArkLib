/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveHeight
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Curve interpolation height acceptance tests

* Concrete heights, and the failure of `curveInterpolationHeight_succ` at `ℓ = 0`.
* A concrete line certificate with two column classes transferred to a curve of degree `3`.
* The same certificate at `ℓ = 0`, where the source's hypothesis `0 < ℓ` is not available.
* The source shape with `0 < ℓ`.
-/

open ReedSolomon.HiddenDerivative

example : curveInterpolationHeight 3 4 = 14 := by decide
example : curveInterpolationHeight 3 4 + 1 - 3 * 2 = 3 * (4 + 1 - 2) :=
  curveInterpolationHeight_column (by norm_num) 4 2

/-- `0 < ℓ` is needed in `curveInterpolationHeight_succ`: at `ℓ = 0` the left side is `1`. -/
example : curveInterpolationHeight 0 4 + 1 ≠ 0 * (4 + 1) := by decide

/-- A line certificate at height `4` with one row: classes of counts `1, 2` and budgets `0, 2`
give `1 * 5 = 5 < 1 * 5 + 2 * 3 = 11`. At `ℓ = 3` the curve height is `14` and the comparison
is `15 < 15 + 2 * 9 = 33`. -/
example :
    1 * (curveInterpolationHeight 3 4 + 1) <
      ∑ i ∈ ({0, 1} : Finset (Fin 2)),
        ![1, 2] i * (curveInterpolationHeight 3 4 + 1 - 3 * ![0, 2] i) :=
  curveInterpolationHeight_preserves_certificate _ ![1, 2] ![0, 2] 1 4 3 (by decide)

/-- The same certificate at `ℓ = 0`: the curve height is `0` and the conclusion `1 < 3` still
follows. -/
example :
    1 * (curveInterpolationHeight 0 4 + 1) <
      ∑ i ∈ ({0, 1} : Finset (Fin 2)),
        ![1, 2] i * (curveInterpolationHeight 0 4 + 1 - 0 * ![0, 2] i) :=
  curveInterpolationHeight_preserves_certificate _ ![1, 2] ![0, 2] 1 4 0 (by decide)

/-- Source shape of `curveInterpolationHeight_preserves_certificate`, with the hypothesis
`0 < ℓ` that the ported theorem no longer needs. -/
example {ι : Type*} (s : Finset ι) (count weight : ι → ℕ) (rows h ℓ : ℕ) (_hℓ : 0 < ℓ)
    (hcertificate : rows * (h + 1) < ∑ i ∈ s, count i * (h + 1 - weight i)) :
    rows * (curveInterpolationHeight ℓ h + 1) <
      ∑ i ∈ s, count i * (curveInterpolationHeight ℓ h + 1 - ℓ * weight i) :=
  curveInterpolationHeight_preserves_certificate s count weight rows h ℓ hcertificate
