/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Tactic.Ring

/-! # Spartan's knowledge-error ledger -/

@[expose] public section

namespace Spartan

open scoped NNReal

/-- The additive error for row dimension `s`, column dimension `t`, and field cardinality `q`.
Real division is noncomputable; this value occurs only in security bounds. -/
noncomputable def totalError (s t q : ℕ) : ℝ≥0 := (4 * s + 2 * t + 1 : ℝ≥0) / q

/-- Zero-check, the first sumcheck, batching, and the second sumcheck contribute
`s + 3s + 1 + 2t` in the numerator. -/
theorem error_ledger (s t q : ℕ) :
    (s : ℝ≥0) / q + s * (3 / (q : ℝ≥0)) + 1 / (q : ℝ≥0) +
      t * (2 / (q : ℝ≥0)) = totalError s t q := by
  simp only [totalError, div_eq_mul_inv]
  ring

end Spartan
