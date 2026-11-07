/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.ReedSolomon

/-! # Reed-Solomon list-size acceptance tests -/

-- `rs_lambda_superpoly_extension` applies at `α = 1/3`, `β = 1/2`.
example : ∃ qs : ℕ → ℕ, StrictMono qs ∧ ∀ i, IsPrimePow (qs i) := by
  obtain ⟨qs, hmono, hpp, -⟩ := CodingTheory.rs_lambda_superpoly_extension (1 / 3) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨qs, hmono, hpp⟩
