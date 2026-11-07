/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.Linear
import Mathlib.Algebra.Field.ZMod

/-! # Random linear code list-size acceptance tests -/

open CodingTheory CodingTheory.RandomLinearInternal

-- The radius `δ = 1/4` lies below `1 - 1/2`, so `H_2(1/4) < 1`.
example : qEntropy 2 (1 / 4) < 1 :=
  qEntropy_lt_one (le_refl 2) (by norm_num) (by norm_num)

-- `random_linear_lambda_lower` applies at `q = 2`, `δ = 1/4`, `ε = 1/2`, with its full conclusion.
example := random_linear_lambda_lower 2 Nat.prime_two.isPrimePow (1 / 4) (by norm_num) (by norm_num)
  (1 / 2) (by norm_num) (by norm_num)

-- `Ber_2(1/4)` puts weight `1/4` on the nonzero symbol and `3/4` on zero.
example : ber 2 (1 / 4 : ℝ) (1 : ZMod 2) = 1 / 4 ∧ ber 2 (1 / 4 : ℝ) (0 : ZMod 2) = 3 / 4 := by
  norm_num [ber]

-- The bad distribution at `q = 2`, `p = 1/4`, `L = 3` is a probability weight.
example : IsProb (badLaw 2 (1 / 4) 3 (ZMod 2)) :=
  isProb_badLaw (le_refl 2) (ZMod.card 2) (by norm_num) (by norm_num) 3
