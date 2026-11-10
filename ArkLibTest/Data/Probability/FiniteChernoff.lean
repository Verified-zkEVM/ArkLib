/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.Probability.FiniteChernoff

/-! # Chernoff exponent acceptance tests -/

open Probability

-- The exponent vanishes on the diagonal.
example : kl 1 1 = 0 := by norm_num [kl, InformationTheory.klFun_apply]

-- For `a ≠ 0` it is `t log(t/a) - t + a`: at `t = 2`, `a = 1` this is `2 log 2 - 1`.
example : kl 2 1 = 2 * Real.log 2 - 1 := by
  norm_num [kl, InformationTheory.klFun_apply]
  ring
