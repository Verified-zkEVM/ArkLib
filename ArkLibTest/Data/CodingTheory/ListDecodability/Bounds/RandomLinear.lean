/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.RandomLinear
import Mathlib.Algebra.Field.ZMod

/-! # Random linear code list-size acceptance tests -/

open CodingTheory.RandomLinearInternal

-- The rows `0, 0, 1` have `3 = 3! / (2! 1!)` row permutations.
example : (rowOrbit (![0, 0, 1] : Fin 3 → ZMod 2)).ncard = 3 := by
  rw [ncard_rowOrbit]
  decide

-- `Ber_2(1/4)` puts weight `1/4` on the nonzero symbol and `3/4` on zero.
example : ber 2 (1 / 4 : ℝ) (1 : ZMod 2) = 1 / 4 ∧ ber 2 (1 / 4 : ℝ) (0 : ZMod 2) = 3 / 4 := by
  norm_num [ber]
