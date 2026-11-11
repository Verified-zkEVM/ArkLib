/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.NumberTheory.Harmonic.Bounds
import ArkLib.ToMathlib.NumberTheory.Harmonic.Thresholds

/-!
# Acceptance cases for explicit harmonic estimates

The examples check the harmonic-number bound at its cutoff and both estimates in the threshold
module at their stated cutoffs.
-/

open Finset Real

/-- The explicit logarithmic bound at its cutoff `n = 32`. -/
example : (harmonic 32 : ℝ) < log 32 + 3 / 5 :=
  harmonic_lt_log_add_three_fifths (by norm_num)

/-- The logarithmic error bound at its cutoff `n = 180`. -/
example : (harmonic 180 : ℝ) - log 180 < 29 / 50 := harmonic_sub_log_lt le_rfl

/-- The reciprocal-square lower bound at its cutoff `n = 203`. -/
example : (41 / 25 : ℝ) < ∑ i : Fin 203, 1 / ((i : ℝ) + 1) ^ 2 :=
  lt_sum_fin_one_div_add_one_sq le_rfl
