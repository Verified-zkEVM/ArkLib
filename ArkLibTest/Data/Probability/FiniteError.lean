/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.Probability.FiniteError

/-! # Runtime checks for finite worst-case probabilities -/

/-- info: (3 : Rat)/4 -/
#guard_msgs in
#eval Probability.maxEventProbability fun (w : Fin 2) (c : Fin 4) ↦ decide (c.val ≤ w.val + 1)

/-- info: 0 -/
#guard_msgs in
#eval Probability.maxEventProbability fun (_ : Fin 0) (_ : Fin 2) ↦ false

/-- info: 0 -/
#guard_msgs in
#eval Probability.maxEventProbability fun (_ : Fin 2) (_ : Fin 0) ↦ true
