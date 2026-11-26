/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.Probability.MaxEventProbability

/-! # Acceptance tests for exact worst-case probabilities -/

open Probability

-- The first member satisfies the event for two challenges and the second member for three.
/-- info: true -/
#guard_msgs in
#eval maxEventProbability (fun (w : Fin 2) (c : Fin 4) ↦ decide (c.val ≤ w.val + 1)) == 3 / 4

-- An empty family gives zero.
/-- info: true -/
#guard_msgs in
#eval maxEventProbability (fun (_ : Fin 0) (_ : Fin 2) ↦ false) == 0

-- An empty challenge space gives zero.
/-- info: true -/
#guard_msgs in
#eval maxEventProbability (fun (_ : Fin 2) (_ : Fin 0) ↦ true) == 0

-- In either context, the best counts at the two first challenges are one and two.
-- A constant reply gives at most two. Choosing the context after the first challenge gives four.
/-- info: true -/
#guard_msgs in
#eval maxEventCountWithReply
  (fun w t r s : Bool ↦ ((r == t) && ((t == w) || s)) || (w && !r && s)) == 3

-- An empty reply type gives zero even when both challenge spaces are nonempty.
/-- info: true -/
#guard_msgs in
#eval maxEventCountWithReply (fun (_ : Unit) (_ : Bool) (_ : Fin 0) (_ : Bool) ↦ true) == 0

/-- info: 'Probability.ofReal_maxEventProbability_eq_iSup_of_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Probability.ofReal_maxEventProbability_eq_iSup_of_iff

/-- info: 'Probability.maxEventCount_eq_maxEventCountWithReply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Probability.maxEventCount_eq_maxEventCountWithReply
