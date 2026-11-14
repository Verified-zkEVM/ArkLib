/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean.Elab.Tactic.Basic

/-! Test-only tactics shared by the interaction-core tests. -/

open Lean Elab Tactic Meta in
/-- Close an equality goal `lhs = rhs` with `Eq.refl lhs`, leaving the definitional check to the
kernel. The elaborator's definitional unfolding does not cache terms with free variables, so
`rfl` on a run with a symbolic secret or hidden bit exceeds the heartbeat budget; the kernel
checks the same proof term directly and rejects it when the sides differ. -/
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)
  let some (_, lhs, _) := goalType.consumeMData.eq?
    | throwError "kernel_rfl: the goal is not an equality"
  goal.assign (← mkEqRefl lhs)
