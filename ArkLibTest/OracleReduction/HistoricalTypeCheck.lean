/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Lean

/-! # Full-type compatibility assertions for historical protocol interfaces -/

open Lean Elab Command Meta

/-- Reuse the current theorem, discharging only historical local hypotheses. -/
elab "historical_exact " proof:term : tactic => do
  Elab.Tactic.evalTactic (← `(tactic| apply $proof))
  unless (← Elab.Tactic.getGoals).isEmpty do
    Elab.Tactic.evalTactic (← `(tactic| all_goals assumption))

/-- Check the full elaborated types, including the explicitness of every binder. -/
elab "assert_historical_type " original:ident expected:ident : command => do
  let originalInfo ← getConstInfo (← resolveGlobalConstNoOverload original)
  let expectedInfo ← getConstInfo (← resolveGlobalConstNoOverload expected)
  liftTermElabM do
    unless ← isDefEq originalInfo.type expectedInfo.type do
      throwError "Historical type mismatch: {original.getId}"
    forallTelescope originalInfo.type fun xs _ =>
      forallTelescope expectedInfo.type fun ys _ => do
        unless xs.size == ys.size do
          throwError "Historical binder count mismatch: {original.getId}"
        for x in xs, y in ys do
          unless (← x.fvarId!.getDecl).binderInfo == (← y.fvarId!.getDecl).binderInfo do
            throwError "Historical binder explicitness mismatch: {original.getId}"
