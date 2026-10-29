/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Batteries.Tactic.Lint.Misc

/-! Diagnostic-capture bypass fixtures for the ArkLib source-policy plugin. -/

#guard_msgs (drop error) in
set_option linter.unusedVariables false in
def guardedOptionSuppression (_x : Nat) := 1

#guard_msgs (drop error) in
@[nolint unusedArguments] def guardedAttributeSuppression (_x : Nat) := 1
