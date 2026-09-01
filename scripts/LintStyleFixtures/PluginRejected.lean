/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Batteries.Tactic.Lint.Misc

/-! Rejected syntax fixtures for the ArkLib source-policy plugin. -/

syntax "customInterp " interpolatedStr(term) : term

macro_rules
  | `(customInterp $value:interpolatedStr) => `(s!$value)

set_option linter.unusedVariables false in
def linterSuppression (x : Nat) := 1

def prettyPrinterSuppression := customInterp /- parser gap -/
  "{set_option pp.universes true in (1 : Nat)}"

def profilerSuppression := set_option profiler true in (1 : Nat)

def traceSuppression := m! -- parser gap
  "{set_option trace.profiler true in (1 : Nat)}"

@[nolint unusedArguments] def attributeSuppression (x : Nat) := 1

def attributeCommandSuppression (x : Nat) := 1
attribute [nolint unusedArguments] attributeCommandSuppression
