/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-! Accepted syntax fixtures for the ArkLib source-policy plugin. -/

/-- A declaration whose name may occur as an argument to another attribute. -/
def nolint := 1

syntax "values!" str : term

macro_rules
  | `(values! $value:str) => `($value)

def inertString : String := "{set_option pp.universes true in (1 : Nat)}"
def ordinaryStringMacro : String := values!"{set_option pp.universes true in (1 : Nat)}"
@[inherit_doc nolint] def ordinaryAttributeArgument := 1
