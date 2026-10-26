/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Interaction.Config
import Lean.Compiler.IR

/-! Acceptance checks for executable scalar LogUp configuration. -/

namespace Logup.Interaction.ConfigTest

example : (Config.create? 0 0 1).isSome = false := by decide
example : (Config.create? 1 3 0).isSome = false := by decide
example : (Config.create? 1 3 4).isSome = false := by decide
example : (Config.create? 0 3 2).isSome = true := by decide

open Lean Elab Command
run_cmd do
  unless ((Config.create? 0 3 2).map fun cfg => cfg.groups.toList.map (List.map Fin.val)) ==
      some [[0, 1], [2]] do
    throwError "checked config changed its concrete consecutive groups"
  unless (Lean.IR.findEnvDecl (← getEnv) ``Config.create?).isSome do
    throwError "checked config has no compiler IR"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Config.isSome_create?, ``Config.flatten_groups, ``Config.length_group_le,
      ``Config.total_pos,
      ``Config.group_count_pos] do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do
      throwError "unexpected axioms in `{name}`: {axioms}"

end Logup.Interaction.ConfigTest
