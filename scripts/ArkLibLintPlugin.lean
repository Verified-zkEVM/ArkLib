/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean.Elab.Command

/-!
# ArkLib build-time source-policy plugin

This plugin rejects linter suppressions while Lean is elaborating each ArkLib module. Inspecting the
actual syntax tree is important: terms inside extensible interpolated strings are active syntax,
while identical text in comments and ordinary strings is inert.
-/

open Lean Elab Command

namespace ArkLib.LintStyle

private def setOptionName? : Syntax → Option Name
  | `(command| set_option $name:ident $_value) => some name.getId
  | `(set_option $name:ident $_value in $_term) => some name.getId
  | `(tactic| set_option $name:ident $_value in $_tactic) => some name.getId
  | _ => none

private def forbiddenOptionRoot? (name : Name) : Option Name :=
  let root := name.getRoot
  if [`linter, `pp, `profiler, `trace].contains root then some root else none

private def isNoLintAttribute (stx : Syntax) : Bool :=
  stx.getKind == `Batteries.Tactic.Lint.nolint

private partial def collectSuppressions (stx : Syntax) (acc : Array (Syntax × MessageData)) :
    Array (Syntax × MessageData) := Id.run do
  let mut result := acc
  if let some name := setOptionName? stx then
    if let some root := forbiddenOptionRoot? name then
      result := result.push (stx,
        m!"Forbidden `set_option {root}.*`; fix the source instead of changing or suppressing the linter")
  if isNoLintAttribute stx then
    result := result.push (stx, m!"`@[nolint]` suppressions are forbidden; fix the declaration")
  for child in stx.getArgs do
    result := collectSuppressions child result
  return result

private def suppressionLinter : ModuleLinter where
  run commands := for command in commands do
    for (location, message) in collectSuppressions command #[] do logErrorAt location message

initialize addModuleLinter suppressionLinter

end ArkLib.LintStyle
