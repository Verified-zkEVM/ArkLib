/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean.Elab.Command
import LintStyle.OracleProtocolPolicy

/-!
# ArkLib build-time source-policy plugin

This plugin rejects linter suppressions except the authorized oracle protocol alias command,
and rejects retired probability notation in each ArkLib module. Inspecting the syntax tree matters: terms inside extensible interpolated strings are active syntax,
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

private def retiredProbabilityToken? : Syntax → Option String
  | .atom _ token =>
    if token == "$ᵖ" || token.startsWith "Pr_{" || token.startsWith "Pr[" ||
        token.startsWith "𝒮[" then some token else none
  | _ => none

private partial def collectSuppressions (stx : Syntax) (acc : Array (Syntax × MessageData)) :
    Array (Syntax × MessageData) := Id.run do
  let mut result := acc
  if let some token := retiredProbabilityToken? stx then
    result := result.push (stx,
      m!"Retired probability notation `{token}`; use native event probabilities, measures, and uniform sampling")
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
  run commands := do
    let authorizedSource := "\n".intercalate oracleProtocolAliasLines.toList
    let env ← getEnv
    let authorizedModule := env.mainModule.toString == oracleProtocolModule &&
      env.contains `Interaction.Core.OracleProtocol
    let authorizedCommands := commands.filter fun command =>
      authorizedModule && command.reprint.any (·.trimAscii.toString == authorizedSource)
    for command in commands do
      -- Accept only one complete alias command, never a surrounding section or term.
      if authorizedCommands.size == 1 && authorizedCommands.contains command then continue
      for (location, message) in collectSuppressions command #[] do logErrorAt location message

initialize addModuleLinter suppressionLinter

end ArkLib.LintStyle
