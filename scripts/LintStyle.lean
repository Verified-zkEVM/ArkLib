/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lake.CLI.Main
import ImportGraph.Imports.FromSource
import LintStyle.Checks
import Lean.Parser.Module

/-!
# ArkLib's Lean-native source linter

Run `lake exe lint-style`. The scope is the generated `ArkLib` umbrella, every ArkLib module it
imports, and every tracked `ArkLibTest` module. No linter exception file is read or supported.
-/

open Lean System System.FilePath
open ArkLib.LintStyle

private structure Config where
  github := false
  selfTestOnly := false

private def usage : String :=
  "Usage: lake exe lint-style [--github] [--self-test]\n" ++
  "  --github    emit GitHub workflow annotations\n" ++
  "  --self-test run deterministic scanner and policy tests only"

private def parseArgs (args : List String) : IO Config := do
  let mut config : Config := {}
  for arg in args do
    match arg with
    | "--github" => config := { config with github := true }
    | "--self-test" => config := { config with selfTestOnly := true }
    | "--help" | "-h" => IO.println usage; IO.Process.exit 0
    | other => throw <| IO.userError s!"unknown lint-style argument: {other}\n{usage}"
  return config

private def sourceLines (content : String) : Array String :=
  let normalized := content.replace "\r\n" "\n"
  let pieces := normalized.splitOn "\n"
  (if normalized.endsWith "\n" then pieces.dropLast else pieces).toArray

private def lintImports (path : FilePath) (content : String) : IO (Array Violation) := do
  let _ ← Lean.parseImports' content path.toString
  let inputCtx := Lean.Parser.mkInputContext content path.toString
  let (headerStx, _, _) ← Lean.Parser.parseHeader inputCtx
  let `(Parser.Module.header| $[module]? $[prelude]? $importsStx*) := headerStx
    | throw <| IO.userError s!"lint-style: could not inspect parsed imports in {path}"
  let mut result : Array Violation := #[]
  for importStx in importsStx do
    if let `(Parser.Module.import| $[public]? $[meta]? import $[all]? $moduleId) := importStx then
      if (path.toString == "ArkLib.lean" || path.toString.startsWith "ArkLib/") &&
          moduleId.getId.getRoot == `ArkLibTest then
        let line := inputCtx.fileMap.toPosition (moduleId.raw.getPos?.getD 0) |>.line
        result := result.push
          { code := "ERR_TEST_IMPORT", line := line,
            message := "Production modules must not import ArkLibTest" }
      if let some (code, message) := importViolation? moduleId.getId then
        let pos := moduleId.raw.getPos?.getD 0
        let line := inputCtx.fileMap.toPosition pos |>.line
        result := result.push { code := code, line := line, message := message }
  return result

private def runImportPositionSelfTest : IO Unit := do
  let testImport := "module\npublic meta import all ArkLibTest.Interaction.Example\n"
  for path in ["ArkLib.lean", "ArkLib/Interaction/Example.lean"] do
    let violations ← lintImports path testImport
    unless violations.any fun v => v.code == "ERR_TEST_IMPORT" && v.line == 2 do
      throw <| IO.userError "lint-style self-test failed: production imported tests"
  let testViolations ← lintImports "ArkLibTest/Interaction/Example.lean" testImport
  unless testViolations.isEmpty do
    throw <| IO.userError "lint-style self-test failed: tests may import other tests"
  let violations ← lintImports "fixture.lean" "/- Mathlib -/\nimport Mathlib\n"
  unless violations.any fun violation => violation.code == "ERR_ROOT_IMPORT" && violation.line == 2 do
    throw <| IO.userError "lint-style self-test failed: import diagnostics must use parser positions"
  let moduleViolations ← lintImports "module-fixture.lean"
    "module\n/- ArkLib -/\npublic meta import all «ArkLib»\n"
  unless moduleViolations.any fun violation =>
      violation.code == "ERR_ROOT_IMPORT" && violation.line == 3 do
    throw <| IO.userError
      "lint-style self-test failed: module-system import diagnostics must use parser positions"

private def formatViolation (github : Bool) (path : FilePath) (v : Violation) : String :=
  if github then
    s!"::error file={path},line={v.line},title={v.code}::{path}:{v.line} {v.code}: {v.message}"
  else
    s!"error: {path}:{v.line}: {v.code}: {v.message}"

private def modulePath (name : Name) : FilePath :=
  mkFilePath (name.components.map (·.toString)) |>.addExtension "lean"

private def arkLibPaths : IO (Array FilePath) := do
  let umbrella : FilePath := "ArkLib.lean"
  let imports ← findImportsFromSource umbrella
  let modules := imports.filter (·.getRoot == `ArkLib)
  if modules.isEmpty then
    throw <| IO.userError "lint-style: ArkLib.lean yielded no ArkLib modules"
  let modulePaths := modules.map modulePath
  let trackedOutput ← IO.Process.output { cmd := "git", args := #["ls-files", "--", "ArkLib"] }
  if trackedOutput.exitCode != 0 then
    throw <| IO.userError s!"git ls-files ArkLib failed: {trackedOutput.stderr}"
  let tracked := trackedOutput.stdout.splitOn "\n" |>.filter (·.endsWith ".lean")
  let closure := modulePaths.toList.map (·.toString)
  let missing := tracked.filter (!closure.contains ·)
  let untrackedByUmbrella := closure.filter (!tracked.contains ·)
  unless missing.isEmpty && untrackedByUmbrella.isEmpty do
    let details :=
      (missing.map (s!"tracked but absent from ArkLib.lean closure: {·}")) ++
      (untrackedByUmbrella.map (s!"in ArkLib.lean closure but not tracked: {·}"))
    throw <| IO.userError <| "lint-style scope is incomplete:\n" ++ "\n".intercalate details
  let testsOutput ← IO.Process.output { cmd := "git", args := #["ls-files", "--", "ArkLibTest"] }
  if testsOutput.exitCode != 0 then
    throw <| IO.userError s!"git ls-files ArkLibTest failed: {testsOutput.stderr}"
  let tests := testsOutput.stdout.splitOn "\n" |>.filter (·.endsWith ".lean")
  return #[umbrella] ++ modulePaths ++ tests.toArray.map FilePath.mk

private def repositoryHygiene (github : Bool) : IO Nat := do
  let output ← IO.Process.output { cmd := "git", args := #["ls-files", "--stage"] }
  if output.exitCode != 0 then
    throw <| IO.userError s!"git ls-files failed: {output.stderr}"
  let mut errors := 0
  let mut lowerPaths : Std.HashMap String String := {}
  for line in output.stdout.splitOn "\n" do
    let fields := line.splitOn "\t"
    if h : fields.length ≥ 2 then
      let metadata := fields[0]
      let path := fields[1]
      if path.endsWith ".lean" && metadata.startsWith "100755 " then
        IO.println <| formatViolation github path
          { code := "ERR_EXEC", line := 1, message := "Lean source files must not be executable" }
        errors := errors + 1
      let lower := path.toLower
      if let some previous := lowerPaths[lower]? then
        if previous != path then
          IO.println <| formatViolation github path
            { code := "ERR_CASE", line := 1,
              message := s!"Path differs from `{previous}` only by letter case" }
          errors := errors + 1
      else
        lowerPaths := lowerPaths.insert lower path
  return errors

private def lintRepository (config : Config) : IO UInt32 := do
  runSelfTests
  runImportPositionSelfTest
  if config.selfTestOnly then
    IO.println "lint-style self-tests passed"
    return 0
  let mut errorCount := 0
  for path in ← arkLibPaths do
    let content ← IO.FS.readFile path
    let lines := sourceLines content
    let mut violations := lintLines lines
    if content.contains "\r\n" then
      violations := violations.push
        { code := "ERR_WIN", line := 1, message := "Windows line endings; use LF" }
    if !content.endsWith "\n" then
      violations := violations.push
        { code := "ERR_EOF", line := max lines.size 1, message := "File must end with a newline" }
    violations := violations ++ (← lintImports path content)
    for v in violations do IO.println (formatViolation config.github path v)
    errorCount := errorCount + violations.size
  errorCount := errorCount + (← repositoryHygiene config.github)
  if errorCount == 0 then
    IO.println "Lean source style checks passed"
  else
    IO.eprintln s!"lint-style: found {errorCount} violation(s); no exceptions or suppressions are supported"
  return violationExitCode errorCount

/-- Entry point for `lake exe lint-style`. -/
def main (args : List String) : IO UInt32 := do
  lintRepository (← parseArgs args)
