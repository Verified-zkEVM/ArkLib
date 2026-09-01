/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lake.CLI.Main
import ImportGraph.Imports.FromSource
import LintStyle.Checks

/-!
# ArkLib's Lean-native source linter

Run `lake exe lint-style`. The default scope is the generated `ArkLib` umbrella and every ArkLib
module it imports. No linter exception file is read or supported.
-/

open Lean System System.FilePath
open ArkLib.LintStyle

private structure Config where
  github := false
  fix := false
  selfTestOnly := false

private def usage : String :=
  "Usage: lake exe lint-style [--github] [--fix] [--self-test]\n" ++
  "  --github    emit GitHub workflow annotations\n" ++
  "  --fix       apply safe whitespace-only fixes (the command still reports violations)\n" ++
  "  --self-test run deterministic scanner and policy tests only"

private def parseArgs (args : List String) : IO Config := do
  let mut config : Config := {}
  for arg in args do
    match arg with
    | "--github" => config := { config with github := true }
    | "--fix" => config := { config with fix := true }
    | "--self-test" => config := { config with selfTestOnly := true }
    | "--help" | "-h" => IO.println usage; IO.Process.exit 0
    | other => throw <| IO.userError s!"unknown lint-style argument: {other}\n{usage}"
  return config

private def sourceLines (content : String) : Array String :=
  let normalized := content.replace "\r\n" "\n"
  let pieces := normalized.splitOn "\n"
  (if normalized.endsWith "\n" then pieces.dropLast else pieces).toArray

private def importLine (lines : Array String) (name : Name) : Nat := Id.run do
  let needle := name.toString
  for h : i in [:lines.size] do
    if lines[i].contains needle then return i + 1
  return 1

private def lintImports (path : FilePath) (content : String) (lines : Array String) :
    IO (Array Violation) := do
  let header ← Lean.parseImports' content path.toString
  let mut result := #[]
  for imp in header.imports do
    if let some (code, message) := importViolation? imp.module then
      result := result.push { code, line := importLine lines imp.module, message }
  return result

private def safeFix (content : String) : String :=
  let normalized := content.replace "\r\n" "\n"
  let lines := normalized.splitOn "\n" |>.map fun line =>
    line.trimAsciiEnd.toString
  let joined := "\n".intercalate lines
  if joined.endsWith "\n" then joined else joined ++ "\n"

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
  return #[umbrella] ++ modules.map modulePath

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
    violations := violations ++ (← lintImports path content lines)
    for v in violations do IO.println (formatViolation config.github path v)
    errorCount := errorCount + violations.size
    if config.fix && safeFix content != content then IO.FS.writeFile path (safeFix content)
  errorCount := errorCount + (← repositoryHygiene config.github)
  if errorCount == 0 then
    IO.println "Lean source style checks passed"
  else
    IO.eprintln s!"lint-style: found {errorCount} violation(s); no exceptions or suppressions are supported"
  if config.fix then return 0 else return (min errorCount 125).toUInt32

/-- Entry point for `lake exe lint-style`. -/
def main (args : List String) : IO UInt32 := do
  lintRepository (← parseArgs args)
