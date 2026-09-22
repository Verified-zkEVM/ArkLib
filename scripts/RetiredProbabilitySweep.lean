/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Lean

/-!
# Retired-probability sweep: the native-measure conversion ledger

Walks the compiled environment and reports every declaration in `ArkLib.*` modules whose
statement or body *directly* references a retiring probability surface: VCVio's scalar
evaluation functions and compatibility classes (`probOutput`, `probEvent`, `probFailure`,
`evalSPMF`, `SPMF`, `NeverFail`, `EvalDistCompatible`, `DiscreteEvalDistCompatible`), the
PMF-based oracle specifications (`OracleSpec.IsUniformSpec`, `OracleSpec.IsProbabilitySpec`,
`PFunctor.IsProbabilitySpec`), and Mathlib's `PMF`. VCVio tracks the same family with its
`usesRetiredProbability` environment linter; ArkLib does not run environment linters in its
validation gate and its own PMF notation emits no deprecation warning, so this executable is the
repository's measure of conversion debt.

The check is direct rather than transitive: a declaration is reported only if one of its own
constants is retired, not because a dependency is. That is the semantic dependency the
conversion removes declaration by declaration.

Modes (run after `lake build`):

```
lake exe retiredsweep                     # summary and per-namespace counts
lake exe retiredsweep --require-empty     # mandatory gate, no baseline exceptions
lake exe retiredsweep --check             # historical migration gate against scripts/retired_probability_baseline.json
lake exe retiredsweep --update-baseline   # rewrite the baseline from the current build
```

`--check` fails exactly when a declaration is reported that the baseline does not cover, so
the ledger can only shrink; `--update-baseline` refuses to grow it. When the ledger is empty,
delete the baseline file and this gate is complete.
-/

open Lean

namespace RetiredProbabilitySweep

/-- Root modules swept when no `--root` is given. -/
def defaultRoots : Array Name := #[`ArkLib]

/-- Retired name prefixes. Prefix matching is on full dotted names (`PMF.map`, `SPMF.bind`,
`NeverFail.mk`, …); unqualified retired names also match an entire component. A theorem name such
as `OptionT.probEvent_liftM` is not itself matched by its spelling: the scan checks direct retired
constants in the declaration's type and body, not transitive dependencies of referenced lemmas. -/
def retiredNames : List Name :=
  [`PMF, `SPMF, `evalSPMF, `probOutput, `probEvent, `probFailure, `NeverFail,
    `EvalDistCompatible, `DiscreteEvalDistCompatible, `OracleSpec.IsUniformSpec,
    `OracleSpec.IsProbabilitySpec, `PFunctor.IsProbabilitySpec, `IsUniformSpec,
    `IsProbabilitySpec, `PMF.uniformOfFintype]

/-- Whether a constant name belongs to the retiring surface: some component of the name is a
retired head name, or a retired qualified name is a prefix. -/
def isRetired (n : Name) : Bool :=
  retiredNames.any fun r =>
    r.isPrefixOf n || (r.components.length == 1 && n.components.any (· == r))

/-- Whether to report a constant: skip compiler-internal auxiliaries, keep `private`
declarations under their user-facing name. -/
def isReportable (n : Name) : Bool :=
  !n.hasMacroScopes && !((privateToUserName? n).getD n).isInternalDetail

structure Entry where
  name : String
  module : String
  retired : Array String
  deriving ToJson, FromJson

structure Baseline where
  retired : Array String
  deriving ToJson, FromJson

def dedupSort (a : Array String) : Array String :=
  (a.qsort (· < ·)).foldl (init := #[]) fun acc x =>
    if acc.back? == some x then acc else acc.push x

/-- Enumerate the reportable declarations of every module under one of `roots` and record the
retired constants each directly uses. -/
def buildEntries (roots : Array Name) : CoreM (Array Entry × Nat) := do
  let env ← getEnv
  let mut entries : Array Entry := #[]
  let mut seen : Std.HashSet Name := {}
  let mut moduleCount := 0
  for (mname, mdata) in env.header.moduleNames.zip env.header.moduleData do
    if roots.any (·.isPrefixOf mname) then
      moduleCount := moduleCount + 1
      for c in mdata.constNames do
        if isReportable c && !seen.contains c then
          seen := seen.insert c
          let some ci := env.find? c | continue
          let used := ci.getUsedConstantsAsSet.toList.filter isRetired
          if !used.isEmpty then
            entries := entries.push {
              name := ((privateToUserName? c).getD c).toString
              module := mname.toString
              retired := dedupSort (used.map (·.toString)).toArray }
  return (entries.qsort (fun a b => a.name < b.name), moduleCount)

def currentBaseline (entries : Array Entry) : Baseline where
  retired := dedupSort (entries.map (·.name))

/-- Compare against the committed baseline. Exit `1` iff a reported declaration is not covered. -/
def runCheck (cur : Baseline) (basePath : String) : IO UInt32 := do
  if !(← System.FilePath.pathExists basePath) then
    if cur.retired.isEmpty then
      IO.println "retiredsweep: no baseline and no retired-probability uses — ledger is empty."
      return 0
    IO.eprintln s!"retiredsweep: baseline {basePath} not found; \
      create it with `lake exe retiredsweep --update-baseline`"
    return 2
  let base ← match Json.parse (← IO.FS.readFile basePath) >>= fromJson? (α := Baseline) with
    | .ok b => pure b
    | .error e =>
      IO.eprintln s!"retiredsweep: cannot parse baseline {basePath}: {e}"
      return 2
  let newUses := cur.retired.filter (!base.retired.contains ·)
  let converted := base.retired.filter (!cur.retired.contains ·)
  if !newUses.isEmpty then
    IO.eprintln s!"retiredsweep: {newUses.size} declaration(s) newly use the retiring \
      probability surface (not in {basePath}); state them with the native measure API instead:"
    for n in newUses do IO.eprintln s!"  {n}"
    return 1
  if !converted.isEmpty then
    IO.println s!"retiredsweep: {converted.size} baseline entr(y/ies) converted; run \
      `lake exe retiredsweep --update-baseline` to shrink the ledger:"
    for n in converted do IO.println s!"  {n}"
  IO.println s!"retiredsweep: check passed ({cur.retired.size} outstanding, \
    baseline {base.retired.size})."
  return 0

/-- Rewrite the baseline from the current build; refuses to grow it. -/
def runUpdate (cur : Baseline) (basePath : String) : IO UInt32 := do
  if ← System.FilePath.pathExists basePath then
    match Json.parse (← IO.FS.readFile basePath) >>= fromJson? (α := Baseline) with
    | .ok base =>
      let newUses := cur.retired.filter (!base.retired.contains ·)
      if !newUses.isEmpty then
        IO.eprintln s!"retiredsweep: refusing to grow {basePath} by {newUses.size} entr(y/ies):"
        for n in newUses do IO.eprintln s!"  {n}"
        return 1
    | .error _ => pure ()
  if cur.retired.isEmpty then
    if ← System.FilePath.pathExists basePath then
      IO.FS.removeFile basePath
    IO.println s!"retiredsweep: ledger empty; removed {basePath}"
    return 0
  IO.FS.writeFile basePath ((toJson cur).pretty ++ "\n")
  IO.println s!"retiredsweep: wrote baseline to {basePath} ({cur.retired.size} entries)"
  return 0

structure Config where
  roots : Array Name := #[]
  out? : Option String := none
  requireEmpty : Bool := false
  check : Bool := false
  update : Bool := false
  baseline : String := "scripts/retired_probability_baseline.json"

def parseArgs : List String → Config → Except String Config
  | [], cfg => .ok cfg
  | "--require-empty" :: rest, cfg => parseArgs rest { cfg with requireEmpty := true }
  | "--check" :: rest, cfg => parseArgs rest { cfg with check := true }
  | "--update-baseline" :: rest, cfg => parseArgs rest { cfg with update := true }
  | "--out" :: path :: rest, cfg => parseArgs rest { cfg with out? := some path }
  | "--baseline" :: path :: rest, cfg => parseArgs rest { cfg with baseline := path }
  | "--root" :: mod :: rest, cfg =>
    parseArgs rest { cfg with roots := cfg.roots.push mod.toName }
  | arg :: _, _ => .error s!"retiredsweep: unknown or incomplete argument: {arg}\n\
      usage: lake exe retiredsweep [--out FILE] [--require-empty] [--check] [--update-baseline] \
      [--baseline FILE] [--root MOD]*"

/-- Per-namespace counts (first component of the declaration name). -/
def namespaceCounts (entries : Array Entry) : Array (String × Nat) :=
  let counts := entries.foldl (init := (∅ : Std.HashMap String Nat)) fun acc e =>
    let head := (e.name.splitOn ".").headD e.name
    acc.insert head (acc.getD head 0 + 1)
  (counts.toArray.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1))

end RetiredProbabilitySweep

open RetiredProbabilitySweep in
unsafe def run (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args {} with
    | .ok cfg => pure cfg
    | .error e => IO.eprintln e; return 2
  if cfg.requireEmpty && (cfg.check || cfg.update) then
    IO.eprintln "retiredsweep: --require-empty cannot be combined with baseline modes"
    return 2
  if cfg.check && cfg.update then
    IO.eprintln "retiredsweep: --check and --update-baseline are mutually exclusive"
    return 2
  let roots := if cfg.roots.isEmpty then defaultRoots else cfg.roots
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← try
      importModules (roots.map ({ module := · })) {} (trustLevel := 1024)
        (loadExts := true)
    catch e =>
      IO.eprintln s!"retiredsweep: cannot import root modules {roots}: {e.toString}"
      return (2 : UInt32)
  let ((entries, moduleCount), _) ← (buildEntries roots).toIO
    { fileName := "<retiredsweep>", fileMap := default } { env }
  let cur := currentBaseline entries
  IO.println s!"retiredsweep: {entries.size} declaration(s) across {moduleCount} modules \
    under {roots} use the retiring probability surface"
  for (ns, k) in (namespaceCounts entries).extract 0 12 do
    IO.println s!"  {ns}: {k}"
  if let some out := cfg.out? then
    let report := Json.mkObj [
      ("roots", toJson (roots.map (·.toString))),
      ("declarationCount", toJson entries.size),
      ("declarations", toJson entries)]
    IO.FS.writeFile out (report.pretty ++ "\n")
    IO.println s!"retiredsweep: wrote report to {out}"
  if cfg.requireEmpty then
    if entries.isEmpty then
      IO.println "retiredsweep: native probability retirement complete; no retired uses."
      return 0
    for entry in entries do
      IO.eprintln s!"  {entry.module}: {entry.name}: {entry.retired}"
    IO.eprintln "retiredsweep: retired probability references are forbidden; no baseline applies."
    return 1
  if cfg.update then
    return (← runUpdate cur cfg.baseline)
  if cfg.check then
    return (← runCheck cur cfg.baseline)
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  try
    run args
  catch e =>
    IO.eprintln s!"retiredsweep: internal error: {e}"
    return 2
