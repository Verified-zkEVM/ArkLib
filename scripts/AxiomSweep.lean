/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Lean

/-!
# Axiom sweep: kernel-level axiom and `sorry` accounting

Walks the compiled environment (the same data the kernel checked) and computes, for every
declaration in `ArkLib.*` modules, the set of axioms its statement and proof ultimately
depend on — the same information as `#print axioms`, for the whole library at once.

Because this reads elaborated `.olean` data rather than source text, it sees exactly what
the kernel accepted: private declarations, macro-generated declarations, and instances are
all included, and no source-level heuristics are involved.

Modes (run after `lake build`):

```
lake exe axiomsweep                     # summary only
lake exe axiomsweep --out report.json   # also write the full per-declaration report
lake exe axiomsweep --check             # gate against scripts/axiom_baseline.json
lake exe axiomsweep --update-baseline   # rewrite the baseline from the current build
```

The committed baseline (`scripts/axiom_baseline.json`) records the currently-known
`sorryAx`-tainted declarations and any declarations depending on non-standard axioms
(anything beyond `propext`, `Classical.choice`, `Quot.sound`). `--check` fails exactly
when a declaration is tainted that the baseline does not cover, so it distinguishes
pre-existing gaps from new regressions. When gaps are closed, `--check` reports them and
stays green; run `--update-baseline` to shrink the file in the same PR.
-/

open Lean

namespace AxiomSweep

/-- Axioms that carry no extra trust assumptions beyond Lean's standard foundation. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Compute, for every constant reachable from the work list, the set of axioms it
transitively depends on, memoised across roots via `memo` (so sweeping thousands of
declarations shares one traversal of the environment).

`gray` marks constants whose dependencies are still being expanded. Cycles — which the
kernel only permits inside mutual inductive families, where no axioms hide — are broken by
treating back-edges as axiom-free. -/
partial def collect (env : Environment) (stack : List Name) (gray : Std.HashSet Name)
    (memo : Std.HashMap Name (Array Name)) : Std.HashMap Name (Array Name) :=
  match stack with
  | [] => memo
  | n :: rest =>
    if memo.contains n then
      collect env rest gray memo
    else match env.find? n with
      | none => collect env rest gray (memo.insert n #[])
      | some ci =>
        if ci matches .axiomInfo _ then
          collect env rest gray (memo.insert n #[n])
        else
          let deps := ci.getUsedConstantsAsSet.toList
          if gray.contains n then
            -- All children are memoised (or lie on a cycle): finalise this constant.
            let axs := deps.foldl (init := #[]) fun acc d =>
              match memo[d]? with
              | some as => as.foldl (init := acc) fun acc a =>
                  if acc.contains a then acc else acc.push a
              | none => acc
            collect env rest gray (memo.insert n axs)
          else
            let pending := deps.filter fun d => !memo.contains d && !gray.contains d
            collect env (pending ++ stack) (gray.insert n) memo

/-- One row of the per-declaration report. -/
structure Entry where
  name : String
  module : String
  kind : String
  line : Option Nat
  axioms : Array String
  deriving ToJson

/-- A declaration depending on axioms beyond the standard foundation (and `sorryAx`,
which is tracked separately). -/
structure NonstandardEntry where
  name : String
  axioms : Array String
  deriving FromJson, ToJson

/-- The committed regression baseline. -/
structure Baseline where
  «sorry» : Array String
  nonstandard : Array NonstandardEntry
  deriving FromJson, ToJson

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Whether to report a constant: skip compiler-internal auxiliaries (`_proof_*`,
`match_*`, equation lemmas, …), whose axiom footprint is inherited by their parent
declaration anyway, but keep `private` declarations (checked under their user-facing
name, since the `_private` mangling would otherwise look internal). -/
def isReportable (n : Name) : Bool :=
  !n.hasMacroScopes && !((privateToUserName? n).getD n).isInternalDetail

/-- Enumerate the reportable declarations of every module under `rootMod` and compute
their axiom closures. -/
def buildEntries (rootMod : Name) : CoreM (Array Entry × Nat) := do
  let env ← getEnv
  let mut targets : Array (Name × Name) := #[]
  let mut moduleCount := 0
  for (mname, mdata) in env.header.moduleNames.zip env.header.moduleData do
    if rootMod.isPrefixOf mname then
      moduleCount := moduleCount + 1
      for c in mdata.constNames do
        if isReportable c then
          targets := targets.push (c, mname)
  let memo := targets.foldl (init := ({} : Std.HashMap Name (Array Name)))
    fun memo (c, _) => collect env [c] {} memo
  let mut entries : Array Entry := #[]
  for (c, mname) in targets do
    let some ci := env.find? c | continue
    let line := (← findDeclarationRanges? c).map (·.range.pos.line)
    entries := entries.push {
      name := c.toString
      module := mname.toString
      kind := kindOf ci
      line := line
      axioms := ((memo[c]?.getD #[]).map toString).qsort (· < ·) }
  return (entries.qsort (fun a b => a.name < b.name), moduleCount)

def isStandard (a : String) : Bool :=
  standardAxioms.any (toString · == a)

def sorryAxName : String := "sorryAx"

/-- Non-standard axioms of an entry: everything beyond the standard foundation, with
`sorryAx` tracked separately. -/
def nonstandardOf (e : Entry) : Array String :=
  e.axioms.filter fun a => !isStandard a && a != sorryAxName

/-- Project the current build's taint sets into baseline form (deterministically
sorted, since `entries` is sorted by name). -/
def currentBaseline (entries : Array Entry) : Baseline where
  «sorry» := (entries.filter (·.axioms.contains sorryAxName)).map (·.name)
  nonstandard := entries.filterMap fun e =>
    let bad := nonstandardOf e
    if bad.isEmpty then none else some { name := e.name, axioms := bad }

/-- Compare the current taint sets against the committed baseline. Returns the exit
code: `1` iff there is a regression (new taint not covered by the baseline). -/
def runCheck (cur : Baseline) (basePath : String) : IO UInt32 := do
  if !(← System.FilePath.pathExists basePath) then
    IO.eprintln s!"axiomsweep: baseline {basePath} not found; \
      create it with `lake exe axiomsweep --update-baseline`"
    return 2
  let base ← match Json.parse (← IO.FS.readFile basePath) >>= fromJson? (α := Baseline) with
    | .ok b => pure b
    | .error e =>
      IO.eprintln s!"axiomsweep: cannot parse baseline {basePath}: {e}"
      return 2
  let newSorry := cur.«sorry».filter (!base.«sorry».contains ·)
  let fixedSorry := base.«sorry».filter (!cur.«sorry».contains ·)
  let newNonstd := cur.nonstandard.filter fun e =>
    match base.nonstandard.find? (·.name == e.name) with
    | none => true
    | some b => e.axioms.any (!b.axioms.contains ·)
  let fixedNonstd := base.nonstandard.filter fun b =>
    (cur.nonstandard.find? (·.name == b.name)).isNone
  let mut failed := false
  if !newSorry.isEmpty then
    failed := true
    IO.eprintln s!"axiomsweep: {newSorry.size} declaration(s) newly depend on sorryAx \
      (not in {basePath}):"
    for n in newSorry do IO.eprintln s!"  {n}"
  if !newNonstd.isEmpty then
    failed := true
    IO.eprintln s!"axiomsweep: {newNonstd.size} declaration(s) newly depend on \
      non-standard axioms (not in {basePath}):"
    for e in newNonstd do IO.eprintln s!"  {e.name} : {e.axioms}"
  if failed then
    IO.eprintln s!"axiomsweep: if intentional (new tagged sorry), refresh the baseline \
      with `lake exe axiomsweep --update-baseline` and commit the diff."
    return 1
  if !fixedSorry.isEmpty || !fixedNonstd.isEmpty then
    IO.println s!"axiomsweep: good news — {fixedSorry.size + fixedNonstd.size} baseline \
      entr(y/ies) no longer tainted; run `lake exe axiomsweep --update-baseline` to shrink \
      the baseline:"
    for n in fixedSorry do IO.println s!"  {n}"
    for e in fixedNonstd do IO.println s!"  {e.name}"
  IO.println "axiomsweep: check passed (no new axiom/sorry taint)."
  return 0

structure Config where
  root : Name := `ArkLib
  out? : Option String := none
  check : Bool := false
  update : Bool := false
  baseline : String := "scripts/axiom_baseline.json"

def parseArgs : List String → Config → Except String Config
  | [], cfg => .ok cfg
  | "--check" :: rest, cfg => parseArgs rest { cfg with check := true }
  | "--update-baseline" :: rest, cfg => parseArgs rest { cfg with update := true }
  | "--out" :: path :: rest, cfg => parseArgs rest { cfg with out? := some path }
  | "--baseline" :: path :: rest, cfg => parseArgs rest { cfg with baseline := path }
  | "--root" :: mod :: rest, cfg =>
    parseArgs rest { cfg with root := mod.toName }
  | arg :: _, _ => .error s!"axiomsweep: unknown or incomplete argument: {arg}\n\
      usage: lake exe axiomsweep [--out FILE] [--check] [--update-baseline] \
      [--baseline FILE] [--root MOD]"

end AxiomSweep

open AxiomSweep in
unsafe def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args {} with
    | .ok cfg => pure cfg
    | .error e => IO.eprintln e; return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{module := cfg.root}] {} (trustLevel := 1024) (loadExts := true)
  let ((entries, moduleCount), _) ← (buildEntries cfg.root).toIO
    { fileName := "<axiomsweep>", fileMap := default } { env }
  let cur := currentBaseline entries
  let distinctNonstd := cur.nonstandard.foldl (init := (#[] : Array String)) fun acc e =>
    e.axioms.foldl (init := acc) fun acc a => if acc.contains a then acc else acc.push a
  IO.println s!"axiomsweep: {entries.size} declarations across {moduleCount} modules \
    under {cfg.root}"
  IO.println s!"  sorryAx-tainted: {cur.«sorry».size}"
  IO.println s!"  non-standard-axiom-tainted: {cur.nonstandard.size} \
    (axioms: {distinctNonstd})"
  if let some out := cfg.out? then
    let report := Json.mkObj [
      ("root", toJson cfg.root.toString),
      ("declarationCount", toJson entries.size),
      ("declarations", toJson entries)]
    IO.FS.writeFile out (report.pretty ++ "\n")
    IO.println s!"axiomsweep: wrote report to {out}"
  if cfg.update then
    IO.FS.writeFile cfg.baseline ((toJson cur).pretty ++ "\n")
    IO.println s!"axiomsweep: wrote baseline to {cfg.baseline}"
    return 0
  if cfg.check then
    return (← runCheck cur cfg.baseline)
  return 0
