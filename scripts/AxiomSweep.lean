/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import Lean

/-!
# Axiom sweep: whole-library kernel-level axiom and `sorry` accounting

Walks the compiled environment (the same data the kernel checked) and computes, for every
declaration in `ArkLib.*` modules, the set of axioms its statement and proof ultimately
depend on — the same information as `#print axioms`, for the whole library at once.

Because this reads elaborated `.olean` data rather than source text, it sees exactly what
the kernel accepted: private declarations and instances are reported, compiler-generated
auxiliaries are traversed (their taint surfaces on the parent declaration), and no
source-level heuristics are involved. The sweep covers what the root modules transitively
import — pair it with the repo's import-completeness gate so every
source file is actually in scope; an unimported file is invisible to any kernel-level
census.

Known blind spots, shared with `#print axioms` (all environment-walking tools):
* structure-field **default values** and autoparams (`:= by sorry`) are re-elaborated at
  each use site and attach to no swept constant of the defining module;
* `example`s never enter the environment;
* files not transitively imported by the swept roots are invisible (pair with the repo's
  import-completeness gate).
A source-level `sorry` grep is the complementary check for the first two.

Modes (run after `lake build`):

```
lake exe axiomsweep                     # summary only
lake exe axiomsweep --out report.json   # also write the full per-declaration report
lake exe axiomsweep --check             # gate against scripts/axiom_baseline.json
lake exe axiomsweep --update-baseline   # rewrite the baseline from the current build
```

The committed baseline (`scripts/axiom_baseline.json`) records the currently-known
`sorryAx`-tainted declarations and any declarations depending on non-standard axioms
(anything beyond `propext`, `Classical.choice`, `Quot.sound` — so native trust axioms
surface here too: `native_decide`-style tactics mint per-declaration
`…._native.<tactic>.ax_<number>_<number>` axioms, recorded under their owning
declaration). `--check` fails exactly when a declaration is tainted that the baseline
does not cover. When gaps are closed, `--check` reports them and stays green; run
`--update-baseline` to shrink the file in the same PR.

The baseline is an allowlist for `sorryAx` debt only. Native trust is held to PolyFun's
zero-debt rule instead: `neverAllowlistable` rejects any `._native.` axiom outside the
explicit `grandfatheredNativeTrust` list, so no baseline edit can widen the trusted
computing base. Exit codes are a contract with CI — `1` is a taint verdict, anything else
an infrastructure failure — which is why `main` traps uncaught exceptions into `2`.

`scripts/test-axiomsweep.sh` exercises all of this against the `AxiomSweepTestFixtures`
library, whose fixtures carry synthetic taint of each shape this file reasons about.
-/

open Lean

namespace AxiomSweep

/-- Root modules swept when no `--root` is given. -/
def defaultRoots : Array Name := #[`ArkLib]

/-- Axioms that carry no extra trust assumptions beyond Lean's standard foundation. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `a` names native-compiler trust: either a bare compiler axiom, or one of the
per-declaration axioms `native_decide`-style tactics mint, which this toolchain names
`Owner._native.<tactic>.ax_<n>_<n>` rather than routing through `Lean.ofReduceBool`. -/
def isNativeTrust (a : String) : Bool :=
  a == "Lean.ofReduceBool" || a == "Lean.trustCompiler" || (a.splitOn "._native.").length > 1

/-- The native trust this repository has already accepted, listed by full axiom name so
any acceptance is auditable in source rather than hidden in a JSON allowlist. ArkLib has
accepted none: the list is empty, and the floor below keeps it that way unless an entry
is consciously added here.

Fails closed: if a private-name index or module path shifts, an entry stops matching and
`--check` goes red until someone consciously re-accepts it. -/
def grandfatheredNativeTrust : List String := []

/-- Axioms that may never be baselined: native-compiler trust beyond what
`grandfatheredNativeTrust` already accepts. Unlike `sorryAx` debt — honest work in
progress, which the baseline is allowed to track — new native trust is a widening of the
trusted computing base, so no baseline edit can green it; remove the dependency instead.

This is the counterpart of PolyFun's zero-debt gate. PolyFun refuses a nonempty baseline
outright; ArkLib cannot, since it carries genuine `sorryAx` debt, so the floor applies the
same "cannot pre-authorize future taint" rule to the part of the baseline where widening
the TCB is at stake. -/
def neverAllowlistable (a : String) : Bool :=
  isNativeTrust a && !grandfatheredNativeTrust.contains a

/-- Phase 1: DFS. Compute, for every constant reachable from the work list, an
under-approximation of the set of axioms it transitively depends on, memoised across
roots via `memo`. Also records the finalisation order — a topological order of the
dependency graph except inside mutual-inductive cycles.

`gray` marks constants whose dependencies are still being expanded. Back-edges (cycles,
which the kernel only permits inside mutual inductive families) contribute nothing in
this phase; `repair` below propagates to the true fixpoint. An axiom contributes itself
plus anything reachable through its *type* (matching Lean's own `CollectAxioms`). -/
partial def collect (env : Environment) (stack : List Name) (gray : Std.HashSet Name)
    (memo : Std.HashMap Name (Array Name)) (order : Array Name) :
    Std.HashMap Name (Array Name) × Array Name :=
  match stack with
  | [] => (memo, order)
  | n :: rest =>
    if memo.contains n then
      collect env rest gray memo order
    else match env.find? n with
      | none => collect env rest gray (memo.insert n #[]) order
      | some ci =>
        let deps := ci.getUsedConstantsAsSet.toList
        if gray.contains n then
          let seed : Array Name := if ci matches .axiomInfo _ then #[n] else #[]
          let axs := deps.foldl (init := seed) fun acc d =>
            match memo[d]? with
            | some as => as.foldl (init := acc) fun acc a =>
                if acc.contains a then acc else acc.push a
            | none => acc
          collect env rest gray (memo.insert n axs) (order.push n)
        else
          let pending := deps.filter fun d => !memo.contains d && !gray.contains d
          collect env (pending ++ stack) (gray.insert n) memo order

/-- Phase 2: propagate to fixpoint. The DFS under-approximates inside mutual-inductive
cycles (a member's taint may not reach its siblings), and — because `memo` persists
across roots — anything finalised after reading such a member inherits the error.
Re-deriving every set in finalisation order until nothing changes computes the least
fixpoint of the closure equations: the true kernel-level axiom dependency set. This is
strictly more accurate than `#print axioms`, whose `CollectAxioms` has the same
mutual-family blind spot this phase repairs. Sets grow monotonically and are bounded,
so termination is immediate; in practice one or two passes suffice. -/
partial def repair (env : Environment) (order : Array Name)
    (memo : Std.HashMap Name (Array Name)) : Std.HashMap Name (Array Name) :=
  let (memo', changed) := order.foldl (init := (memo, false)) fun (memo, changed) n =>
    match env.find? n with
    | none => (memo, changed)
    | some ci =>
      let deps := ci.getUsedConstantsAsSet.toList
      let seed : Array Name := if ci matches .axiomInfo _ then #[n] else #[]
      let axs := deps.foldl (init := seed) fun acc d =>
        match memo[d]? with
        | some as => as.foldl (init := acc) fun acc a =>
            if acc.contains a then acc else acc.push a
        | none => acc
      let old := (memo[n]?.getD #[]).size
      if axs.size == old then (memo, changed)
      else (memo.insert n axs, true)
  if changed then repair env order memo' else memo'

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

/-- Whether `s` is a nonempty string of ASCII decimal digits. -/
def isDecimal (s : String) : Bool :=
  !s.isEmpty && s.toList.all fun c => '0' ≤ c && c ≤ '9'

/-- Collapse exactly the generated counter suffix of native trust axioms
(`Foo._native.native_decide.ax_1_1` → `Foo._native.native_decide`), so baselines key by
owning declaration rather than a rebuild-volatile counter. Names that merely contain
`._native.` or resemble a generated suffix are preserved: collapsing them would let two
distinct axioms share one baseline key, so real taint could hide behind an accepted
entry. -/
def normalizeAxiomName (s : String) : String :=
  match s.splitOn "._native." with
  | [owner, tail] =>
    match tail.splitOn "." with
    | [tactic, counter] =>
      match counter.splitOn "_" with
      | ["ax", major, minor] =>
        if !owner.isEmpty && !tactic.isEmpty && isDecimal major && isDecimal minor then
          owner ++ "._native." ++ tactic
        else
          s
      | _ => s
    | _ => s
  | _ => s

/-- Sort and deduplicate (normalisation can identify adjacent names). -/
def dedupSort (a : Array String) : Array String :=
  (a.qsort (· < ·)).foldl (init := #[]) fun acc x =>
    if acc.back? == some x then acc else acc.push x

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
`match_*`, numbered equation lemmas, …), whose axiom footprint is inherited by their
parent declaration, but keep `private` declarations (checked under their user-facing
name, since the `_private` mangling would otherwise look internal). On-demand aux
lemmas with symbolic names (`.eq_def`, `.congr_simp`) are reported. -/
def isReportable (n : Name) : Bool :=
  !n.hasMacroScopes && !((privateToUserName? n).getD n).isInternalDetail

/-- Enumerate the reportable declarations of every module under one of `roots` and
compute their axiom closures. -/
def buildEntries (roots : Array Name) : CoreM (Array Entry × Nat) := do
  let env ← getEnv
  let mut targets : Array (Name × Name) := #[]
  let mut seen : Std.HashSet Name := {}
  let mut moduleCount := 0
  for (mname, mdata) in env.header.moduleNames.zip env.header.moduleData do
    if roots.any (·.isPrefixOf mname) then
      moduleCount := moduleCount + 1
      for c in mdata.constNames do
        -- A realised constant (e.g. `.congr_simp`) can appear in several modules'
        -- `constNames`; report it once, under the first module that carries it.
        if isReportable c && !seen.contains c then
          seen := seen.insert c
          targets := targets.push (c, mname)
  let (memo0, order) :=
    targets.foldl (init := (({} : Std.HashMap Name (Array Name)), (#[] : Array Name)))
      fun (memo, order) (c, _) => collect env [c] {} memo order
  let memo := repair env order memo0
  let mut entries : Array Entry := #[]
  for (c, mname) in targets do
    let some ci := env.find? c | continue
    let line := (← findDeclarationRanges? c).map (·.range.pos.line)
    entries := entries.push {
      name := c.toString
      module := mname.toString
      kind := kindOf ci
      line := line
      axioms := dedupSort ((memo[c]?.getD #[]).map (normalizeAxiomName ·.toString)) }
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
    match cur.nonstandard.find? (·.name == b.name) with
    | none => true
    | some c => b.axioms.any (!c.axioms.contains ·)
  let mut failed := false
  let floor := cur.nonstandard.filter fun e => e.axioms.any neverAllowlistable
  if !floor.isEmpty then
    failed := true
    IO.eprintln s!"axiomsweep: {floor.size} declaration(s) depend on never-allowlistable \
      axioms (bare native-compiler trust) — the baseline cannot green these:"
    for e in floor do IO.eprintln s!"  {e.name} : {e.axioms.filter neverAllowlistable}"
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

/-- Rewrite the baseline from the current build. Refuses while never-allowlistable taint
is present: `--check` would reject the result anyway (the floor is enforced there, not
here), so writing it would only produce a baseline that looks authoritative and is not.
Recording new `sorryAx` debt is fine — that is what the baseline is for. -/
def runUpdate (cur : Baseline) (basePath : String) : IO UInt32 := do
  let floor := cur.nonstandard.filter fun e => e.axioms.any neverAllowlistable
  if !floor.isEmpty then
    IO.eprintln s!"axiomsweep: refusing to update {basePath} while \
      {floor.size} declaration(s) depend on never-allowlistable axioms:"
    for e in floor do IO.eprintln s!"  {e.name} : {e.axioms.filter neverAllowlistable}"
    IO.eprintln "axiomsweep: remove the dependency; the baseline cannot pre-authorize it."
    return 1
  IO.FS.writeFile basePath ((toJson cur).pretty ++ "\n")
  IO.println s!"axiomsweep: wrote baseline to {basePath}"
  return 0

structure Config where
  roots : Array Name := #[]
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
    parseArgs rest { cfg with roots := cfg.roots.push mod.toName }
  | arg :: _, _ => .error s!"axiomsweep: unknown or incomplete argument: {arg}\n\
      usage: lake exe axiomsweep [--out FILE] [--check] [--update-baseline] \
      [--baseline FILE] [--root MOD]*\n      (--check and --update-baseline are mutually exclusive)"

end AxiomSweep

open AxiomSweep in
/-- Tool body. Exit codes are a contract with CI, which reads `1` as a taint verdict and
anything else as an infrastructure failure; `main` wraps this so an uncaught exception
cannot masquerade as the former. -/
unsafe def run (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args {} with
    | .ok cfg => pure cfg
    | .error e => IO.eprintln e; return 2
  if cfg.check && cfg.update then
    IO.eprintln "axiomsweep: --check and --update-baseline are mutually exclusive"
    return 2
  let roots := if cfg.roots.isEmpty then defaultRoots else cfg.roots
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← try
      importModules (roots.map ({ module := · })) {} (trustLevel := 1024)
        (loadExts := true)
    catch e =>
      IO.eprintln s!"axiomsweep: cannot import root modules {roots}: {e.toString}\n\
        (roots must be importable modules — glob-based libs without an umbrella \
        module cannot be swept by library name)"
      return (2 : UInt32)
  let ((entries, moduleCount), _) ← (buildEntries roots).toIO
    { fileName := "<axiomsweep>", fileMap := default } { env }
  let cur := currentBaseline entries
  let distinctNonstd := cur.nonstandard.foldl (init := (#[] : Array String)) fun acc e =>
    e.axioms.foldl (init := acc) fun acc a => if acc.contains a then acc else acc.push a
  IO.println s!"axiomsweep: {entries.size} declarations across {moduleCount} modules \
    under {roots}"
  IO.println s!"  sorryAx-tainted: {cur.«sorry».size}"
  IO.println s!"  non-standard-axiom-tainted: {cur.nonstandard.size} \
    (axioms: {distinctNonstd})"
  if let some out := cfg.out? then
    let report := Json.mkObj [
      ("roots", toJson (roots.map (·.toString))),
      ("declarationCount", toJson entries.size),
      ("declarations", toJson entries)]
    IO.FS.writeFile out (report.pretty ++ "\n")
    IO.println s!"axiomsweep: wrote report to {out}"
  if cfg.update then
    return (← runUpdate cur cfg.baseline)
  if cfg.check then
    return (← runCheck cur cfg.baseline)
  return 0

open AxiomSweep in
unsafe def main (args : List String) : IO UInt32 := do
  try
    run args
  catch e =>
    IO.eprintln s!"axiomsweep: internal error: {e}"
    return 2
