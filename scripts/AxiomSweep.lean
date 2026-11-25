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
lake exe axiomsweep --check             # fail on any sorry or non-standard axiom
```

`--check` is a zero-debt gate: it fails when any swept declaration depends on an axiom
beyond `propext`, `Classical.choice` and `Quot.sound`. That covers `sorryAx` and native
trust: `native_decide`-style tactics mint per-declaration
`…._native.<tactic>.ax_<number>_<number>` axioms, which the report records under their
owning declaration. There is no allowlist. A result that still needs a `sorry` starts as an
issue and merges once it is proved. CI relies on the exit codes: `1` means a
taint verdict and anything else an infrastructure failure. That is why `main` turns uncaught
exceptions into exit code `2`.

`scripts/test-axiomsweep.sh` exercises all of this against the `AxiomSweepTestFixtures`
library, whose fixtures carry synthetic taint of each shape this file reasons about.
-/

open Lean

namespace AxiomSweep

/-- Root modules swept when no `--root` is given. -/
def defaultRoots : Array Name := #[`ArkLib]

/-- Axioms that carry no extra trust assumptions beyond Lean's standard foundation. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Phase 1: DFS. Compute, for every constant reachable from the work list, an
under-approximation of the set of axioms it transitively depends on, memoised across
roots via `memo`. Also records the finalisation order — a topological order of the
dependency graph except inside mutual-inductive cycles.

`gray` marks constants whose dependencies are still being expanded. Back-edges (cycles,
which the kernel only permits inside mutual inductive families) contribute nothing in
this phase; `repair` below propagates to the true fixpoint. Axioms contribute themselves,
and their types are still traversed, matching Lean's own `CollectAxioms`. -/
partial def collect (env : Environment) (stack : List Name)
    (gray : Std.HashSet Name) (memo : Std.HashMap Name (Array Name)) (order : Array Name) :
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
fixpoint of the closure equations for axioms. This is
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

/-- Whether `s` is a nonempty string of ASCII decimal digits. -/
def isDecimal (s : String) : Bool :=
  !s.isEmpty && s.toList.all fun c => '0' ≤ c && c ≤ '9'

/-- Collapse exactly the generated counter suffix of native trust axioms
(`Foo._native.native_decide.ax_1_1` → `Foo._native.native_decide`), so the report names
the owning declaration rather than a rebuild-volatile counter. Names that merely contain
`._native.` or resemble a generated suffix are preserved, so two distinct axioms never
share one report name. -/
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

/-- Axioms of an entry beyond the standard foundation, `sorryAx` included. -/
def nonstandardOf (e : Entry) : Array String :=
  e.axioms.filter (!isStandard ·)

/-- The zero-debt gate. Returns the exit code: `1` iff some declaration depends on
`sorryAx` or on another axiom beyond the standard foundation. -/
def runCheck (entries : Array Entry) : IO UInt32 := do
  let tainted := entries.filter fun e => !(nonstandardOf e).isEmpty
  if tainted.isEmpty then
    IO.println "axiomsweep: check passed (no sorry or non-standard axioms)."
    return 0
  IO.eprintln s!"axiomsweep: {tainted.size} declaration(s) depend on sorryAx or on \
    non-standard axioms:"
  for e in tainted do IO.eprintln s!"  {e.name} : {nonstandardOf e}"
  IO.eprintln "axiomsweep: prove these or remove the dependency. ArkLib merges no sorry \
    and no axiom beyond propext, Classical.choice and Quot.sound."
  return 1

structure Config where
  roots : Array Name := #[]
  out? : Option String := none
  check : Bool := false

def parseArgs : List String → Config → Except String Config
  | [], cfg => .ok cfg
  | "--check" :: rest, cfg => parseArgs rest { cfg with check := true }
  | "--out" :: path :: rest, cfg => parseArgs rest { cfg with out? := some path }
  | "--root" :: mod :: rest, cfg =>
    parseArgs rest { cfg with roots := cfg.roots.push mod.toName }
  | arg :: _, _ => .error s!"axiomsweep: unknown or incomplete argument: {arg}\n\
      usage: lake exe axiomsweep [--out FILE] [--check] [--root MOD]*"

end AxiomSweep

open AxiomSweep in
/-- Tool body. Exit codes are a contract with CI, which reads `1` as a taint verdict and
anything else as an infrastructure failure; `main` wraps this so an uncaught exception
cannot masquerade as the former. -/
unsafe def run (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args {} with
    | .ok cfg => pure cfg
    | .error e => IO.eprintln e; return 2
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
  let sorryCount := (entries.filter (·.axioms.contains sorryAxName)).size
  let others := entries.filter fun e => (nonstandardOf e).any (· != sorryAxName)
  let distinctOthers := others.foldl (init := (#[] : Array String)) fun acc e =>
    (nonstandardOf e).foldl (init := acc) fun acc a =>
      if a == sorryAxName || acc.contains a then acc else acc.push a
  IO.println s!"axiomsweep: {entries.size} declarations across {moduleCount} modules \
    under {roots}"
  IO.println s!"  sorryAx-tainted: {sorryCount}"
  IO.println s!"  non-standard-axiom-tainted: {others.size} (axioms: {distinctOthers})"
  if let some out := cfg.out? then
    let report := Json.mkObj [
      ("roots", toJson (roots.map (·.toString))),
      ("declarationCount", toJson entries.size),
      ("declarations", toJson entries)]
    IO.FS.writeFile out (report.pretty ++ "\n")
    IO.println s!"axiomsweep: wrote report to {out}"
  if cfg.check then
    return (← runCheck entries)
  return 0

open AxiomSweep in
unsafe def main (args : List String) : IO UInt32 := do
  try
    run args
  catch e =>
    IO.eprintln s!"axiomsweep: internal error: {e}"
    return 2
