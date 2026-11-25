/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Lean

/-!
# Universe rule: every universe parameter occurs in an argument type

Record D2 (`docs/design/interaction-rebuild/D2-ownership-and-universes.md`, "Universe policy")
states the rule: every universe parameter of an ArkLib declaration occurs in the type of one of
its arguments. A universe that only the result type, a structure field or a `Prop` body mentions
gets a fresh value at each use, which is what forces universe pins and lift lemmas.

This executable checks the rule on the compiled environment, for each constant in a module under
`ArkLib.Interaction` or `ArkLib.Relation`. It opens the constant's type with
`forallTelescopeReducing` and collects the level parameters of every binder type with
`collectLevelParams`. It reports each level parameter of the constant that it did not collect.
`docs/design/interaction-layer/universe-policy.md` ("Undetermined universes") describes the same
scan and its first results.

The rule already permits the result universe of a generic monad argument `m : Type → Type v` and
the universes of an arbitrary `P : PFunctor`, since the argument's type mentions them. The one
policy exception is the adversary universe (`AdversaryModel`, `ExtractionInterface` and the
declarations that take them), which the allowlist records with reason `adversary`.

Output: one line per violation, `module declaration universe`, sorted, on standard output.
Summaries and errors go to standard error.

```
lake exe universe-rule                        # check against scripts/universe_rule_allowlist.txt
lake exe universe-rule --report               # print the violations and exit 0
lake exe universe-rule --explain-skips        # also list skipped constants that break the rule
lake exe universe-rule --allowlist FILE       # check against another allowlist
lake exe universe-rule --import M --root P    # import module M, check modules under prefix P
```

Exit codes:

* `0`: every violation is on the allowlist, and every allowlist entry matches a violation.
* `1`: a violation is not on the allowlist, or an entry matches no violation. Fix the
  declaration, or delete the stale entry to shrink the allowlist.
* `2`: an infrastructure failure, such as bad arguments, an import failure or a malformed
  allowlist.

The allowlist has one entry per line: the violation line, then ` # `, then a one-line reason.
Lines that are empty or start with `#` are comments.

`scripts/test-universe-rule.sh` checks this program against the fixtures in
`scripts/UniverseRuleTestFixtures/`.
-/

open Lean Meta

namespace UniverseRule

/-- Modules the checker imports when no `--import` or `--root` is given. -/
def defaultImports : Array Name := #[`ArkLib]

/-- Module prefixes the checker covers when no `--root` is given. -/
def defaultRoots : Array Name := #[`ArkLib.Interaction, `ArkLib.Relation]

/-- Name components that the `inductive` and `structure` commands generate next to a type `T`
(`T.noConfusionType`, `T.ctorIdx`) or next to a constructor (`T.mk.injEq`, `T.mk.sizeOf_spec`). -/
def inductiveSuffixes : List String :=
  ["noConfusionType", "noConfusion", "ctorIdx", "toCtorIdx", "ctorElim", "ctorElimType",
    "injEq", "inj", "sizeOf_spec"]

/-- The inductive type that a generated constant `T.x` or `T.ctor.x` belongs to. -/
def generatedFor? (env : Environment) (n : Name) : Option InductiveVal :=
  match n with
  | .str p s =>
    if !inductiveSuffixes.contains s then none else
    match env.find? p with
    | some (.inductInfo v) => some v
    | some (.ctorInfo c) =>
      match env.find? c.induct with
      | some (.inductInfo v) => some v
      | _ => none
    | _ => none
  | _ => none

/-- Whether `levels` are the inductive type's own level parameters, possibly followed by more
(the motive universe of an eliminator). -/
def ownLevels (ind : InductiveVal) (levels : List Name) : Bool :=
  ind.levelParams.isPrefixOf levels

/-- Why a constant is not a user declaration, or `none` if the checker applies the rule to it.

The rule is about the declarations someone writes, because those are the constants that clients
name and that need universe pins. Lean generates other constants from each declaration, and a
generated constant has its source's level parameters, possibly with an eliminator's motive
universe added. The checker skips generated constants and checks their source instead. A
structure whose field alone mentions a universe is then reported once, not once per constructor,
projection and `sizeOf` instance. An equation lemma restates its definition case by case with
binders of its own. It can therefore leave one of the definition's universes undetermined (as
`Interaction.logMove.eq_1` does at the time of writing), and the checker still checks the
definition itself.
`--explain-skips` lists the skipped constants that would break the rule, to audit these rules.
The checker skips:

* names with macro scopes, which hygiene generates;
* internal names (`Name.isInternalDetail`): `_private` prefixes aside, these are the auxiliary
  `match_<n>`, `proof_<n>`, `eq_<n>` equation lemmas, `_cstage`, `_unsafe_rec`, `_sizeOf` and
  similar components that start with `_`;
* the `eq_def` and `eq_unfold` equation lemmas;
* recursors, the auxiliary recursors (`casesOn`, `recOn`, `below`, `brecOn`, `binductionOn`),
  `noConfusion`, and matchers;
* constructors, structure projections and the other constants the `inductive` and `structure`
  commands generate (`inductiveSuffixes`) whose level parameters are the type's own: the type
  itself is checked instead;
* instances that `deriving` generates. A derived instance for `T` takes exactly `T`'s parameters
  and has `T`'s level parameters. It therefore breaks the rule exactly when `T` does. Lean does
  not tag derived instances, and the checker recognizes one by its shape. Its type is a class
  applied to an inductive type `T` from the same module, at exactly the instance's level
  parameters. Its declaration range starts inside `T`'s, at the `deriving` clause. -/
def skipReason? (env : Environment) (n : Name) (ci : ConstantInfo) : CoreM (Option String) := do
  if n.hasMacroScopes then return some "macro scopes"
  let user := privateToUserName n
  if user.isInternalDetail then return some "internal name"
  if let .str _ s := user then
    if s == "eq_def" || s == "eq_unfold" then return some "equation lemma"
  match ci with
  | .recInfo _ => return some "recursor"
  | .ctorInfo c =>
    if let some (.inductInfo v) := env.find? c.induct then
      if ownLevels v c.levelParams then return some "constructor"
  | _ => pure ()
  if isAuxRecursor env n then return some "auxiliary recursor"
  if isNoConfusion env n then return some "noConfusion"
  if isMatcherCore env n then return some "matcher"
  if let some info := env.getProjectionFnInfo? n then
    if let some (.ctorInfo c) := env.find? info.ctorName then
      if let some (.inductInfo v) := env.find? c.induct then
        if ownLevels v ci.levelParams then return some "projection"
  if let some v := generatedFor? env user then
    if ownLevels v ci.levelParams then return some "generated by inductive"
  if let some ind ← derivedFor? env n ci then
    return some s!"derived instance for {ind}"
  return none
where
  /-- The inductive type that `n` is a derived instance for, if it has that shape. -/
  derivedFor? (env : Environment) (n : Name) (ci : ConstantInfo) : CoreM (Option Name) := do
    unless Meta.isInstanceCore env n do return none
    let some mod := env.getModuleIdxFor? n | return none
    let some instRange ← findDeclarationRanges? n | return none
    -- The instance type, under its binders, is `C … (T …)` for some inductive `T`.
    let body := ci.type.getForallBody
    let candidates := body.getAppArgs.filterMap fun a =>
      match a.getAppFn with
      | .const t us => some (t, us)
      | _ => none
    for (t, us) in candidates do
      let some (.inductInfo v) := env.find? t | continue
      -- `T` is applied to exactly the instance's level parameters. The deriving handler names
      -- them afresh (`u_1` for `T`'s `u`), and the names need not match `T`'s own.
      unless us.length == v.levelParams.length do continue
      unless us == ci.levelParams.map Level.param do continue
      unless env.getModuleIdxFor? t == some mod do continue
      let some tRange ← findDeclarationRanges? t | continue
      let r := tRange.range
      let p := instRange.range.pos
      if r.pos.line ≤ p.line && p.line ≤ r.endPos.line then
        return some t
    return none

/-- The level parameters of `ci` that occur in no argument type. -/
def undetermined (ci : ConstantInfo) : MetaM (List Name) := do
  if ci.levelParams.isEmpty then return []
  forallTelescopeReducing ci.type fun xs _ => do
    let mut s : CollectLevelParams.State := {}
    for x in xs do
      s := collectLevelParams s (← instantiateMVars (← inferType x))
    return ci.levelParams.filter (!s.params.contains ·)

/-- One violation: a declaration and a universe parameter that no argument type mentions. -/
structure Violation where
  module : Name
  decl : Name
  level : Name

def Violation.line (v : Violation) : String :=
  s!"{v.module} {v.decl} {v.level}"

/-- The result of a scan. -/
structure Scan where
  violations : Array Violation := #[]
  modules : Nat := 0
  checked : Nat := 0
  skipped : Nat := 0
  /-- Skipped constants with an undetermined universe, with the reason for the skip. -/
  skippedViolations : Array String := #[]
  errors : Array String := #[]

/-- Check every constant in a module under one of `roots`. With `explain`, also record the skipped
constants that would break the rule, to audit the skip rules. -/
def scan (roots : Array Name) (explain : Bool) : MetaM Scan := do
  let env ← getEnv
  let mut out : Scan := {}
  for (mname, mdata) in env.header.moduleNames.zip env.header.moduleData do
    unless roots.any (·.isPrefixOf mname) do continue
    out := { out with modules := out.modules + 1 }
    for n in mdata.constNames do
      let some ci := env.find? n | continue
      if let some reason ← skipReason? env n ci then
        out := { out with skipped := out.skipped + 1 }
        if explain then
          let us ← try undetermined ci catch _ => pure []
          for u in us do
            out := { out with skippedViolations :=
              out.skippedViolations.push s!"{mname} {n} {u} ({reason})" }
        continue
      out := { out with checked := out.checked + 1 }
      try
        for u in ← undetermined ci do
          let v : Violation := { module := mname, decl := privateToUserName n, level := u }
          out := { out with violations := out.violations.push v }
      catch e =>
        out := { out with errors := out.errors.push s!"{n}: {← e.toMessageData.toString}" }
  return out

/-- An allowlist entry: a violation line and the reason it is allowed. -/
structure Entry where
  line : String
  reason : String
  lineNo : Nat

/-- Collapse runs of whitespace so that spacing in the allowlist does not matter. -/
def normalize (s : String) : String :=
  " ".intercalate ((s.splitOn " ").filter (· ≠ "")) |>.trimAscii.toString

/-- Parse the allowlist. Each entry is `module declaration universe # reason`. -/
def parseAllowlist (text : String) : Except String (Array Entry) := do
  let mut out := #[]
  let mut lineNo := 0
  for raw in text.splitOn "\n" do
    lineNo := lineNo + 1
    let l := (raw.replace "\t" " ").trimAscii.toString
    if l.isEmpty || l.startsWith "#" then continue
    match l.splitOn " # " with
    | entry :: rest@(_ :: _) =>
      let reason := (" # ".intercalate rest).trimAscii.toString
      let entry := normalize entry
      if (entry.splitOn " ").length != 3 then
        throw s!"line {lineNo}: expected `module declaration universe # reason`, got `{l}`"
      if reason.isEmpty then throw s!"line {lineNo}: missing reason"
      out := out.push { line := entry, reason, lineNo }
    | _ => throw s!"line {lineNo}: expected `module declaration universe # reason`, got `{l}`"
  return out

structure Config where
  imports : Array Name := #[]
  roots : Array Name := #[]
  allowlist : String := "scripts/universe_rule_allowlist.txt"
  report : Bool := false
  explain : Bool := false

def usage : String :=
  "usage: lake exe universe-rule [--report] [--explain-skips] [--allowlist FILE] [--import MOD]* \
    [--root PREFIX]*"

def parseArgs : List String → Config → Except String Config
  | [], cfg => .ok cfg
  | "--report" :: rest, cfg => parseArgs rest { cfg with report := true }
  | "--explain-skips" :: rest, cfg => parseArgs rest { cfg with explain := true }
  | "--allowlist" :: path :: rest, cfg => parseArgs rest { cfg with allowlist := path }
  | "--import" :: m :: rest, cfg => parseArgs rest { cfg with imports := cfg.imports.push m.toName }
  | "--root" :: m :: rest, cfg => parseArgs rest { cfg with roots := cfg.roots.push m.toName }
  | arg :: _, _ => .error s!"universe-rule: unknown or incomplete argument: {arg}\n{usage}"

end UniverseRule

open UniverseRule in
unsafe def run (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args {} with
    | .ok cfg => pure cfg
    | .error e => IO.eprintln e; return 2
  let roots := if cfg.roots.isEmpty then defaultRoots else cfg.roots
  -- With `--root` and no `--import`, the roots are the modules to import.
  let imports :=
    if !cfg.imports.isEmpty then cfg.imports
    else if cfg.roots.isEmpty then defaultImports else cfg.roots
  let allowlist ← if cfg.report then pure #[] else
    if !(← System.FilePath.pathExists cfg.allowlist) then
      IO.eprintln s!"universe-rule: allowlist {cfg.allowlist} not found"
      return 2
    match parseAllowlist (← IO.FS.readFile cfg.allowlist) with
    | .ok a => pure a
    | .error e =>
      IO.eprintln s!"universe-rule: {cfg.allowlist}: {e}"
      return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← try
      importModules (imports.map ({ module := · })) {} (trustLevel := 1024) (loadExts := true)
    catch e =>
      IO.eprintln s!"universe-rule: cannot import {imports}: {e.toString}"
      return 2
  let (res, _) ← ((scan roots cfg.explain).run' {} {}).toIO
    { fileName := "<universe-rule>", fileMap := default, maxHeartbeats := 0 } { env }
  if res.modules == 0 then
    IO.eprintln s!"universe-rule: no imported module is under {roots}"
    return 2
  for e in res.errors do IO.eprintln s!"universe-rule: cannot check {e}"
  for l in res.skippedViolations.qsort (· < ·) do IO.eprintln s!"skipped: {l}"
  let lines := (res.violations.map (·.line)).qsort (· < ·)
  for l in lines do IO.println l
  IO.eprintln s!"universe-rule: checked {res.checked} constants in {res.modules} modules under \
    {roots} (skipped {res.skipped} generated constants); {lines.size} violations"
  if !res.errors.isEmpty then return 2
  if cfg.report then return 0
  let mut seen : Std.HashSet String := {}
  for e in allowlist do
    if seen.contains e.line then
      IO.eprintln s!"universe-rule: {cfg.allowlist}:{e.lineNo}: duplicate entry `{e.line}`"
      return 2
    seen := seen.insert e.line
  let found : Std.HashSet String := Std.HashSet.ofArray lines
  let unlisted := lines.filter (!seen.contains ·)
  let stale := allowlist.filter (!found.contains ·.line)
  if !unlisted.isEmpty then
    IO.eprintln s!"universe-rule: {unlisted.size} violations are not on {cfg.allowlist}. \
      Make each universe occur in an argument type (record D2, \"Universe policy\"):"
    for l in unlisted do IO.eprintln s!"  {l}"
  if !stale.isEmpty then
    IO.eprintln s!"universe-rule: {stale.size} entries of {cfg.allowlist} match no violation. \
      Delete them so the allowlist shrinks:"
    for e in stale do IO.eprintln s!"  {cfg.allowlist}:{e.lineNo}: {e.line}"
  if !unlisted.isEmpty || !stale.isEmpty then return 1
  IO.eprintln s!"universe-rule: passed ({allowlist.size} allowlisted violations)"
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  try
    run args
  catch e =>
    IO.eprintln s!"universe-rule: internal error: {e}"
    return 2
