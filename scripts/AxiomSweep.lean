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
lake exe axiomsweep --must-depend-on    # check scripts/must_depend_on.json (see below)
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

`--must-depend-on` reuses the same environment walk for a different question: does the
*proof* of a named conformance theorem actually use the shared declarations it is meant to
reuse? Requirements are committed in `scripts/must_depend_on.json`. The semantics are
documented in the `--must-depend-on` section below: proof bodies only, dead code
dropped, constants reachable from the statement blocked, and gaps the proof relies on
rejected. Exit `1` means an
unmet requirement, `2` a configuration error such as an unknown name.

`scripts/test-axiomsweep.sh` exercises all of this against the `AxiomSweepTestFixtures`
library, whose fixtures carry synthetic taint of each shape this file reasons about, and
proofs that do and do not use a shared lemma.
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

/-- A closure problem over the compiled environment's constant-dependency graph: which
constants count as edges out of a constant, and which marked names a constant contributes
by itself. The closure of a constant is the set of marked names reachable from it.

The axiom sweep (`axiomTraversal`) marks axioms and follows every constant a declaration's
type or value mentions; the `--must-depend-on` mode (`proofTraversal`) marks the required
shared declarations and follows proofs and definition bodies only. Both are solved by the
same two phases below. -/
structure Traversal where
  edges : ConstantInfo → List Name
  seed : Name → ConstantInfo → Array Name

/-- The axiom census: every constant in a declaration's type or value is an edge, and an
axiom contributes itself plus anything reachable through its *type* (matching Lean's own
`CollectAxioms`). -/
def axiomTraversal : Traversal where
  edges ci := ci.getUsedConstantsAsSet.toList
  seed n ci := if ci matches .axiomInfo _ then #[n] else #[]

/-- Phase 1: DFS. Compute, for every constant reachable from the work list, an
under-approximation of its closure under `trav` (for the axiom sweep, the set of axioms it
transitively depends on), memoised across roots via `memo`. Also records the finalisation
order — a topological order of the dependency graph except inside mutual-inductive cycles.

`gray` marks constants whose dependencies are still being expanded. Back-edges (cycles,
which the kernel only permits inside mutual inductive families) contribute nothing in
this phase; `repair` below propagates to the true fixpoint. -/
partial def collect (env : Environment) (trav : Traversal) (stack : List Name)
    (gray : Std.HashSet Name) (memo : Std.HashMap Name (Array Name)) (order : Array Name) :
    Std.HashMap Name (Array Name) × Array Name :=
  match stack with
  | [] => (memo, order)
  | n :: rest =>
    if memo.contains n then
      collect env trav rest gray memo order
    else match env.find? n with
      | none => collect env trav rest gray (memo.insert n #[]) order
      | some ci =>
        let deps := trav.edges ci
        if gray.contains n then
          let axs := deps.foldl (init := trav.seed n ci) fun acc d =>
            match memo[d]? with
            | some as => as.foldl (init := acc) fun acc a =>
                if acc.contains a then acc else acc.push a
            | none => acc
          collect env trav rest gray (memo.insert n axs) (order.push n)
        else
          let pending := deps.filter fun d => !memo.contains d && !gray.contains d
          collect env trav (pending ++ stack) (gray.insert n) memo order

/-- Phase 2: propagate to fixpoint. The DFS under-approximates inside mutual-inductive
cycles (a member's taint may not reach its siblings), and — because `memo` persists
across roots — anything finalised after reading such a member inherits the error.
Re-deriving every set in finalisation order until nothing changes computes the least
fixpoint of the closure equations — for the axiom sweep, the true kernel-level axiom
dependency set. This is strictly more accurate than `#print axioms`, whose `CollectAxioms`
has the same mutual-family blind spot this phase repairs. Sets grow monotonically and are bounded,
so termination is immediate; in practice one or two passes suffice. -/
partial def repair (env : Environment) (trav : Traversal) (order : Array Name)
    (memo : Std.HashMap Name (Array Name)) : Std.HashMap Name (Array Name) :=
  let (memo', changed) := order.foldl (init := (memo, false)) fun (memo, changed) n =>
    match env.find? n with
    | none => (memo, changed)
    | some ci =>
      let deps := trav.edges ci
      let axs := deps.foldl (init := trav.seed n ci) fun acc d =>
        match memo[d]? with
        | some as => as.foldl (init := acc) fun acc a =>
            if acc.contains a then acc else acc.push a
        | none => acc
      let old := (memo[n]?.getD #[]).size
      if axs.size == old then (memo, changed)
      else (memo.insert n axs, true)
  if changed then repair env trav order memo' else memo'

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
      fun (memo, order) (c, _) => collect env axiomTraversal [c] {} memo order
  let memo := repair env axiomTraversal order memo0
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

/-! ### `--must-depend-on`: required proof dependencies

The question is whether the *proof* of a subject `T` uses a required declaration `D`, as
opposed to `T`'s statement mentioning it. The check walks the same dependency graph with the
same two-phase solver as the axiom sweep, changed in three ways.

* **Proof edges.** Every constant is entered through its body (a proof or a definition
  body), never through its statement. Restating a claim as a lemma `L` and proving `T := L`
  therefore does not count as use. A constant with no body (an inductive, constructor,
  recursor, axiom or quotient) contributes everything `getUsedConstantsAsSet` reports for
  it. Dead code is removed from bodies, to a fixpoint, before their constants are read:
  a `have` or `let` whose variable is never used, a β-redex whose argument is discarded,
  and the major premise of a `casesOn` on a proposition whose minor premises ignore every
  field (what `obtain`, `rcases` and `cases` produce for an unused proof). A
  `have _ := D x` that the proof never consults is therefore not use.
* **The statement is blocked.** Let `S` be every constant reachable through proof edges
  from `T`'s statement. A proof term repeats its statement's constants (in binder types,
  implicit arguments and casts), so the walk from `T`'s proof treats each member of `S` as
  a leaf and never enters it. Without this rule, anything the body of a statement-named
  definition, instance or structure uses would count as use. `D` holds iff it occurs
  directly in `T`'s proof, or is an edge of some constant outside `S` that the walk
  reaches. When `D` is reachable but only through `S`, the result is reported distinctly as
  undecidable from the graph. This is still exit `1`, an unmet claim and not a broken
  file, because only the author can repair it: a requirement must name a theorem that the
  proof invokes itself.
* **No gaps the proof relies on.** `sorryAx` is marked like a required name and found by
  the same walk, so a subject fails (exit `1`, with a witness path) exactly when `sorryAx`
  is reachable from its live proof term through proof edges, with `S` blocked. A gap the
  proof relies on, directly or in any lemma or definition it enters, fails the
  requirement, since such a proof demonstrates nothing about reuse. A gap inside an object
  the statement names (production debt in a field unrelated to the claim) does not; the
  axiom baseline still accounts for it.

Compiler-generated and private constants (`_proof_n`, matchers, equation lemmas,
`_private` helpers) are ordinary constants of the graph and are walked through like any
other, so real use routed through them counts.

This is a guard against *accidental* non-reuse, not against an adversarial author. A
mention that survives elaboration but does no work still counts, for instance an argument
passed to a function that ignores it, or a discriminant of a `match` whose arms ignore it
(matcher applications are not simplified). Statement-blocking also has a cost in the other
direction: real use that happens only inside the body of something the statement names
fails, and the author must name a theorem the proof invokes directly instead. Lemmas that
`simp only` or `dsimp` apply by `rfl` leave no constant in the proof term, so they fail too.

Missing or ambiguous names, unknown keys, a subject without a proof term, and a subject
declared outside its configured module are configuration errors (exit `2`), never a silent
pass. -/

/-- The body under `k` leading lambdas, if `e` has them. -/
def lambdaBody? : Nat → Expr → Option Expr
  | 0, e => some e
  | k + 1, .lam _ _ b _ => lambdaBody? k b
  | _ + 1, _ => none

/-- Whether `e` mentions any of the loose bound variables `0, …, k - 1`. -/
def usesBVarsBelow (e : Expr) (k : Nat) : Bool :=
  (List.range k).any e.hasLooseBVar

/-- A placeholder for a dead subterm. It mentions no constant, and the rewritten term is
only ever read for its constants, never type-checked. -/
def deadTerm : Expr := .sort .zero

/-- If `s` is a `casesOn` on a proposition whose eliminator ignores the proof, the index of
that dead major premise. That is: the inductive is a `Prop` with at least one constructor,
the motive ignores its indices and the major premise, and every minor premise ignores every
constructor field. Any single minor premise then proves the result by itself, so the major
premise is not used.
This is what `obtain`, `rcases` and `cases` produce for an unused proof. -/
def deadCasesOnMajor? (env : Environment) (s : Expr) : Option Nat := do
  let .const c _ := s.getAppFn | none
  guard (isCasesOnRecursor env c)
  let .inductInfo iv ← env.find? c.getPrefix | none
  guard iv.type.getForallBody.isProp
  -- Without a constructor there is no minor premise to stand in for the major one: eliminating
  -- an empty proposition (`False.casesOn`, `obtain ⟨⟩ := h`) uses its proof essentially.
  guard !iv.ctors.isEmpty
  let args := s.getAppArgs
  let majorIdx := iv.numParams + 1 + iv.numIndices
  guard (args.size ≥ majorIdx + 1 + iv.ctors.length)
  guard (args[majorIdx]! != deadTerm)
  let motiveBody ← lambdaBody? (iv.numIndices + 1) args[iv.numParams]!
  guard !(usesBVarsBelow motiveBody (iv.numIndices + 1))
  for (ctor, i) in iv.ctors.zipIdx do
    let .ctorInfo cv ← env.find? ctor | none
    let minorBody ← lambdaBody? cv.numFields args[majorIdx + 1 + i]!
    guard !(usesBVarsBelow minorBody cv.numFields)
  return majorIdx

/-- One top-down pass of dead-code removal:
* a `let`/`have` (or `letFun`) whose variable the body never uses is replaced by its body;
* a β-redex whose bound variable is unused is replaced by its body;
* the major premise of a `casesOn` that ignores its proof (`deadCasesOnMajor?`) is
  replaced by `deadTerm`. -/
partial def dropDeadOnce (env : Environment) (e : Expr) : Expr :=
  e.replace fun s =>
    let body? : Option Expr := match s with
      | .letE _ _ _ b _ => if b.hasLooseBVar 0 then none else some b
      | .app (.lam _ _ b _) _ => if b.hasLooseBVar 0 then none else some b
      | _ =>
        if s.isAppOfArity ``letFun 4 then
          match s.appArg! with
          | .lam _ _ b _ => if b.hasLooseBVar 0 then none else some b
          | _ => none
        else none
    match body? with
    | some b => some (dropDeadOnce env (b.lowerLooseBVars 1 1))
    | none =>
      (deadCasesOnMajor? env s).map fun i =>
        dropDeadOnce env (mkAppN s.getAppFn (s.getAppArgs.set! i deadTerm))

/-- Remove dead code to a fixpoint. A single top-down pass cannot see that a binder becomes
dead once the code below it is removed: a chain of unused `have`s, a `have` consumed only by
a discarding redex, nested discarding redexes, or a `casesOn` whose minor premises read a
field only through dead code. Each pass shrinks the term, so iteration terminates. -/
partial def dropDeadBinders (env : Environment) (e : Expr) : Expr :=
  let e' := dropDeadOnce env e
  if e' == e then e else dropDeadBinders env e'

/-- The constants a body can consult once dead code is removed. -/
def liveConstants (env : Environment) (e : Expr) : List Name :=
  (dropDeadBinders env e).getUsedConstantsAsSet.toList

/-- Proof edges: the live constants of a declaration's body, or, for a declaration without
a body, everything `getUsedConstantsAsSet` reports (its type and, for inductive families,
constructors and recursors, the declarations it is generated from). -/
def proofEdges (env : Environment) (ci : ConstantInfo) : List Name :=
  match ci.value? (allowOpaque := true) with
  | some v => liveConstants env v
  | none => ci.getUsedConstantsAsSet.toList

/-- The closure problem of `--must-depend-on`: proof edges, not entering any `blocked`
constant (it is a leaf), marking the required names. -/
def proofTraversal (env : Environment) (required : Std.HashSet Name)
    (blocked : Std.HashSet Name := {}) : Traversal where
  edges ci := if blocked.contains ci.name then [] else proofEdges env ci
  seed n _ := if required.contains n then #[n] else #[]

/-- One configured requirement: `theorem` (declared in `module`) must use every name in
`mustDependOn` in its proof. `note` is free text for reviewers, since JSON has no
comments. -/
structure Requirement where
  «theorem» : String
  module : String
  mustDependOn : Array String
  note : Option String := none
  deriving FromJson, ToJson

/-- The committed requirement file. -/
structure Requirements where
  requirements : Array Requirement
  deriving FromJson, ToJson

/-- Reject keys outside `allowed`: `FromJson` ignores them, so a misspelt key such as
`mustAlsoDependOn` would otherwise be dropped silently. -/
def checkKeys (j : Json) (allowed : List String) (ctx : String) : Except String Unit := do
  let obj ← j.getObj?
  for k in obj.keys do
    if !allowed.contains k then
      throw s!"unknown key \"{k}\" in {ctx} (allowed: {allowed})"

/-- Parse a requirement file strictly: no unknown keys at either level. -/
def parseRequirements (j : Json) : Except String Requirements := do
  checkKeys j ["requirements"] "the requirement file"
  if let .ok (.arr rs) := j.getObjVal? "requirements" then
    for r in rs do
      checkKeys r ["theorem", "module", "mustDependOn", "note"] "a requirement"
  fromJson? j

/-- Reject a requirement that could only pass vacuously, before importing anything.
Duplicates and self-references are rejected after name resolution, where two spellings of
one declaration are recognised as the same. -/
def validateRequirements (reqs : Requirements) : Except String Unit := do
  for r in reqs.requirements do
    if r.mustDependOn.isEmpty then
      throw s!"the requirement for {r.«theorem»} lists no dependencies"

/-- Resolve a configured name to a constant of `env`: the name itself, or else the one
constant whose printed name, or whose user-facing name if it is private, is `s`. Private
declarations can thus be named as written in source; an ambiguous name is an error. -/
def resolveName (env : Environment) (s : String) : Except String Name := do
  let n := s.toName
  if env.contains n then return n
  let hits := env.constants.fold (init := (#[] : Array Name)) fun acc c _ =>
    if c.toString == s || (privateToUserName? c).map (·.toString) == some s then
      acc.push c
    else acc
  match hits.toList with
  | [c] => return c
  | [] => throw s!"unknown declaration {s} (not in the environment of the configured \
      modules)"
  | _ => throw s!"{s} names several private declarations {hits}; use the full name"

/-- How one required name relates to the proof of its subject. -/
inductive Verdict where
  /-- Used; carries a witness path from the subject, and whether the statement names it
  too (in which case the use is a direct occurrence in the proof term). -/
  | used (path : List Name) (alsoInStatement : Bool)
  /-- Not used; the statement names it. -/
  | namedByStatement
  /-- Not used; reachable only through constants the statement names. -/
  | throughStatement
  /-- Not used, and not reachable from the statement either. -/
  | absent

/-- A shortest path from `t` to `d` under `trav`, whose first step is one of `roots` (the
constants `t`'s term mentions), read off the solved closure `memo`. The search is
breadth-first and only enters constants whose closure contains `d`. So it is linear in the
part of the graph that leads to `d`, and it succeeds whenever `d` is in a root's closure. -/
def witness (env : Environment) (trav : Traversal) (memo : Std.HashMap Name (Array Name))
    (d t : Name) (roots : List Name) : Option (List Name) := Id.run do
  if roots.contains d then return some [t, d]
  let leadsTo (n : Name) : Bool := (memo[n]?.getD #[]).contains d
  let mut parent : Std.HashMap Name Name := {}
  let mut queue : Array Name := #[]
  for r in roots do
    if leadsTo r && !parent.contains r then
      parent := parent.insert r t
      queue := queue.push r
  let mut i := 0
  let mut found : Option Name := none
  while found.isNone && i < queue.size do
    let n := queue[i]!
    i := i + 1
    let some ci := env.find? n | continue
    let succs := trav.edges ci
    if succs.contains d then
      found := some n
    else
      for s in succs do
        if leadsTo s && !parent.contains s && s != t then
          parent := parent.insert s n
          queue := queue.push s
  let some last := found | return none
  -- Walk the parent links back to `t`; each is set once, so this terminates.
  let mut path : List Name := [d]
  let mut cur := last
  for _ in [0:parent.size + 1] do
    path := cur :: path
    if cur == t then break
    cur := parent[cur]?.getD t
  return some path

/-- The checked outcome of one requirement. -/
structure Outcome where
  subject : Name
  module : Name
  /-- A witness path to `sorryAx`, if the subject's proof relies on it. -/
  sorryPath? : Option (List Name)
  /-- Statement-closure constants the proof reaches (as blocked leaves) that carry
  `sorryAx`: admitted debt the proof touches only through objects the statement names. -/
  statementSorry : Array Name
  verdicts : Array (Name × Verdict)

/-- Resolve and check every requirement against `env`. `.error` is a configuration error. -/
def evaluateRequirements (env : Environment) (reqs : Requirements) :
    Except String (Array Outcome) := do
  let mut resolved : Array (Name × Name × ConstantInfo × Expr × Array Name) := #[]
  for r in reqs.requirements do
    let t ← resolveName env r.«theorem»
    let some ci := env.find? t | throw s!"unknown declaration {r.«theorem»}"
    let some idx := env.getModuleIdxFor? t
      | throw s!"{t} has no defining module in the imported environment"
    let mname := env.allImportedModuleNames[idx.toNat]!
    if mname.toString != r.module then
      throw s!"{t} is declared in {mname}, not in the configured module {r.module}"
    let some v := ci.value? (allowOpaque := true)
      | throw s!"{t} ({kindOf ci}) has no proof term whose dependencies could be checked"
    if resolved.any (·.1 == t) then
      throw s!"{t} has more than one requirement entry; merge them"
    let ds ← r.mustDependOn.mapM (resolveName env)
    for d in ds do
      if d == t then throw s!"the requirement for {t} lists the theorem itself"
      if (ds.filter (· == d)).size > 1 then
        throw s!"the requirement for {t} lists {d} more than once"
    resolved := resolved.push (t, mname, ci, v, ds)
  resolved.mapM fun (t, mname, ci, v, ds) => do
    -- `S`: everything reachable from the statement. `order` lists every constant the walk
    -- finalised, which is every constant it reached.
    let typeRoots := ci.type.getUsedConstantsAsSet.toList
    let strav := proofTraversal env (({} : Std.HashSet Name).insert ``sorryAx)
    let (smemo0, sOrder) := collect env strav typeRoots {} {} #[]
    let smemo := repair env strav sOrder smemo0
    let blocked : Std.HashSet Name := typeRoots.foldl (·.insert ·) (.ofArray sOrder)
    -- `sorryAx` is marked like a required name, so only a gap the proof itself relies on
    -- counts: one admitted inside an object the statement names is blocked with it.
    let required : Std.HashSet Name := ds.foldl (·.insert ·) ({} : Std.HashSet Name)
    let trav := proofTraversal env (required.insert ``sorryAx) blocked
    let roots := liveConstants env v
    let (memo0, order) := collect env trav roots {} {} #[]
    let memo := repair env trav order memo0
    let reaches (d : Name) : Bool :=
      roots.any fun c => c == d || (memo[c]?.getD #[]).contains d
    let sorryPath? := witness env trav memo ``sorryAx t roots
    if reaches ``sorryAx && sorryPath?.isNone then
      throw s!"internal error: {t} relies on sorryAx but no path was found"
    -- The blocked leaves the walk reached are the roots and finalised constants in `S`.
    let statementSorry : Array Name :=
      if sorryPath?.isSome then #[] else
        let reachedLeaves := (roots.toArray ++ order).filter blocked.contains
        let hits := reachedLeaves.filter fun c => (smemo[c]?.getD #[]).contains ``sorryAx
        (hits.foldl (init := (#[] : Array Name)) fun acc c =>
          if acc.contains c then acc else acc.push c).qsort (·.toString < ·.toString)
    let verdicts ← ds.mapM fun d => do
      let inType := typeRoots.contains d
      let reached := reaches d
      match witness env trav memo d t roots with
      | some path => pure (d, Verdict.used path inType)
      | none =>
        if reached then throw s!"internal error: {d} is reached from {t} but no path found"
        else if inType then pure (d, .namedByStatement)
        else if blocked.contains d then pure (d, .throughStatement)
        else pure (d, .absent)
    pure { subject := t, module := mname, sorryPath?, statementSorry, verdicts }

/-- Render a witness path. -/
def renderPath (path : List Name) : String := " -> ".intercalate (path.map toString)

/-- Print the outcomes. Returns the exit code: `1` iff some requirement is unmet. -/
def reportRequirements (results : Array Outcome) : IO UInt32 := do
  let mut unmet := 0
  let mut total := 0
  for o in results do
    IO.println s!"axiomsweep: {o.subject} ({o.module}) must depend on:"
    if let some path := o.sorryPath? then
      unmet := unmet + 1
      IO.println s!"  UNMET   the proof depends on sorryAx, so it cannot demonstrate reuse\n\
        \x20           via {renderPath path}"
    if !o.statementSorry.isEmpty then
      IO.println s!"  note    admitted debt (sorryAx) is reachable only through constants the \
        statement names: {o.statementSorry}. Not counted against the proof; the axiom \
        baseline tracks it."
    for (d, verdict) in o.verdicts do
      total := total + 1
      match verdict with
      | .used path alsoInStatement =>
        let note := if alsoInStatement then " (also named by the statement)" else ""
        IO.println s!"  ok      {d}{note}\n            via {renderPath path}"
      | .namedByStatement =>
        unmet := unmet + 1
        IO.println s!"  UNMET   {d}: named by the statement, but not used by the proof"
      | .throughStatement =>
        unmet := unmet + 1
        IO.println s!"  UNMET   {d}: reachable only through constants named by the \
          statement; requirement cannot distinguish use. Require a theorem the proof \
          invokes directly."
      | .absent =>
        unmet := unmet + 1
        IO.println s!"  UNMET   {d}: not used by the proof"
  if unmet > 0 then
    IO.eprintln s!"axiomsweep: {unmet} must-depend-on failure(s) across {results.size} \
      requirement(s). A proof must invoke each listed declaration, without sorry; naming \
      it in the statement or importing its module is not enough."
    return 1
  IO.println s!"axiomsweep: must-depend-on passed ({total} required proof \
    dependenc(y/ies) across {results.size} requirement(s))."
  return 0

structure Config where
  roots : Array Name := #[]
  out? : Option String := none
  check : Bool := false
  update : Bool := false
  baseline? : Option String := none
  mustDependOn : Bool := false
  requirements? : Option String := none

/-- The committed regression baseline read by `--check` and `--update-baseline`. -/
def defaultBaseline : String := "scripts/axiom_baseline.json"

/-- The committed requirement file read by `--must-depend-on`. -/
def defaultRequirements : String := "scripts/must_depend_on.json"

def parseArgs : List String → Config → Except String Config
  | [], cfg => .ok cfg
  | "--check" :: rest, cfg => parseArgs rest { cfg with check := true }
  | "--update-baseline" :: rest, cfg => parseArgs rest { cfg with update := true }
  | "--out" :: path :: rest, cfg => parseArgs rest { cfg with out? := some path }
  | "--baseline" :: path :: rest, cfg => parseArgs rest { cfg with baseline? := some path }
  | "--root" :: mod :: rest, cfg =>
    parseArgs rest { cfg with roots := cfg.roots.push mod.toName }
  | "--must-depend-on" :: rest, cfg => parseArgs rest { cfg with mustDependOn := true }
  | "--requirements" :: path :: rest, cfg =>
    parseArgs rest { cfg with requirements? := some path }
  | arg :: _, _ => .error s!"axiomsweep: unknown or incomplete argument: {arg}\n\
      usage: lake exe axiomsweep [--out FILE] [--check] [--update-baseline] \
      [--baseline FILE] [--root MOD]*\n      (--check and --update-baseline are mutually \
      exclusive)\n       lake exe axiomsweep --must-depend-on [--requirements FILE]"

/-- Import `roots` with every proof body visible, or report why not. -/
unsafe def importRoots (roots : Array Name) : IO (Option Environment) := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  try
    some <$> importModules (roots.map ({ module := · })) {} (trustLevel := 1024)
      (loadExts := true)
  catch e =>
    IO.eprintln s!"axiomsweep: cannot import root modules {roots}: {e.toString}\n\
      (roots must be importable modules — glob-based libs without an umbrella \
      module cannot be swept by library name)"
    return none

/-- The `--must-depend-on` mode: import the modules the requirement file names and check
every requirement. With no requirements configured nothing is imported. -/
unsafe def runMustDependOn (path : String) : IO UInt32 := do
  if !(← System.FilePath.pathExists path) then
    IO.eprintln s!"axiomsweep: requirement file {path} not found"
    return 2
  let reqs ← match Json.parse (← IO.FS.readFile path) >>= parseRequirements with
    | .ok r => pure r
    | .error e =>
      IO.eprintln s!"axiomsweep: cannot parse requirement file {path}: {e}"
      return 2
  if let .error e := validateRequirements reqs then
    IO.eprintln s!"axiomsweep: invalid requirement file {path}: {e}"
    return 2
  if reqs.requirements.isEmpty then
    IO.println s!"axiomsweep: no must-depend-on requirements configured in {path}."
    return 0
  let modules := reqs.requirements.foldl (init := (#[] : Array Name)) fun acc r =>
    if acc.contains r.module.toName then acc else acc.push r.module.toName
  let some env ← importRoots modules | return 2
  match evaluateRequirements env reqs with
  | .ok results => reportRequirements results
  | .error e =>
    IO.eprintln s!"axiomsweep: cannot check requirement file {path}: {e}"
    return 2

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
  if cfg.mustDependOn then
    if cfg.check || cfg.update || cfg.out?.isSome || !cfg.roots.isEmpty ||
        cfg.baseline?.isSome then
      IO.eprintln "axiomsweep: --must-depend-on takes its modules from the requirement \
        file and cannot be combined with --check, --update-baseline, --baseline, --out or \
        --root"
      return 2
    return (← runMustDependOn (cfg.requirements?.getD defaultRequirements))
  if cfg.requirements?.isSome then
    IO.eprintln "axiomsweep: --requirements is only meaningful with --must-depend-on"
    return 2
  let roots := if cfg.roots.isEmpty then defaultRoots else cfg.roots
  let some env ← importRoots roots | return 2
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
    return (← runUpdate cur (cfg.baseline?.getD defaultBaseline))
  if cfg.check then
    return (← runCheck cur (cfg.baseline?.getD defaultBaseline))
  return 0

open AxiomSweep in
unsafe def main (args : List String) : IO UInt32 := do
  try
    run args
  catch e =>
    IO.eprintln s!"axiomsweep: internal error: {e}"
    return 2
