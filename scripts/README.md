# ArkLib Scripts 

This directory contains various utility scripts for the ArkLib project.

## Available Scripts

### Build and Validation
- **`validate.sh`** - Recommended convenience wrapper for routine local validation
- **`build-project.sh`** - Compile-only helper (`lake build`)
- **`build_timing_report.sh`** - CI timing/report helper for the library build, the native build, and the validation wrapper
- **`module_times.py`** - Per-module compile-time table that travels with the CI build cache
- **`build_timing_metadata.py`** - Versioned attribution metadata writer/validator for timing artifacts
- **`test-build-timing-report.sh`** - Deterministic report, metadata, and workflow-policy fixtures
- **`update-lib.sh`** - Update ArkLib.lean with all imports from source files
- **`check-imports.sh`** - Check whether `ArkLib.lean` is up to date with all tracked source modules
- **`check-warning-log.py`** - Fail on scoped warning classes found in a captured build log
- **`AxiomSweep.lean`** (`lake exe axiomsweep`) - Kernel-level axiom/`sorry` accounting with a
  committed regression baseline (`axiom_baseline.json`); see "Axiom Sweep" below
- **`test-axiomsweep.sh`** - Executable fixture matrix certifying the axiomsweep tool itself
  (gate directions, native-trust floor, exit-code contract, `--must-depend-on` verdicts),
  against the fixtures in `AxiomSweepTestFixtures/`
- **`must_depend_on.json`** - Shared declarations each conformance proof must use, checked by
  `lake exe axiomsweep --must-depend-on`; see "Required proof dependencies" below
- **`source-trust-audit.py`** - Deterministic source-token inventory for constructs outside
  the environment sweep's visibility, with optional Git-ref comparison
- **`test-source-trust-audit.py`** - Focused lexer/diff fixtures for the source inventory
- **`ToyProblemRuntime.lean`** (`lake exe toyproblem-runtime`) - Compiled small-parameter checks
  for KoalaBear sextic arithmetic, executable interleaved-RS extraction, and the C6.9 virtual
  output-oracle and exact-extractor paths
- **`SumcheckRuntime.lean`** (`lake exe sumcheck-runtime`) - Compiled checks of CompPoly-backed
  round messages and the honest multivariate prover in the shared native Sumcheck executor,
  including continuation effects, abort, original-oracle evaluation and zero remaining rounds.
- **`HachiRuntime.lean`** (`lake exe hachi-runtime`) - Compiled small-parameter checks that the
  nonrecursive Hachi honest-prover path executes: the balanced committer, the computable honest
  lift quotient, the concrete Ajtai lift commitment, and the terminal reveal-and-check. `--full`
  additionally runs the whole composed opening and checks the verifier accepts — it passes, in
  about six minutes, which is why it is not gated: the honest sumcheck prover dominates the cost
  of the entire chain. `--timing` reports per-check costs
- **`check-docs-integrity.py`** - Check docs links and the `CLAUDE.md` symlink
- **`LintStyle.lean`** and **`LintStyle/Checks.lean`** (`lake exe lint-style`) - Lean-native,
  exception-free source policy, including import discipline, whitespace, headers, line/file size,
  and hazardous-Unicode checks. It verifies that every tracked Lean file under `ArkLib/` and `ArkLibTest/` file is in the
  `ArkLib.lean` closure, and independently rejects forbidden option and `nolint`-attribute syntax
  even if module code captures diagnostics or mutates Lean's in-process linter registry. The same
  lexical pass rejects raised elaboration budgets (`set_option maxHeartbeats`, `maxRecDepth`, and
  `synthInstance.*`, code `ERR_BUDGET`): make the proof cheaper instead. This
  lexical backstop is deliberately conservative across literal bodies (and across comments for
  forbidden options), and reserves policy-like quoted identifiers and syntax quotations;
  suppression examples belong in the out-of-scope fixtures
- **`ArkLibLintPlugin.lean`** - end-of-module Lean syntax-tree gate rejecting `set_option` linter,
  pretty-printer, profiler, and trace changes and `@[nolint]` attributes, including suppressions
  nested in tactics, terms, extensible interpolated strings, and diagnostic-capturing commands.
  The plugin supplies precise syntax diagnostics; it is not presented as a sandbox against
  arbitrary hostile Lean metaprogramming, so the independent source pass remains mandatory

### Dependency Analysis
- **`dependency_analysis/`** - Complete dependency analysis toolkit
  - Generate dependency graphs for all ArkLib modules
  - Interactive exploration of dependencies
  - Visual representations (PNG, SVG)
  - See `dependency_analysis/README.md` for detailed usage

### Knowledge Base
- **`kb/`** - Scripts for syncing and inspecting the repository knowledge base
  - Export bibliography metadata
  - Extract citation usage from `ArkLib/**/*.lean`
  - Regenerate derived KB indexes, scaffold missing cited-paper stubs, and lint KB structure
  - Resolve review context from cited keys or changed Lean files
  - See `kb/README.md` for usage

## Quick Start

### Recommended Routine Validation
```bash
./scripts/validate.sh
```

### Validation With Optional Checks
```bash
# Build API docs too
./scripts/validate.sh --docs

# Build site / blueprint output too
./scripts/validate.sh --site

# Check the axiom/sorry regression baseline too
./scripts/validate.sh --axioms
```

### Generate Dependency Graphs
```bash
cd scripts/dependency_analysis
python generate_dependency_graph.py --root ../../ --output-dir ../../dependency_graphs
```

### Compile Only
```bash
./scripts/build-project.sh
```

### Toy-Problem Runtime Gate
```bash
lake exe toyproblem-runtime
```

### Nonrecursive-Hachi Runtime Gate
```bash
lake exe hachi-runtime            # the fast checks; this is what validate.sh gates on
lake exe hachi-runtime --full     # also runs the composed opening (slow)
lake exe hachi-runtime --timing   # per-check timings
```

### Build Timing Helper
```bash
bash scripts/build_timing_report.sh --help
```

### Update Library Imports
```bash
# Update ArkLib.lean with all imports
./scripts/update-lib.sh

# Check if imports are up to date
./scripts/check-imports.sh

# Run only the Lean-native source-policy gate
lake exe lint-style

# Test the build-time suppression plugin against accepted and rejected syntax fixtures
./scripts/test-lint-plugin.sh

```

### Check Docs Integrity
```bash
python3 ./scripts/check-docs-integrity.py
```

### Knowledge Base Indexes
```bash
python3 ./scripts/kb/sync_from_bib.py
python3 ./scripts/kb/extract_lean_citations.py
python3 ./scripts/kb/regenerate.py
python3 ./scripts/kb/check_generated.py
python3 ./scripts/kb/lint.py
python3 ./scripts/kb/review_context.py --files ArkLib/ProofSystem/Fri/Spec/SingleRound.lean
```

### Axiom Sweep

Kernel-level accounting of what every `ArkLib.*` declaration ultimately depends on — the
same information as `#print axioms`, computed for the whole library at once from the built
`.olean` data (so private and macro-generated declarations are included and no source
heuristics are involved). Requires a completed `lake build`.

Building the executable links VCVio's FFI static libraries, whose C sources live in git
submodules that Lake does not fetch; `./scripts/validate.sh --axioms` and CI initialize
them automatically, but on a direct first `lake exe axiomsweep` you may need:

```bash
git -C .lake/packages/VCVio submodule update --init --recursive
```

```bash
# Summary: total declarations, sorryAx-tainted, non-standard-axiom-tainted
lake exe axiomsweep

# Full per-declaration report (name, module, kind, line, axioms)
lake exe axiomsweep --out /tmp/axiom-report.json

# Regression gate: fail iff current taint is not covered by the baseline
lake exe axiomsweep --check

# Refresh the baseline (after intentionally adding a tagged sorry, or after
# closing gaps); commit the resulting diff in the same PR
lake exe axiomsweep --update-baseline
```

The committed baseline makes the distinction the repo cares about mechanical. Pre-existing
`sorry` gaps are allowed while recorded; additions fail `--check` until an intentional
`lake exe axiomsweep --update-baseline` diff is reviewed and committed. Removed debt is
reported without failing so cleanup is never discouraged; refresh the baseline in the same
PR. The baseline is an allowlist for `sorryAx` debt only; native-compiler trust (`Lean.ofReduceBool`,
`Lean.trustCompiler`, and the per-declaration `…._native.<tactic>.ax_<n>_<n>` axioms
minted by `native_decide`-style tactics) is never allowlistable — `--check` fails on it
regardless of the baseline, and `--update-baseline` refuses to write while it is present.
CI and `./scripts/validate.sh --axioms` both run the check enforcing.

The tool itself is certified by `./scripts/test-axiomsweep.sh`, which builds the isolated
`AxiomSweepTestFixtures` library (deliberate synthetic taint of every shape the sweep
reasons about: direct and transitive `sorry`, axiom-in-type, mutual-inductive inheritance,
generated native-trust names and near-miss collisions, and an unimported file) and checks
report determinism, every gate direction, and the exit-code contract (`1` = taint verdict,
`2` = infrastructure failure). CI runs it as an enforcing step:

```bash
lake build AxiomSweepTestFixtures
./scripts/test-axiomsweep.sh
```

#### Required proof dependencies (`--must-depend-on`)

A conformance theorem is only evidence of reuse if its proof actually invokes the shared
declarations. Importing their module, or naming them in the statement, shows nothing.
`lake exe axiomsweep --must-depend-on` checks the requirements committed in
`must_depend_on.json`:

```json
{
  "requirements": [
    {
      "theorem": "ArkLibTest.Conformance.Example.conforms",
      "module": "ArkLibTest.Conformance.Example",
      "mustDependOn": ["ArkLib.Shared.lawA", "ArkLib.Shared.lawB"],
      "note": "optional free text for reviewers"
    }
  ]
}
```

The check walks the same compiled-environment dependency graph as the axiom census, with
the same solver, and asks what the **proof term** of `theorem` uses:

- **Proof edges.** Every constant is entered through its body (a proof or a definition
  body), never its statement. Wrapping the claim in a lemma and applying that lemma
  therefore fails. A constant with no body (an inductive, constructor, recursor or axiom)
  contributes everything `getUsedConstantsAsSet` reports for it: its type, plus the
  constructors, the inductives, or the recursor's generating declarations. Dead code is
  removed first, repeatedly until nothing changes, so chains are caught too. That covers a
  `have` or `let` whose variable is unused, a β-redex that discards its argument, and the
  major premise of a `casesOn` on a proposition with at least one constructor, whose minor
  premises ignore every field:
  the shape `obtain`, `rcases` and `cases` produce for an unused proof. A
  `have _ := lawA x` that the proof never consults is therefore not use.
- **The statement is blocked.** Let `S` be everything reachable from the theorem's
  statement through proof edges. A proof term repeats its statement's constants (binder
  types, implicit and `rfl` arguments, casts), so members of `S` are leaves of the walk and
  are never entered. A name holds iff it occurs directly in the proof term, or is an edge
  of some constant outside `S` that the walk reaches. Without this rule, whatever the body
  of a statement-named definition, instance or structure uses would count as use. A name
  reachable only through `S` fails with "reachable only through constants named by the
  statement; requirement cannot distinguish use". That is exit `1`, an unmet claim rather
  than a broken file, because only the author can fix it.
- **No gaps the proof relies on.** `sorryAx` is found by the same walk as the required
  names: from the live proof term, through proof edges, with `S` blocked. If it is
  reachable, the requirement fails (exit `1`) with a witness path, whether the gap is in
  the proof itself or in a lemma or definition the proof enters. A gap inside an object the
  statement names does not count, for example production debt in a field unrelated to the
  claim. Conformance statements can therefore name objects that still carry `sorry`, and
  the axiom baseline accounts for that debt. Admitted facts inside statement-named objects,
  even a law field the proof projects out, are reported in a `note` naming those constants;
  they do not fail the requirement, and the axiom baseline tracks them.
- Generated and private constants (`_proof_n`, `match_n`, equation lemmas, `_private`
  helpers) are walked through like any other, so use routed through them counts.

The check has trade-offs and limits:

- **Statement blocking costs real uses.** Use that happens only inside the body of
  something the statement names fails. Require a theorem the proof invokes directly
  instead. A name the statement mentions itself still passes when the proof term repeats
  it, and the report then adds "(also named by the statement)". So prefer names the
  statement does not mention.
- **`rfl` lemmas leave no trace.** A lemma that `simp only` or `dsimp` applies by `rfl`
  leaves no constant in the proof term, so a requirement on it fails even though the proof
  relied on it.
- **It counts mentions, not use.** It guards against *accidental* non-reuse, not against an
  adversarial author. A mention that survives elaboration still counts even if it does no
  work: for example, an argument passed to a function that ignores it, or a discriminant of a
  `match` whose arms ignore it (matcher applications are not simplified). Reviewers must
  still read the proof of each registered conformance theorem for uses like that.

Each satisfied dependency is printed with a shortest witness path. All of the following
exit `2`: unknown or ambiguous names, unknown JSON keys, a subject with no proof term (an
axiom, say), a subject declared outside its `module`, an empty or duplicated requirement,
an unparsable file, and combining the mode with `--check`, `--update-baseline`,
`--baseline`, `--out` or `--root`. Private declarations can be named as they are written in
source. Only the modules named by `module` are imported, and the default file has no
requirements, so with nothing configured the check imports nothing. The check reads built
`.olean` files and does not rebuild the modules it imports, so after a standalone edit run
`lake build` and `lake test` first. `./scripts/validate.sh --axioms` and CI run it as an
enforcing step after `lake test`. On a real ArkLib theorem, one requirement takes a few
seconds (more under load).

The fixture matrix covers every outcome. `AxiomSweepTestFixtures/MustDependOn.lean` holds
the shared declarations and the direct, transitive, private and generated-auxiliary uses,
plus the absent, statement-only and wrapper-statement-only names.
`AxiomSweepTestFixtures/MustDependOn/Statement.lean` is a separate consumer module holding
the statement-blocking cases and the dead-code cases (`have`, chained `have`s, discarding
redexes, `obtain`). It also holds the `sorry` cases (in the proof, in a helper, and in a
statement-named object, which passes), the `simp only` case, and the uses that must keep
passing. The matrix also exercises each configuration error.

### Source Trust Inventory

`source-trust-audit.py` complements axiomsweep by lexically scanning every tracked
Lean file under `ArkLib/` and `ArkLibTest/`, whether imported or not. It masks nested comments, strings,
and quoted identifiers, then inventories exact admission, `example`, explicit-`axiom`, and
native/compiler-trust reference tokens. This sees admissions in examples and
defaults/autoparams that attach to no environment declaration. It deliberately reports rather
than bans `sorry` debt, and native references are conservative visibility because metaprogram
syntax quotations can mention a tactic without executing it. The kernel-level sweep owns the
enforcing taint verdict and zero-native-trust floor.

```bash
python3 scripts/test-source-trust-audit.py
python3 scripts/source-trust-audit.py --base-ref origin/main --json /tmp/source-trust.json
```

### `build_timing_report.sh`

Helper used by CI to measure and render build timings for the library build, the native build,
and the `./scripts/validate.sh` path. The library build starts from the cached `main` build, so
its wall time covers only what the change invalidated. The report therefore also lists the
modules Lake rebuilt against their times in the module table restored with the cache (see
`module_times.py` below). Each timing artifact records the measured checkout, PR head/base,
dependency-manifest hash, cache provenance, and runner image, and carries the module tables
before and after the run; the report shows wall time beside `user + sys` CPU work. This supports
[`../.github/workflows/ci.yml`](../.github/workflows/ci.yml).

The three measurements share one tree and run in order, so each leaves it warmer than the last.
`native_build` exists to hold the `.c.o` chain that the compiled executables link
(`toyproblem-runtime` and `hachi-runtime`): that is the cost which swings on `.lake` cache state,
and billing it separately keeps the validation wrapper's row comparable across dependency bumps.
Any new compiled executable run by `validate.sh` has to be added to that command as well. See
[`../docs/wiki/quickstart.md`](../docs/wiki/quickstart.md) for how to read the rows.

`./scripts/test-build-timing-report.sh` exercises metadata validation, module-table updates,
rendering with and without a restored build, native-command ownership, and the stale-run guard in
the trusted reporter.

### `module_times.py`

Keeps `.lake/build/arklib-module-times.json`, the latest compile time of every ArkLib module.
After each CI build, `update` overlays the `Built <module> (<time>)` lines from the build logs
and drops modules whose source file is gone. Lake rebuilds a module whenever its source or an
import changes, so each entry was measured against the inputs the module still has, and the
table's sum estimates clean-build compile time. The table is saved with the build cache on
`main`.

```bash
python3 scripts/module_times.py update .lake/build/arklib-module-times.json \
  --commit "$(git rev-parse HEAD)" /tmp/build-timing/library_build.log
```

## Requirements

- Python 3.6+ (for Python scripts)
- Lean 4 (for Lean scripts)
- Graphviz (for dependency visualization)
- Virtual environment (`.venv`) for Python dependencies

## Notes

- Most scripts should be run from the ArkLib root directory
- Python scripts require the virtual environment to be activated
- Some scripts may require specific Lean toolchain versions
- `validate.sh` is the recommended local wrapper; use the lower-level scripts directly when you
  want to run or debug one piece in isolation
- `validate.sh` enforces a zero non-`sorry` warning budget across `ArkLib/**`
- New `ArkLib/**/*.lean` files must be staged before `update-lib.sh` or `check-imports.sh`
