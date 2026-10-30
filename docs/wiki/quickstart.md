# Quickstart

This page is the recommended agent playbook for commands and validation.
Use it as the main guide for routine local checks.

## Dependency versions

Before a large contribution or a forward-port, fetch the intended upstream remote and
compare your branch with its merge target (`git log HEAD..origin/main --oneline`,
`git diff HEAD origin/main -- lean-toolchain lakefile.toml lake-manifest.json`).
Review intervening API additions before writing replacement infrastructure. If the
checkout contains unrelated work, use a separate worktree for the forward-port and
leave that work intact.

`lean-toolchain` names the Lean release. `lakefile.toml` pins doc-gen4 and CompPoly to the
matching release tag and VCVio to an exact commit; Mathlib and PolyFun arrive through those
packages. `lake-manifest.json` records the exact resolved revision of every package, so read it,
not this page, for the current versions. A newer PolyFun revision must be validated against VCVio
before ArkLib can adopt it, so a VCVio bump and its PolyFun revision move together.
ArkLib uses native measures throughout its probability statements; the
[migration ledger](../design/native-measure-ledger.md) records the conversion and upstream API map.
Validate a changed dependency set with `./scripts/validate.sh --axioms` before merging.

Keep each check on a coherent source and artifact graph with the same toolchain and dependency
manifest. With parallel worktrees or artifact overlays, verify that every imported module resolves
to its intended source revision, including transitive dependencies. Freeze those artifacts while a
check runs; replacing imported output during elaboration invalidates its evidence. After changing
a dependency revision, rebuild its dependents before checking clients. Use the normal isolated
`lake build` and full validation as the final authority for scratch or overlay checks.

For focused checks, prefer `lake build ArkLib.Path.To.Module`. A direct `lake env lean` invocation
does not inherit the package's Lean options or build-time source-policy plugin. In particular,
a probe using default `autoImplicit` can accept an undeclared parameter that the project rejects.
Treat such a probe as provisional until the source passes the project build.

## Recommended Validation

For a convenient routine check, run:

```bash
./scripts/validate.sh
```

On a cold clone, fetch precompiled dependencies first:

```bash
lake exe cache get
./scripts/validate.sh
```

Validation also runs the native-probability retirement fixtures and
`lake exe retiredsweep --require-empty`. This gate rejects direct retired API references in
ArkLib declaration types and bodies, without a baseline exception. See
[probability conventions](probability-conventions.md) when porting an older branch.

## Validation By Change Type

### Existing Lean files only

```bash
./scripts/validate.sh
```

### Added, renamed, or deleted files under `ArkLib/`

```bash
git add path/to/newfile.lean
./scripts/validate.sh
```

`./scripts/update-lib.sh` only considers tracked files, and fails fast if untracked
`ArkLib/**/*.lean` files are present.

### Compile-time acceptance tests

Place examples and regression tests under `ArkLibTest/`, mirroring the production module path.
Run `lake test` to build them; `./scripts/validate.sh` runs this target by default and rejects all
test warnings, including admissions. Stage new tests so source linting and the trust inventory
include them. Production modules must not import tests.

Typed Interaction PRs also have a focused hosted check, including when stacked on a feature
branch. It compiles all tracked modules under `ArkLib/Interaction/`, `ArkLibTest/Interaction/`,
`ArkLib/ProofSystem/Sumcheck/Interaction/` and `ArkLibTest/ProofSystem/Sumcheck/Interaction/` with
the existing build-time source-policy plugin and rejects every warning in those modules,
including admissions. This is early feedback, not a replacement for `lake test` or the full
validation/axiom gate before merging to `main`. The semantic acceptance requirements live in
[`../design/01c-access-execution-contract.md`](../design/01c-access-execution-contract.md).

### Lean source-policy checks

```bash
lake exe lint-style
```

`./scripts/validate.sh` runs this gate by default. The Lean executable scans every module imported
by `ArkLib.lean` and every tracked `ArkLibTest` module, parses import headers with Lean itself, and has no exception file. It allows
project-specific mathematical Unicode notation, while rejecting invisible controls, bidirectional
controls, and nonstandard space characters that can conceal source changes. It also rejects
blanket package-root imports. The normal `lake build` loads ArkLib's Lean syntax-tree plugin, which
rejects source-level linter suppressions in their actual parsed context.

The header policy understands the Lean module system, so `module`, `public import`, `meta import`
and `import all` all parse, and it pins the canonical header order every file under `ArkLib/`
follows. See [`module-system.md`](module-system.md).

If the task is specifically Lean warning cleanup, follow
[`../skills/fix-lean-warnings.md`](../skills/fix-lean-warnings.md).

### Filling a `sorry`, or work that must stay axiom-clean

```bash
./scripts/validate.sh --axioms
```

This first runs `./scripts/test-axiomsweep.sh` — the executable fixture matrix under
`scripts/AxiomSweepTestFixtures/` that certifies the sweep tool itself (gate directions,
the native-trust floor, and the exit-code contract) — and then
`lake exe axiomsweep --check`: a kernel-level sweep of every `ArkLib.*`
declaration's axiom dependencies (the `#print axioms` information, library-wide) diffed
against the committed baseline `scripts/axiom_baseline.json`. It fails on *new* `sorryAx`
or non-standard-axiom taint, while reporting closed gaps without blocking cleanup.

A PR may be opened with unfinished proofs, but merging into `main` must not introduce new
`sorry`/`admit` or additional admitted proof debt. Compare the source and baseline diffs against
the canonical base; a baseline edit cannot make new debt mergeable, and closing another gap does
not offset a new admission. Refresh the baseline only for verified closures or renames of
existing debt, and commit that reviewed bookkeeping in the same PR:

```bash
lake exe axiomsweep --update-baseline
```

The baseline's `sorry` and `nonstandard` lists are empty. Its `solicited` list holds the only
admitted statements: true external results, each with a tracking issue linked from its docstring,
whose proofs are left open for contributors
([issue #1352](https://github.com/Verified-zkEVM/ArkLib/issues/1352)). The sweep rejects a
solicited entry that no longer depends on `sorryAx`, depends on another nonstandard axiom, lacks
its issue link, or has a dependent outside the solicited list, and `--update-baseline` preserves
the list. Adding an entry needs maintainer review; see
[`scripts/README.md`](../../scripts/README.md) for the exact rules.

Native-compiler trust
(`Lean.ofReduceBool`, `Lean.trustCompiler`, and the per-declaration
`…._native.<tactic>.ax_<n>_<n>` axioms that `native_decide`-style tactics mint) is held to
a zero-debt rule: no baseline edit can green it, and `--update-baseline` refuses to write
while such taint is present — remove the dependency instead.

CI enforces both the fixture matrix and the library regression check (see `ci.yml`).
It also runs `scripts/source-trust-audit.py` over every tracked Lean file under `ArkLib/` and `ArkLibTest/`.
That deterministic, comment/string-aware inventory reports source-only constructs that an
environment sweep cannot see reliably: admissions in examples or defaults/autoparams and
constructs in files outside the imported roots. Compare this inventory with the PR base when
checking for new admissions, for example with
`python3 scripts/source-trust-audit.py --base-ref origin/main` after fetching the canonical base.
The inventory complements the kernel sweep; neither a net count nor a refreshed baseline
substitutes for reviewing new source admissions. Working branches may still contain unfinished
proofs while their PR is under review.

### Docstrings, blueprint, or website changes

For prose-only docstring corrections or citation relocation, run the normal validation gate,
compile the changed Lean modules directly, and verify citation keys and links. Full API
documentation generation is optional for these edits; it also processes imported dependencies
and can be substantially slower than a warm Lean build.

When changing documentation rendering, build configuration, or generated API-page behavior, or
when a complete API preview is requested, run:

```bash
./scripts/validate.sh --docs
```

For website or blueprint output, run:

```bash
./scripts/validate.sh --site
```

`./scripts/build-web.sh` assembles the site, and skips blueprint generation if `leanblueprint`
is not installed. If blueprint output matters, install it first:

```bash
python3 -m pip install leanblueprint
```

## Important Notes

- `./scripts/validate.sh` is the recommended convenience wrapper for routine local validation.
  `./scripts/validate.sh --help` lists its default and optional checks.
- By default it runs `lake build` and `lake test`, rejects non-`sorry` warnings under `ArkLib/` and
  every warning under `ArkLibTest/`, runs the Lean-native source-policy gate and its plugin tests,
  runs the retired-API sweep, runs the compiled `toyproblem-runtime`, `hachi-runtime`,
  `sumcheck-runtime`, and `fri-extractor-runtime` checks, checks generated imports, tests the
  build-timing report, checks documentation integrity, and lints knowledge-base inputs.
- The lower-level scripts remain valid when you only want one specific check.
- `docs/kb/_generated/**` freshness is handled by the KB workflow's rolling generated-files PR,
  not by ordinary PR validation (see [generated files](generated-files.md)).
- `scripts/build-project.sh` is a compile-only helper, not the convenience wrapper.
- `scripts/README.md` is the inventory of helper scripts.
- Only run docs and site builds when those surfaces are relevant; they are slower and more
  tool-dependent than normal Lean builds.
- `--lint` remains a deprecated compatibility flag; style linting is always enforced.

## Checking axiom hygiene correctly

New declarations may depend only on a subset of `{propext, Classical.choice, Quot.sound}`.
Custom axioms, new admissions, and native-compiler trust dependencies must not merge (see
[Review and Merge Readiness](../../CONTRIBUTING.md#review-and-merge-readiness)). Two traps make a
naive check report success on something that should fail:

- **`#print axioms` is only meaningful for declarations that elaborated cleanly.**
  (`Lean.collectAxioms` does traverse both the type and the value, so a `sorry`-patched
  statement *does* report `sorryAx` — but a declaration that failed to elaborate outright may
  not exist to probe at all, and probing a *different*, successfully-elaborated declaration
  proves nothing about the broken one.) Check the file compiles with zero errors first; a
  belt-and-braces `(← getConstInfo n).type.hasSorry = false` assertion is cheap in sweep
  metaprograms. A silent `#print axioms` result on its own is not evidence the intended
  statement was proved.
- **A metaprogram sweep over the environment silently skips private declarations**, whose internal
  names are mangled. De-mangle with `Lean.privateToUserName?` before filtering by module, or the
  sweep will quietly under-report.

When reporting results, prefer "axiom-clean against the baseline" over "axiom-free", and state the
counting basis (public / source-level / all-non-internal) — declaration totals are not comparable
across differently-written probes, whereas the set of `sorryAx` carriers is.

## Compiled execution checks

Some things a theorem cannot state — that a definition compiles to code at all, and that running
it gives the expected answer — are checked by compiled executables under `scripts/`, declared as
`lean_exe` targets in `lakefile.toml` and run by `validate.sh`:

| target | file | what it certifies |
| --- | --- | --- |
| `toyproblem-runtime` | `scripts/ToyProblemRuntime.lean` | the toy-problem launch cone |
| `hachi-runtime` | `scripts/HachiRuntime.lean` | the nonrecursive Hachi honest-prover path |
| `sumcheck-runtime` | `scripts/SumcheckRuntime.lean` | CompPoly messages and honest multivariate execution, including private effects, public abort and the retained original oracle |
| `fri-extractor-runtime` | `scripts/FriExtractorRuntime.lean` | measured FRI extraction, input guards, raw interpolation corner cases, and exact small instruction counts |

**Put them here, not under `ArkLib/`.** A file under `ArkLib/` is picked up by the generated
library root, so a `#eval` in one is paid on every build by everyone; and `#eval` runs in the
interpreter, which is far slower than compiled code. The pattern each file follows is a
`check : String → Bool → IO Unit` that throws on failure, a `run : IO Unit` listing the checks,
and `def main := run`.

Two things to get right when adding one:

- **Make each check lazy** — `def myCheck : Unit → Bool := fun _ => …`, not `def myCheck : Bool`.
  Top-level values of non-function type are evaluated at *module initialization*, so an eager
  check runs before `main` does. A slow one then hangs the executable before it can print
  anything, and per-check timings all read zero because the work already happened.
- **Keep the gated checks fast, and put slow ones behind a flag.** `hachi-runtime` gates on its
  millisecond checks and hides its composed protocol run behind `--full` (that run passes, but
  takes about six minutes — the honest sumcheck prover dominates), with `--timing` for per-check
  costs.

## Optional Direct Commands

You can still run the underlying pieces directly when debugging a specific issue:

```bash
lake build
lake exe toyproblem-runtime
lake exe hachi-runtime
lake exe sumcheck-runtime
lake exe fri-extractor-runtime
./scripts/check-imports.sh
python3 ./scripts/check-docs-integrity.py
python3 ./scripts/kb/lint.py
./scripts/test-axiomsweep.sh
lake exe axiomsweep --check
```

If you specifically need to regenerate `ArkLib.lean`, use:

```bash
./scripts/update-lib.sh
```

If blueprint output matters and `leanblueprint` is missing:

```bash
python3 -m pip install leanblueprint
```

## CI Mapping

- [`../../.github/workflows/ci.yml`](../../.github/workflows/ci.yml)
  runs the timing-enabled main build on PRs, merge groups, pushes to `main`, and a nightly
  schedule. It builds incrementally from the latest `main` build (see
  [Build Cache](#build-cache)), times the library build, the native build, and the
  `./scripts/validate.sh` path, runs the
  source trust inventory plus axiom-sweep fixture matrix and library regression baseline
  (all axiom verdicts enforcing), and reuses that build for blueprint/declaration
  validation and API-documentation generation. The PR-head job has read-only contents
  permission; on pushes, a separate job deploys its generated static-site artifact with
  Pages/OIDC permission. It uploads timing artifacts consumed by the trusted
  [`../../.github/workflows/build-timing-report.yml`](../../.github/workflows/build-timing-report.yml)
  workflow, which renders the report and posts it on the PR.
- [`../../.github/workflows/interaction.yml`](../../.github/workflows/interaction.yml)
  provides focused compilation and zero-warning checks for typed Interaction production and
  acceptance modules. It also runs on feature-base stacked PRs. Its read-only job restores,
  but never saves, the dependency and build caches and does not retain checkout credentials. Passing
  this check does not waive the full validation/axiom gate for the eventual `main` target.
- [`../../.github/workflows/check-imports.yml`](../../.github/workflows/check-imports.yml)
  checks that `ArkLib.lean` matches the tracked source tree.
- [`../../.github/workflows/docs-integrity.yml`](../../.github/workflows/docs-integrity.yml)
  checks that `AGENTS.md` exists and local markdown links resolve.
- [`../../.github/workflows/kb-generated.yml`](../../.github/workflows/kb-generated.yml)
  regenerates KB indexes and missing cited-paper stubs nightly and after pushes to `main` that
  change the bibliography, KB papers or sources, or the KB scripts. It updates one rolling PR from
  the `automation/kb-generated` branch and enables auto-merge on it.
- [`../../.github/workflows/summary.yml`](../../.github/workflows/summary.yml) posts an automated
  summary on each opened or updated PR, and
  [`../../.github/workflows/review.yml`](../../.github/workflows/review.yml) runs an automated
  review when a maintainer comments `/review` on a PR.
- [`../../.github/workflows/update.yml`](../../.github/workflows/update.yml) checks for new Lean
  and Mathlib releases every seven days and opens an update PR or issue for each, and
  [`../../.github/workflows/release-tag.yml`](../../.github/workflows/release-tag.yml) tags a
  release when `lean-toolchain` changes on `main`.

To validate a stacked PR while it targets a feature branch, dispatch the existing CI, import,
and docs-integrity workflows on its published head branch:

```bash
review_branch=your-published-head-branch
gh workflow run ci.yml --ref "$review_branch"
gh workflow run check-imports.yml --ref "$review_branch"
gh workflow run docs-integrity.yml --ref "$review_branch"
gh run list --branch "$review_branch" --event workflow_dispatch \
  --json workflowName,headSha,status,conclusion,url
```

Check that each run's `headSha` equals the reviewed commit, and retain the run URLs with the
validation evidence. A later push needs checks for its new head. Dispatch uses the existing
read-only CI build job; the Pages publisher runs only on push events. Local validation, required
GitHub reviews, and the eventual main-target and merge-queue checks still apply.

Pull requests enter GitHub's merge queue after their normal review and required checks pass. The
queue creates a temporary integration ref containing the queued changes on current `main`; the CI,
import, and docs-integrity workflows run again on that `merge_group` ref before GitHub may merge it.
The CI validation path includes the Lean-native source-policy gate. PR-only timing comparisons and
comments remain attached to the ordinary PR run and are intentionally skipped for merge groups,
which do not carry a pull-request payload.

## Build Cache

CI keeps two caches. The dependency cache holds `.lake/packages` and is keyed by
`lake-manifest.json` and `lean-toolchain`. The build cache holds ArkLib's own `.lake/build`; every
`main` run saves one, and every run restores the newest. Lake decides what to rebuild from content
hashes of each module's source and imports, so a restored build is only a starting point: a PR
rebuilds the modules it changed and everything that imports them, and nothing else. Lake stores
each module's messages in its trace, so warnings from modules it does not rebuild are replayed and
the warning budgets still see them.

Only `main` saves caches. Pull request and merge-queue runs restore them and discard their own
build, so untrusted code never publishes an artifact another run loads, and the repository's 10 GB
cache budget holds `main` builds only. For the same reason a push to `main` waits for the running
`main` build instead of cancelling it.

The nightly scheduled run, and a manual run with `clean_build` set, skips the build cache and
builds from scratch. That keeps an absolute build-time trend and checks that nothing passes only
because of stale cached output.

## Manual Timing Helper

If you need to reproduce the timing workflow locally, the same helper script can
capture a measurement and render a report:

```bash
export BUILD_TIMING_LOG_DIR=/tmp/build-timing
bash scripts/build_timing_report.sh run library_build /tmp/build-timing/results.jsonl -- \
  bash -eo pipefail -c 'lake build'
bash scripts/build_timing_report.sh run native_build /tmp/build-timing/results.jsonl -- \
  bash -eo pipefail -c 'lake build toyproblem-runtime hachi-runtime sumcheck-runtime fri-extractor-runtime lint-style'
bash scripts/build_timing_report.sh run test_path /tmp/build-timing/results.jsonl -- \
  bash -eo pipefail -c './scripts/validate.sh'
bash scripts/build_timing_report.sh render /tmp/build-timing/results.jsonl
```

Read the rows in that order, because they share one tree and each leaves it warmer:

- `library_build` is `lake build` on whatever the build cache left: the changed modules and their
  importers, or everything when no cache was restored.
- `native_build` carries the `.c.o` chain that the compiled executables link — currently
  `toyproblem-runtime`, `hachi-runtime`, `sumcheck-runtime`, `fri-extractor-runtime`, and `lint-style`.
  It is the row that swings on `.lake` cache state, so a dependency bump shows its cost here. **Adding a compiled executable to
  `validate.sh` means
  adding it to this command too**, or its link cost lands in `test_path` instead.
- `test_path` is therefore the cost of the validation gate itself on an already-built project,
  not of a cold `./scripts/validate.sh`. CI passes no flags, so `--docs`, `--site` and
  `--axioms` never appear in it.

A row whose measurement could not be taken renders as `measurement failed`, not as a missing row.

Wall time of an incremental build depends on how much the change invalidated, so it is not
comparable across PRs. The per-module comparison is. Lake prints `Built <module> (<time>)` exactly
for the modules it rebuilt, and `scripts/module_times.py` keeps a table of the latest such time
for every module in `.lake/build/arklib-module-times.json`, which travels with the build cache.
The report compares each rebuilt module against that table, and the table's sum before and after
the run estimates clean-build compile time without running a clean build. Module times are printed
with the precision Lake reported (`22`, `3.5`, `0.770`); Lake emits whole seconds above 10s.

Timing artifacts include the PR head, actual measured checkout (normally GitHub's synthetic PR
merge commit), exact base, dependency-manifest hash, exact/fallback cache state, and runner
image/version. Reports show both wall time and CPU work (`user + sys`). Movement in both suggests
changed compilation work or runner speed; wall-only movement more often indicates scheduling or I/O
contention. These diagnostics improve attribution, but one hosted-runner sample is still not a
performance verdict. Per-file rows are leads to remeasure, not blocking regression claims.
