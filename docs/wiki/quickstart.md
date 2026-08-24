# Quickstart

This page is the recommended agent playbook for commands and validation.
Use it as the main guide for routine local checks.

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

### Lean-heavy refactors or cleanup

```bash
./scripts/validate.sh --lint
```

This adds `./scripts/lint-style.sh` to the convenience wrapper. The main CI build runs with
`lint: false`, so this is opt-in.
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
against the committed baseline `scripts/axiom_baseline.json`. It fails only on *new*
`sorryAx` or non-standard-axiom taint, so pre-existing gaps stay allowed. If you
intentionally add a tagged `sorry` (or close one), refresh and commit the baseline:

```bash
lake exe axiomsweep --update-baseline
```

The baseline is an allowlist for `sorryAx` debt only. Native-compiler trust
(`Lean.ofReduceBool`, `Lean.trustCompiler`, and the per-declaration
`…._native.<tactic>.ax_<n>_<n>` axioms that `native_decide`-style tactics mint) is held to
a zero-debt rule: no baseline edit can green it, and `--update-baseline` refuses to write
while such taint is present — remove the dependency instead.

CI runs the fixture matrix as an enforcing step and the library check report-only while
the baseline soaks (see `ci.yml`).

### Docstrings, blueprint, or website changes

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
- By default it runs `lake build`, the compiled `toyproblem-runtime` checks,
  `./scripts/check-imports.sh`, and `python3 ./scripts/check-docs-integrity.py`, plus
  knowledge-base linting from source inputs.
- The lower-level scripts remain valid when you only want one specific check.
- `docs/kb/_generated/**` freshness is handled by generated-files PRs from the main-branch KB
  workflow, not by ordinary PR validation.
- `scripts/build-project.sh` is a compile-only helper, not the convenience wrapper.
- `scripts/README.md` is the inventory of helper scripts.
- Only run docs and site builds when those surfaces are relevant; they are slower and more
  tool-dependent than normal Lean builds.
- `--lint` fails on `main` as well as on feature branches: `scripts/lint-style.sh` reports a
  large pre-existing style backlog, and `validate.sh` runs under `set -euo pipefail`, so `--lint`
  **aborts the script before `--docs`**. To exercise the docgen gate, run
  `./scripts/validate.sh --docs` on its own. When checking that a branch adds no new style lint,
  compare the `(file, error-kind)` multiset against the merge-base rather than the total count.

## Checking axiom hygiene correctly

ArkLib's axiom-clean baseline is exactly `{propext, Classical.choice, Quot.sound}` (see
[`../skills/prove-milestone.md`](../skills/prove-milestone.md) invariant 6). Two traps make a
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

## Optional Direct Commands

You can still run the underlying pieces directly when debugging a specific issue:

```bash
lake build
lake exe toyproblem-runtime
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
  runs the timing-enabled main build on PRs and pushes to `main`, measures a
  clean build, a warm rebuild, and the `./scripts/validate.sh` path, runs the
  axiom-sweep fixture matrix (enforcing) and the library sweep report-only,
  reuses that build for blueprint and declaration validation, and builds and
  deploys API documentation on pushes to `main`. It then uploads timing artifacts
  and posts a comparison report on same-repo PRs.
- [`../../.github/workflows/check-imports.yml`](../../.github/workflows/check-imports.yml)
  checks that `ArkLib.lean` matches the tracked source tree.
- [`../../.github/workflows/docs-integrity.yml`](../../.github/workflows/docs-integrity.yml)
  checks local markdown links and the `CLAUDE.md` symlink.
- [`../../.github/workflows/kb-generated.yml`](../../.github/workflows/kb-generated.yml)
  opens generated-files PRs for KB indexes and missing cited-paper stubs after pushes to `main`.

## Manual Timing Helper

If you need to reproduce the timing workflow locally, the same helper script can
capture a measurement and render a report:

```bash
bash scripts/build_timing_report.sh run clean_build /tmp/build-timing.jsonl -- \
  bash -eo pipefail -c 'rm -rf .lake/build && lake build'
bash scripts/build_timing_report.sh run warm_rebuild /tmp/build-timing.jsonl -- \
  bash -eo pipefail -c 'lake build'
bash scripts/build_timing_report.sh run native_build /tmp/build-timing.jsonl -- \
  bash -eo pipefail -c 'lake build toyproblem-runtime'
bash scripts/build_timing_report.sh run test_path /tmp/build-timing.jsonl -- \
  bash -eo pipefail -c './scripts/validate.sh'
bash scripts/build_timing_report.sh render /tmp/build-timing.jsonl
```

Read the rows in that order, because they share one tree and each leaves it warmer:

- `clean_build` and `warm_rebuild` bracket the incremental-build signal.
- `native_build` carries the `.c.o` chain that `lake exe toyproblem-runtime` links. It is the row
  that swings on `.lake` cache state, so a dependency bump shows its cost here.
- `test_path` is therefore the cost of the validation gate itself on an already-built project,
  not of a cold `./scripts/validate.sh`. CI passes no flags, so `--lint`, `--docs`, `--site` and
  `--axioms` never appear in it.

A row whose measurement could not be taken renders as `measurement failed`, not as a missing row.
Per-target times are printed with the precision Lake reported (`22`, `3.5`, `0.770`); Lake emits
whole seconds above 10s, so those figures are not accurate to two decimals.
