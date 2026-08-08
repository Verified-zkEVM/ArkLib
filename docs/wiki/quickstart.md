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

`./scripts/update-lib.sh` only considers tracked files, and now fails fast if untracked
`ArkLib/**/*.lean` files are present.

### Lean-heavy refactors or cleanup

```bash
./scripts/validate.sh --lint
```

This adds `./scripts/lint-style.sh` to the convenience wrapper. The main CI build currently runs
with lint disabled, so treat this as opt-in for now.
If the task is specifically Lean warning cleanup, follow
[`../skills/fix-lean-warnings.md`](../skills/fix-lean-warnings.md).

### Docstrings, blueprint, or website changes

```bash
./scripts/validate.sh --docs
```

For website or blueprint output, run:

```bash
./scripts/validate.sh --site
```

`./scripts/build-web.sh` is still what assembles the site, and it skips blueprint generation if
`leanblueprint` is not installed. If blueprint output matters, install it first:

```bash
python3 -m pip install leanblueprint
```

## Important Notes

- `./scripts/validate.sh` is the recommended convenience wrapper for routine local validation.
- By default it runs `lake build`, `./scripts/check-imports.sh`, and
  `python3 ./scripts/check-docs-integrity.py`, plus knowledge-base linting from source inputs.
- The lower-level scripts remain valid when you only want one specific check.
- `docs/kb/_generated/**` freshness is handled by generated-files PRs from the main-branch KB
  workflow, not by ordinary PR validation.
- `scripts/build-project.sh` is now just a compile-only helper, not the convenience wrapper.
- `scripts/README.md` is still useful as an inventory of helper scripts.
- Only run docs and site builds when those surfaces are relevant; they are slower and more
  tool-dependent than normal Lean builds.
- `--lint` currently fails on `main` as well as on feature branches: `scripts/lint-style.sh`
  reports a large pre-existing style backlog and `validate.sh` runs under `set -euo pipefail`, so
  `--lint` **aborts the script before `--docs`**. To exercise the docgen gate, run
  `./scripts/validate.sh --docs` on its own. When checking that a branch adds no new style lint,
  compare the `(file, error-kind)` multiset against the merge-base rather than the total count.

## Checking axiom hygiene correctly

ArkLib's axiom-clean baseline is exactly `{propext, Classical.choice, Quot.sound}` (see
[`../skills/prove-milestone.md`](../skills/prove-milestone.md) invariant 6). Two traps make a
naive check report success on something that should fail:

- **`#print axioms` / `Lean.collectAxioms` do not traverse a declaration's *type*.** A theorem
  whose *statement* failed to elaborate gets a `sorry`-typed header and reports **no axioms at
  all** — it looks *cleaner* than a genuine theorem. Always also assert
  `(← getConstInfo n).type.hasSorry = false`, or check the declaration compiles with zero errors
  first. A silent `#print axioms` result is not by itself evidence of anything.
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
./scripts/check-imports.sh
python3 ./scripts/check-docs-integrity.py
python3 ./scripts/kb/lint.py
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
  clean build, a warm rebuild, and the `./scripts/validate.sh` path, then
  uploads timing artifacts and posts a comparison report on same-repo PRs.
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
bash scripts/build_timing_report.sh render /tmp/build-timing.jsonl
```
