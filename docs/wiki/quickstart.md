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

This adds the baseline-aware declaration linter (`lake lint -- --no-build ArkLib`) and cheap
tracked Lean file metadata checks. The full text-style sweep remains available as
`./scripts/lint-style.sh` for cleanup work. CI uses `./scripts/lint-style-diff.py` to reject only
style regressions in changed `ArkLib/**/*.lean` files. The lint workflow also runs the Lean
text-style linter (`lake env lean --run scripts/lint-style.lean`) across ArkLib; the diff wrapper
keeps legacy Python checks that have not yet been ported upstream.
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
  cached build, a warm rebuild, `lake lint -- --no-build ArkLib`, and the
  `./scripts/validate.sh` path, then
  uploads timing artifacts and posts a comparison report on same-repo PRs.
- [`../../.github/workflows/lint.yml`](../../.github/workflows/lint.yml)
  runs text and style linting: trailing whitespace, tracked Lean file metadata, and
  no-new-text-style-errors checks for changed `ArkLib/**/*.lean` files.
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
bash scripts/build_timing_report.sh run cached_build /tmp/build-timing.jsonl -- \
  bash -eo pipefail -c 'lake build'
bash scripts/build_timing_report.sh render /tmp/build-timing.jsonl
```
