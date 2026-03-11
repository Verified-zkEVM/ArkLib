# Quickstart

This page is the canonical agent playbook for commands and validation.
Use it instead of treating `scripts/README.md` as the source of truth for what to run.

## Baseline

For ordinary Lean work:

```bash
lake build
```

On a cold clone, fetch precompiled dependencies first:

```bash
lake exe cache get
lake build
```

## Validation By Change Type

### Existing Lean files only

```bash
lake build
```

### Added, renamed, or deleted files under `ArkLib/`

```bash
git add path/to/newfile.lean
./scripts/check-imports.sh
lake build
```

`./scripts/update-lib.sh` uses `git ls-files 'ArkLib/*.lean'`, so new files must be staged or
tracked before the import check sees them.

### Lean-heavy refactors or cleanup

```bash
./scripts/lint-style.sh
```

This is a manual pre-PR check. The main CI build currently runs with lint disabled.
If the task is specifically Lean warning cleanup, follow
[`../skills/fix-lean-warnings.md`](../skills/fix-lean-warnings.md).

### Docstrings, blueprint, or website changes

```bash
DISABLE_EQUATIONS=1 lake build ArkLib:docs
./scripts/build-web.sh
```

`./scripts/build-web.sh` skips blueprint generation if `leanblueprint` is not installed. If
blueprint output matters, install it first:

```bash
python3 -m pip install leanblueprint
```

## Important Notes

- There is no single perfect local "run everything" script. `lake build` checks the package
  build, while import freshness for `ArkLib.lean` is a separate step.
- Do not use `scripts/build-project.sh` as the authoritative validator; it is only commented
  examples today.
- `scripts/README.md` is still useful as an inventory of helper scripts.
- Only run doc and website builds when those surfaces are relevant; they are slower and more
  tool-dependent than normal Lean builds.
