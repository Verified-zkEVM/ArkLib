# ArkLib Agent Guide

Lean 4 formalization of SNARK-related theory, interactive oracle reductions, and proof systems.
Start with [`README.md`](README.md) for project overview.

`AGENTS.md` is the canonical root guide. `CLAUDE.md` is a symlink to this file.

## Fast Start

1. For a convenient routine check, start with `./scripts/validate.sh`.
2. On a cold clone, run `lake exe cache get` first.
3. If you add, rename, or delete files under `ArkLib/`, `git add` new paths before validation.
4. If you also want Lean style linting, run `./scripts/validate.sh --lint`.
5. For docstring or docs work, `./scripts/validate.sh --docs` is a convenient add-on check.
6. Only build site or blueprint output when touching `blueprint/` or `home_page/`:
   `./scripts/validate.sh --site`.

## Where To Work

- `ArkLib/Data/` - reusable math, coding theory, polynomials, and supporting definitions.
- `ArkLib/OracleReduction/` - core IOR abstractions and security theory.
- `ArkLib/ProofSystem/` - protocol formalizations built on the core.
- `ArkLib/CommitmentScheme/` - commitments and opening arguments.
- `ArkLib/ToMathlib/`, `ArkLib/ToVCVio/` - bridge layers.
- `blueprint/src/` - deep design docs and bibliography.
- `scripts/` - repo utilities.

## Guardrails

- Lean defaults: `autoImplicit = false`; the long-file linter cap is `1500` unless a file opts
  out locally.
- `ArkLib.lean` is generated; do not hand-edit it.
- Edit source, not derived output such as `.lake/`, `blueprint/web/`, `blueprint/print/`,
  `dependency_graphs/`, or `home_page/docs/`.
- Pre-existing `sorry` blocks exist in active formalizations; distinguish existing gaps from new
  regressions.
- If a PR changes commands, repo structure, generated outputs, or the blueprint/citation
  workflow, update the matching page in [`docs/wiki/`](docs/wiki/README.md) in the same PR.
- Promote recurring agent learnings into [`docs/wiki/`](docs/wiki/README.md); do not let stable
  guidance live only in ephemeral notes.

## Deeper Docs

- [`docs/wiki/README.md`](docs/wiki/README.md) - hub and maintenance rules.
- [`docs/skills/README.md`](docs/skills/README.md) - reusable cross-cutting workflows.
- [`docs/wiki/quickstart.md`](docs/wiki/quickstart.md) - commands and validation.
- [`docs/wiki/repo-map.md`](docs/wiki/repo-map.md) - structure and module routing.
- [`docs/wiki/generated-files.md`](docs/wiki/generated-files.md) - source-of-truth rules for
  derived outputs.
- [`docs/wiki/blueprint-and-citations.md`](docs/wiki/blueprint-and-citations.md) - blueprint,
  references, and citations.

## Canonical Project Docs

- [`README.md`](README.md) - project overview.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) - style, naming, docstrings, citations, and large
  contributions.
- [`ROADMAP.md`](ROADMAP.md) - planned directions.
- [`BACKGROUND.md`](BACKGROUND.md) - background references.
