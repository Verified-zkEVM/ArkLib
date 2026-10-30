# Generated and Derived Files

Edit the source of truth, not the output.

| Path | What it is | Edit directly? | Source of truth / refresh path |
| --- | --- | --- | --- |
| `ArkLib.lean` | generated umbrella imports | No | `./scripts/update-lib.sh` or `./scripts/check-imports.sh` |
| `.lake/` | build artifacts and cache | No | `lake build`, `lake exe cache get` |
| `blueprint/lean_decls` | referenced Lean declarations | No | official Lean blueprint post-parse callback over `blueprint/src/`; `leanblueprint web` refreshes it in CI |
| `blueprint/web/`, `blueprint/print/` | generated blueprint output | No | `leanblueprint web`, `leanblueprint pdf`, or `./scripts/build-web.sh` |
| `blueprint/src/print.pdf` | generated blueprint PDF inside source tree | No | `leanblueprint pdf` |
| `home_page/docs/` | copied API docs for the site | No | `./scripts/build-web.sh` |
| `dependency_graphs/` | generated dependency visualizations | No | rerun scripts under `scripts/dependency_analysis/` |
| `scripts/axiom_baseline.json`, `sorry` and `nonstandard` lists | kernel-level accounting of admitted debt; both lists are empty on `main` | No | `lake exe axiomsweep --update-baseline` after `lake build`, only for verified closures or renames of existing debt. Baseline edits cannot authorize new debt. Native-trust taint prevents the update |
| `scripts/axiom_baseline.json`, `solicited` list | reviewed solicited proofs: true external results left open for contributors | Only with maintainer review | hand-maintained; `--update-baseline` preserves it. A PR that proves an entry removes it. Rules in [`scripts/README.md`](../../scripts/README.md), tracking [issue #1352](https://github.com/Verified-zkEVM/ArkLib/issues/1352) |
| `docs/kb/_generated/references.json` | normalized bibliography export | No | `python3 ./scripts/kb/sync_from_bib.py` |
| `docs/kb/_generated/lean-citations.json` | generated map from Lean files to cited keys | No | `python3 ./scripts/kb/extract_lean_citations.py` |
| `docs/kb/_generated/declarations.json` | declaration catalog across `ArkLib/` (file, line, kind, namespace, name, brief signature, docstring head) | No | `python3 ./scripts/kb/extract_declarations.py` |
| `docs/kb/_generated/dedup-report.md` | duplicate-candidate review aid (same-short-name groups + cross-file near-duplicate docstrings) derived from the catalog | No | `python3 ./scripts/kb/find_dedup_candidates.py` |

`python3 ./scripts/kb/regenerate.py` refreshes all four `docs/kb/_generated/` files in one run and
scaffolds missing cited-paper stubs (`--no-paper-stubs` skips the stubs). The KB workflow runs it;
ordinary feature PRs do not (see below).

## Important Notes

- `./scripts/update-lib.sh` only uses tracked `ArkLib/**/*.lean` files, and fails fast if
  untracked Lean files would be skipped. `git add` new paths before running validation.
- The generator wraps any `public import` that would exceed 100 characters, placing its module
  name on an indented continuation line.
- After merging `main` into a branch that adds Lean files, rerun `./scripts/update-lib.sh` and
  stage `ArkLib.lean`. Resolving the umbrella conflict with only one side can omit the branch's
  modules. Branches predating the module-system migration also need the
  [current file headers](module-system.md#the-canonical-file-shape) before validation.
  Keep compile-time canaries in the mirrored `ArkLibTest/` path, where `lake test` checks them
  without exporting test helpers through the production umbrella.
- Do not commit `docs/kb/_generated/**` changes from ordinary feature PRs. They are proposed by
  the single rolling generated-files PR maintained by `.github/workflows/kb-generated.yml`.
- The KB refresh runs nightly, on manual dispatch, and immediately after bibliography or KB source
  changes. Ordinary Lean merges are batched into the nightly refresh. The workflow updates the
  stable `automation/kb-generated` branch and explicitly dispatches the fixed CI, import, and docs
  workflows so bot-authored checks start automatically. The canonical CI validation path includes
  the Lean-native source-policy gate. The generated-path allowlist and repository human-review gate
  remain intact.
- Do not use GitHub's **Update branch** action on the rolling KB PR: a plain base merge does not
  regenerate its indexes. Dispatch the KB workflow or wait for the next nightly refresh instead.
- Missing cited-paper stubs under `docs/kb/papers/` and `docs/kb/sources/` are also scaffolded by
  that workflow. Commit paper pages in feature PRs only when they contain real ArkLib-specific
  content.
- Generated site and blueprint output are for review and deployment, not authoring.
- If a path looks derived, confirm its source of truth before editing it.

## Reusing local documentation caches

The pinned local doc-gen4 backend stores collected module data in
`.lake/build/api-docs.db`; its `.lake/build/doc-data/` files include completion markers and
build traces. A bibliography change can invalidate dependency `docInfo` facets as well as
ArkLib's own docs, so a warm Lean build can still need substantial documentation regeneration.
When reusing a completed documentation cache between matching dependency/bibliography snapshots,
wait for all documentation writers in both the source and destination to finish. Take a
consistent SQLite backup, including committed WAL pages, together with its matching module/core
`doc-data/` artifacts and bibliography data.
HTML generation has separate `*.docs_built` and
`*.docsHeader_built` completion files, with matching `.hash` and `.trace` files. For an identical
source snapshot, copy their HTML, static assets and `doc-manifest.json` too, or omit/quarantine
those exact HTML-marker families so doc-gen4 regenerates local outputs. Invalidate those HTML
markers when source content or the root-module set changes, even if old HTML exists, to ensure
a fresh rendering and index from the updated database. Preserve the module/core `*.doc` markers
and bibliography data; broad `*.doc*` invalidation discards the reusable module-data cache.
Completion markers alone supply neither database rows nor HTML/static files.

Use isolated writable caches for concurrent builds. Copied Lean traces can retain absolute source
paths from the former worktree. When changing source after relocation, check that affected module
traces refer to the current source path; stale foreign inputs can leave an incompatible compiled
module in use. With all writers stopped, quarantine those affected module traces and rebuild them
from the current source. Do not rewrite generated trace metadata. For a stack of related slices,
retaining one worktree path allows later validation runs to reuse completed artifacts without
concurrent writers.

A copied documentation database can also retain retired module rows. Its global name lookup can
then mix obsolete and current declaration documentation even when the generated module manifest
matches the current imports. Check affected declaration pages against their source, including
structure fields. Use a matching clean snapshot or regenerate the database with the pinned backend.
If using its module-deletion API to prune an isolated, backed-up copy, first prove each module is
absent from both source and registered files and that no retained module imports it. Verify database
integrity, foreign keys and unchanged retained rows before installing the consistent snapshot.
Before rerendering, quarantine each retired module's `declaration-data-{module}.bmp`,
`backrefs-{module}.json` and stale pages, along with the exact HTML completion markers. The backend
merges those per-module index and backreference files independently of its current import/database
closure. Preserve current module/core data. Overlay site assembly can retain removed pages, so
check its copy too. Do not patch rendered HTML or trace data.
