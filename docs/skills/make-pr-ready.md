# /make-pr-ready

Use this workflow to get a branch into shape before opening or finalizing a pull request.
It is a general checklist skill that chains the project's contribution guidelines, lint cleanup,
and citation generation into one pass.

## Goal

Leave the branch in a state where every contribution guideline is met, no Lean warnings remain,
and citation metadata is regenerated and consistent — so the PR can be opened without follow-up
churn.

## TODO List

Work through these in order. Do not stop until every item is complete.

### 0. Establish the real PR base

- Run `git fetch origin main` first, then compute scope and `_generated/` drift against
  **`origin/main`**, not local `main`. The local `main` ref can be many commits stale (e.g. you
  branched, then `origin/main` advanced via merges you never pulled). Diffing `main...HEAD` against
  a stale local `main` inflates the file list and can report phantom `_generated/` drift that
  actually matches the remote. Use `git diff --stat origin/main...HEAD` for scope and
  `git diff --quiet origin/main...HEAD -- docs/kb/_generated/` for the CI guard's real view.
- **Also account for uncommitted work.** `origin/main...HEAD` (three-dot) only shows *committed*
  changes; a make-pr-ready pass often runs with staged/working-tree edits still in flight (e.g. a
  half-finished file). Those appear only in `git diff HEAD` (or `git diff origin/main`, two-dot).
  Compute the real PR surface as the **union** of `git diff --stat origin/main...HEAD` (committed)
  and `git diff --stat HEAD` (uncommitted), and audit/lint every file in that union — not just the
  committed ones. The whole-tree view is `git diff --stat origin/main`.
- **If `_generated/` drift is already committed** (the branch committed regenerated outputs, not
  just dirtied the working tree), `git checkout origin/main -- docs/kb/_generated/` stages a
  *revert*, and you must **commit it** for the guard to pass — the guard compares the committed
  branch tip to `main`, so an uncommitted revert leaves HEAD still drifted. After staging the
  revert, `git diff --cached --stat` shows huge index-vs-HEAD numbers for `_generated/` — that is
  the size of the revert, **not** new drift; do not panic. Confirm the post-commit guard view with
  `git diff --cached --quiet origin/main -- docs/kb/_generated/` (must be clean).

### 1. Follow the contribution guidelines

- Read [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md) in full and make sure every changed file
  follows it. Check at least:
  - **Naming**: files `UpperCamelCase.lean`, types/structures `UpperCamelCase`, functions/terms
    `lowerCamelCase`, theorems/proofs `snake_case`, acronyms treated as words, American English
    spelling, and the theorem-naming logic (`_of_`, `left`/`right`, `ext`/`iff`/`inj`/`mono`).
  - **Symbol naming**: translate statements into names with the standard symbol dictionary;
    standardize on `≤`/`<`, avoid `≥`/`>` in statements.
  - **Variable conventions**: match the Mathlib-style variable roles (e.g. `R`/`M`/`G`/`F` for
    algebraic carriers, `i`/`j`/`k` for indices).
  - **Syntax and formatting**: lines under 100 chars, 2-space indent, spaces around `:`/`:=`/infix
    operators, `fun x ↦` over `λ`, `where` syntax for instances/structures, `by` at end of line,
    aligned `calc`, no empty lines inside definitions/proofs, prefer `<|`/`|>` over parentheses.
  - **File headers**: Apache 2.0 copyright/license/authors block at the top of every new file.
  - **Documentation**: module docstring (`/-! ... -/` with title, summary, notation, references)
    on each file; `/-- ... -/` docstrings on every definition and major theorem; sectioning
    comments where helpful.
  - **Normal forms, transparency, deprecation**: respect the standard-form, `def`/`abbrev`/
    `irreducible`, and `@[deprecated ...]` policies when relevant to the diff.
- Verify with `./scripts/validate.sh` (add `--lint` for style linting and `--docs` for docstring
  checks). Fix anything it flags.
  - If you added or removed `ArkLib/**.lean` files, run `./scripts/update-lib.sh` **and then
    `git add ArkLib.lean`**: the import check (`check-imports.sh`) uses `git diff --quiet`
    (working tree vs index), so a regenerated-but-unstaged `ArkLib.lean` still reports
    "Import file is out of date".
  - `--docs` runs the full `doc-gen4` site build (`bibPrepass` + per-module pages), which is
    memory- and disk-heavy and may be killed (exit 137) or fill the disk in constrained
    environments. That failure is about the doc *renderer*, not your docstrings/citations —
    verify those directly (every decl has a `/-- … -/`; citation keys resolve in
    `references.bib`; the `kb` regeneration below is consistent) and note the `--docs` limitation
    rather than churning on it.
  - `--lint` (`lint-style.sh`) reports **repo-wide pre-existing** style debt — hundreds of
    `ERR_*` lines in files you did not touch. Do **not** try to clear all of it; scope style
    fixes to your changed files (lint them individually with
    `python3 scripts/lint-style.py <your-files>`), and treat the **default** `validate.sh`
    (build + Data warning budget + `check-imports` + `check-docs-integrity` + `kb/lint`) as the
    real gate. Capture its true exit with `rc=$?` on its own line — a trailing
    `… ; echo "EXIT $?"` reports the `echo`'s exit (always 0) and masks a failing validate.
  - The **Data warning budget** fails on any non-`sorry` warning under `ArkLib/Data/`. A
    toolchain/Mathlib bump commonly introduces **deprecation** warnings (e.g.
    `X has been deprecated: Use Y instead`) — fix these by switching to the suggested name.
- Confirm the eventual PR title/description will follow the
  `<type>(<scope>): <subject>` convention (imperative, lowercase, no trailing dot) and includes
  motivation, contrast with previous behavior, and issue references.

### 2. Fix Lean warnings

- Follow the [`fix-lean-warnings.md`](fix-lean-warnings.md) skill end to end for every changed
  `.lean` file: check with `ReadLints` / `lake env lean path/to/File.lean`, fix by safety order,
  re-check after each batch, and do not stop until `ReadLints` is clean and the file still builds.

### 3. Generate citations correctly

- Make sure every paper cited in a Lean docstring uses a citation key (e.g. `[BCIKS20]`), each
  citing file has a `## References` section, and every key has a matching BibTeX entry in
  `blueprint/src/references.bib` (see the citation policy in
  [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md) and the workflow in
  [`../wiki/blueprint-and-citations.md`](../wiki/blueprint-and-citations.md)).
- **Do not commit `docs/kb/_generated/` changes in a feature PR.** The CI job's first step,
  "Reject generated KB updates in PRs" ([`ci.yml`](../../.github/workflows/ci.yml)), fails the
  build if your branch's `docs/kb/_generated/` differs from `main` in **any** way — and a
  **deletion counts as a diff** just like a modification or addition. These files are refreshed
  only on `main`, by [`kb-generated.yml`](../../.github/workflows/kb-generated.yml), which opens an
  `automation/kb-generated-*` PR after merge. The guard runs before the Lean build, so a stray
  `_generated/` diff blocks CI before the build even starts (and removing the files does **not**
  help — the directory must match `main` exactly).
- You may regenerate the derived metadata **locally to check consistency** — do not hand-edit it —
  but **revert the `_generated/` outputs before committing** so the directory matches `main`:

  ```bash
  python3 ./scripts/kb/sync_from_bib.py          # writes docs/kb/_generated/references.json
  python3 ./scripts/kb/extract_lean_citations.py # writes docs/kb/_generated/lean-citations.json
  # ... inspect for consistency, then:
  git checkout origin/main -- docs/kb/_generated/ # restore to main's state; do NOT stage these
  ```

  If your branch has already diverged in `docs/kb/_generated/` (drift, an accidental delete, or a
  regenerate that got committed), restore it the same way: `git fetch origin main` then
  `git checkout origin/main -- docs/kb/_generated/`, and commit so the guard passes.
- Confirm the regenerated files are consistent (no dangling keys, no missing entries), but stage
  **only** your source changes plus any scaffolded `docs/kb/papers/` / `docs/kb/sources/` pages
  (those are *not* under `_generated/` and are allowed in feature PRs) — never the `_generated/`
  outputs.
- `kb/lint.py` does **not** verify that every cited key has a BibTeX entry. Check for dangling
  keys yourself: grep each `[KEY]` used in docstrings against `blueprint/src/references.bib` and
  add any missing entry (then regenerate). A key can be "present-looking" but actually a different
  paper — confirm the entry's title/authors match the citation, not just that the key exists.
- Also check the **reverse direction — orphan entries**: a BibTeX key (and/or a scaffolded
  `docs/kb/papers/<KEY>.md` + `docs/kb/sources/<KEY>/` page) that **no** `[KEY]` in any `.lean`
  docstring or blueprint `.tex` actually cites. `kb/lint` passes on these (they are internally
  consistent), but they are cruft a reviewer will question — especially a kb page whose
  `related_modules` frontmatter points at files that do not cite it. For each orphan, decide with
  the author whether to (a) wire it in as a real `[KEY]` citation in the relevant file (+ a
  `## References` section), or (b) remove it: drop the bib entry and `git rm` the
  `papers/<KEY>.md` + `sources/<KEY>/` pages. After removing, grep tracked files for any markdown
  link to the deleted page (`check-docs-integrity.py` fails on a broken link).
- If you **moved or renamed** any `.lean` file, regeneration does **not** fix hand-maintained
  `docs/kb/papers/*.md` pages (they are scaffolded once, then curated). Grep `docs/**/*.md` for the
  old path and update curated links + `related_modules` frontmatter — the default `validate.sh`
  `check-docs-integrity.py` step fails on broken links. Running `kb/regenerate.py` after adding a
  new cited key also **scaffolds** a new `docs/kb/papers/<KEY>.md` + `docs/kb/sources/<KEY>/`;
  stage those too.

### 4. Suggest skill improvements

- After completing the pass, tell the user whether this skill could be improved: any new recurring
  guideline gap, a missing or stale step, a better ordering, or a check worth adding. Follow the
  Maintenance Rule in [`README.md`](README.md) and update this file if the improvement is likely to
  help the next agent.

## Persistence Rule

Only consider the PR ready when:

1. `./scripts/validate.sh` (with `--lint` / `--docs` as appropriate) succeeds.
2. `ReadLints` is clean for every changed `.lean` file.
3. Citation metadata is regenerated and consistent.
4. You have reported any suggested improvements to this skill.
