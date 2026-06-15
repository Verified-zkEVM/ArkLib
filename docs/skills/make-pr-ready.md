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
- Regenerate the derived citation metadata — do not hand-edit it:

  ```bash
  python3 ./scripts/kb/sync_from_bib.py          # refresh docs/kb/_generated/references.json
  python3 ./scripts/kb/extract_lean_citations.py # refresh docs/kb/_generated/lean-citations.json
  ```

- Confirm the regenerated files are consistent (no dangling keys, no missing entries) and stage
  them alongside your source changes.

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
