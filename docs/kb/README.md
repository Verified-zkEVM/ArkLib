# ArkLib Knowledge Base

This directory is ArkLib's persistent knowledge base for papers, concepts, audits, and filed
research/review notes.

Use this directory for substantive reference content.
Use [`../wiki/README.md`](../wiki/README.md) for operational guidance about working in the repo.

## Purpose

The knowledge base exists to make paper-driven work easier for both humans and agents.
It should help with:

- understanding what a cited paper contributes to ArkLib;
- mapping a Lean citation key to a repository-local summary page;
- giving review workflows a stable repository path for paper context;
- recording durable paper-to-ArkLib audits and comparisons;
- filing high-value answers that would otherwise be lost in chat history.

## Quick Start

If you only need the practical workflow:

1. If a Lean file cites `[KEY]`, start at `docs/kb/papers/KEY.md`.
2. If that page does not exist yet, add the BibTeX entry first if needed, then scaffold the paper
   page and source metadata.
3. If your PR changes how ArkLib uses or interprets a paper, update the corresponding KB page in
   the same PR.
4. Before sending a paper-driven PR for review, attach the relevant KB paper pages or use
   `python3 ./scripts/kb/review_context.py`.

Useful commands:

```bash
python3 ./scripts/kb/sync_from_bib.py
python3 ./scripts/kb/extract_lean_citations.py
python3 ./scripts/kb/lint.py
python3 ./scripts/kb/review_context.py --files ArkLib/ProofSystem/Whir/ProximityGen.lean --format review
```

## When To Touch The KB

You should usually update `docs/kb/` when:

- you add a new citation key to a Lean file;
- you add a substantial new paper-driven development;
- you discover that the current paper page is missing an important ArkLib touchpoint;
- you produce a durable theorem matrix, comparison, or review note that will help future work.

You usually do not need to update `docs/kb/` for:

- purely local refactors that do not change paper context;
- small proof edits in a paper-backed file where the KB page remains accurate;
- transient scratch notes that are not worth preserving.

## Canonical Identifier

The BibTeX key is the canonical identifier for a paper across:

- Lean docstring citations like `[BCIKS20]`;
- `blueprint/src/references.bib`;
- paper pages under `docs/kb/papers/`;
- source metadata under `docs/kb/sources/`.

If a paper is cited in Lean as `[KEY]`, the preferred landing page for it is:

- `docs/kb/papers/KEY.md`

## Content Types

- [`index.md`](index.md) - content-oriented KB index.
- [`log.md`](log.md) - append-only chronology of KB changes and ingests.
- [`papers/`](papers/README.md) - canonical paper pages for cited or active BibTeX keys.
- [`concepts/`](concepts/README.md) - cross-paper topic pages.
- [`audits/`](audits/README.md) - source-to-ArkLib comparison artifacts.
- [`queries/`](queries/README.md) - filed answers to recurring research/review questions.
- [`sources/`](sources/README.md) - metadata and optional local source artifacts.
- [`_generated/references.json`](_generated/references.json) - normalized bibliography export.
- [`_generated/lean-citations.json`](_generated/lean-citations.json) - generated citation map from
  `ArkLib/**/*.lean`.

## How To Read The KB

For most contributor tasks:

- start from a paper page in `papers/`;
- move to a concept page if several papers or modules are involved;
- use an audit page when you need theorem-by-theorem comparison;
- use `sources/KEY/metadata.yml` when you need provenance or the public source URL.

If you are unsure where to start, use [`index.md`](index.md) first.

## Maintenance Contract

- `blueprint/src/references.bib` remains the bibliographic source of truth.
- `docs/kb/` is the source of truth for ArkLib-specific synthesis and cross-linking.
- Paper pages should describe what ArkLib uses from a paper, not merely restate the abstract.
- Prefer stable, reviewable markdown over ad hoc scratch notes.
- If a PR introduces a new paper citation key that matters to active work, add or scaffold the
  corresponding paper page in the same PR when practical.
- If a PR substantially changes ArkLib's interpretation, coverage, or formalization status for a
  paper, update the corresponding KB page or audit page in the same PR.

## Source Policy

- Prefer public URLs already present in `references.bib`.
- Keep metadata even when a full local source artifact is not committed.
- Do not require committed PDFs for every paper.
- Only commit local PDFs when redistribution is appropriate and the benefit is clear.
- When a local PDF is not committed, the repository should still contain:
  - the paper page;
  - the source metadata;
  - a public source URL when available.

## Common Tasks

### I found `[KEY]` in a Lean file and want context

1. Open `docs/kb/papers/KEY.md`.
2. Read the `Main ArkLib Touchpoints` section.
3. Follow links to any concept or audit pages if the work spans several files.

### I am adding a new cited paper

1. Add the BibTeX entry in `blueprint/src/references.bib`.
2. Run `python3 ./scripts/kb/sync_from_bib.py`.
3. Run `python3 ./scripts/kb/scaffold_paper.py KEY`.
4. Replace the stub page with an ArkLib-specific summary.
5. Run `python3 ./scripts/kb/lint.py`.

### I am updating a paper-backed development

1. Update the paper page if ArkLib's interpretation, scope, or touchpoints changed.
2. If the change is theorem-by-theorem or gap-analysis heavy, add or update an audit page.
3. Append a short entry to [`log.md`](log.md) if the KB changed in a durable way.

### I want review context for a PR

1. Run `python3 ./scripts/kb/review_context.py --files <changed-lean-files> --format review`.
2. Paste the output into a `/review` comment.

## Workflows

### Add a new paper

1. Add or update the BibTeX entry in `blueprint/src/references.bib`.
2. Run `python3 ./scripts/kb/sync_from_bib.py`.
3. Scaffold or add `docs/kb/papers/KEY.md`.
4. Add `docs/kb/sources/KEY/metadata.yml`.
5. Update [`index.md`](index.md) and append to [`log.md`](log.md).

### Minimal update checklist

For a new cited paper, the minimum acceptable KB update is:

- BibTeX entry in `blueprint/src/references.bib`
- paper page in `docs/kb/papers/KEY.md`
- source metadata in `docs/kb/sources/KEY/metadata.yml`
- regenerated `docs/kb/_generated/references.json`

Better, when practical:

- regenerate `docs/kb/_generated/lean-citations.json`
- add the new page to [`index.md`](index.md)
- append a short entry to [`log.md`](log.md)
- replace any stub text with an ArkLib-specific summary before merge

### Investigate a paper-driven PR

1. Resolve the cited BibTeX key from the changed Lean files.
2. Read the corresponding paper page under `docs/kb/papers/`.
3. Read any linked concept pages or audit pages.
4. Attach relevant KB pages as review context via `.github/workflows/review.yml`.

### Example: add a new cited paper

Suppose you add `[NEWKEY]` to a Lean module.

1. Add `NEWKEY` to `blueprint/src/references.bib`.
2. Run:

```bash
python3 ./scripts/kb/sync_from_bib.py
python3 ./scripts/kb/scaffold_paper.py NEWKEY
```

3. Edit:
   - `docs/kb/papers/NEWKEY.md`
   - `docs/kb/sources/NEWKEY/metadata.yml`
4. Add ArkLib-specific touchpoints and notes.
5. Run:

```bash
python3 ./scripts/kb/lint.py
python3 ./scripts/check-docs-integrity.py
```

### Example: use the KB during review

If a PR changes `ArkLib/ProofSystem/Whir/ProximityGen.lean`, run:

```bash
python3 ./scripts/kb/review_context.py \
  --files ArkLib/ProofSystem/Whir/ProximityGen.lean \
  --format review
```

This should resolve the relevant paper keys and generate a `/review` comment block that includes:

- public paper URLs in `External:`
- KB paper pages in `Internal:`
- a short citation-focused note in `Comments:`

### Periodic maintenance

1. Regenerate the bibliography and citation indexes.
2. Check for cited keys without paper pages.
3. Check for stale or missing source metadata.
4. File durable comparisons or review results under `audits/` or `queries/`.
