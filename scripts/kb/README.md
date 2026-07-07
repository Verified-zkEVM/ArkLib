# Knowledge Base Scripts

These scripts maintain the generated indexes that support `docs/kb/`.

They are intentionally lightweight and use only the Python standard library.

## Scripts

- `sync_from_bib.py` - export `blueprint/src/references.bib` into
  `docs/kb/_generated/references.json`
- `extract_lean_citations.py` - scan `ArkLib/**/*.lean` and generate
  `docs/kb/_generated/lean-citations.json`
- `extract_declarations.py` - scan `ArkLib/**/*.lean` and generate
  `docs/kb/_generated/declarations.json`, a catalog of every declaration
  (file, line, kind, namespace, name, brief signature, docstring head)
- `find_dedup_candidates.py` - derive `docs/kb/_generated/dedup-report.md`
  from the catalog: same-short-name groups across files + cross-file
  near-duplicate docstrings, a review aid for spotting duplication in PRs
- `regenerate.py` - refresh all generated indexes and scaffold missing cited paper pages
- `check_generated.py` - check that the committed generated indexes are fresh on `main`
- `scaffold_paper.py KEY` - create a stub paper page and source metadata file for `KEY`
- `lint.py` - validate paper-page structure and report cited keys without paper pages
- `review_context.py` - resolve citation keys, KB paper pages, and external URLs for review
  comments

## Usage

Run from the repo root:

```bash
python3 ./scripts/kb/sync_from_bib.py
python3 ./scripts/kb/extract_lean_citations.py
python3 ./scripts/kb/extract_declarations.py
python3 ./scripts/kb/find_dedup_candidates.py
python3 ./scripts/kb/regenerate.py
python3 ./scripts/kb/check_generated.py
python3 ./scripts/kb/lint.py
python3 ./scripts/kb/review_context.py --files ArkLib/ProofSystem/Fri/Spec/SingleRound.lean --format review
```

## Intended Workflow

1. Update `blueprint/src/references.bib`
2. Update an existing paper page when the PR changes ArkLib's interpretation or use of that paper
3. Do not commit `docs/kb/_generated/**` changes in feature PRs
4. Let the main-branch KB workflow open a follow-up PR for regenerated indexes and missing
   cited paper/source stubs

Run `python3 ./scripts/kb/regenerate.py` locally when you need to inspect the generated state.
Commit the generated results only from the main-branch automation, not from ordinary feature PRs.

## Review Workflow Notes

`review_context.py` emits a comment body shaped for `.github/workflows/review.yml`.
The current workflow accepts three sources of review context:

- explicit `External:` URLs from the review comment;
- explicit `Internal:` repo paths from the review comment;
- free-form `Comments:` from the review comment.

Use `review_context.py` locally to infer citation-backed `External:` and `Internal:` entries from
changed Lean files or explicit BibTeX keys, then paste its output into a `/review` comment.
