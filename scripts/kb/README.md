# Knowledge Base Scripts

These scripts maintain the generated indexes that support `docs/kb/`.

They are intentionally lightweight and use only the Python standard library.

## Scripts

- `sync_from_bib.py` - export `blueprint/src/references.bib` into
  `docs/kb/_generated/references.json`
- `extract_lean_citations.py` - scan `ArkLib/**/*.lean` and generate
  `docs/kb/_generated/lean-citations.json`
- `check_generated.py` - check that the committed generated indexes are fresh
- `scaffold_paper.py KEY` - create a stub paper page and source metadata file for `KEY`
- `lint.py` - validate paper-page structure and report cited keys without paper pages
- `review_context.py` - resolve citation keys, KB paper pages, and external URLs for review
  comments

## Usage

Run from the repo root:

```bash
python3 ./scripts/kb/sync_from_bib.py
python3 ./scripts/kb/extract_lean_citations.py
python3 ./scripts/kb/check_generated.py
python3 ./scripts/kb/lint.py
python3 ./scripts/kb/review_context.py --files ArkLib/ProofSystem/Fri/Spec/SingleRound.lean --format review
```

## Intended Workflow

1. Update `blueprint/src/references.bib`
2. Regenerate `references.json`
3. Regenerate `lean-citations.json`
4. Update or scaffold the affected `docs/kb/papers/KEY.md` pages

## Review Workflow Notes

`review_context.py` emits a comment body shaped for `.github/workflows/review.yml`.
The current workflow accepts three sources of review context:

- explicit `External:` URLs from the review comment;
- explicit `Internal:` repo paths from the review comment;
- free-form `Comments:` from the review comment.

Use `review_context.py` locally to infer citation-backed `External:` and `Internal:` entries from
changed Lean files or explicit BibTeX keys, then paste its output into a `/review` comment.
