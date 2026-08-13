# Knowledge Base Workflow

Use this page when a task depends on understanding an external paper or other durable reference in
ArkLib terms.

The operational rule is:

- `docs/wiki/` explains how to work in the repo.
- [`../kb/README.md`](../kb/README.md) stores the persistent substantive knowledge.

## When To Use The KB

- A Lean file cites a paper key like `[BCIKS20]` and you need paper context.
- A PR is paper-driven and review should compare the code against a source.
- A chat answer, comparison, or theorem matrix would be valuable beyond the current conversation.
- You are deciding whether a paper version or citation key should be treated as canonical.

## Basic Workflow

1. Resolve the citation key from the Lean file or bibliography.
2. Read the corresponding page under `docs/kb/papers/KEY.md`.
3. Read any linked concept pages or audit pages.
4. If the KB is missing the page, add the BibTeX entry first if needed. Stub-only paper pages and
   source metadata are proposed by generated-files PRs after merge.
5. If your work changes ArkLib's interpretation or coverage of a paper, update the KB in the same
   PR when practical.

The current KB policy is:

- every citation key used in `ArkLib/**/*.lean` should have at least a paper page stub on `main`;
- active or review-critical papers should have a non-stub page;
- deep theorem matrices belong under `docs/kb/audits/`.

## Maintenance Rules

- `blueprint/src/references.bib` is the bibliographic source of truth.
- The BibTeX key is the canonical identifier across Lean, bibliography, and KB pages.
- Feature PRs should not commit `docs/kb/_generated/**`; generated-files PRs from the
  main-branch KB workflow refresh those files.
- Keep process guidance here in `docs/wiki/`; keep paper content in `docs/kb/`.
- Prefer persistent pages over branch-local scratch notes when the result will help future PRs or
  reviewers.

## Review Integration

`.github/workflows/review.yml` resolves the citation keys of the changed Lean files from
`docs/kb/_generated/lean-citations.json` on the base ref and passes the corresponding
`docs/kb/papers/KEY.md` pages to the reviewer as `spec_refs`. A `/review` comment can add to that:

- lines under `Internal:` are merged into `spec_refs`, so this is where to attach an audit page or
  any KB page the automatic resolution misses;
- lines under `External:` and `Comments:` become free-text instructions, so this is where public
  paper URLs go.

Because the resolution reads the base ref, a paper page added in the same PR is not picked up
automatically — attach it under `Internal:`.

To prepare a comment body locally, use:

```bash
python3 ./scripts/kb/review_context.py \
  --files ArkLib/ProofSystem/Fri/Spec/SingleRound.lean \
  --format review
```

or pass explicit keys with `--keys BCIKS20,ACFY24`. The helper reads the committed
`lean-citations.json`, so a file whose citations changed in the working tree needs `--keys`.

The helper emits a `/review` comment body in the sections the workflow parses:

```text
/review
External:
- https://eprint.iacr.org/2020/654
Internal:
- docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md
Comments:
Focus on whether the formalization matches the cited paper statements.
```
