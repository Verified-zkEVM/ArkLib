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
4. If the KB is missing the page, add the BibTeX entry first if needed, then scaffold the paper
   page and source metadata.
5. If your work changes ArkLib's interpretation or coverage of a paper, update the KB in the same
   PR when practical.

The current KB policy is:

- every citation key used in `ArkLib/**/*.lean` should have at least a paper page stub;
- active or review-critical papers should have a non-stub page;
- deep theorem matrices belong under `docs/kb/audits/`.

## Maintenance Rules

- `blueprint/src/references.bib` is still the bibliographic source of truth.
- The BibTeX key is the canonical identifier across Lean, bibliography, and KB pages.
- Keep process guidance here in `docs/wiki/`; keep paper content in `docs/kb/`.
- Prefer persistent pages over branch-local scratch notes when the result will help future PRs or
  reviewers.

## Review Integration

For `.github/workflows/review.yml`, attach:

- KB paper pages via `repo_context_refs`;
- KB audit pages for deep source-to-code comparison;
- public paper URLs via `external_refs` when raw source text is needed.

This keeps review prompts grounded in repository-local context instead of rebuilding it ad hoc.

For local preparation of those fields, use:

```bash
python3 ./scripts/kb/review_context.py \
  --files ArkLib/ProofSystem/Fri/Spec/SingleRound.lean \
  --format review
```

or pass explicit keys with `--keys BCIKS20,ACFY24`.

The helper emits a normal `/review` comment body using the sections supported by the current
workflow:

```text
/review
External:
- https://eprint.iacr.org/2020/654
Internal:
- docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md
Comments:
Focus on whether the formalization matches the cited paper statements.
```
