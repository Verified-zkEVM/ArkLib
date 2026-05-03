---
kind: paper
bibkey: codingtheory
title: "Essential coding theory"
year: 2012
bib_source: blueprint/src/references.bib
source_metadata: ../sources/codingtheory/metadata.yml
status: seeded
related_concepts:
  - reed-solomon-proximity
related_modules:
  - ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean
---

# codingtheory

## At A Glance

`codingtheory` is ArkLib's broad textbook-style coding-theory reference paired with
`listdecoding` in the Johnson-bound layer.
It provides background for alphabet-free and classical coding-theory statements used in reusable
support modules.

## What ArkLib Uses From This Paper

- Background and comparative reference for
  [`ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean`](../../../ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean).
- General coding-theory framing for statements that are not tied to a single cryptographic protocol.

## Main ArkLib Touchpoints

- [`ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean`](../../../ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean)
  cites `codingtheory` directly and uses it for the alphabet-free Johnson-bound discussion.

## Version Notes

- This key refers to a draft/book-style reference rather than a conventional conference paper.
- Reviewers should expect it to serve as mathematical background rather than as a protocol-specific
  theorem source.

## Known Divergences From ArkLib

- ArkLib packages the mathematics into reusable Lean APIs and concrete finitary statements, not as
  textbook exposition.

## Open Formalization Gaps

- If more coding-theory layers begin depending on this reference, add a broader audit page for the
  Johnson-bound and list-decoding support modules.

## Source Access

- Source metadata: [`../sources/codingtheory/metadata.yml`](../sources/codingtheory/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
