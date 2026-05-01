---
kind: paper
bibkey: listdecoding
title: "Algorithmic results in list decoding"
year: 2007
bib_source: blueprint/src/references.bib
source_metadata: ../sources/listdecoding/metadata.yml
status: seeded
related_concepts:
  - reed-solomon-proximity
related_modules:
  - ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean
---

# listdecoding

## At A Glance

`listdecoding` is ArkLib's general list-decoding background reference for the Johnson-bound layer.
It is one of the main theory references for the reusable coding-theory API rather than a
protocol-specific paper.

## What ArkLib Uses From This Paper

- Johnson-bound background for
  [`ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean`](../../../ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean).
- General list-decoding terminology that later proximity-gap and Reed-Solomon developments rely on.

## Main ArkLib Touchpoints

- [`ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean`](../../../ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean)
  explicitly says it references theorems from `listdecoding` by default.

## Version Notes

- Read together with [`codingtheory.md`](codingtheory.md), which is the other main reference cited
  in the Johnson-bound file.

## Known Divergences From ArkLib

- ArkLib extracts reusable algebraic and combinatorial statements from the broader list-decoding
  literature rather than mirroring the book/report structure directly.

## Open Formalization Gaps

- If the Johnson-bound layer becomes a review hotspot, add an audit page mapping theorem numbers to
  concrete Lean lemmas.

## Source Access

- Source metadata: [`../sources/listdecoding/metadata.yml`](../sources/listdecoding/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
