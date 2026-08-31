---
kind: paper
bibkey: BGM23
title: "Generic Reed-Solomon codes achieve list-decoding capacity"
year: "2023"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/BGM23/metadata.yml
status: stub
related_modules:
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean
---

# BGM23

## At A Glance

`BGM23` is Brakensiek–Gopi–Makam, *Generic Reed-Solomon codes achieve list-decoding capacity*, STOC
2023 — the first of the randomly-punctured-Reed-Solomon capacity results, over an exponentially large
alphabet.

## What ArkLib Uses From This Paper

Nothing directly. [ABF26] cites it as context for Theorem 3.6 — an exponential-alphabet predecessor of [AGL24] Theorem 1.1.

## Main ArkLib Touchpoints

Mentioned in the reference list of [Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean); the formalized statement in that
cluster is [AGL24]'s.

## Known Divergences From ArkLib

Not applicable — nothing from this paper is formalized.

## Open Formalization Gaps

The whole paper. It is context for `rs_random_domain_lambda_le`, not an input to it.

## Source Access

- Source metadata: [`../sources/BGM23/metadata.yml`](../sources/BGM23/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
