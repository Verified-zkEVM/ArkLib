---
kind: paper
bibkey: AGGLZ25
title: "Random Reed-Solomon codes achieve list-decoding capacity with linear-sized alphabets"
year: "2025"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/AGGLZ25/metadata.yml
status: stub
related_modules:
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean
---

# AGGLZ25

## At A Glance

`AGGLZ25` is Alrabiah–Guo–Guruswami–Li–Zhang, *Random Reed-Solomon codes achieve list-decoding capacity
with linear-sized alphabets*, Advances in Combinatorics (2025) — combining [BGM23] and [GZ23].

## What ArkLib Uses From This Paper

Nothing directly. [ABF26] cites it as context for Theorem 3.6 — the combination of [BGM23] and [GZ23], cited alongside [AGL24] Theorem 1.1.

## Main ArkLib Touchpoints

Mentioned in the reference list of [Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean); the formalized statement in that
cluster is [AGL24]'s.

## Known Divergences From ArkLib

Not applicable — nothing from this paper is formalized.

## Open Formalization Gaps

The whole paper. It is context for `rs_random_domain_lambda_le`, not an input to it.

## Source Access

- Source metadata: [`../sources/AGGLZ25/metadata.yml`](../sources/AGGLZ25/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
