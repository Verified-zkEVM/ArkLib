---
kind: paper
bibkey: GGR11
title: "List Decoding Tensor Products and Interleaved Codes"
year: "2011"
bib_source: blueprint/src/references.bib
canonical_url: https://doi.org/10.1137/090778280
source_metadata: ../sources/GGR11/metadata.yml
status: seeded
related_concepts:
  - reed-solomon-proximity
related_modules:
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds/Interleaved.lean
---

# GGR11

## At A Glance

`GGR11` studies list decoding of tensor products and interleaved codes. ArkLib uses its Theorem
2.5 for the width-independent list-size comparison quoted as ABF26 Lemma 2.10.

## What ArkLib Uses From This Paper

- For a finite alphabet, a nonempty row-wise interleaving, and radius below the base code's
  relative minimum distance, Theorem 2.5 bounds the interleaved list size by
  `choose (b + r) r * Lambda(C, δ)^r` with the paper's ceiling and logarithm parameters.
- The Lean carrier keeps the finite-alphabet hypothesis and uses the canonical `Code.Lambda`
  value in `ℕ∞`.

## Main ArkLib Touchpoints

- [`ListDecodability/Bounds/Interleaved.lean`](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/Interleaved.lean)
  contains the proved `InterleavedCode.lambda_interleaved_le_choose_mul_pow`.
- The [ABF26 audit](../audits/open-problems-list-decoding-and-correlated-agreement.md) records the
  parameter conversion and source scope.

## Version Notes

- ArkLib cites the 2011 SIAM Journal on Computing version, volume 40, issue 5, pages 1432–1462.

## Known Divergences From ArkLib

- `Code.Lambda` is `ℕ∞`-valued so an infinite point list is represented by `⊤`; the cited finite
  alphabet ensures the theorem's intended finite setting.
- Interleaving uses ArkLib's canonical column-wise `interleavedCodeSet` representation.

## Source Access

- Source metadata: [`../sources/GGR11/metadata.yml`](../sources/GGR11/metadata.yml)
- DOI: [10.1137/090778280](https://doi.org/10.1137/090778280)
