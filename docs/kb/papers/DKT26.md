---
kind: paper
bibkey: DKT26
title: "{Reed--Solomon} Codes Beyond {Johnson}: Efficient Decoding and Smaller Cryptographic Proofs"
year: "2026"
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2026/2056
source_metadata: ../sources/DKT26/metadata.yml
status: stub
---

# DKT26

## At A Glance

TODO: summarize the paper in ArkLib terms.

## What ArkLib Uses From This Paper

TODO: list the main definitions, theorems, or protocol ideas ArkLib relies on.

## Main ArkLib Touchpoints

- [`ArkLib/Data/CodingTheory/HiddenDerivative/`](../../../ArkLib/Data/CodingTheory/HiddenDerivative/):
  interpolation spaces, local constraints, symbolic certificates, and parameter choices.
- [`ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/`](../../../ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/):
  Reed–Solomon list-size bounds, including first-order and capacity bounds.
- [`ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/`](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/):
  line, affine-family, and power-batching agreement bounds.
- [`ArkLib/Data/Polynomial/Differential/`](../../../ArkLib/Data/Polynomial/Differential/):
  differential equations, separant chains, unique lifting, and rational Taylor charts.

## Version Notes

The library's numbered [DKT26] citations use the November 2026 revision of
[ePrint 2026/2056](https://eprint.iacr.org/2026/2056).

The historical per-file [port correspondence notes](../../design/reed-solomon-port-correspondence.md)
use the earlier published ePrint numbering, including Section 6.1, equations (70)–(72), and
Appendix A.6, Lemma A.4 for the regular Taylor chart. Those historical locators are preserved;
the library now cites Section 8.2, equations (56)–(58), and Appendix A.2, Lemma A.3 for these
constructions.

## Known Divergences From ArkLib

TODO: record material interface or statement-shape differences.

## Open Formalization Gaps

TODO: record important missing theorems, abstractions, or proof gaps.

## Source Access

- Source metadata: [`../sources/DKT26/metadata.yml`](../sources/DKT26/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
