---
kind: paper
bibkey: ACFY25
title: "WHIR: Reed-Solomon Proximity Testing with Super-Fast Verification"
year: "2025"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/ACFY25/metadata.yml
status: seeded
related_concepts:
  - reed-solomon-proximity
related_modules:
  - ArkLib/Data/CodingTheory/ProximityGap/Errors.lean
---

# ACFY25

## At A Glance

`ACFY25` is the published EUROCRYPT 2025 version of WHIR. ArkLib uses this key where exact theorem
numbering from the published version matters, while `ACFY24` tracks the earlier ePrint lineage.

## What ArkLib Uses From This Paper

- Lemma 4.10's unique-decoding MCA-from-CA direction below half the relative minimum distance.
- In Lean, `mcaError ≤ epsCa` is proved by counting the bad affine-line parameters. The reverse
  inequality follows from the general CA-to-MCA comparison, and the equality follows by
  antisymmetry.

## Main ArkLib Touchpoints

- [`ProximityGap/Errors.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean) contains
  `mcaError_le_epsCa_of_pos_of_two_mul_lt_dist` and the derived
  `mcaError_eq_epsCa_of_pos_of_two_mul_lt_dist` equality.
- The [ABF26 audit](../audits/open-problems-list-decoding-and-correlated-agreement.md) records the
  statement-level comparison and the explicit open-radius hypothesis.

## Version Notes

- `ACFY24` is the ePrint version; `ACFY25` is the published EUROCRYPT version.
- Lean citations use `ACFY25` for the published Lemma 4.10 locator.

## Known Divergences From ArkLib

- The Lean statement is restricted to linear codes over the field alphabet and assumes `0 < δ`.
- ArkLib's MCA value is the generator-parametric `CoreDefinitions.mcaError`; the corresponding
  affine-line value is `mcaError (AffineLineGenerator F) C δ`.

## Source Access

- Source metadata: [`../sources/ACFY25/metadata.yml`](../sources/ACFY25/metadata.yml)
- Bibliographic record: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
