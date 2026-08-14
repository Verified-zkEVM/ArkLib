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

- Lemma 4.10's equality between affine-line mutual correlated agreement and correlated agreement
  below half the relative minimum distance.
- In Lean, only the `mcaError ≤ epsCA` direction is an external leaf. The reverse direction is
  proved as ABF26 Fact 4.5, and the equality is derived by antisymmetry.

## Main ArkLib Touchpoints

- [`ProximityGap/Errors.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean) contains
  the admitted `mcaError_le_epsCA_below_udr` direction and the derived
  `mcaError_eq_epsCA_below_udr` equality.
- The [ABF26 audit](../audits/open-problems-list-decoding-and-correlated-agreement.md) records the
  statement-level comparison and the explicit open-radius hypothesis.

## Version Notes

- `ACFY24` is the ePrint version; `ACFY25` is the published EUROCRYPT version.
- ArkLib uses `ACFY25` for the Lemma 4.10 locator rather than silently transferring numbering
  between versions.

## Known Divergences From ArkLib

- The trusted Lean statement is restricted to linear codes over the field alphabet and carries
  `0 < δ` explicitly.
- ArkLib's MCA value is the generator-parametric `CoreDefinitions.mcaError`; `epsMCA` is only its
  reducible affine-line paper spelling.

## Open Formalization Gaps

- Prove `mcaError_le_epsCA_below_udr` in-tree and remove the external leaf.

## Source Access

- Source metadata: [`../sources/ACFY25/metadata.yml`](../sources/ACFY25/metadata.yml)
- Bibliographic record: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
