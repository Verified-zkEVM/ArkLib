---
kind: paper
bibkey: BBS24
title: "Formal Verification of the Sumcheck Protocol"
year: 2024
bib_source: blueprint/src/references.bib
source_metadata: ../sources/BBS24/metadata.yml
status: seeded
related_modules:
  - ArkLib/ProofSystem/Sumcheck/Spec/General.lean
---

# BBS24

## At A Glance

`BBS24` is ArkLib's current sum-check formal-verification reference.
It provides direct comparison context for the repo's sum-check specification layer.

## What ArkLib Uses From This Paper

- Background and comparison context for the sum-check protocol formalization.
- A concrete external reference point for what a prior formalized sum-check development looks like.

## Main ArkLib Touchpoints

- [`ArkLib/ProofSystem/Sumcheck/Spec/General.lean`](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean)
  cites `BBS24` in its module docstring.

## Known Divergences From ArkLib

- ArkLib's long-term architecture places sum-check inside a broader oracle-reduction and
  proof-system framework rather than formalizing it in isolation.
- This makes the comparison useful, but not necessarily one-to-one at the API level.

## Open Formalization Gaps

- Add a fuller theorem-to-theorem comparison if sum-check becomes a focused audit target.

## Source Access

- Source metadata: [`../sources/BBS24/metadata.yml`](../sources/BBS24/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
