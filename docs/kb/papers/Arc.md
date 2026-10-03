---
kind: paper
bibkey: Arc
title: "Arc: Accumulation for Reed-Solomon Codes"
year: 2024
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2024/1731
source_metadata: ../sources/Arc/metadata.yml
status: investigated
related_modules:
  - ArkLib/OracleReduction/Basic.lean
  - ArkLib/OracleReduction/Security/RoundByRound.lean
---

# Arc

## At A Glance

Bünz, Mishra, Nguyen and Wang develop hash-based accumulation through relation-to-relation
interactive oracle reductions. ARC is an important source for ArkLib's target semantics,
but its scalar-state extraction contract differs from WARP's later witness-indexed contract.

## What ArkLib Uses From This Paper

The [broader comparison](../audits/interaction-literature-map.md) records ARC Definition 5.5,
its extractor's input information, Remark 5.6's limitation, and the distinction from WARP.
The connection is a formalization target and structural comparison, not a complete source
equivalence theorem or a claim that ARC originated every earlier use of IORs.

## Main ArkLib Touchpoints

- [Oracle reductions](../../../ArkLib/OracleReduction/Basic.lean): input/output claims and oracle interfaces.
- [Round-by-round security](../../../ArkLib/OracleReduction/Security/RoundByRound.lean): several
  extractor and state variants that must be compared separately.
- [Native claims](../../../ArkLib/Interaction/Oracle/Claim.lean): dependent target relations.

## Version Notes

The inspected 57-page PDF has an October 25, 2024 cover date; ePrint's latest revision metadata
is June 5, 2025. Use the hash below to disambiguate it.

## Source Access

- [Canonical ePrint](https://eprint.iacr.org/2024/1731).
- [Metadata](../sources/Arc/metadata.yml). No PDF is committed.
