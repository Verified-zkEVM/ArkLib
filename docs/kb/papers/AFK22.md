---
kind: paper
bibkey: AFK22
title: "Fiat-Shamir Transformation of Multi-Round Interactive Proofs"
year: "2022"
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2021/1377
source_metadata: ../sources/AFK22/metadata.yml
status: seeded
related_modules:
  - ArkLib/OracleReduction/Security/TranscriptTree.lean
  - ArkLib/OracleReduction/Security/SpecialSoundness.lean
---

# AFK22

## At A Glance

`AFK22` analyzes the Fiat-Shamir transformation of multi-round public-coin interactive proofs,
showing that for `(k₁, …, kμ)`-special-sound protocols the loss can be much smaller than the
generic `Qᵘ` bound. For ArkLib it is background for the tree-of-transcripts viewpoint used by
special-soundness-style extractors.

## What ArkLib Uses From This Paper

- The tree-of-transcripts extraction strategy for multi-round special-sound protocols, which
  informs ArkLib's transcript-tree extraction abstractions.

## Main ArkLib Touchpoints

- [`ArkLib/OracleReduction/Security/TranscriptTree.lean`](../../../ArkLib/OracleReduction/Security/TranscriptTree.lean)
  provides the shared tree abstraction used by special soundness and CWSS.
- [`ArkLib/OracleReduction/Security/SpecialSoundness.lean`](../../../ArkLib/OracleReduction/Security/SpecialSoundness.lean)
  uses that tree abstraction for plain `(k)`-special soundness.

## Version Notes

- TCC 2022 (Springer LNCS); extended version in Journal of Cryptology, 2023. ePrint 2021/1377.

## Known Divergences From ArkLib

- ArkLib's tree of transcripts (`ChallengeTree`) branches only at challenge rounds and is
  arity-indexed; it abstracts the transcript bundle consumed by tree-based extractors.

## Source Access

- Source metadata: [`../sources/AFK22/metadata.yml`](../sources/AFK22/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
