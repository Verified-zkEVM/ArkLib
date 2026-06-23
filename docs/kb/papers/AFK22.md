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
  - ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness.lean
---

# AFK22

## At A Glance

`AFK22` analyzes the Fiat–Shamir transformation of multi-round public-coin interactive proofs,
showing that for `(k₁, …, kμ)`-special-sound protocols the soundness/knowledge loss is much smaller
than the generic `Qᵘ` bound. For ArkLib it is the reference for the **rewinding / forking** analysis
that turns (coordinate-wise) special soundness into knowledge soundness.

## What ArkLib Uses From This Paper

- The tree-of-transcripts extraction strategy and forking analysis for multi-round special-sound
  protocols, which informs ArkLib's transcript-tree extraction abstractions.

## Main ArkLib Touchpoints

- [`ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness.lean`](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness.lean)
  cites `AFK22` for the Fiat–Shamir / forking analysis backing the rewinding knowledge extractor.

## Version Notes

- TCC 2022 (Springer LNCS); extended version in Journal of Cryptology, 2023. ePrint 2021/1377.

## Known Divergences From ArkLib

- ArkLib's tree of transcripts (`ChallengeTree`) branches only at challenge rounds and is
  arity-indexed; the forking primitive used is `VCVio.CryptoFoundations.forkReplay` rather than the
  paper's abstract rewinding argument.

## Open Formalization Gaps

- The forking-based construction of an accepting, structured tree from a single prover — the core of
  the knowledge-soundness implication — is not yet formalized (a `sorry` in the implication
  theorem).

## Source Access

- Source metadata: [`../sources/AFK22/metadata.yml`](../sources/AFK22/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
