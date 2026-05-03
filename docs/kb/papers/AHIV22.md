---
kind: paper
bibkey: AHIV22
title: "Ligero: Lightweight sublinear arguments without a trusted setup"
year: 2017
bib_source: blueprint/src/references.bib
source_metadata: ../sources/AHIV22/metadata.yml
status: seeded
related_concepts:
  - reed-solomon-proximity
related_modules:
  - ArkLib/Data/CodingTheory/InterleavedCode.lean
  - ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean
  - ArkLib/Data/CodingTheory/Prelims.lean
---

# AHIV22

## At A Glance

`AHIV22` is ArkLib's current Ligero-family reference for interleaved-code and affine-line
proximity statements that sit adjacent to the main `BCIKS20` development.
In ArkLib it is not the dominant coding-theory reference, but it does provide a secondary line of
proximity-gap results that inform reusable interleaving and Reed-Solomon proximity interfaces.

## What ArkLib Uses From This Paper

- Interleaved-code and row-span style statements used in
  [`ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean).
- Reference context for why the interleaved-code API in
  [`ArkLib/Data/CodingTheory/InterleavedCode.lean`](../../../ArkLib/Data/CodingTheory/InterleavedCode.lean)
  is shaped to support proximity-gap style reasoning.
- Supporting proximity-gap language referenced in
  [`ArkLib/Data/CodingTheory/Prelims.lean`](../../../ArkLib/Data/CodingTheory/Prelims.lean).

## Main ArkLib Touchpoints

- [`ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean)
  contains the direct `AHIV22`-tagged statements, currently phrased as Lemma 4.3 through Lemma 4.5.
- [`ArkLib/Data/CodingTheory/InterleavedCode.lean`](../../../ArkLib/Data/CodingTheory/InterleavedCode.lean)
  cites `AHIV22` alongside `BCIKS20` in the main interleaving API docstring.
- [`ArkLib/Data/CodingTheory/Prelims.lean`](../../../ArkLib/Data/CodingTheory/Prelims.lean)
  cites `AHIV22` in comments connecting reusable definitions back to proximity-gap results.

## Version Notes

- The module docstring in
  [`ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean)
  explicitly notes a specific version date.
- The BibTeX key `AHIV22` currently points to the Ligero paper title with year `2017`, so the key
  name and publication year should be treated carefully when discussing provenance.

## Known Divergences From ArkLib

- ArkLib uses reusable code-theory and interleaving APIs rather than following the paper's
  presentation literally.
- The repo treats these results as part of a broader proximity-gap toolbox, not as an isolated
  Ligero-only formalization layer.

## Open Formalization Gaps

- The direct `AHIV22` lemmas in
  [`ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean)
  still contain proof gaps and should be treated as incomplete when used for review context.
- If this paper becomes a central review target, add a dedicated audit page instead of expanding
  this landing page further.

## Source Access

- Source metadata: [`../sources/AHIV22/metadata.yml`](../sources/AHIV22/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
