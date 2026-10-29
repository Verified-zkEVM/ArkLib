---
kind: paper
bibkey: GWZC19
title: "Plonk: Permutations over lagrange-bases for oecumenical noninteractive arguments of knowledge"
year: 2019
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2019/953.pdf
source_metadata: ../sources/GWZC19/metadata.yml
status: seeded
related_modules:
  - ArkLib/ProofSystem/Plonk/Basic.lean
---

# GWZC19

## At A Glance

`GWZC19` is the main Plonk reference used by ArkLib's current Plonk entry-point module.
The present repo coverage is still early and architectural rather than a full end-to-end
formalization of the original paper.

## What ArkLib Uses From This Paper

- High-level protocol framing for the `ProofSystem/Plonk` subtree.
- Motivation for breaking Plonk into reusable protocol components rather than treating it as one
  monolithic proof-system file.

## Main ArkLib Touchpoints

- [`ArkLib/ProofSystem/Plonk/Basic.lean`](../../../ArkLib/ProofSystem/Plonk/Basic.lean)
  is the current repository landing point for the Plonk formalization effort and cites `GWZC19`
  directly.

## Version Notes

- The BibTeX entry points at the 2019 ePrint PDF.
- ArkLib currently uses this paper as the canonical Plonk reference for the `ProofSystem/Plonk`
  subtree.

## Known Divergences From ArkLib

- The current ArkLib file is a roadmap-style entry module rather than a complete protocol
  formalization.
- The repo explicitly plans to decompose Plonk into modular components and later extensions, which
  is a stronger modularity boundary than the original paper presentation.

## Open Formalization Gaps

- The Plonk subtree is still skeletal.
- If active Plonk work resumes, this page should be expanded with concrete ArkLib touchpoints beyond
  the single entry module, or replaced by an audit page once there is enough theorem-level content.

## Source Access

- Source metadata: [`../sources/GWZC19/metadata.yml`](../sources/GWZC19/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
