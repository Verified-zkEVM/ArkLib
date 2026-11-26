---
kind: paper
bibkey: LPS24
title: "On Knowledge-Soundness of Plonk in {ROM} from Falsifiable Assumptions"
year: 2024
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2024/994
source_metadata: ../sources/LPS24/metadata.yml
status: seeded
related_modules:
  - ArkLib/ProofSystem/Plonk/Relation/Basic.lean
---

# LPS24

## At A Glance

`LPS24` connects AGM-style reasoning back to Plonk knowledge-soundness, which matches ArkLib's
long-term protocol ambitions.

## What ArkLib Uses From This Paper

- Conceptual linkage between AGM-style reasoning and Plonk knowledge-soundness questions.

## Main ArkLib Touchpoints

- No ArkLib file cites `LPS24`.
- [`ArkLib/ProofSystem/Plonk/Relation/Basic.lean`](../../../ArkLib/ProofSystem/Plonk/Relation/Basic.lean) is the
  natural neighboring subtree when this reference matters in protocol work.

## Version Notes

- This is the ePrint version currently recorded in `references.bib`.
- In ArkLib, `LPS24` matters mainly as a modeling and motivation reference until the AGM and Plonk
  subtrees are more complete.

## Known Divergences From ArkLib

- ArkLib has not yet formalized a full `LPS24`-style knowledge-soundness development.
- ArkLib has no group-oracle model, group representation, or adversary execution for the AGM.
  Generic and algebraic group models are developed in VCVio
  (`VCVio/CryptoFoundations/GroupModel/`), where an algebraic adversary's representation is
  `GroupModel.AlgebraicPoint`.

## Open Formalization Gaps

- If AGM or Plonk work becomes active, this page should likely grow into an audit page covering
  which parts of the knowledge-soundness argument are actually present in ArkLib.

## Source Access

- Source metadata: [`../sources/LPS24/metadata.yml`](../sources/LPS24/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
