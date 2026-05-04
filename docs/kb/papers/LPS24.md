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
  - ArkLib/AGM/Basic.lean
  - ArkLib/ProofSystem/Plonk/Basic.lean
---

# LPS24

## At A Glance

`LPS24` is the second main reference cited by ArkLib's Algebraic Group Model file.
It is especially relevant because it connects AGM-style reasoning back to Plonk
knowledge-soundness, which matches ArkLib's long-term protocol ambitions.

## What ArkLib Uses From This Paper

- Background for the current AGM mechanization in
  [`ArkLib/AGM/Basic.lean`](../../../ArkLib/AGM/Basic.lean).
- Conceptual linkage between AGM-style reasoning and Plonk knowledge-soundness questions.

## Main ArkLib Touchpoints

- [`ArkLib/AGM/Basic.lean`](../../../ArkLib/AGM/Basic.lean) cites `LPS24` directly.
- [`ArkLib/ProofSystem/Plonk/Basic.lean`](../../../ArkLib/ProofSystem/Plonk/Basic.lean) is the
  natural neighboring subtree when this reference matters in protocol work.

## Version Notes

- This is the ePrint version currently recorded in `references.bib`.
- In ArkLib, `LPS24` matters mainly as a modeling and motivation reference until the AGM and Plonk
  subtrees are more complete.

## Known Divergences From ArkLib

- ArkLib has not yet formalized a full `LPS24`-style knowledge-soundness development.
- The current AGM file focuses on oracle interfaces, group tables, and adversary execution
  structure rather than on the paper's end results.

## Open Formalization Gaps

- If AGM or Plonk work becomes active, this page should likely grow into an audit page covering
  which parts of the knowledge-soundness argument are actually present in ArkLib.

## Source Access

- Source metadata: [`../sources/LPS24/metadata.yml`](../sources/LPS24/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
