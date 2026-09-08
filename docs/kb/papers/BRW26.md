---
kind: paper
bibkey: BRW26
title: "Flock: Fast Proving for Batch Boolean Computations"
year: 2026
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2026/1329
status: reviewed
related_concepts:
  - ring-switching
---

# BRW26

## At A Glance

Bünz, Rothblum and Wang's *Flock: Fast Proving for Batch Boolean Computations* uses coordinate
packing and weighted scalar reconstruction in Appendix B. Appendix C supplies the distinct
list-decoding and out-of-domain (OOD) commitment analysis.

## What ArkLib Uses From This Paper

The coordinate argument transposes base-field coordinates of extension-field partial values.
Remark 5 requires faithful coordinates: basis independence over the base field does not justify
recombining arbitrary extension-field values as base-field coordinates.

Ordinary claims use equality-weighted partial values. Appendix B.3's quirky claims use
`L_σ(ζ) * eq(ρ,b)`, combining Lagrange and Boolean weights in the `(σ,b)` packing order.
`ScalarHead/Quirky.lean` defines the original interpolated extension, proves its degree and node
semantics, and derives this reconstruction. Both ordinary and quirky layouts instantiate the
shared checked scalar head with completeness and zero-error knowledge contracts.

The multiplier evaluator uses multiplication matrices, with Boolean interpolation at each layer.
Its specification is the multilinear extension of the Boolean table obtained by applying a
base-linear coordinate functional to equality weights. The functional need not be multiplicative.
`Multiplier.lean` proves correctness at arbitrary challenge points and counts one matrix-vector
action per retained variable, excluding preprocessing.

## Main ArkLib Touchpoints

- [`ScalarHead/Layout.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/ScalarHead/Layout.lean) and
  [`Quirky.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/ScalarHead/Quirky.lean) — ordinary and quirky source layouts.
- [`ScalarHead/Phase.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/ScalarHead/Phase.lean) — common checked scalar reconstruction.
- [`Multiplier.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Multiplier.lean) — public multiplication-matrix evaluator.
- [Ring-switching concept](../concepts/ring-switching.md) and [coverage audit](../audits/ring-switching-model-coverage.md).

## Implementation Boundary

The base commitment interface allows multiple candidates, and deterministic reconstruction and
completeness do not require functionality. The generic randomized knowledge bound explicitly
requires functionality. Flock's Ligerito integration instead uses lists of nearby codewords and
OOD selection, with its own binding bad event; Remark 11 accounts for the candidate-list factor
when the first selection is omitted. This list/OOD security and a production Flock PCS integration
are not implemented.

The generic scalar/family composition sends partial values and a second checked-slice message;
Flock uses a single partial-family message.

## Source Access

- [Cryptology ePrint Archive, 2026/1329](https://eprint.iacr.org/2026/1329).
- [Bibliography](../../../blueprint/src/references.bib), key `BRW26`.
- The 45-page PDF has creation metadata 2026-06-28. Locators: Appendix B pp.36–40;
  multiplication matrices B.2.1 pp.38–39 and B.4 p.39; list/OOD analysis Appendix C pp.40–44.
  The coverage audit records the PDF hash.
