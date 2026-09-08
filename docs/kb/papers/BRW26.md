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

Flock is a SNARK for batched Boolean computations by Benedikt Bünz, Ron Rothblum, and
William Wang. ArkLib's ring-switching design uses Appendix B's coordinate packing and
weighted claim reconstruction, together with Appendix C's distinct commitment boundary.
The [coverage audit](../audits/ring-switching-model-coverage.md) pins the inspected PDF.

## What ArkLib Uses From This Paper

Appendix B represents partial evaluation values over an extension field by coordinates
over the base field, transposes the coordinate matrix, and packs its rows. Faithful
coordinates are essential: independence over the base field does not justify recombining
arbitrary extension-field values as though they were base-field coordinates (Remark 5).

The ordinary scalar head checks equality-weighted partial values. Appendix B.3 also handles
quirky claims, with weights `L_σ(ζ) * eq(ρ,b)` combining a univariate interpolation coordinate
and Boolean coordinates. This requires a concrete reconstruction theorem for those weights;
a head restricted to ordinary equality weights does not implement that case.
`Packing/ScalarHead/Quirky.lean` defines the original interpolated extension, proves its
degree and node semantics, and derives those exact weights with the `(σ,b)` packing order.
The checked scalar phase has actual execution, completeness and zero-error knowledge proofs.

Appendix B.2's matrix evaluator is implemented in `Packing/Multiplier.lean`, with proved
correctness at every challenge point and an instrumented count of matrix-vector actions. Its specification is the multilinear extension of the Boolean table obtained
by applying a base-linear coordinate functional to equality weights. That functional is
not a ring homomorphism, so it cannot simply be applied to an arbitrary-point equality
evaluation in an unrelated challenge algebra.

## Main ArkLib Touchpoints

- [Ring-switching concept](../concepts/ring-switching.md) — the shared algebra and distinct
  scalar, full-family, trace, and lift protocols.
- [Model and coverage audit](../audits/ring-switching-model-coverage.md) — exact Flock
  weights, source locations, multiplier semantics, and binding requirements.
- [DP24](DP24.md) — the binary-tower protocol lineage of the existing packing pipeline.

## Security And Implementation Boundary

Flock's Ligerito integration admits lists of nearby codewords and uses out-of-domain
selection during commitment. That selection has its own bad event; Remark 11 explains
the candidate-list factor when the first selection is omitted. A theorem that assumes
an exactly functional commitment relation does not discharge this integration boundary.
Coordinate algebra, the concrete weighted heads, and the generic sumcheck tail are implemented.
The base commitment interface admits multiple candidates: a permanent test runs the actual
scalar/family composition with a cardinality-two oracle. Its deterministic behavior and
completeness do not require functionality. The implemented randomized bound is the explicit
exact-functional specialization; list/OOD security remains a separate formalization obligation.

## Source Access

- [Flock on the Cryptology ePrint Archive](https://eprint.iacr.org/2026/1329).
- [Bibliographic source](../../../blueprint/src/references.bib), key `BRW26`.
- Inspected version: 45-page PDF with creation metadata 2026-06-28; Appendix B pp.36–40
  and Appendix C pp.40–44. The coverage audit records its SHA-256.
