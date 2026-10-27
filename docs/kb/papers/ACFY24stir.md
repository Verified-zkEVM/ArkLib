---
kind: paper
bibkey: ACFY24stir
title: "STIR: Reed-Solomon proximity testing with fewer queries"
year: 2024
bib_source: blueprint/src/references.bib
source_metadata: ../sources/ACFY24stir/metadata.yml
status: seeded
related_concepts:
  - reed-solomon-proximity
related_modules:
  - ArkLib/ProofSystem/Stir
  - ArkLib/Data/CodingTheory/ListDecodability.lean
---

# ACFY24stir

## At A Glance

`ACFY24stir` is the current STIR reference cited across ArkLib's `ProofSystem/Stir` subtree.
It is the main KB landing page for STIR-specific protocol work and its interaction with the
underlying Reed-Solomon proximity and list-decoding machinery.

## What ArkLib Uses From This Paper

- Protocol-level context for the STIR formalization.
- STIR-specific theorem references in the `ProofSystem/Stir` subtree.
- Comparison context for list-decoding and Reed-Solomon proximity notions shared with WHIR and
  `BCIKS20`.

### Quotienting

`Quotienting.funcQuotient` and `Quotienting.polyQuotient` implement Definitions 4.2 and 4.3.
For a polynomial `f`, let `A` interpolate its values on the finite set `S`, and let
`V_S = ∏ s ∈ S, (X - C s)`. The quotienting module proves:

- `vanishingPoly_dvd_sub_ansPoly`: `V_S` divides `f - A`.
- `vanishingPoly_mul_polyQuotient`: multiplying the polynomial quotient by `V_S` recovers `f - A`.
- `degree_polyQuotient_lt`: if `f.degree < d` and `S.card ≤ d`, the quotient has degree below
  `d - S.card`. The degree is `WithBot ℕ`, so the boundary `S.card = d` forces the zero polynomial.
- `eval_polyQuotient_of_not_mem`: outside `S`, evaluation gives `(f(x) - A(x)) / V_S(x)`.

The function quotient agrees with polynomial quotient evaluations on `S` only when `Fill` supplies
those evaluations. The degree bound uses an upper-bound parameter `d`, rather than a strict bound
relative to the actual degree of `f`. The results hold over arbitrary fields, without a field-size
or characteristic assumption.

`Quotienting.quotienting` formalizes Lemma 4.4 for an arbitrary injective evaluation domain. Its
distance bound allows every nonnegative distance parameter, and it explicitly assumes that the
degree parameter is at most the evaluation-domain size so codeword interpolation recovers the
claimed low-degree polynomial.

## Main ArkLib Touchpoints

- [`ArkLib/Data/CodingTheory/ListDecodability.lean`](../../../ArkLib/Data/CodingTheory/ListDecodability.lean)
- [`ArkLib/ProofSystem/Stir/Combine.lean`](../../../ArkLib/ProofSystem/Stir/Combine.lean)
- [`ArkLib/ProofSystem/Stir/MainThm.lean`](../../../ArkLib/ProofSystem/Stir/MainThm.lean)
- [`ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean`](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean)
- [`ArkLib/ProofSystem/Stir/ProximityGap.lean`](../../../ArkLib/ProofSystem/Stir/ProximityGap.lean)
- [`ArkLib/ProofSystem/Stir/Quotienting.lean`](../../../ArkLib/ProofSystem/Stir/Quotienting.lean)

## Version Notes

- This page tracks the STIR conference-version key currently present in `references.bib`.
- Keep separate from WHIR-related keys even when the coding-theory prerequisites overlap.

## Known Divergences From ArkLib

- ArkLib expresses much of the reusable mathematics in shared coding-theory modules rather than in
  STIR-only files.
- As a result, not every paper notion will appear first in the `ProofSystem/Stir` subtree.

## Open Formalization Gaps

- Add a deeper audit page once STIR theorem coverage becomes a focused review target.

## Source Access

- Source metadata: [`../sources/ACFY24stir/metadata.yml`](../sources/ACFY24stir/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
