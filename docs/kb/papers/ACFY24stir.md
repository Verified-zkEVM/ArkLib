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

### Proximity gap

`STIR.proximity_gap` proves Theorem 4.1 from the correlated-agreement theorem for powers curves.
For positive degree and `0 < δ < 1 - √ρ`, a powers combination of `m` words being within distance
`δ` with probability greater than `err⋆` gives a single set of size at least `(1 - δ)|L|` on which
every word agrees with a codeword. The arity is unrestricted, and the unique-decoding branch
includes its endpoint. The functions are indexed from zero, so the coefficient of `fⱼ` is `rʲ`.
The positive-degree assumption makes the paper's positive-rate regime explicit: the totalized error
formula does not support degree zero.

### Section 5 ingredients

`StirIOP.Params`, `ParamConditions`, `Distances` and `CodeParams` retain Construction 5.2's
parameter, domain and list-decoding conditions. In particular, the repetition condition uses the
next degree, `tᵢ + 1 ≤ dᵢ₊₁` for `i < M`, without constraining `t_M`.
`stirRelation` describes exact-codeword completeness at radius zero, and `stirOpenRelation`
describes the strict soundness language whose complement includes distance exactly `δ`.

Construction 5.2, Lemma 5.4 and Theorem 5.1 remain unformalized targets. Their numerical bounds are
recorded in the module docstring and blueprint. There are no exported Section 5 protocol theorems:
an arbitrary existential protocol without query bounds can be an exhaustive exact-membership
verifier, so those bounds alone do not characterize STIR.

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
- The proximity-gap theorem and the Section 5 targets follow the ePrint 2024/390 revision dated
  2025-01-27. In that revision Theorem 5.1 requires
  `|F| = Ω(λ · 2^λ · d² · |L|^{3.5} / log(1/ρ))` (also Theorem 1 and Appendix C.1), and the
  blueprint and module docstring use the exponent `7/2`. An earlier version of the blueprint had
  `|L|²`.
- Keep separate from WHIR-related keys even when the coding-theory prerequisites overlap.

## Known Divergences From ArkLib

- ArkLib expresses much of the reusable mathematics in shared coding-theory modules rather than in
  STIR-only files.
- As a result, not every paper notion will appear first in the `ProofSystem/Stir` subtree.
- The strict soundness relation and corrected parameters are formalized, but no concrete STIR
  prover, verifier or transcript has been assembled. The paper's Section 5 results are documented
  as targets rather than exported as arbitrary-protocol existence statements.

## Open Formalization Gaps

- Add a deeper audit page once STIR theorem coverage becomes a focused review target.
- Construction 5.2 is not formalized, so Lemma 5.4 and Theorem 5.1 cannot yet be stated about the
  STIR protocol itself.
- Verifier query complexity: `OracleVerifier.numQueries` is a stub, and the paper counts the `k`
  points read together as one symbol. VCVio has `IsQueryBound`, `IsQueryBoundP` and
  `IsPerIndexQueryBound` that a statement could use.
- Lemma 5.4 needs the paper's vector of per-challenge errors for the concrete protocol.
- The challenge representation must support exact uniform sampling from evaluation domains and
  their complements. Fixed-length uniformly sampled field vectors do not generally encode these
  distributions.
- Appendix C.1 requires `|F| > 10^7 (λ+1) 2^{λ+1} d² |L|^{3.5} (1 + max{1/(-log(1-δ')),
  1/(-log(1.05 √ρ))})`, which grows as `δ' → 0`, while Theorem 5.1 prints no `δ` in its `Ω`. Read
  from the paper only; it matters once the query clauses are stated.

## Source Access

- Source metadata: [`../sources/ACFY24stir/metadata.yml`](../sources/ACFY24stir/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
