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

## Main ArkLib Touchpoints

- [`ArkLib/Data/CodingTheory/ListDecodability.lean`](../../../ArkLib/Data/CodingTheory/ListDecodability.lean)
- [`ArkLib/ProofSystem/Stir/Combine.lean`](../../../ArkLib/ProofSystem/Stir/Combine.lean)
- [`ArkLib/ProofSystem/Stir/MainThm.lean`](../../../ArkLib/ProofSystem/Stir/MainThm.lean)
- [`ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean`](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean)
- [`ArkLib/ProofSystem/Stir/ProximityGap.lean`](../../../ArkLib/ProofSystem/Stir/ProximityGap.lean)

## Version Notes

- This page tracks the STIR conference-version key currently present in `references.bib`.
- The statements of `Stir/ProximityGap.lean` and `Stir/MainThm.lean` were checked against the
  ePrint 2024/390 revision dated 2025-01-27. In that revision Theorem 5.1 requires
  `|F| = Ω(λ · 2^λ · d² · |L|^{3.5} / log(1/ρ))` (also Theorem 1 and Appendix C.1), and the
  blueprint and Lean use the exponent `7/2`. An earlier version of the blueprint had `|L|²`.
- Keep separate from WHIR-related keys even when the coding-theory prerequisites overlap.

## Known Divergences From ArkLib

- ArkLib expresses much of the reusable mathematics in shared coding-theory modules rather than in
  STIR-only files.
- As a result, not every paper notion will appear first in the `ProofSystem/Stir` subtree.
- `STIR.proximity_gap` (Theorem 4.1), `StirIOP.stir_rbr_soundness` (Lemma 5.4) and
  `StirIOP.stir_main` (Theorem 5.1) are still admitted. Their statements follow the paper, with
  these differences:
  - the functions of Theorem 4.1 are numbered from `0`, so the weight of `fⱼ` is `rʲ`, and
    `degree ≥ 1` is assumed (the paper's `err⋆` divides by the rate; with `x / 0 = 0` the
    statement is false for `degree = 0`);
  - Lemma 5.4 and Theorem 5.1 are existence statements about a vector IOP. ArkLib does not
    formalize Construction 5.2, so they do not force the protocol to be STIR. In Lemma 5.4 the
    protocol is chosen from the parameters alone, before the distances `δᵢ` and list sizes `ℓᵢ`,
    as in the paper;
  - soundness is stated for the oracles that are at least `δ`-far from the code
    (`stirOpenRelation`, strict), completeness for the codewords;
  - every challenge of Lemma 5.4 is given the maximum of the four error families, which is weaker
    than the paper's vector of per-round errors; the round `i` of the paper is `j + 1` for
    `j : Fin M`;
  - the constants of the `Ω` and `O` bounds of Theorem 5.1 are chosen before the parameters
    (`O_k` for the proof length), and the two query-complexity items are not stated.

## Open Formalization Gaps

- Add a deeper audit page once STIR theorem coverage becomes a focused review target.
- Construction 5.2 is not formalized, so Lemma 5.4 and Theorem 5.1 cannot yet be stated about the
  STIR protocol itself.
- Verifier query complexity: `OracleVerifier.numQueries` is a stub, and the paper counts the `k`
  points read together as one symbol. VCVio has `IsQueryBound`, `IsQueryBoundP` and
  `IsPerIndexQueryBound` that a statement could use.
- The paper's vector of per-round errors in Lemma 5.4 is collapsed to its maximum.
- Appendix C.1 requires `|F| > 10^7 (λ+1) 2^{λ+1} d² |L|^{3.5} (1 + max{1/(-log(1-δ')),
  1/(-log(1.05 √ρ))})`, which grows as `δ' → 0`, while Theorem 5.1 prints no `δ` in its `Ω`. Read
  from the paper only; it matters once the query clauses are stated.

## Source Access

- Source metadata: [`../sources/ACFY24stir/metadata.yml`](../sources/ACFY24stir/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
