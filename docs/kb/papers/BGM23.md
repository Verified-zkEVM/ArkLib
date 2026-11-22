---
kind: paper
bibkey: BGM23
title: "Generic Reed-Solomon codes achieve list-decoding capacity"
year: "2023"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/BGM23/metadata.yml
status: stub
related_modules:
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds/ReedSolomon/FullRank.lean
---

# BGM23

## At A Glance

`BGM23` is Brakensiek–Gopi–Makam, *Generic Reed-Solomon codes achieve list-decoding capacity*, STOC
2023 — the first of the randomly-punctured-Reed-Solomon capacity results, over an exponentially large
alphabet.

## What ArkLib Uses From This Paper

Nothing directly. [ABF26] cites it as context for Theorem 3.6 — an exponential-alphabet predecessor of [AGL24] Theorem 1.1.

## Main ArkLib Touchpoints

Mentioned in the reference list of [Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean); the formalized statement in that
cluster is [AGL24]'s.

`exists_ne_zero_Lambda_le_of_eval_ne_zero` in
[FullRank.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/ReedSolomon/FullRank.lean):
over every field, a nonzero polynomial `P` such that at every point `α` with pairwise distinct
coordinates and `P(α) ≠ 0` the Reed-Solomon code of dimension `k` has `Λ ≤ ℓ` at relative radius
`ℓ/(ℓ+1)·(1 − k/n)`. Over every infinite field such points exist (`exists_embedding_Lambda_le`).
This paper's finite-field statement, with its field size, is not formalized.

## Known Divergences From ArkLib

`exists_ne_zero_Lambda_le_of_eval_ne_zero` is this paper's list-decoding theorem in a weaker
form: generic points are those off the zero set of a nonzero polynomial, the list size is the
ordinary `Λ` rather than average-radius list-decodability, and there is no bound on the field
size. Its proof goes through
[AGL24]'s full-column-rank theorem for the reduced intersection matrix
(`exists_det_submatrix_ne_zero_of_isWeaklyPartitionConnected`), not through this paper's
non-reduced intersection matrix.

## Open Formalization Gaps

Everything beyond the list-size form at generic evaluation points above: the average-radius
statement and the finite-field statement with its exponential field-size bound. It is context for
`rs_random_domain_lambda_le`, not an input to it.

## Source Access

- Source metadata: [`../sources/BGM23/metadata.yml`](../sources/BGM23/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
