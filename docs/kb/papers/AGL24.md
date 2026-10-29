---
kind: paper
bibkey: AGL24
title: "Randomly punctured Reed-Solomon codes achieve list-decoding capacity over linear-sized fields"
year: "2024"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/AGL24/metadata.yml
status: seeded
related_modules:
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean
---

# AGL24

## At A Glance

`AGL24` is Alrabiah–Guruswami–Li, *Randomly punctured Reed-Solomon codes achieve list-decoding capacity
over linear-sized fields*, STOC 2024 — Reed-Solomon codes on a random evaluation domain are
list-decodable up to the generalized Singleton bound over an alphabet linear in `n`.

## What ArkLib Uses From This Paper

Theorem 1.1: for `ε ∈ (0,1)`, `L ≥ 2` and a prime power `q ≥ n + k·2^{10L/ε}`, with probability at least
`1 − 2^{−Ln}` a randomly punctured Reed-Solomon code of block length `n` and rate `k/n` is
`(L/(L+1)(1 − R − ε), L)` average-radius list-decodable.

## Main ArkLib Touchpoints

`rs_random_domain_lambda_le` in [Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean) (admitted).

## Known Divergences From ArkLib

ArkLib states the plain `Λ` bound, of which the source's average-radius form is a strengthening — the
safe direction.

The sample space is [ABF26]'s `binom(F, n)` literally: the subtype `{S : Finset F // S.card = n}` under
`PMF.uniformOfFintype`, with the code indexed by the drawn subset (`↥S → F`), so no ordering is chosen
and no push-forward is needed. [AGL24] samples an ordered tuple of pairwise-distinct points, which
induces the same distribution over codes.

The source's stated consequence — at `ℓ = 2(1−ρ−η)/η` — is not formalized: its `ℓ` is real-valued, so it
needs a rounding the source does not fix.

## Open Formalization Gaps

Theorem 1.1 itself. Its predecessors [BGM23], [GZ23] and the combined [AGGLZ25] are unformalized
context.

## Source Access

- Source metadata: [`../sources/AGL24/metadata.yml`](../sources/AGL24/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
