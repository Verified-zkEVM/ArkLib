---
kind: paper
bibkey: BDG24
title: "Improved field size bounds for higher order {MDS} codes"
year: "2024"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/BDG24/metadata.yml
status: seeded
related_modules:
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean
---

# BDG24

## At A Glance

`BDG24` is Brakensiek–Dhar–Gopi, *Improved field size bounds for higher order MDS codes*, IEEE Trans.
Inf. Theory 70(10) (2024) — the `ℓ = 2` progenitor of the large-alphabet barrier, generalized by
[AGL23].

## What ArkLib Uses From This Paper

Cited by [ABF26] alongside [AGL23] for [ABF26] Theorem 3.10.

## Main ArkLib Touchpoints

`large_alphabet_lambda_lower` in [Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean), whose proved linear-code barrier cites both papers.

## Known Divergences From ArkLib

**Locator unverified.** [ABF26] cites "Corollary 1.7, Thm 1.8". In the arXiv version (2212.11262v2)
those numbers are a statement about MR tensor codes and an average-radius `LD-MDS(≤2)` corollary, and
all of that paper's items are `ε`-free *exact*-achievement results rather than the `η`-parameterized
form; the journal version may renumber. Only [AGL23] visibly supports the `η`-form, of which this paper
is the `ε = 0`, `ℓ = 2`, linear-MDS corner. Check the journal PDF before relying on the locators.

## Open Formalization Gaps

Nothing from this paper is formalized separately; its linear-code barrier is subsumed by the proved
[AGL23] theorem.

## Source Access

- Source metadata: [`../sources/BDG24/metadata.yml`](../sources/BDG24/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
