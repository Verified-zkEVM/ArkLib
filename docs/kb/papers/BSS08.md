---
kind: paper
bibkey: BSS08
title: "Short PCPs with polylog query complexity"
year: 2008
bib_source: blueprint/src/references.bib
canonical_url: https://doi.org/10.1137/050646445
source_metadata: ../sources/BSS08/metadata.yml
status: seeded
related_modules:
---

# BSS08

## At A Glance

`BSS08` is Ben-Sasson–Sudan, *Short PCPs with polylog query complexity*, SIAM Journal on
Computing **38**(2) (2008) 551–607 — the Reed-Solomon PCP-of-proximity paper. Its Proposition 6.3
is the bivariate division statement: for `P, P' ∈ F[Z, Y]` with `P'` having an invertible leading
coefficient, there are `Q', Q` with `P = Q' * P' + Q`.

**Nothing in ArkLib cites this key today.** It was cited from `ProofSystem/Stir/Folding.lean`,
whose §4.4 folding development used Proposition 6.3 (via Mathlib's `MonomialOrder.div` under the
lexicographic order) to build the remainder `Q` with `P(z) = Q'(z,y)·(y − q(z)) + Q(z,y)`. That
file was rewritten when STIR Lemma 4.9 was proved by a different route, and the citation went with
it.

So this is a real reference that lost its citation site to a refactor, not a stray key. Restore
the `[BSS08]` citation if a future proof again goes through bivariate division; otherwise the key
and this page can be dropped.

## What ArkLib Uses From This Paper

- Nothing, at present. Historically: Proposition 6.3, the bivariate division property.

## Main ArkLib Touchpoints

- None. The former one was `ArkLib/ProofSystem/Stir/Folding.lean`.

## Source Access

- Source metadata: [`../sources/BSS08/metadata.yml`](../sources/BSS08/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
