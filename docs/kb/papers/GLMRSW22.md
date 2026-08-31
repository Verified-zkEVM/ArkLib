---
kind: paper
bibkey: GLMRSW22
title: "Bounds for list-decoding and list-recovery of random linear codes"
year: "2022"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/GLMRSW22/metadata.yml
status: seeded
related_modules:
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean
---

# GLMRSW22

## At A Glance

`GLMRSW22` is Guruswami–Li–Mosheiff–Resch–Silas–Wootters, *Bounds for list-decoding and list-recovery
of random linear codes*, IEEE Trans. Inf. Theory 68(2) (2022) — the source of the random-linear-code
list-size lower bound.

## What ArkLib Uses From This Paper

Theorem 4.1: for a prime power `q`, `p ∈ (0, 1 − 1/q)` and `δ ∈ (0,1)` there is `ε_{p,q,δ} > 0` such
that for `ε ∈ (0, ε_{p,q,δ})` and `n` large, a random linear code of rate `1 − h_q(p) − ε` is not
`(p, ⌊h_q(p)/ε − δ⌋)`-list-decodable with probability `1 − q^{−Ω(n)}`.

## Main ArkLib Touchpoints

`random_linear_lambda_lower` in [Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean) (admitted), with the derived existence form
`random_linear_lambda_lower_exists`.

## Known Divergences From ArkLib

**The random model is uniform-random-subspace.** §1.1: "A random linear code is a uniformly random
subspace of `F_q^n` of certain dimension." ArkLib has no distribution over linear codes, so the
`1 − q^{−Ω(n)}` conclusion is carried in the equivalent finite **counting** form over
`{C | finrank C = k}` — which is therefore the source's probability exactly, not an approximation.
(Its §1.2 working model is the kernel of a uniformly random parity-check matrix, the same distribution
conditioned on full rank, by `GL_n`-invariance.)

**Endpoint corrected to the primary source.** This paper defines `(p, L)`-list-decodable with a
*strict* inequality, `|{c ∈ C : δ(c,z) ≤ p}| < L`, so "not `(p, ⌊·⌋)`-list-decodable" is
`Λ ≥ ⌊·⌋`. Accordingly, Lean counts the bad event `Λ < ⌊·⌋` and the derived existence theorem
concludes `⌊·⌋ ≤ Λ`. [ABF26] prints the unsupported strict `>`; Lean deliberately does not inherit
that off-by-one strengthening.

The dimension is pinned into the band `ρ ≤ k/n ≤ ρ + 1/n`, the source treating `ρ·n` as an integer.

## Open Formalization Gaps

Theorem 4.1 itself, and the list-recovery half of the paper, which ArkLib does not touch.

## Source Access

- Source metadata: [`../sources/GLMRSW22/metadata.yml`](../sources/GLMRSW22/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
