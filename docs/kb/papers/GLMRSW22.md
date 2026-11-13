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
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds/RandomLinear.lean
  - ArkLib/Data/CodingTheory/Basic/ParityCheck.lean
  - ArkLib/Data/Probability/FiniteEntropy.lean
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds/RandomLinear/Main.lean
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds/RandomLinear/NotRare.lean
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds/RandomLinear/BerP.lean
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

`random_linear_lambda_lower` in
[Bounds/RandomLinear.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/RandomLinear.lean), with the
derived existence form `random_linear_lambda_lower_exists`. Both are proved. The proof is in
[Bounds/RandomLinear/](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/RandomLinear):

- the source's lemma that the bad distribution is not implicitly rare is
  `RandomLinearInternal.entQ_badLaw_mulVec_lower` in
  [NotRare.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/RandomLinear/NotRare.lean);
- its lemma on `v + αw` for Bernoulli `v` is `RandomLinearInternal.entQ_add_mul_ber_lower` in
  [BerP.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/RandomLinear/BerP.lean);
- the counting bound is `RandomLinearInternal.random_linear_contains_list` in
  [Main.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/RandomLinear/Main.lean).

## Known Divergences From ArkLib

**The random model is uniform-random-subspace.** §1.1: "A random linear code is a uniformly random
subspace of `F_q^n` of certain dimension." ArkLib has no distribution over linear codes, so the
`1 − q^{−Ω(n)}` conclusion is carried in the equivalent finite **counting** form over
`{C | finrank C = k}` — which is therefore the source's probability exactly, not an approximation.
Its §1.2 working model is the code of a uniformly random parity-check tuple. The proof transfers
from that model to uniform subspaces by counting: every code of dimension `n - m` has the same
number of independent tuples (`card_fiber_pcCode`), at least half of all tuples are independent
(`card_linIndep_ge`), so the fraction of bad codes is at most twice the fraction of bad tuples
(`ncard_subspace_le_of_pc`).

**Endpoint corrected to the primary source.** This paper defines `(p, L)`-list-decodable with a
*strict* inequality, `|{c ∈ C : δ(c,z) ≤ p}| < L`, so "not `(p, ⌊·⌋)`-list-decodable" is
`Λ ≥ ⌊·⌋`. Accordingly, Lean counts the bad event `Λ < ⌊·⌋` and the derived existence theorem
concludes `⌊·⌋ ≤ Λ`. [ABF26] prints the unsupported strict `>`; Lean deliberately does not inherit
that off-by-one strengthening.

The dimension is pinned into the band `ρ ≤ k/n ≤ ρ + 1/n`, the source treating `ρ·n` as an integer.

**Abundance is proved directly.** The source cites a threshold lemma of Mosheiff, Resch, Ron-Zewi,
Silas and Wootters (LDPC codes achieve list-decoding capacity, 2019) for the step from "not
implicitly rare" to "contains a bad matrix". ArkLib does not formalise that lemma. It proves the
needed case by a second-moment count over parity-check matrices for the row orbit of one bad matrix
(`RandomLinearInternal.card_pc_avoid_le`). Its rows are the bad distribution rounded to counts that sum to
`n` (`RandomLinearInternal.exists_badMatrix`), which makes the source's remark on non-integral types
precise. The source bounds a conditional entropy with Fano's and Hoeffding's inequalities. ArkLib
bounds it by the entropy of the error of a plurality decoder, with a Chernoff bound
(`RandomLinearInternal.prodLaw_plurality_err_le`).

## Open Formalization Gaps

The list-recovery half of the paper, which ArkLib does not touch.

## Source Access

- Source metadata: [`../sources/GLMRSW22/metadata.yml`](../sources/GLMRSW22/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
