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
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds/ReedSolomon/Certificate.lean
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds/ReedSolomon/FullRank.lean
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds/ReedSolomon/IntersectionMatrix.lean
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds/ReedSolomon/RankLoss.lean
  - ArkLib/Data/CodingTheory/ListDecodability/PartitionConnected.lean
  - ArkLib/Data/Probability/Uniform.lean
  - ArkLib/ToMathlib/Combinatorics/Enumerative/Descents.lean
  - ArkLib/ToMathlib/Combinatorics/Hypergraph/GenericZeroPattern.lean
  - ArkLib/ToMathlib/Combinatorics/Hypergraph/PartitionConnected.lean
  - ArkLib/ToMathlib/Fintype/CardEmbedding.lean
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

`IsWeaklyPartitionConnected` in
[PartitionConnected.lean](../../../ArkLib/ToMathlib/Combinatorics/Hypergraph/PartitionConnected.lean):
weak partition-connectivity, the minimal-subset lemma
(`exists_isWeaklyPartitionConnected_subtype`), and the combinatorial step of robustness to deletions
(`IsWeaklyPartitionConnected.delete`).

`IsWeaklyPartitionConnected.exists_isGenericZeroPattern` in
[GenericZeroPattern.lean](../../../ArkLib/ToMathlib/Combinatorics/Hypergraph/GenericZeroPattern.lean):
the source's corollary that a weakly partition-connected hypergraph gives a generic zero pattern,
proved without the hypergraph orientation theorem the source uses; it assumes nonempty edges, which
the source's proof assumes implicitly.

`exists_isWeaklyPartitionConnected_agreement_of_sum_hammingDist_le` in
[PartitionConnected.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/PartitionConnected.lean):
a bad list-decoding configuration gives a weakly partition-connected agreement hypergraph, with its
list-size form `exists_isWeaklyPartitionConnected_agreement_of_lt_Lambda`.

`intersectionMatrix` in
[IntersectionMatrix.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/ReedSolomon/IntersectionMatrix.lean):
the source's reduced intersection matrix of a hypergraph, with `IsRigid`, its full column rank at
evaluation points in polynomial form (`isRigid_iff_mulVec_injective`,
`isRigid_iff_exists_aeval_det_ne_zero`); the source's lemma that reduced intersection matrices of
agreement hypergraphs are not full column rank (`not_isRigid_of_mem_code`); the per-variable degree
bound on maximal minors (`degreeOf_det_submatrix_le`); and row deletion and exchange of variables
(`intersectionMatrix_apply_of_eq`, `rename_intersectionMatrix_apply`).

`exists_det_submatrix_ne_zero_of_isWeaklyPartitionConnected` in
[FullRank.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/ReedSolomon/FullRank.lean):
the source's full-column-rank theorem for reduced intersection matrices (`lem:int-mat-1` in the
source), as a nonzero maximal minor of the intersection matrix over `MvPolynomial ι F` for any
field `F`. The proof is the source's appendix proof through generic zero patterns, run at a point
of the infinite field `RatFunc F`
(`exists_isRigid_of_isWeaklyPartitionConnected`) in place of the source's reduction to large
finite fields. Its corollary `exists_embedding_Lambda_le`: over every infinite field there are
evaluation points at which the Reed-Solomon code of dimension `k` has `Λ ≤ ℓ` at relative radius
`ℓ/(ℓ+1)·(1 − k/n)`. This is the infinite-field list-size form; it is not [BGM23]'s finite-field
statement and gives no bound on the field size.

`Tuple.card_filter_card_descents_lt_le` in
[Descents.lean](../../../ArkLib/ToMathlib/Combinatorics/Enumerative/Descents.lean): the counting
step of the source's certificate count (`cor:count` in the source): over a finite linear order
`α`, at most `C(|α|, r) · m^r` injective tuples `Fin r ↪ α` have fewer than `m` descents. The
source applies it with `m = 2^t`. That certificates have fewer than `2^t` descents is
`IsCertificate.card_descents_lt` in
[Certificate.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/ReedSolomon/Certificate.lean);
the source's certificate-structure lemma (`lem:count`) states at most `2^t`, and its proof gives
fewer, which the count needs.

`exists_embedding_isCertificate_of_not_isRigid` in
[Certificate.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/ReedSolomon/Certificate.lean):
the source's certificates of rank loss (`alg:matrix`, `alg:certificate`, and `lem:well-defined`
through `lem:count`), for a `(k + 2r)`-weakly partition-connected hypergraph on `t = s + 1`
vertices. `certificateState` is the source's matrix sequence as a function of the list of earlier
certificate indices (`certificateState_append_singleton`); its minors are nonzero
(`certificateMinor_ne_zero`) of degree at most `s * (k - 1)` in each variable
(`degreeOf_certificateMinor_le`). Every point at which the hypergraph is not rigid has a
certificate of length `r` (`exists_isCertificate_of_not_isRigid`); a certificate of length at most
`r` is injective (`IsCertificate.injective`) and has fewer than `2^t` descents
(`IsCertificate.card_descents_lt`). `exists_embedding_certificatePolynomial_of_not_isRigid` attaches
the minors to the certificate's indices (`certificatePolynomial`). The source's `lem:del` is
`exists_det_submatrix_ne_zero_of_card_le` in
[FullRank.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/ReedSolomon/FullRank.lean),
and its exchange of variables of the same type is `det_submatrix_relabel` in
[IntersectionMatrix.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/ReedSolomon/IntersectionMatrix.lean).
The edges are not ordered by type; the bank is consumed from its smallest edge of each type, which
is the source's choice of the next unused bank element of that type; variables are swapped rather
than replaced, which agrees because the incoming variable does not occur in the minor; and a
certificate is described by the source's events `E_j`, `F_j` rather than as the output of its
algorithm with the choice of the smallest index.

`card_filter_not_isRigid_mul_pow_le` in
[RankLoss.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/ReedSolomon/RankLoss.lean):
the source's main lemma (`lem:main`) in counting form. For a `(k + 2r)`-weakly partition-connected
hypergraph on `t = s + 1` vertices, the number `N` of tuples `α : Fin n ↪ F` of pairwise distinct
evaluation points at which it is not rigid satisfies
`N · (q − n + 1)^r ≤ C(n, r) · 2^{tr} · (s(k − 1))^r · |Fin n ↪ F|`, where `q = |F|`. The proof
takes the source's union bound, over certificates with fewer than `2^t` descents, of its bound on
one certificate (`cor:product`), which is `card_filter_isCertificate_mul_pow_le`. That bound applies
the sequential Schwartz–Zippel bound over pairwise-distinct points (the source's `lem:product`),
`MvPolynomial.card_filter_injective_sequential_le` in
[SchwartzZippelPrefix.lean](../../../ArkLib/ToMathlib/MvPolynomial/SchwartzZippelPrefix.lean), to
the minors of the certificate. `card_filter_not_isRigid_mul_le` in RankLoss.lean is the
single-minor bound for a `k`-weakly partition-connected hypergraph,
`N · (q − n + 1) ≤ n · s(k − 1) · |Fin n ↪ F|`: a nonzero maximal minor has total degree at most
`n · s(k − 1)`, and Schwartz–Zippel over pairwise-distinct points
(`MvPolynomial.card_filter_injective_eval_eq_zero_le` in
[SchwartzZippel.lean](../../../ArkLib/ToMathlib/MvPolynomial/SchwartzZippel.lean))
applies to it. The source states this single-minor bound only as a remark in its proof overview,
as the probability bound `1 − Lk²/q`.

## Known Divergences From ArkLib

ArkLib states the plain `Λ` bound, of which the source's average-radius form is a strengthening — the
safe direction.

ArkLib's reduced intersection matrix has entries in `MvPolynomial ι R` rather than the fraction
field; full column rank is stated at evaluation points (`IsRigid`) and through maximal minors, and
the per-variable degree bound on maximal minors is `s * (k - 1)`, the count in the source's proof,
sharper than its stated `(t − 1)k`.

The rank-loss bounds count tuples of pairwise distinct points instead of bounding probabilities;
dividing by `|Fin n ↪ F|` gives the probability under a uniform such tuple. Their denominator is
`q − n + 1`, the least number of values left for a coordinate, which the source lowers to `q − n`;
their degree is `s(k − 1)` in place of `(t − 1)k`. The certificate length `r` is free, for a
`(k + 2r)`-weakly partition-connected hypergraph, in place of the source's `r = ⌊εn/2⌋` for a
`(k + εn)`-weakly partition-connected one, and the source's assumptions `t ≥ 2` and `k ≥ 1` are not
needed.

The sample space is [ABF26]'s `binom(F, n)` literally: the subtype `{S : Finset F // S.card = n}`
sampled with `$ᵗ`, with the code indexed by the drawn subset (`↥S → F`), so no ordering is chosen
and no push-forward is needed. [AGL24] samples an ordered tuple of pairwise-distinct points. An
event that depends only on the set of drawn points has the same probability under both samplers:
`prEvent_uniformSample_finsetCard_eq_embedding` in
[Uniform.lean](../../../ArkLib/Data/Probability/Uniform.lean), from the count
`Fintype.card_filter_embedding_map_univ` in
[CardEmbedding.lean](../../../ArkLib/ToMathlib/Fintype/CardEmbedding.lean) (every `n`-element set
is the image of `n!` embeddings `Fin n ↪ F`).

The source's stated consequence — at `ℓ = 2(1−ρ−η)/η` — is not formalized: its `ℓ` is real-valued, so it
needs a rounding the source does not fix.

## Open Formalization Gaps

Theorem 1.1 itself. Of its predecessors, [BGM23] is formalized only in its infinite-field list-size
form (`exists_embedding_Lambda_le`: no field-size bound, not average-radius); [GZ23] and the
combined [AGGLZ25] are unformalized context.

## Source Access

- Source metadata: [`../sources/AGL24/metadata.yml`](../sources/AGL24/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
