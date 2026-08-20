---
kind: paper
bibkey: AGL23
title: "{AG} codes have no list-decoding friends: approaching the generalized Singleton bound requires exponential alphabets"
year: "2023"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/AGL23/metadata.yml
status: seeded
related_modules:
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean
---

# AGL23

## At A Glance

`AGL23` is Alrabiah–Guruswami–Li, *AG codes have no list-decoding friends: approaching the generalized
Singleton bound requires exponential alphabets*, arXiv:2308.13424 (2023) — the large-alphabet barrier,
generalizing [BDG24] from `ℓ = 2` to all `ℓ` and, crucially, to non-linear codes.

## What ArkLib Uses From This Paper

Theorem 1.1: for `L ≥ 2` and `R ∈ (0,1)` there is `α_{L,R}` such that for all `ε > 0` and all
`n ≥ Ω_{L,R}(1/ε)`, a rate-`R` code of alphabet size `q` that is `(L/(L+1)(1 − R − ε), L)`
list-decodable has `q ≥ 2^{α_{L,R}/ε}`.

## Main ArkLib Touchpoints

`large_alphabet_lambda_lower` in [Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean), proved in-tree for linear codes over a field, and its axiom-clean consequence
`large_alphabet_card_ge_exp_of_inv_length` — attaining the generalized Singleton bound *exactly*
forces `|F| ≥ 2^{Ω(n)}`, which is the one use [ABF26] puts the barrier to.

## Known Divergences From ArkLib

Theorem 1.1 **as printed omits the rate hypothesis** — "Let `C` be a code of length `n` with alphabet
size `q` that is …-list-decodable" — which cannot be intended, since a one-codeword code is
list-decodable at any radius over `𝔽₂`. The hypothesis is present in the abstract and in the worked
Propositions 3.2/3.3 and Theorem 4.3 ("a code of rate `R`"), which is what the Lean follows.

The Lean pins the rate by *equality*, hence is vacuous at irrational `ρ` and inhabited only for
`ρ·n ∈ ℕ`. A two-sided band would remove that, and is licensed by the source's own technique — Prop 3.2
rounds `R` down to a multiple of `3/n` and takes "any subcode of `C` of rate `R′`", Prop 3.3 notes
"Subcode `C′` has rate at least `R′ = R − (1/n)`" — but not by its printed statement, so it is recorded
rather than taken.

ArkLib restricts to linear codes over a field, which drops precisely this paper's headline advance over
[BDG24].

## Open Formalization Gaps

The alphabet-generic, non-linear strengthening. Also: `α` and `n₀` are non-constructive
existentials here, so the statement cannot reject a *concrete* parametrization; that would need
constants extracted from the source's proof
(`α_R = α'_R/10`, `I₀ = {1, …, 4εn}` are explicit there, so it is extractable).

## Source Access

- Source metadata: [`../sources/AGL23/metadata.yml`](../sources/AGL23/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
