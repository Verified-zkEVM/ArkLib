---
kind: paper
bibkey: Eli57
title: "List decoding for noisy channels"
year: "1957"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/Eli57/metadata.yml
status: seeded
related_modules:
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean
---

# Eli57

## At A Glance

`Eli57` is Elias, *List decoding for noisy channels*, RLE Technical Report 335, MIT (1957) — the
paper that introduced list decoding, and the origin of the volume/averaging lower bound on list
size.

## What ArkLib Uses From This Paper

[ABF26] Lemma 3.7: for a code with `|C| = q^k`, `Λ(C, δ) ≥ Vol_q(δ, n) / q^{n−k}`. The argument is
an averaging one — the mean point-list size over uniformly random centres is `|C|·Vol/q^n`, so some
centre attains at least the mean.

## Main ArkLib Touchpoints

`linear_lambda_ge_elias_volume` in [Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean), **proved in-tree and axiom-clean** by
the source's own argument, with `sum_ncard_closeCodewordsRel_eq` as the Fubini step.

## Known Divergences From ArkLib

ArkLib's version is stated for a linear code over a field; [ABF26] states it for an arbitrary
`C : Σ^k → Σ^n`. Linearity is used exactly once, to get `|C| = q^k`, so the generalisation is nearly
free.

## Open Formalization Gaps

The alphabet-generic restatement above. The entropy form is Corollary 3.8, which needs the [MS77]
volume estimate — see [`MS77.md`](MS77.md).

## Source Access

- Source metadata: [`../sources/Eli57/metadata.yml`](../sources/Eli57/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
