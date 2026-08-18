---
kind: paper
bibkey: GHSZ02
title: "Combinatorial bounds for list decoding"
year: "2002"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/GHSZ02/metadata.yml
status: seeded
related_modules:
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean
---

# GHSZ02

## At A Glance

`GHSZ02` is Guruswami–Håstad–Sudan–Zuckerman, *Combinatorial bounds for list decoding*, IEEE Trans.
Inf. Theory 48(5) (2002) — the source of large list sizes for Reed-Solomon codes over *prime* fields,
where the extension-field structure [BKR06] exploits is unavailable.

## What ArkLib Uses From This Paper

Corollary 20, as rendered by [ABF26] Theorem 3.13: for large primes `p` there is a word `w` with
`|Λ(RS[F_p, F_p, ⌊p^α⌋], 1 − ((1−β)/α)·p^{α−1}, w)| > Ω(p^{p^α·β/2})`. The averaging engine is Lemma 19:
for an MDS `[n,k]_q` code and `a ≥ k`,
`(1/e)·C(n,a)·q^{k−a} ≤ E_x[|B(x, n−a) ∩ C|] ≤ C(n,a)·q^{k−a}`.

## Main ArkLib Touchpoints

`rs_lambda_large_prime` in [Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean), proved in-tree and axiom-clean.

## Known Divergences From ArkLib

**A source hypothesis [ABF26] drops.** Lemma 19 needs `a ≥ k`, i.e. `(1−γ)/ε ≥ 1`, i.e. **`α + β ≤ 1`**
in [ABF26]'s variables. The Lean carries it. (Dropping it looks harmless — `α + β > 1` gives `a < k`,
hence a larger ball and a longer list — but the cited inequality is then outside its stated range.)

**Statement versus proof.** Corollary 20 as *stated* bounds the paper's asymptotic quantity
`L_q^{poly}`; the per-`n`, single-code `Ω(n^{(γ/2)n^ε})` claim [ABF26] quotes lives in its *proof*
("Use an MDS `[n,k]_q` code with `n = q` and `k = n^ε`, such as a Reed-Solomon code").

The variable map is `ε ↦ α`, `γ ↦ β`. The local copy is a scanned two-column paper whose text layer
drops relation symbols, so Corollary 20's own display could not be transcribed verbatim; the proof text
could.

## Open Formalization Gaps

The stronger asymptotic wrapper from Corollary 20; the per-code consequence used by [ABF26] is
proved in-tree.

## Source Access

- Source metadata: [`../sources/GHSZ02/metadata.yml`](../sources/GHSZ02/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
