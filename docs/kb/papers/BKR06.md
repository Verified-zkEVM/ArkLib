---
kind: paper
bibkey: BKR06
title: "Subspace polynomials and list decoding of Reed-Solomon codes"
year: "2006"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/BKR06/metadata.yml
status: seeded
related_modules:
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean
---

# BKR06

## At A Glance

`BKR06` is Ben-Sasson–Kopparty–Radhakrishnan, *Subspace polynomials and list decoding of Reed-Solomon
codes*, FOCS 2006 — superpolynomial list sizes for full-length Reed-Solomon codes over extension
fields, via subspace polynomials.

## What ArkLib Uses From This Paper

Corollary 2.2 (low rate), as rendered by [ABF26] Theorem 3.12: for infinitely many `q` there is a word
`w` with `|Λ(RS[F_q, F_q, ⌊q^α⌋], 1 − q^{β−1}, w)| ≥ q^{(α−β²)·log₂ q}`. It rests on Theorem 2.1, which
produces a family `P` of polynomials of degree `q^u` and a word `w` with `|P| ≥ q^{(u+1)m−v²}` and
`agree(w, P) ≥ q^v`.

## Main ArkLib Touchpoints

`rs_lambda_superpoly_extension` in [Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean) (admitted).

## Known Divergences From ArkLib

**Log base.** The source's `N^{(δ−ρ²)log₂ N}` fixes the base at `2`, so the Lean uses `Real.logb 2`;
a natural log would weaken the exponent by `1/ln 2`.

**Degree convention — harmless.** [BKR06] defines `RS[N, K]` by degree **≤ K** and its witnessing family
has degree exactly `K`, whereas [ABF26]'s `RS[F, L, k]` — and `ReedSolomon.code` — is degree **< k**. The
cited witnesses therefore sit one degree above the code, but they are monic subspace polynomials
`∏_{a ∈ L}(X − a)`, so subtracting any fixed member gives `|P|` distinct polynomials of degree `< K`, all
agreeing with the shifted word `w − P₀` on the same `≥ q^v` points. The construction transfers.

**Rationality — not harmless.** Corollary 2.2 requires `δ, ρ ∈ ℚ` and its proof needs `u = δm`, `v = ρm`
integral; [ABF26] states it for real `α, β`. At exact `u, v` the source beats the target by a slack of
`+m`, while `u = ⌊αm⌋, v = ⌈βm⌉` costs `−2βm − 1` — the same order, so the naive approximation falls
short *polynomially*. It looks recoverable ("for infinitely many `q`" lets one choose the subsequence of
`m`, and by Weyl equidistribution there are infinitely many `m` with `{αm}`, `{βm}` both near `0`), but
that is a Diophantine argument the source does not contain.

## Open Formalization Gaps

Corollary 2.2 itself, and the real-`α, β` case in particular — see above.

## Source Access

- Source metadata: [`../sources/BKR06/metadata.yml`](../sources/BKR06/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
