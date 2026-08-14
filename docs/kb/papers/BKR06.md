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

Corollary 2.2 (low rate): for rational `0 < α < β < 1` and infinitely many `q` there is a word `w`
with `|Λ(RS[F_q, F_q, ⌊q^α⌋], 1 − q^{β−1}, w)| ≥ q^{(α−β²)·log₂ q}`. It rests on Theorem 2.1,
which produces a family `P` of polynomials of degree `q^u` and a word `w` with
`|P| ≥ q^{(u+1)m−v²}` and `agree(w, P) ≥ q^v`. [ABF26] Theorem 3.12 silently changes the rational
parameters to reals; ArkLib follows the primary source instead.

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

**Rationality is encoded, not approximated.** Corollary 2.2 requires `δ, ρ ∈ ℚ` and its proof needs
`u = δm`, `v = ρm` integral. The Lean declaration therefore binds `α β : ℚ`, coercing them
explicitly to `ℝ` in real powers and logarithmic exponents. There is no admitted all-real
compatibility alias. Naive floor/ceiling approximation loses same-order slack and does not justify
the all-real statement printed by [ABF26].

## Open Formalization Gaps

Corollary 2.2 itself. An arbitrary-real extension is also open and would require a separate proof.

## Source Access

- Source metadata: [`../sources/BKR06/metadata.yml`](../sources/BKR06/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
