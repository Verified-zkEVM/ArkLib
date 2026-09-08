---
kind: paper
bibkey: RSG
title: "Ring switching, generalized"
bib_source: blueprint/src/references.bib
canonical_url: https://github.com/leanEthereum/leanVM-b/blob/main/misc/ring-switching-generalized.pdf
status: reviewed
related_concepts:
  - ring-switching
---

# RSG

## At A Glance

This note generalizes coordinate ring switching to packing and evaluation extensions with
independent degrees over a common base. The inspected note has three pages and no printed
author byline or date. Its credits attribute the idea to Lev Soukhanov and `[[alloc]init]`.
ArkLib uses `RSG` as a citation key, not as an authorship or publication claim.

## What ArkLib Uses From This Paper

The input is a full family of evaluations at one point over the evaluation field E.
The packed polynomial has coefficients in P. Choosing bases of E and P over B identifies
the claimed family with a coordinate matrix over B; transposition and packing give the
slice targets. Neither an embedding from E to P nor one from P to E is needed.

The verifier derives slices publicly, batches them using a fresh scalar challenge, runs
degree-two sumcheck, and requests a packed-polynomial opening. The note permits challenges
in an extension C of P when the downstream PCS supports C-valued evaluation points.
The commitment continues to concern the original P-coefficient polynomial.

## Main ArkLib Touchpoints

- [Ring-switching concept](../concepts/ring-switching.md) — finite-free coordinate model.
- [Model and coverage audit](../audits/ring-switching-model-coverage.md) — relation shapes,
  source pin, challenge extension, and acceptance cases.
- [DP24](DP24.md) and [Flock](BRW26.md) — scalar input protocols requiring their own
  reconstruction head before a full-family reduction.

## Protocol Variants And Proof Boundary

The note uses powers with exponents 1 through e, with batching loss `e/|C|`.
Zero-based powers give a distinct collision event at zero and the bound `(e−1)/|C|`
for a nonempty family. Prover-supplied slices checked against the public family are
another valid variant with an additional message; the note derives its slices publicly.

Finite-free coordinate transport extends to commutative rings. The note's field root
bound does not automatically extend to uniform challenges over rings with zero divisors.
Likewise, the reduction needs the downstream commitment's real extraction or binding
semantics. A carrier instance or an identity commitment alone does not certify a PCS
integration.

`Packing/Tail/FullFamilyOpening.lean` implements the checked-slice variant through the actual
sumcheck sequence and terminal opening relation, with state-aware completeness and exact-object
worst-case RBR knowledge under explicit functionality and injective compatible P→C transport.
The batching challenge uses the selected strategy's error; each scalar tail challenge uses
`2/|C|`, and the terminal has no challenge. `Packing/Multiplier.lean` proves the multiplication-
matrix evaluator without assuming an E→C embedding. An actual downstream opening proof still
needs its own contract on that same packed commitment relation.

## Source Access

- [Public note](https://github.com/leanEthereum/leanVM-b/blob/main/misc/ring-switching-generalized.pdf).
- [Bibliographic source](../../../blueprint/src/references.bib), key `RSG`.
- Inspected version: three-page PDF with creation metadata 2026-07-01. The
  [coverage audit](../audits/ring-switching-model-coverage.md) records its SHA-256;
  PDF metadata is not a publication date.
