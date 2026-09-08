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

*Ring switching, generalized* separates the packing and evaluation extensions over a common base.
Its three-page note has no printed author byline or date; the credits attribute the idea to Lev
Soukhanov and `[[alloc]init]`.

## What ArkLib Uses From This Paper

The input is a full family of evaluations at one point over E. The packed polynomial has
coefficients in P. Bases of E and P over B identify the claimed family with a B-coordinate
matrix; transposition and packing give the slice targets. No embedding between E and P is needed.

The verifier derives the slices publicly, batches them with a fresh scalar challenge, runs
degree-two sumcheck and requests a packed opening. Challenges may lie in an extension C of P
when the downstream PCS supports C-valued evaluation points for the original P-polynomial.

## Main ArkLib Touchpoints

- [`FiniteObservation.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/FiniteObservation.lean) — arbitrary finite weighted coordinate reconstruction, also used by tensor packing and Hachi monomial evaluation.
- [`Relations.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Relations.lean) — Boolean full-family/slice equivalence.
- [`Tail/FullFamilyOpening.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Tail/FullFamilyOpening.lean) — checked-slice reduction through product sumcheck to the same packed evaluation relation.
- [`Multiplier.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Multiplier.lean) — multiplication-matrix evaluation without an `E → C` embedding.
- [Coverage audit](../audits/ring-switching-model-coverage.md) — equations, source correspondence and commitment assumptions.

## Protocol Variants And Proof Boundary

The note uses exponents 1 through e with batching loss `e/|C|`. Zero-based powers give a distinct
bound `(e−1)/|C|` for a nonempty family. ArkLib's checked-slice variant adds a prover message
checked against the public family; the note derives those slices without a message.

Finite-free transport holds over commutative rings. The randomized knowledge theorem requires
finite-domain challenges, functional compatibility and injective compatible `P → C` transport.
Each retained-variable challenge adds `2/|C|`; the terminal adds no challenge error. The actual
composed reduction has completeness from every initial state and ends at `pc.evalRel`; a
downstream opening argument supplies its own contract.

The note begins with public partial values. [DP24](DP24.md) and [Flock](BRW26.md) begin with one
scalar claim and therefore require their own checked reconstruction head. Hachi shares the
finite-observation algebra but retains its trace/CWSS protocol over the cyclotomic ring.

## Source Access

- [Public note](https://github.com/leanEthereum/leanVM-b/blob/main/misc/ring-switching-generalized.pdf).
- [Bibliography](../../../blueprint/src/references.bib), key `RSG`.
- Three-page PDF with creation metadata 2026-07-01; reduction p.1, soundness and multiplier
  evaluation p.2. The coverage audit records its SHA-256. PDF metadata is not a publication date.
