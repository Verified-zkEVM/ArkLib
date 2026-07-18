---
kind: paper
bibkey: HMZ25
title: "Sublinear Proofs over Polynomial Rings"
year: "2025"
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2025/199
source_metadata: ../sources/HMZ25/metadata.yml
status: seeded
related_modules:
  - ArkLib/Commitments/Functional/Hachi/RingSwitch/Basic.lean
  - ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean
  - ArkLib/Commitments/Functional/Hachi/RingSwitch/Rlin.lean
---

# HMZ25

## At A Glance

`HMZ25` (Huang–Mao–Zhang, ePrint 2025/199) builds sublinear-size proof systems for rank-one
constraint satisfaction over polynomial rings `Z_Q[X]/(X^N + 1)`. ArkLib uses one specific idea
from it: the **ring-switching lift**, which Hachi ([`NOZ26`](NOZ26.md), §4.3, Figure 4 / Lemma 9)
adopts to move a linear claim over the cyclotomic ring `Rq` into an extension field where the
sumcheck runs.

## What ArkLib Uses From This Paper

The lift itself: `M z = y` over `Rq = Zq[X]/(X^d + 1)` holds **iff** there is a quotient `r` with
`M z = y + (X^d + 1)·r` over `Zq[X]`. The prover commits to the lifted witness `(z, r)`, the
verifier samples a random evaluation point `X := α` in an extension field `F ⊇ Zq`, and both
sides evaluate the lifted rows at `α`. This "switches" the `Rq`-statement into `F`.

## Main ArkLib Touchpoints

- [`ArkLib/Commitments/Functional/Hachi/RingSwitch/Basic.lean`](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Basic.lean)
  — umbrella module; overview of the lift and the folder structure.
- [`ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean`](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean)
  — the two-round lift reduction and its CWSS skeleton (Hachi Figure 4 / Lemma 9).
- [`ArkLib/Commitments/Functional/Hachi/RingSwitch/Rlin.lean`](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Rlin.lean)
  — the zero-round entry adapter reshaping Hachi's Eq. (20) output into the unstructured linear
  relation `R^lin` the lift addresses.

## Version Notes

Cited via the ePrint version (2025/199). ArkLib follows Hachi's [`NOZ26`](NOZ26.md) presentation
of the lift rather than the original Ring-R1CS setting.

## Known Divergences From ArkLib

ArkLib formalizes only the lift step as used inside Hachi's opening argument, not the paper's
full Ring-R1CS proof system.

## Open Formalization Gaps

The interpolation-based extraction for Hachi's Lemma 9 (`lift_coordinateWiseSpecialSound`) is
currently a `sorry`-level skeleton; see the module docstrings under
`ArkLib/Commitments/Functional/Hachi/RingSwitch/`.

## Source Access

- Source metadata: [`../sources/HMZ25/metadata.yml`](../sources/HMZ25/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
