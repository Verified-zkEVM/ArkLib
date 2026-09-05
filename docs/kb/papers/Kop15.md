---
kind: paper
bibkey: Kop15
title: "List-Decoding Multiplicity Codes"
year: "2015"
bib_source: blueprint/src/references.bib
canonical_url: https://theoryofcomputing.org/articles/v011a005/
source_metadata: ../sources/Kop15/metadata.yml
status: active
related_modules:
  - ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Contracts.lean
  - ArkLib/Data/CodingTheory/ReedSolomon/LowRateListDecoding/Main.lean
---

# Kop15

## At A Glance

`Kop15` is Swastik Kopparty, *List-Decoding Multiplicity Codes*, Theory of Computing 11(5),
2015. Its Theorem 4.3 solves a univariate polynomial differential equation involving Hasse
derivatives and bounds the number of low-degree solutions.

## What ArkLib Uses From This Paper

`BCPZZ26` restates Theorem 4.3 as its Theorem 2.1. With derivative order `d`, message degree less
than the prime field size, individual variable degree less than `q`, and weighted degree less than
`q²`, the specialization used by `BCPZZ26` has at most `q^(4d+6)` solutions. This is the exact list
bound in ArkLib's headline target.

## Main ArkLib Touchpoints

- [`Main.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/LowRateListDecoding/Main.lean) uses
  the specialized exact bound.
- [`Contracts.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Contracts.lean)
  leaves the equation validity predicate and exact list bound parametric, so improved solver
  analyses do not change decoder integration.
- The future implementation should live behind a reusable CompPoly differential-equation solver,
  not inside the paper-specific interpolation proof.

## Version Notes

The canonical source is the final Theory of Computing article. The theorem-number correspondence is
`Kop15` Theorem 4.3 = `BCPZZ26` Theorem 2.1.

## Known Divergences From ArkLib

No theorem from this paper is formalized yet. The headline target uses only the exact specialized
solution bound, not a runtime theorem.

## Open Formalization Gaps

- Define the differential-equation relation using Hasse derivatives.
- Formalize the extension-field initial conditions and lifting recursion.
- Prove solver soundness, completeness, and the general solution-count bound.
- Connect a concrete implementation to a cost model before claiming `q^O(d+1)` time.

## Source Access

- Source metadata: [`../sources/Kop15/metadata.yml`](../sources/Kop15/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
