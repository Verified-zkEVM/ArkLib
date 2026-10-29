---
kind: paper
bibkey: CHA24
title: "Fully succinct arguments over the integers from first principles"
year: 2024
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2024/1548
source_metadata: ../sources/CHA24/metadata.yml
status: seeded
related_modules:
  - ArkLib/Data/MvPolynomial/PrimeFingerprint.lean
---

# CHA24

## At A Glance

Campanelli and Hall-Andersen introduce fingerprinting to reduce claims over the integers to
claims over prime fields in their integer-argument framework and Zaratan construction.
ArkLib cites this paper for the provenance of integer fingerprinting. Its direct multivariate
formalization target is [BGKLSW26, Lemma 4.8](BGKLSW26.md).

## What ArkLib Uses From This Paper

An integer polynomial is reduced modulo a sampled prime and evaluated at a sampled field point.
The error analysis separates primes dividing every coefficient from zeros of a nonzero
polynomial over a prime field. ArkLib makes this reusable in a counting module, with native
probability statements in a separate module.

## Main ArkLib Touchpoints

- [`PrimeFingerprint.lean`](../../../ArkLib/Data/MvPolynomial/PrimeFingerprint.lean) cites
  `CHA24` and proves the prime-divisor count and averaged zero-fraction bounds.
- [`PrimeFingerprintProbability.lean`](../../../ArkLib/Data/MvPolynomial/PrimeFingerprintProbability.lean)
  gives the two-stage sampler and its native probability bound.
- [The BitZ paper page](BGKLSW26.md) maps these bounds to their protocol consumer and records the
  sampling and coefficient-bound conventions.

## Scope

The citation records the fingerprinting technique's provenance. ArkLib does not implement the
Zaratan argument or its commitment scheme here, and does not assign a CHA24 theorem number to
the multivariate statement. Use BGKLSW26's revision and numbering for that theorem correspondence.

## Source Access

- [Public ePrint paper and revision history](https://eprint.iacr.org/2024/1548)
- [Source metadata](../sources/CHA24/metadata.yml)
- [Repository bibliography](../../../blueprint/src/references.bib)
