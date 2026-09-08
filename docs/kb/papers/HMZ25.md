---
kind: paper
bibkey: HMZ25
title: "Sublinear Proofs over Polynomial Rings"
year: "2025"
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2025/199
source_metadata: ../sources/HMZ25/metadata.yml
status: seeded
related_concepts:
  - ring-switching
related_modules:
  - ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean
  - ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean
  - ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean
  - ArkLib/Data/Lattices/CyclotomicRing/QuotientLift.lean
  - ArkLib/Commitments/Functional/Hachi/RingSwitch/Basic.lean
  - ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean
  - ArkLib/Commitments/Functional/Hachi/RingSwitch/Rlin.lean
---

# HMZ25

## At A Glance

Huang, Mao and Zhang's *Sublinear Proofs over Polynomial Rings* constructs proof systems for
Ring-R1CS. ArkLib uses its quotient-evaluation lift through Hachi's Figure 4/Lemma 9 presentation.
For a monic modulus f of degree d, a linear equality in the quotient becomes

```text
M(X)·z(X) = y(X) + f(X)·r(X),    deg r < d.
```

Evaluating at an extension-field point gives field arithmetic. Conversely, a defect of degree
at most 2d−1 that vanishes at 2d distinct points is zero.

## What ArkLib Uses From This Paper

`Lift.Presentation` and `IsPresentation` describe a quotient by any monic modulus, canonical
representatives and their laws. The generic algebra proves quotient-witness correspondence and
field-target interpolation recovery. Hachi instantiates it with the cyclotomic modulus `X^d+1`.

`Lift/Reduction.lean` uses the committed-scalar shell: the prover commits to a lifted witness,
receives a scalar challenge, and outputs the evaluated relation with commitment consistency and
admissibility. The witness `(z,r)` is not sent in the clear. The generic certificate is CWSS with
a collision escape, using a `2d`-challenge extraction kernel and an injective coefficient embedding.

## Main ArkLib Touchpoints

- [`Lift/Presentation.lean`](../../../ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean) and
  [`Reduction.lean`](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean) — quotient algebra and field-target protocol.
- [`CommittedScalar.lean`](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean) — commitment-anchored scalar phase and collision escape.
- [`CyclotomicRing/QuotientLift.lean`](../../../ArkLib/Data/Lattices/CyclotomicRing/QuotientLift.lean) — Hachi's presentation laws.
- [`Hachi/RingSwitch/Reduction.lean`](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean) and
  [`RhoDigits.lean`](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/RhoDigits.lean) — cyclotomic instance and committed quotient-digit encoding.

## Implementation Boundary

ArkLib's coverage is the lift used by [Hachi](NOZ26.md); the full Ring-R1CS system is outside it.
The paper also uses Galois rings with exceptional challenge sets, whose distinct elements have
invertible differences. This security generalization is outside the field-target interpolation
contract, although the presentation algebra itself is over commutative rings.

Hachi's commitment is binding on short openings. The transcript-tree escape event targets two
distinct short openings of the same commitment; the ordinary relation and extractor remain
unchanged. Hachi commits balanced digits of r with reconstruction and per-digit shortness proofs,
while the generic algebra retains raw r as its witness. The resulting short-collision-to-Module-SIS
implication is local to the supplied key; key-sampling and recursive integration are separate.

## Source Access

- [Cryptology ePrint Archive, 2025/199](https://eprint.iacr.org/2025/199).
- [Source metadata](../sources/HMZ25/metadata.yml) and [bibliography](../../../blueprint/src/references.bib).
- The [coverage audit](../audits/ring-switching-model-coverage.md) uses the 31-page PDF headed
  2025-02-10: exceptional sets §2.1 p.7, Definition 2/Proposition 2; lift construction §4 pp.17–26.
  The landing page separately lists a 2026-05-21 revision.
