---
kind: paper
bibkey: NOZ26
title: "Hachi: Efficient Lattice-Based Multilinear Polynomial Commitments over Extension Fields"
year: "2026"
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2026/156
source_metadata: ../sources/NOZ26/metadata.yml
status: seeded
related_modules:
  - ArkLib/Data/Lattices/CyclotomicRing/Modulus.lean
  - ArkLib/CommitmentScheme/Ajtai/Gadget.lean
  - ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean
  - ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean
---

# NOZ26

## At A Glance

`NOZ26` is the Nguyen–O'Rourke–Zhang Hachi paper, an extension-field multilinear polynomial
commitment over power-of-two cyclotomic rings. ArkLib formalizes its commitment-layer building
blocks: the power-of-two cyclotomic modulus, the base-`b` gadget decomposition `G⁻¹`, and the
inner-outer commitment with weak binding.

## What ArkLib Uses From This Paper

- The power-of-two cyclotomic ring `R_q = Z_q[X]/(X^d + 1)` (`powTwoCyclotomic`).
- The base-`b` digit (gadget) decomposition `G⁻¹` and its reconstruction law.
- The inner-outer commitment and its weak-binding hypotheses (`q ≡ 5 (mod 8)`, `deg φ` a power
  of two, `κ² < q`).

## Main ArkLib Touchpoints

- [`ArkLib/Data/Lattices/CyclotomicRing/Modulus.lean`](../../../ArkLib/Data/Lattices/CyclotomicRing/Modulus.lean)
  — `powTwoCyclotomic`.
- [`ArkLib/CommitmentScheme/Ajtai/Gadget.lean`](../../../ArkLib/CommitmentScheme/Ajtai/Gadget.lean)
  — the gadget matrix and `gadgetDecompose`.
- [`ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean`](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean)
  — weak binding.

## Open Formalization Gaps

- The norm-growth and short-element invertibility inputs (`Mic07`, `LS18`) are deferred.
- The sumcheck / ring-switching evaluation machinery of the paper is not yet formalized.

## Source Access

- Source metadata: [`../sources/NOZ26/metadata.yml`](../sources/NOZ26/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
