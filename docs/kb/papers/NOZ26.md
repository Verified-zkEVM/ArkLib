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
  - ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness.lean
  - ArkLib/Data/Lattices/CyclotomicRing/Modulus.lean
  - ArkLib/CommitmentScheme/Ajtai/Gadget.lean
  - ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean
  - ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean
---

# NOZ26

## At A Glance

`NOZ26` ("Hachi") is the Nguyen–O'Rourke–Zhang concretely efficient lattice-based multilinear
polynomial commitment scheme over extension fields, improving on Greyhound (CRYPTO 2024). ArkLib
draws on the paper in two distinct ways: its **commitment-layer building blocks** (the power-of-two
cyclotomic ring, the base-`b` gadget decomposition, and the inner-outer commitment with weak
binding) and its **security-analysis machinery** (the multi-round form of coordinate-wise special
soundness in Definition 3 and the soundness-error bound in Lemma 4).

## What ArkLib Uses From This Paper

Commitment layer:

- The power-of-two cyclotomic ring `R_q = Z_q[X]/(X^d + 1)` (`powTwoCyclotomic`).
- The base-`b` digit (gadget) decomposition `G⁻¹` and its reconstruction law.
- The inner-outer commitment and its weak-binding hypotheses (`q ≡ 5 (mod 8)`, `deg φ` a power
  of two, `κ² < q`).

Security analysis:

- **Definition 3 (coordinate-wise special soundness, multi-round).** This is the notion ArkLib
  formalizes as `Verifier.coordinateWiseSpecialSound`: existence of a tree-based extractor that
  turns any structured, accepting tree of transcripts into a valid input witness.
- The §2.3 description of the special-sound family `SS(S, ℓ, k)`, rendered as
  `CoordinateWise.IsSpecialSoundFamily`.

## Main ArkLib Touchpoints

- [`ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness.lean`](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness.lean)
  cites `NOZ26` in its module docstring and follows its Definition 3 for the multi-round
  coordinate-wise special-soundness notion.
- [`ArkLib/Data/Lattices/CyclotomicRing/Modulus.lean`](../../../ArkLib/Data/Lattices/CyclotomicRing/Modulus.lean)
  — `powTwoCyclotomic`.
- [`ArkLib/CommitmentScheme/Ajtai/Gadget.lean`](../../../ArkLib/CommitmentScheme/Ajtai/Gadget.lean)
  — the gadget matrix and `gadgetDecompose`.
- [`ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean`](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean)
  — weak binding.

## Version Notes

- Cryptology ePrint Archive, Paper 2026/156. ArkLib tracks the ePrint version.
- Read together with [`FMN24.md`](FMN24.md), which introduces coordinate-wise special soundness.

## Known Divergences From ArkLib

- ArkLib phrases the definition over its own IOR machinery (`ProtocolSpec`, `Verifier`,
  `ChallengeTree`) rather than the paper's interactive-argument syntax. The transcript tree is made
  arity-indexed and challenge-branching only, abstracting away the commitment scheme of the paper.

## Open Formalization Gaps

- The norm-growth and short-element invertibility inputs (`Mic07`, `LS18`) are deferred.
- The sumcheck / ring-switching evaluation machinery of the paper is not yet formalized.

## Source Access

- Source metadata: [`../sources/NOZ26/metadata.yml`](../sources/NOZ26/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
</content>
</invoke>
