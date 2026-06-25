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
  - ArkLib/ProofSystem/RingSwitching/Profile.lean
  - ArkLib/Data/Lattices/CyclotomicRing/Core/Modulus.lean
  - ArkLib/Commitments/Functional/Hachi/Gadget.lean
  - ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean
  - ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean
---

# NOZ26

## At A Glance

`NOZ26` ("Hachi", Nguyen–O'Rourke–Zhang, ePrint 2026/156) is a concretely efficient lattice-based
multilinear polynomial commitment scheme over extension fields, built on power-of-two cyclotomic
rings, with a "square-root" verifier-time complexity under Module-SIS. ArkLib touches it from two
directions: it formalizes the paper's **commitment-layer building blocks** (cyclotomic modulus,
gadget decomposition, inner-outer commitment), and it treats Hachi as the **second intended
instance** of the generic ring-switching abstraction (the first being Binius / [`DP24`](DP24.md)).

## What ArkLib Uses From This Paper

Commitment layer:

- The power-of-two cyclotomic ring `R_q = Z_q[X]/(X^d + 1)` (`powTwoCyclotomic`).
- The base-`b` digit (gadget) decomposition `G⁻¹` and its reconstruction law.
- The inner-outer commitment and its weak-binding hypotheses (`q ≡ 5 (mod 8)`, `deg φ` a power
  of two, `κ² < q`).

Ring-switching layer:

- The **extension-field → cyclotomic-ring reduction**: Hachi reduces evaluation proofs over `F_{q^k}`
  to equivalent statements over a power-of-two cyclotomic ring `R_q`. This is the ring-switching
  shape ArkLib factors out as `RingSwitchingProfile`.
- The packing-layer instantiation: `L = R_q`, carrier `A = R_q`, `φ₀ = id`, `φ₁ = σ₋₁` (order-two
  automorphism), basis `ψ` from its **Theorem 2** — which discharges the profile's reconstruction
  laws for the Hachi instance.
- Parameter translation: Hachi's Theorem 2 packs `d/k` subfield elements. ArkLib's
  `RingSwitchingProfile ... κ` uses `2^κ` for this packing rank, so this `κ` is
  `log₂(d/k)` in Hachi notation, not Hachi's extension-degree parameter `k`/`κ`.

## Main ArkLib Touchpoints

- [`../../../ArkLib/ProofSystem/RingSwitching/Profile.lean`](../../../ArkLib/ProofSystem/RingSwitching/Profile.lean)
- [`ArkLib/Data/Lattices/CyclotomicRing/Core/Modulus.lean`](../../../ArkLib/Data/Lattices/CyclotomicRing/Core/Modulus.lean)
  — `powTwoCyclotomic`.
- [`ArkLib/Commitments/Functional/Hachi/Gadget.lean`](../../../ArkLib/Commitments/Functional/Hachi/Gadget.lean)
  — the gadget matrix and `gadgetDecompose`.
- [`ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean`](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean)
  — weak binding.
- Concept page: [`../concepts/ring-switching.md`](../concepts/ring-switching.md)

## Known Divergences From ArkLib

- ArkLib has not yet built the Hachi ring-switching instance; the abstraction is designed to admit
  it but only the Binius instance is implemented.
- `R_q` is **not an integral domain**, so the generic `[IsDomain L]` Schwartz–Zippel soundness
  theorem does not instantiate Hachi. Hachi soundness (a CWSS-style argument) is a separate theorem
  with a different error and is out of scope for the current ring-switching module.

## Open Formalization Gaps

- Construct `hachiProfile : RingSwitchingProfile R_qH R_q κ_pack` and discharge
  `decomposeRows_spec` / `decomposeColumns_spec` via Theorem 2, with `2^κ_pack = d/k`.
- Formalize Hachi-specific soundness separately (does not reuse the field/domain soundness theorem).
- The norm-growth and short-element invertibility inputs (`Mic07`, `LS18`) are deferred.
- The sumcheck / ring-switching evaluation machinery of the paper is not yet formalized.

## Version Notes

- Builds on the ring-switching idea of Huang–Mao–Zhang (ePrint 2025) and integrates Greyhound
  (CRYPTO 2024); track which version is cited if proof obligations depend on exact statements.

## Source Access

- Source metadata: [`../sources/NOZ26/metadata.yml`](../sources/NOZ26/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib) (key `NOZ26`)
- ePrint: https://eprint.iacr.org/2026/156
