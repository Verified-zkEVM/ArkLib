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
  - ArkLib/ProofSystem/RingSwitching/Packing/Profile.lean
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

- The **extension-field → cyclotomic-ring reduction** (§3): Hachi reduces evaluation proofs over
  `F_{q^k}` to equivalent statements over a power-of-two cyclotomic ring `R_q`. This is the
  ring-switching shape ArkLib factors out as `RingSwitchingProfile`.
- The **cyclotomic-ring → extension-field lift** (§4.3, Figure 4 / **Lemma 9**, following
  [`HMZ25`](HMZ25.md)): the *simplified* Figure 4 extraction kernel is **formalized and proven** as
  `liftPackage` in Hachi's
  `Commitments/Functional/Hachi/RingSwitch/Reduction.lean` — the CWSS certificate is the
  `liftPackage.isCWSS` field, and the generic theorem underneath it is
  `RingSwitching.Lift.coordinateWiseSpecialSound` — the cyclotomic instance of the generic
  `Lift` construction `ProofSystem/RingSwitching/Lift/` (over the
  committed-scalar shell in
  `OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean`), with the
  presentation law-discharge lemmas in
  `Data/Lattices/CyclotomicRing/QuotientLift.lean`. It is consumed at row 4 of the Hachi opening
  chain (composed in `Hachi/Composition.lean`).
  Design decisions recorded there: the never-sent `(z, r)` is the output-relation witness
  (D6); the `w̃`-commitment is the abstract, norm-conditioned weak-binding `LiftCom`
  (Remark 2 / Lemma 7), its binding break threaded backwards through all seams as an escape
  budget (`Set.withEscape`, design G1); the witness type carries `deg ρᵢ ≤ d − 1`
  (the paper's `Z_q^{<d}`); the extraction target is `R^lin` over `R_q`, equivalent to the
  paper's `Z_q[X]` identity by the quotient-witness correspondence.
  **Scope** (matching the "Paper-model boundary" note in `Hachi/RingSwitch/Reduction.lean`): what is
  formalized is the simplified raw-`(z, r)` Figure 4 / Lemma 9 kernel. The paper's p. 18 honest
  protocol commits `(z, r₁, …, r_log_b(q))` with per-digit norm bounds — "there is a hidden gadget
  decomposition of `r`" — and that encoding, its reconstruction identity, and an honest-prover
  completeness bound are **not** formalized; `RhoShort` records the resulting admissibility
  requirement abstractly. Separately, the escape-threaded CWSS certificate carries no security
  content for a nonempty escape set; `liftPackage` is instantiated with `esc = ∅`, so this is latent
  rather than live.
- The packing-layer instantiation: `L = R_q`, carrier `A = R_q`, `φ₀ = id`, `φ₁ = σ₋₁` (order-two
  automorphism), basis `ψ` from its **Theorem 2** — which discharges the profile's reconstruction
  laws for the Hachi instance.
- Parameter translation: Hachi's Theorem 2 packs `d/k` subfield elements. ArkLib's
  `RingSwitchingProfile ... κ` uses `2^κ` for this packing rank, so this `κ` is
  `log₂(d/k)` in Hachi notation, not Hachi's extension-degree parameter `k`/`κ`.

## Main ArkLib Touchpoints

- [`../../../ArkLib/ProofSystem/RingSwitching/Packing/Profile.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Profile.lean)
- [`ArkLib/Data/Lattices/CyclotomicRing/Core/Modulus.lean`](../../../ArkLib/Data/Lattices/CyclotomicRing/Core/Modulus.lean)
  — `powTwoCyclotomic`.
- [`ArkLib/Commitments/Functional/Hachi/Gadget.lean`](../../../ArkLib/Commitments/Functional/Hachi/Gadget.lean)
  — the gadget matrix and `gadgetDecompose`.
- [`ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean`](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean)
  — weak binding.
- Concept page: [`../concepts/ring-switching.md`](../concepts/ring-switching.md)

## Known Divergences From ArkLib

- ArkLib has not yet built the **§3 packing** ring-switching instance (`RingSwitchingProfile`); that
  abstraction is designed to admit it but only the Binius instance is implemented. The §4.3 `HMZ25`
  lift *is* built — see the Lemma 9 entry above.
- `R_q` is **not an integral domain**, so the generic `[IsDomain L]` Schwartz–Zippel soundness
  theorem does not instantiate Hachi. Hachi's **§3 packing** soundness (a CWSS-style argument) is a
  separate theorem with a different error and is out of scope for the current ring-switching module.
- ArkLib phrases the definition over its own IOR machinery (`ProtocolSpec`, `Verifier`,
  `ChallengeTree`) rather than the paper's interactive-argument syntax. The transcript tree is made
  arity-indexed and challenge-branching only, abstracting away the commitment scheme of the paper.

## Open Formalization Gaps

- Construct `hachiProfile : RingSwitchingProfile R_qH R_q κ_pack` and discharge
  `decomposeRows_spec` / `decomposeColumns_spec` via Theorem 2, with `2^κ_pack = d/k`
  (the §3 packing head; the §4.3 HMZ25 lift, Lemma 9, is done — see above).
- Formalize Hachi-specific soundness separately (does not reuse the field/domain soundness
  theorem): done through Lemma 9 (rows 1–4 of the opening chain); Lemmas 10–11 and the
  recursion adapters remain skeletons (see `Hachi/Composition.lean`'s inventory).
- The norm-growth and short-element invertibility inputs (`Mic07`, `LS18`) are deferred.

## Version Notes

- Cryptology ePrint Archive, Paper 2026/156. ArkLib tracks the ePrint version.
- Read together with [`FMN24.md`](FMN24.md), which introduces coordinate-wise special soundness.
- Builds on the ring-switching idea of Huang–Mao–Zhang (ePrint 2025) and integrates Greyhound
  (CRYPTO 2024); track which version is cited if proof obligations depend on exact statements.

## Source Access

- Source metadata: [`../sources/NOZ26/metadata.yml`](../sources/NOZ26/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib) (key `NOZ26`)
- ePrint: https://eprint.iacr.org/2026/156
