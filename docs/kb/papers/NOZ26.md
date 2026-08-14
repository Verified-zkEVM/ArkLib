---
kind: paper
bibkey: NOZ26
title: "Hachi: Efficient Lattice-Based Multilinear Polynomial Commitments over Extension Fields"
year: "2026"
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2026/156
source_metadata: ../sources/NOZ26/metadata.yml
status: active-audit
related_modules:
  - ArkLib/Data/Lattices/CyclotomicRing/Subfield.lean
  - ArkLib/ProofSystem/RingSwitching/Packing/Profile.lean
  - ArkLib/Data/Lattices/CyclotomicRing/Core/Modulus.lean
  - ArkLib/Commitments/Functional/Hachi/Gadget/Core.lean
  - ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean
  - ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean
  - ArkLib/Commitments/Functional/Hachi/ZeroCheck/Reduction.lean
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

- The §3 subfield layer: `R_q^H`, its cardinality `q^k`, the packing bijection `ψ`, the trace
  inner-product identity, and Lemma 6's norm bound. The final Lemma 5 field/isomorphism
  declarations retain one explicit proof gap; see the dedicated audit below.
- The **extension-field → cyclotomic-ring reduction**: Hachi reduces evaluation proofs over `F_{q^k}`
  to equivalent statements over a power-of-two cyclotomic ring `R_q`. This is the ring-switching
  shape ArkLib factors out as `RingSwitchingProfile`.
- The **extension-field → cyclotomic-ring reduction** (§3): Hachi reduces evaluation proofs over
  `F_{q^k}` to equivalent statements over a power-of-two cyclotomic ring `R_q`. This is the
  ring-switching shape ArkLib factors out as `RingSwitchingProfile`.
- The **cyclotomic-ring → extension-field lift** (§4.3, Figure 4 / **Lemma 9**, following
  [`HMZ25`](HMZ25.md)): the *simplified* Figure 4 extraction kernel is **formalized and proven** as
  `liftPackage` in Hachi's
  `Commitments/Functional/Hachi/RingSwitch/Reduction.lean` — the CWSS certificate is the
  `liftPackage.isCWSS` field, and the generic theorem underneath it is
  `RingSwitching.Lift.coordinateWiseSpecialSoundWithEscape` — the cyclotomic instance of the
  generic `Lift` construction `ProofSystem/RingSwitching/Lift/` (over the
  committed-scalar shell in
  `OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean`), with the
  presentation law-discharge lemmas in
  `Data/Lattices/CyclotomicRing/QuotientLift.lean`. It is consumed at row 4 of the Hachi opening
  chain (composed in `Hachi/Composition.lean`).
  Design decisions recorded there: the never-sent `(z, r)` is the output-relation witness;
  the `w̃`-commitment is the abstract, norm-conditioned weak-binding `LiftCom`
  (Remark 2 / Lemma 7), and its binding break is carried by an **escape event** on the transcript
  tree (`CommittedScalar.escEvent`, whose hardness target is the short-collision set
  `LiftCom.Collision`) rather than by widened relations — so relations and extractor stay ordinary,
  and events compose along the chain without a seam; the witness type carries `deg ρᵢ ≤ d − 1`
  (the paper's `Z_q^{<d}`); the extraction target is `R^lin` over `R_q`, equivalent to the
  paper's `Z_q[X]` identity by the quotient-witness correspondence.
  **Scope** (matching the "Paper-model boundary" note in `Hachi/RingSwitch/Reduction.lean`): what is
  formalized is the simplified raw-`(z, r)` Figure 4 / Lemma 9 kernel. The paper's p. 18 honest
  protocol commits `(z, r₁, …, r_log_b(q))` with per-digit norm bounds — "there is a hidden gadget
  decomposition of `r`" — and that encoding, its reconstruction identity, and an honest-prover
  completeness bound are **not** formalized; `RhoShort` records the resulting admissibility
  requirement abstractly.
- The packing-layer instantiation: `L = R_q`, carrier `A = R_q`, `φ₀ = id`, `φ₁ = σ₋₁` (order-two
  automorphism), basis `ψ` from its **Theorem 2** — which discharges the profile's reconstruction
  laws for the Hachi instance.
- Parameter translation: Hachi's Theorem 2 packs `d/k` subfield elements. ArkLib's
  `RingSwitchingProfile ... κ` uses `2^κ` for this packing rank, so this `κ` is
  `log₂(d/k)` in Hachi notation, not Hachi's extension-degree parameter `k`/`κ`.

## Main ArkLib Touchpoints

- [`ArkLib/Data/Lattices/CyclotomicRing/Subfield.lean`](../../../ArkLib/Data/Lattices/CyclotomicRing/Subfield.lean)
  — umbrella for Lemma 5, Theorem 2, and Lemma 6.
- [`../../../ArkLib/ProofSystem/RingSwitching/Packing/Profile.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Profile.lean)
- [`ArkLib/Data/Lattices/CyclotomicRing/Core/Modulus.lean`](../../../ArkLib/Data/Lattices/CyclotomicRing/Core/Modulus.lean)
  — `powTwoCyclotomic`.
- [`ArkLib/Commitments/Functional/Hachi/Gadget/Core.lean`](../../../ArkLib/Commitments/Functional/Hachi/Gadget/Core.lean)
  — the gadget matrix and `gadgetDecompose`.
- [`ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean`](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean)
  — weak binding.
- Concept page: [`../concepts/ring-switching.md`](../concepts/ring-switching.md)

## Known Divergences From ArkLib

- ArkLib has not yet built the Hachi ring-switching instance; the abstraction is designed to admit
  it but only the Binius instance is implemented.
- Hachi Lemma 5 is only **conditionally complete**: `fixedSubring_isField` and
  `fixedSubringEquivGaloisField` depend on the sorried factor-swap lemma
  `no_selfReciprocal_factor`. Eq. (7), the fixed-subring cardinality, Theorem 2, and Lemma 6 do
  not depend on that gap. Lemma 6 is fully proved, under the weaker odd-characteristic
  assumption actually used by its coefficient argument.
- `R_q` is **not an integral domain**, so the generic `[IsDomain L]` Schwartz–Zippel soundness
  theorem does not instantiate Hachi. Hachi soundness (a CWSS-style argument) is a separate theorem
  with a different error and is out of scope for the current ring-switching module.
- Hachi Lemma 10's uniform-vector CWSS argument is invalid for multivariate multilinear
  polynomials: a coordinate-wise star supplies only an axis cross, which does not determine the
  polynomial. ArkLib's zero-check (`ZeroCheck/Reduction.lean`) draws each of the `m₀ + m₁`
  coordinates in its own two-child scalar round and extracts with the nested-tree zero test
  (`NestedEvaluationTree.eq_zero_of_vanishes_comp`), whose leaves form a genuine `2^(m₀+m₁)`-point grid
  rather than a star. (An earlier rendering restricted the two evaluation points to Kronecker
  curves at `D = max(2, 2^{m₀}, 2^{mα})`; it was superseded — its branching factor is exponential —
  and is no longer formalized.) The
  corrected CWSS theorem is proof-`sorry`-free and is composed into the escape-threaded opening
  chain (`Composition.lean`); the weak-binding disjunct is discharged through `LiftCom`'s
  norm-conditioned collision. At the batching bridge, shortness is **derived** from the range
  identity `H₀ ≡ 0` (`hZero_eq_zero_imp_liftShort`), so `relBatched` drops the shortness conjunct.
  At the point-check and sumcheck seams, `relNestedZeroCheck`/`nestedRoundRel` **do** carry a
  `liftShort` conjunct, but as the commitment's shortness index rather than as a range assumption:
  `LiftCom.Collision` is defined on pairs of distinct *short* openings, so it is what makes the
  weak-binding branch a Module-SIS break. Since `relBatched` is norm-free, shortness is never
  derived from an assumption of shortness.
  The identities themselves are represented and point-evaluated as `CMlPolynomialEval`
  Boolean-value vectors, matching the paper's multilinear `H₀` and `Hα`; Mathlib `MvPolynomial`
  appears only inside the zero test's proof, reached through
  `CMlPolynomialEval.eval_eq_MvPolynomial_MLE`. Eq. (22)'s public
  contraction `∑_{u,ℓ} M̃_α(i,u)·w̃(u,ℓ)·α̃(ℓ)` is built (`mAlphaTilde`, `alphaTilde`,
  `alphaContract`) and **proved** equal to the per-row `α`-defect that `H_α`'s table stores
  (`alphaDefect_wTable`, `hAlpha_eq_zero_iff_alphaDefect`), so §4.3's "represent the constraints by
  polynomials" step is derived rather than assumed.
  See
  [`../audits/noz26-zero-check-lemma10.md`](../audits/noz26-zero-check-lemma10.md).
- Separately from the axis-cross repair, ArkLib's zero-check diverges from the printed §4.3 in three
  further places, each deliberate and each because the paper is internally inconsistent there. The
  range summand carries **no `1_{≤μ}` indicator**: `F_{0,τ₀}` on p. 22 has one but Eq. (23)'s `H₀`
  does not, and the bullet above Eq. (23) constrains `u ∈ [μ + n]`, so the paper's own
  `∑_{u,ℓ} F_{0,τ₀} = H₀(τ₀)` is false as printed; ArkLib follows Eq. (23) and range-checks the `r`
  rows as well as the `z` rows. Lemma 10 asks for `D` transcripts from `SS(F_{q^k}, 2, D)` although
  that family has `ℓ(k−1)+1 = 2D − 1` elements, and ArkLib uses `2D − 1`. The prose above Lemma 10
  treats `(τ₀, τ₁)` as `log μ + log d + log n` coordinates, contradicting the lemma's own `ℓ = 2`,
  and `τ₀`'s stated domain `F^{log μ + log d}` on p. 20 disagrees with `w̃`'s domain
  `[μ + n] × [d]`; ArkLib takes `ℓ = 2` and pins `m₀` to `log(μ + n) + log d`.

- ArkLib phrases the definition over its own IOR machinery (`ProtocolSpec`, `Verifier`,
  `ChallengeTree`) rather than the paper's interactive-argument syntax. The transcript tree is made
  arity-indexed and challenge-branching only, abstracting away the commitment scheme of the paper.

## Open Formalization Gaps

- Construct `hachiProfile : RingSwitchingProfile R_qH R_q κ_pack` and discharge
  `decomposeRows_spec` / `decomposeColumns_spec` via Theorem 2, with `2^κ_pack = d/k`.
- Close `no_selfReciprocal_factor`, the sole local gap preventing an unconditional proof of
  Lemma 5's field/isomorphism conclusion.
- Complete the still-sorried Hachi-specific links, notably Lemma 9, the sumcheck bridge and
  summands, Lemma 11, final evaluation, and recursion handoff. The corrected Lemma 10 and its
  batching bridge are already proved.
- Lemma 6's packing norm growth is complete. The separate Micciancio product-norm and
  Lyubashevsky–Seiler short-invertibility inputs used by the commitment security layer are also
  proved in their respective modules.
- Resolve the flagged `Z`-packing/partial-evaluation knowledge-soundness gap in the recursion chain.

Detailed Lemma 5–6 correspondence and proof status:
[`../audits/noz26-subfield-lemmas5-6.md`](../audits/noz26-subfield-lemmas5-6.md).

## Version Notes

- Cryptology ePrint Archive, Paper 2026/156. ArkLib tracks the January 30, 2026 ePrint version for
  the zero-check audit.
- Read together with [`FMN24.md`](FMN24.md), which introduces coordinate-wise special soundness.
- Builds on the ring-switching idea of Huang–Mao–Zhang (ePrint 2025) and integrates Greyhound
  (CRYPTO 2024); track which version is cited if proof obligations depend on exact statements.

## Source Access

- Source metadata: [`../sources/NOZ26/metadata.yml`](../sources/NOZ26/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib) (key `NOZ26`)
- ePrint: https://eprint.iacr.org/2026/156
