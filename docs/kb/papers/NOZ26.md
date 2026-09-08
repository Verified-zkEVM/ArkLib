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
gadget decomposition, inner-outer commitment), and develops Hachi's ring-switching constructions.
Its §3 trace relocation and §4.3 quotient lift have different laws and security boundaries from
the randomized coordinate-packing protocol used by Binius / [DP24](DP24.md).

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
- The **extension-field → cyclotomic-ring reduction** (§3.1): a one-message deterministic
  trace relocation. It packs monomial coefficients over the fixed subfield, sends a ring
  evaluation Y, and checks `Tr_H(Y·σ₋₁(v))=(d/k)·y`. `Hachi/TraceHead/` implements this head
  over the actual fixed subring: monomial packing inverses, unit cancellation of d/k, actual
  guarded execution, completeness, CWSS, and source coverage using the real committer. Its
  output retains the same norm-conditioned opening at `relPolyEval`. See the
  [coverage audit](../audits/ring-switching-model-coverage.md).
  The actual ψ basis is identified with `PackingData` coordinates, including the numeric
  monomial-index transport. `TraceHead.unpack_eval_eq_observation` invokes the shared
  `PackingData.readback_coordinateSlices` law. The actual head's observation adapter uses that
  unconditional identity; its honest checking and read-back invoke shared `CheckedObservation`
  lemmas, carrying both dependencies into production completeness and CWSS. The real scaled-trace
  guard is proved equivalent to observation for arbitrary sent ring values. The common algebra
  allows arbitrary finite weights; Hachi instantiates monomial weights at fixed-subring points.
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
  **Scope** (matching the "Paper-model boundary — closed" note in
  `Hachi/RingSwitch/Reduction.lean`): the generic Figure 4 / Lemma 9 kernel is the simplified
  raw-`(z, r)` one, but the **Hachi instance now commits the digits**. The paper's p. 18 honest
  protocol commits `(z, r₁, …, r_log_b(q))` with per-digit norm bounds — "there is a hidden gadget
  decomposition of `r`" — and that encoding *is* formalized, at the Hachi boundary:
  `rhoDigits` (`Hachi/RingSwitch/RhoDigits.lean`) with the reconstruction identity
  `rhoDigits_reconstruct` / `rhoDigits_evalAt`, committed by `liftMessage` at width `μ + n·δ`,
  `δ = clog_b q`. Honest completeness is unconditional
  (`liftReduction_perfectCompleteness_image`, `RingSwitch/Completeness.lean`): the quotient half of
  `liftShort` is a discharged conclusion at radius `⌊b/2⌋`, for an *arbitrary* quotient
  (`rhoDigits_valMinAbs_natAbs_le`, `rhoDigitsShort_of_digitBaseOk`).

  Committing the raw quotient instead admits only the unconditional bound `q/2`
  (`rhoShort_half`) — sharp, since the `R^lin` matrix carries the Ajtai key — forcing a zero-check
  range base of at least `q/2 + 1` and, with the batching bridge's pull-back orientations, the
  collapse `γ = q/2 = bZero − 1`. `HonestRangeParams.ofPinnedDigitBase b` — `bZero = b`,
  `γ = b − 1` — is the witness for the two-sided regime: it satisfies the pull-back orientation
  `bZero − 1 ≤ γ`, and `pinned_of_soundness_orientations` applied to it gives
  `γ = bZero − 1 ∧ γ < q/2`, so the pinned regime is realizable at `O(b)`.

  `moduleSIS_relation_of_mem_Collision` states the payoff: `LiftCom.Collision` satisfies
  `ModuleSIS.relation` for the lift's Ajtai key at radius `2·bound` (nonzero via
  `liftMessage_injective`, short, in the kernel). Scope: that key is a *parameter* of
  `hachiLiftCom`, not yet sampled by `keygen` alongside the inner-outer commitment's own — so the
  collision-to-Module-SIS reduction is complete locally, while the end-to-end security integration
  ([NOZ26] §4.5, `outputToModuleSIS_valid_of_verified`) is not.
- Theorem 2 gives a finite-free packing map ψ and the scaled trace pairing. These support
  a separate trace head; the existing `RingSwitchingProfile` reconstruction laws do not by
  themselves certify that protocol. A Boolean-table version additionally needs explicit
  transport from the paper's monomial coefficients, with commitment and norm accounting.
- Parameter translation: Hachi's Theorem 2 packs `d/k` subfield elements. ArkLib's
  `RingSwitchingProfile ... κ` uses `2^κ` for this packing rank, so this `κ` is
  `log₂(d/k)` in Hachi notation, not Hachi's extension-degree parameter `k`/`κ`.

## Main ArkLib Touchpoints

- [`ArkLib/Data/Lattices/CyclotomicRing/Subfield.lean`](../../../ArkLib/Data/Lattices/CyclotomicRing/Subfield.lean)
  — umbrella for Lemma 5, Theorem 2, and Lemma 6.
- [`ArkLib/Commitments/Functional/Hachi/TraceHead/Basic.lean`](../../../ArkLib/Commitments/Functional/Hachi/TraceHead/Basic.lean)
  — the scalar head and actual honest committer connection.
- [`ArkLib/Data/Lattices/CyclotomicRing/Core/Modulus.lean`](../../../ArkLib/Data/Lattices/CyclotomicRing/Core/Modulus.lean)
  — `powTwoCyclotomic`.
- [`ArkLib/Commitments/Functional/Hachi/Gadget/Core.lean`](../../../ArkLib/Commitments/Functional/Hachi/Gadget/Core.lean)
  — the gadget matrix and `gadgetDecompose`.
- [`ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean`](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean)
  — weak binding.
- Concept page: [`../concepts/ring-switching.md`](../concepts/ring-switching.md)

## Known Divergences From ArkLib

- The implemented §3.1 trace head uses the actual fixed subring without relying on its
  unfinished identification with `GF(q^k)`. Its ring/trace infrastructure is noncomputable,
  and it is not yet packaged as an executable scalar Scheme. The trace remains unnormalized:
  Theorem 2 and `traceH_psi_mul_conj` retain d/k, while the p.13 prose saying it fixes subfield
  elements omits that factor. The formal head cancels the actual unit d/k.
- Hachi §3.2 and §4.5 compress field-valued partials through `Σ_i y_i Z^i`, but powers of Z
  form a basis only over the base field. For two partials, errors `(Zδ,−δ)` preserve that
  equation while altering reconstruction at a by `δ(Z−a)`. This is the noninjective
  recombination rejected by Flock Remark 5. The recursive pull-back needs a sound replacement;
  ψ alone does not repair it without new layout, commitment, trace, norm, and security proofs.
  See the [coverage audit](../audits/ring-switching-model-coverage.md).
- Hachi Lemma 5 is only **conditionally complete**: `fixedSubring_isField` and
  `fixedSubringEquivGaloisField` depend on the sorried factor-swap lemma
  `no_selfReciprocal_factor`. Eq. (7), the fixed-subring cardinality, Theorem 2, and Lemma 6 do
  not depend on that gap. Lemma 6 is fully proved, under the weaker odd-characteristic
  assumption actually used by its coefficient argument.
- `R_q` is **not an integral domain**. Field-style Schwartz–Zippel with denominator `|R_q|`
  does not apply. The §3.1 trace head is deterministic; Hachi's downstream security uses its
  CWSS chain and norm-conditioned binding/collision escape.
- Hachi Lemma 10's uniform-vector CWSS argument is invalid for multivariate multilinear
  polynomials: a coordinate-wise star supplies only an axis cross, which does not determine the
  polynomial. ArkLib's zero-check (`ZeroCheck/Reduction.lean`) draws each of the `m₀ + m₁`
  coordinates in its own two-child scalar round and extracts with the nested-tree zero test
  (`NestedEvaluationTree.eq_zero_of_vanishes_comp`), whose leaves form a genuine `2^(m₀+m₁)`-point grid
  rather than a star. (An earlier rendering restricted the two evaluation points to Kronecker
  curves at `D = max(2, 2^{m₀}, 2^{mα})`; it was superseded — its branching factor is exponential,
  and it also cost ~21 bits of soundness — and is no longer formalized. The quantitative record is
  in `docs/kb/audits/noz26-zero-check-lemma10.md`, "Superseded: the one-round Kronecker-seed
  repair".) The corrected CWSS theorem is proof-`sorry`-free and is composed into the
  escape-threaded opening chain (`Composition.lean`). Its named extractor is executable:
  `ChallengeTree.LeafWitnesses`
  supplies an `Option` candidate opening for each leaf and it directly returns the all-left entry,
  while classical choice remains proof-local to the certificate. The weak-binding disjunct is
  discharged through `LiftCom`'s norm-conditioned collision. The repair costs nothing on the
  honest side: splitting the two vector challenges into scalar rounds leaves the interactive
  protocol unchanged, and `ZeroCheck/Completeness.lean` proves the honest prover accepted with
  probability one (`nestedZeroCheckReduction_perfectCompleteness`, axiom-clean, error exactly
  zero — `relBatched` asserts the identities, so both polynomials vanish wherever the challenges
  land). At the batching bridge, shortness is **derived** from the range identity `H₀ ≡ 0`
  (`hZero_eq_zero_imp_liftShort`), so `relBatched` drops the shortness conjunct.
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
  `∑_{u,ℓ} F_{0,τ₀} = H₀(τ₀)` is false as printed; ArkLib follows Eq. (23) and range-checks the quotient-digit
  rows as well as the `z` rows. Lemma 10 asks for `D` transcripts from `SS(F_{q^k}, 2, D)` although
  that family has `ℓ(k−1)+1 = 2D − 1` elements, and ArkLib uses `2D − 1`. The prose above Lemma 10
  treats `(τ₀, τ₁)` as `log μ + log d + log n` coordinates, contradicting the lemma's own `ℓ = 2`,
  and `τ₀`'s stated domain `F^{log μ + log d}` on p. 20 disagrees with `w̃`'s domain
  `[μ + n·δ] × [d]`; ArkLib takes `ℓ = 2` and pins `m₀` to `log(μ + n·δ) + log d`.

- **Figure 9's `τ = 4` does not follow the paper's own rule for `τ`, and ArkLib uses `τ = 5`.**
  §4.4 fixes the folded-witness digit count as *the smallest integer `τ` with `b^τ > β`*, for the
  deterministic bound `β := 2ʳ·ω·b`. At Figure 9's own parameters (`b = 16`, `r = 10`, `ω = 16`)
  that is `β = 262144`, and `16⁴ = 65536 < β`, so §4.4's rule yields `τ = 5`. The same holds under
  the sharper `β = 2ʳ·ω·⌊b/2⌋ = 131072` that ArkLib proves (`vecLInftyNorm_honestZ_le`, using
  `‖sᵢ‖∞ ≤ ⌊b/2⌋` from the balanced digits of §2.1 together with [Mic07]): `16⁴` is still short.
  Figure 9 nonetheless tabulates `τ = 4`, alongside `z = 30583` for the maximum `L∞` norm of `z`.
  That `30583` is *exactly* `(16−1−8)·(1+16+16²+16³)` — the largest value four balanced base-`16`
  digits represent (`HachiParams.balancedDigitCapacity_four_eq`). This numerical agreement does
  not establish how the table's norm bound was obtained. The paper does not derive `30583` as a
  deterministic bound or reconcile it with §4.4's figure. Section 4.2 defines `τ := ⌈log_b β⌉`
  using the maximum norm, and asserts completeness without analyzing Figure 3's abort when
  `‖z‖∞ > β`. A `τ = 4` profile needs a justified completeness bound for that abort. Statistical
  analysis of the implementation's independently signed sparse challenges is a possible route;
  the paper does not supply that analysis.
  ArkLib formalizes the deterministic reading, where `τ = 5` is minimal
  (`HachiParams.tau_minimal`); everything else in Figure 9 is used verbatim. The τ = 4 statistical
  track is separate and not part of the profile in `Params.lean`.

- ArkLib phrases the definition over its own IOR machinery (`ProtocolSpec`, `Verifier`,
  `ChallengeTree`) rather than the paper's interactive-argument syntax. The transcript tree is made
  arity-indexed and challenge-branching only, abstracting away the commitment scheme of the paper.

## Open Formalization Gaps

- Package the proved §3.1 head with the full nonrecursive opening when an external scalar
  Scheme is needed. Its actual weak-opening and MsgShort seams are available; preserve the
  downstream collision escapes and distinguish semantic definitions from executable code.
- Close `no_selfReciprocal_factor`, the sole local gap preventing an unconditional proof of
  Lemma 5's field/isomorphism conclusion.
- Complete the still-sorried Hachi-specific links: what remains is the §4.5 recursion tail —
  partial evaluation (Eq. (24)), the `Z`-packing bridge (Eqs. (25)–(26), which carries the flagged
  soundness defect described above), and the trace handoff (Eqs. (27)–(28)). Everything through the sumcheck is
  proved in **both** directions: Lemma 8, the corrected Lemma 10 and its batching bridge, Lemma 9
  (the lift), the sumcheck bridge and summands, Lemma 11, and the final evaluation, each with
  coordinate-wise special soundness and perfect completeness, and the one-iteration soundness
  certificate (`hachi_iteration_coordinateWiseSpecialSoundWithEscape`) is `sorry`-free. The
  nonrecursive completeness chain uses proved pure/guarded composition with state-uniform suffix
  correctness. Its composed completeness and perfect-correctness theorems
  (`Hachi/Correctness.lean`) have only standard axiom dependencies.
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
