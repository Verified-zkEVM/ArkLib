# Ring Switching

Packing reduces a scalar polynomial claim to an evaluation of the same packed polynomial under
its original commitment. The packing algebra `P` and opening algebra `E` have independent finite
bases over a common commutative ring `B`; neither an embedding `P → E` nor equal ranks is needed.
The challenge algebra `C` receives packed coefficients and supplies the sumcheck challenges.

A separate construction, `Lift`, replaces a quotient-ring equality by an exact polynomial equality
before evaluating it in a field. Its data and security contracts remain separate from packing.
`ProofSystem/RingSwitching/Basic.lean` routes both families.

## Coordinate equations

`PackingData` specifies bases indexed by `ιP` and `ιE`. A source layout gives components `pᵢ`,
a query `q`, an opening point `x(q)` and reconstruction weights `wᵢ(q)`. Its certified identity is

`eval(q,p) = ∑ᵢ wᵢ(q) · pᵢ(x(q))`.

`packedMLE` groups the components in the packing basis; `unpack` is its inverse. A component-value
family `α : ιP → E` determines its transpose `ιE → P`. For challenge weights `vᵤ(c)`, the verifier
computes `derivedTarget α v = ∑ᵤ vᵤ(c) · transpose(α)ᵤ`. If `α` is honest, this equals the Boolean
hypercube sum of the same packed polynomial times the public multiplier `A(q,c)`.
`Multiplier` evaluates that polynomial using a read-once matrix program; the terminal
verifier executes this evaluator. The equality certificate links it to the sumcheck polynomial.

`ClaimLayout` includes prefix and suffix packing. `ClaimLayout/Quirky` gives the skipped/extra-bit
Lagrange layout with an explicit injective node map. Hachi's monomial-coefficient layout lives
with its own trace head. `Packing/Conformance` gives the tensor carrier's column/opening and
row/slice identities and the final equality-value equation.

## One shared protocol

Import `ArkLib.ProofSystem.RingSwitching.Packing.RingSwitch`. Supply:

- `PackingData B`, the retained dimension `m` and a `ClaimLayout`;
- a first-message carrier `M` and an equivalence `M ≃ (ιP → E)`;
- a `BatchingRule C ιE`, giving the sampled challenge and its weights;
- a `PackedCommitment P m`, giving the original oracle collection and compatibility relation.

`Head` sends one encoded component-value family, checks scalar reconstruction, samples the batching
challenge and derives the product-sumcheck target. Its output is directly the initial
`ProductSumcheck.Statement`; no formatting phase intervenes. The `m` scalar rounds send degree-two
polynomials. The terminal sends one evaluation value `v` and checks `A(q,c)(r) * v = target`.
The endpoint is `pc.evalRelWithContext (layout.Query × rule.Challenge)`: the original query and
batching challenge remain public, the oracle collection is unchanged, and the witness is the
same packed polynomial. The terminal does not cancel a zero multiplier or itself certify that
`v` is the true opening; that remains the downstream opening's relation.

A separate `pc.Honest` constructor provides a compatible oracle for every polynomial. Security
uses only the compatibility relation, with no coverage assumption. Source restrictions such as
an inherited residual relation `R(q,p)` require separate maintained transport through the
protocol; retaining `q` does not prove those restrictions.

## Completeness and round-by-round security

`RingSwitch.perfectCompleteness` uses a sampleable commutative challenge ring and the layout's
reconstruction law. It does not require a separation certificate or no-zero-divisors assumption.

`BatchingStrategy` adds a collision certificate to a rule. Full round-by-round
knowledge soundness requires a finite sampleable challenge ring with no zero divisors,
`pc.Functional`, and injectivity of `algebraMap P C`. Functionality fixes the compatible packed
polynomial before each challenge. The explicit finite sum in `RingSwitch.rbrError_sum` is

`bat.error + m * (2 / card C)`.

The head has one batching challenge, the loop `m` scalar challenges, and the terminal none.
`perfectCompleteness_and_rbrKnowledgeSoundness` bundles completeness, security and this
exact sum. It makes no ordinary knowledge-soundness claim.

For the head alone, equal component evaluations at the fixed query suffice: the compatible
polynomials need not be equal or form a finite set. `Head.pr_exists_derivedTarget_le_of_partials_eq`
preserves this point-local collision law, and `bad_event_le_of_partials_eq` adds the guard.
The standalone `Head.rbrKnowledgeSoundnessWith_of_partials_eq` uses the same weaker
premise for every fixed query and oracle statement, with the extractor and knowledge states.
`TensorPrefix.pr_exists_target_collision_le_of_embedded_eval_eq` states the carrier collision law.

The head also permits a fixed list covering **all** compatible packed candidates before
the challenge, charging only incorrect candidates. This head bound does not imply bounded-list
tail security, adaptive-list extraction or preservation of inherited residual constraints.
`Batching/CoordinateSample` also certifies nontrivial head separation over rings with zero divisors.

`RingSwitch.append_rbrKnowledgeSoundness` closes any opening already typed at the
contextual same-commitment endpoint. `append_perfectCompleteness` supplies the separate
completeness composition. An opening complete only on exact encodings uses exact compatibility
for the completeness relation; relaxed-radius compatibility remains the security relation.

## Concrete consumers and migration

`Packing/TensorPrefix` defines the tensor-prefix/equality-fold specialization through the shared
program. It preserves the original tensor carrier `P.A`, decoded by `P.columnEquiv`, and proves
the original scalar check and row-target equation, honest transmitted message, packed
source, extraction and terminal equality multiplier. This is the DP24 specialization; there is
no second certified phase implementation.

`Binius/FRIBinius/RingSwitch` appends the Binary Basefold contextual opening. Its existing
zero-round frontier projects the final evaluation and formats the witness, with no extra wire
phase. Exact first-codeword encodings give completeness; unique-radius compatibility gives
round-by-round security. `fullError_sum_le` transports the full challenge sum
to the frontend loss plus the backend's closed-form upper bound. The concrete nonconstant
`GF(16)/GF(2)` acceptance fixture instantiates both and bounds that sum strictly below one.

`OpeningAdapter` converts a standard `MLIOPCS` to a contextual opening by a zero-round
projection, with completeness and round-by-round security transport from its
`rbrKnowledgeSoundness` field. Conversion to ordinary knowledge soundness remains admitted.

The full `RingSwitch/{UnequalRankSuffix,Quirky}` fixtures use packing rank four over `GF(16)`, opening rank three
over `GF(8)`, and challenge algebra `GF(16)`. They exercise nonconstant sources, effective packed
coordinates, honest and rejected executions, query retention and exact error sum `1/4`.
Their clear polynomial oracle is a specification fixture, not a PCS. A separate zero-variable
fixture exercises commutative-ring completeness over `ZMod 4`.

Obligations for the reference Flock in the interaction layer are maintained in the
[consumer guide](../../wiki/ring-switching-consumers.md#flock-in-the-interaction-layer-and-acceptance).

For implementation steps and a worked example, see
[Adding a ring-switching consumer](../../wiki/ring-switching-consumers.md).

## Other constructions

- **Hachi §3.1 trace head** ([`../papers/NOZ26.md`](../papers/NOZ26.md),
  `Commitments/Functional/Hachi/TraceHead/`): `L = R_q`,
  `A = R_q`, `φ₀ = id`, `φ₁ = σ₋₁`, `β = ψ` (Theorem 2). The carrier is `L` itself, so for
  `κ > 0` this is **not** a `RingSwitchingProfile` instance; it uses the coordinate layer
  directly (`PackingData.ofBaseOpening`, `packedMLE`, its own `ClaimLayout`, and
  `CheckedObservation`). The evaluation point is engineered to be
  subfield-valued, so the reduction is **deterministic**
  (one message + one trace check, no challenges, no sum-check). `R_q` is not a domain, so the
  Schwartz–Zippel soundness theorem does not apply — Hachi soundness is a separate (CWSS)
  argument. The formalized head computes over CompPoly's `CMlPolynomial`; its read-back
  `unpackCoefficients_eval` is proved directly, and its `observation` is a `CheckedObservation`
  written by hand. The packing is also stated in the `MvPolynomial`-based coordinate layer,
  through `CMlPolynomial.equivMvPolynomialDeg1` (`TraceHead/Coefficients.lean`):
  - the packing data is `PackingData.ofBaseOpening` of `ψ`: the fixed subring is the opening
    algebra, with one opening coordinate (`ιE = Unit`), and the shared transpose is `ψ` itself;
  - `traceHeadLayout` instantiates the `ClaimLayout` contract, splitting the
    **monomial coefficients** of the packed variables (not the Boolean-restriction
    `packedSuffixLayout`); its `reconstruct` is Hachi's own proof (`evalSplit_eq_eval` and the
    evaluation bridge);
  - the packed polynomial is the shared `packedMLE` of the layout's components
    (`toMvPolynomialDeg1_packCoefficients`).

  The conformance theorem `trace_head_conforms`
  (`ArkLib/Commitments/Functional/Hachi/TraceHead/Conformance.lean`) states the accepting condition
  through that layer: a passing check whose forwarded claim opens validly is exactly a valid weak
  opening for which the sent value is the single shared slice (`sliceRel`) of the `packedMLE` of
  the decoded committed polynomial's components, and the claimed scalar is the layout-weighted sum
  of its `ψ`-coordinates. This layout has one opening coordinate and introduces no batching
  challenge or sumcheck. Concrete acceptance and rejection fixtures remain in
  `ArkLibTest/ProofSystem/RingSwitching/Conformance/Hachi.lean`.
- **HMZ25 `Lift` construction** ([`../papers/HMZ25.md`](../papers/HMZ25.md)): the
  *opposite* direction, `S ≅ R[X]/(φ)` → a field `F` — lift `M z = y` to `R[X]` and evaluate
  at a random `α`. **Formalized generically** in `ProofSystem/RingSwitching/Lift/`
  over any monic-modulus presentation (`Presentation`/`IsPresentation` — not
  cyclotomic-specific), with CWSS at `k = 2·deg φ` proven once from the presentation laws,
  on top of the committed-scalar shell
  (`OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean`).
  Hachi's link 4 (`Commitments/Functional/Hachi/RingSwitch/Reduction.lean`) is the proven
  cyclotomic instance (`cyclotomicPresentation`). It does **not** instantiate
  `RingSwitchingProfile`; what it shares with DP24 is the `pSpecScalar` wire shape and the
  top-level layer of `ProofSystem/RingSwitching/` (round-shape verifiers, embed-and-evaluate
  transport).

## Core References

- [`../papers/DP24.md`](../papers/DP24.md) — origin of ring switching for binary towers.
- [`../papers/NOZ26.md`](../papers/NOZ26.md) — Hachi; the extension-field→cyclotomic-ring reduction.
- [`../papers/RSG.md`](../papers/RSG.md) — ring switching with independent packing and opening bases.
- [`../papers/BRW26.md`](../papers/BRW26.md) — Flock; scalar-claim heads and the quirky layout.

## Main ArkLib Touchpoints

- Pure coordinates and interpolation: `ProofSystem/RingSwitching/Packing/Coordinates.lean`,
  `Relations.lean`, `Multiplier.lean`, `ClaimLayout.lean`, `ClaimLayout/Quirky.lean`.
- Operational and certified batching: `Packing/Batching.lean`, `DerivedBatching.lean`.
- Shared protocol: `Packing/Head.lean`, `ProductSumcheck/`, `RingSwitch.lean`.
- Tensor-prefix and Binius consumer: `Packing/TensorPrefix.lean`,
  `Binius/FRIBinius/RingSwitch.lean`, `Binius/BinaryBasefold/Opening.lean`.
- Deterministic trace: `Commitments/Functional/Hachi/TraceHead/`.
- Quotient lifting: `ProofSystem/RingSwitching/Lift/`.

Implementation progress and landing dependencies belong in tracker #1286 and the public design
roadmap, rather than duplicated status inventories on this concept page.
