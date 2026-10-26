# LogUp statements and implementation correspondence

LogUp uses sums of weighted reciprocals to test finite collections of messages. The common
algebraic statement is that every key has net weight zero in a field. Table inclusion and integer
multiset equality are applications with additional hypotheses preventing count wraparound.
The [executable formalization](../../design/logup.md) implements native grouped-Sumcheck
weighted balance, scalar indexed lookup and typed tuple/bus indexed lookup, with actual terminal
authentication, whole-prover soundness and executable honest defaults.

## Reference versions

The protocol reference is Ulrich Haböck, *Multivariate lookups based on logarithmic derivatives*,
[ePrint 2022/1530](https://eprint.iacr.org/2022/1530), citation key [Hab22](../papers/Hab22.md).
Statement numbers refer to the author-uploaded document dated March 31, 2023. Its Protocol 2
exposes a partial-sum size controlling helper count and algebraic degree. The ePrint landing page
reports a later archive update on February 20, 2025; byte identity with the inspected author copy
has not been established. [Source metadata](../sources/Hab22/metadata.yml) records the inspected
copy and the unavailable raw-PDF digest. A live ePrint URL alone does not fix the revision.

Implementation references below are pinned source snapshots. Their equations and interfaces are
comparison targets; their comments are not formal security premises.

| Implementation | Revision | Primary source and use |
| --- | --- | --- |
| Plonky3 | `9734387626cf5a859885de6a6b30dc49532ed96c` | [LogUp gadget](https://github.com/Plonky3/Plonky3/blob/9734387626cf5a859885de6a6b30dc49532ed96c/lookup/src/logup.rs): grouped fraction arithmetic and accumulator constraints |
| Plonky3 | same | [Challenge encoding](https://github.com/Plonky3/Plonky3/blob/9734387626cf5a859885de6a6b30dc49532ed96c/lookup/src/challenges.rs), [count bounds](https://github.com/Plonky3/Plonky3/blob/9734387626cf5a859885de6a6b30dc49532ed96c/lookup/src/count.rs), and [lookup planning](https://github.com/Plonky3/Plonky3/blob/9734387626cf5a859885de6a6b30dc49532ed96c/multi-stark/src/lookup/mod.rs): schema, challenge order, and overflow obligations |
| Plonky3 | same | [Fractional GKR verifier](https://github.com/Plonky3/Plonky3/blob/9734387626cf5a859885de6a6b30dc49532ed96c/multi-stark/src/fractional_gkr/verifier.rs): proof shape, root denominator check, and output opening claims |
| OpenVM stark-backend | `362c7ad8c6b042b320471a137e3eadec7ec69a44` | [Interaction contract](https://github.com/openvm-org/stark-backend/blob/362c7ad8c6b042b320471a137e3eadec7ec69a44/docs/interactions.md) and [interaction types](https://github.com/openvm-org/stark-backend/blob/362c7ad8c6b042b320471a137e3eadec7ec69a44/crates/stark-backend/src/interaction/mod.rs): field balance, lookup and permutation specializations, selectors and height budgets |
| OpenVM stark-backend | same | [Fractional sumcheck prover](https://github.com/openvm-org/stark-backend/blob/362c7ad8c6b042b320471a137e3eadec7ec69a44/crates/stark-backend/src/prover/logup_zerocheck/fractional_sumcheck_gkr.rs) and [verifier](https://github.com/openvm-org/stark-backend/blob/362c7ad8c6b042b320471a137e3eadec7ec69a44/crates/stark-backend/src/verifier/fractional_sumcheck_gkr.rs): fraction tree and cubic Sumcheck checks |
| SP1 | `d83ed91f96701209613720708f36ffce0e98ed33` | [LogUp GKR verifier](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/hypercube/src/logup_gkr/verifier.rs), [round polynomial](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/hypercube/src/logup_gkr/logup_poly.rs), and [typed interactions](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/hypercube/src/lookup/interaction.rs): private computation on folded tables, dimensions, padding, and claim checks |
| Stwo | `826591c6c371376810ca8213b5812d5daf6d5092` | [Constraint LogUp](https://github.com/starkware-libs/stwo/blob/826591c6c371376810ca8213b5812d5daf6d5092/crates/constraint-framework/src/logup.rs) and [trace generator](https://github.com/starkware-libs/stwo/blob/826591c6c371376810ca8213b5812d5daf6d5092/crates/constraint-framework/src/prover/logup.rs): tuple compression, cumulative sums, batch inversion |
| Stwo | same | [GKR verifier](https://github.com/starkware-libs/stwo/blob/826591c6c371376810ca8213b5812d5daf6d5092/crates/stwo/src/prover/lookups/gkr_verifier.rs): fraction-addition gate and explicit partial-verification boundary |

OpenVM's [On the Soundness of Interactions via LogUp](https://github.com/openvm-org/stark-backend/blob/362c7ad8c6b042b320471a137e3eadec7ec69a44/docs/Soundness_of_Interactions_via_LogUp.pdf),
dated March 13, 2025, is a further mathematical reference for isolating one message during tuple
compression and distinguishing field balance from integer statements. Its rational-function
claims must be interpreted with an explicit domain for evaluation at poles. A Lean theorem about
total field division cannot silently import the convention that a rational evaluation is undefined.

## Different protocols share a fraction operation

The shared operation is the division-free addition of unnormalized pairs,
`(a,b),(c,d) -> (a*d+c*b,b*d)`. Agreement with addition of evaluated fractions requires nonzero
denominators; the pair operation itself does not. Neutral padding is `(0,1)`.

The revised Haböck construction supplies a helper for each group of terms, constrains its
denominator-cleared row identity, batches those identities using an equality kernel, and runs one
Sumcheck followed by oracle evaluation. Plonky3's `lookup` crate also provides a construction with
fraction columns and a shared accumulator. Fractional GKR instead builds a binary tree of the pair
operation and reduces layer claims with Sumcheck. These are separate protocol constructions.

The pinned Plonky3, OpenVM, SP1 and Stwo snapshots expose fractional-GKR machinery. This does not
make their complete proof systems identical. In particular, the Plonky3 fractional verifier returns
opening claims for the original numerator and denominator tables, and Stwo names its entry point
`partially_verify_batch`. Their callers owe authentication of the returned claims. A complete
ArkLib endpoint performs the final oracle check; its underlying native reduction separately
exports the evaluation claim for composition. These are distinct acceptance contracts.

Plonky3's [LogUp* implementation](https://github.com/Plonky3/Plonky3/blob/9734387626cf5a859885de6a6b30dc49532ed96c/multi-stark/src/logup_star/mod.rs)
has an indexed-read statement and challenge-dependent pushforward weights. Its ability to operate
in small characteristic is not a property of ordinary integer-multiplicity LogUp.

## Characteristic and witness contracts

For a lookup, requests have weight one and a table contributes prover-supplied negative weights.
A missing key cannot balance when its positive query count remains nonzero in the field.
An integer count equal to the characteristic does vanish, regardless of the degree or size of an
extension field used for challenges.

ArkLib scalar and tuple lookup configurations therefore carry an explicit characteristic
certificate and query budget `M*2^n<p`. The declared collection has `P` physical table pieces; no
`P*2^n<p` budget is required for the missing-key converse. Enabled-request and signed-count
interpretations remain caller obligations. Bounded cast-count equality recovers `Vector.Perm`
algebraically; the inclusion endpoint plus equal lengths does not prove a permutation. General
weighted balance has no integer interpretation or characteristic lower bound.
The Plonky3 `Count` wrapper and OpenVM `count_weight` record static budgets; their stated magnitude
and selector obligations still need caller constraints. A budget label alone does not prove them.

For an executable lookup prover, the natural constructive witness is an actual table index for
each query. Histogramming these indices supplies a valid multiplicity assignment even with
duplicates. This avoids runtime classical choice and normalization by duplicate counts.
It changes the paper's normalized honest assignment while preserving the per-key balance
equations under the paper's nonzero-count assumptions. Histogram correctness itself does not
need those assumptions. Equivalence of the equations is the appropriate correspondence statement.

## Compression contracts

The canonical encoding in
[`TaggedTuple.lean`](../../../ArkLib/Data/Polynomial/TaggedTuple.lean) is
`tag*beta^W + sum_j payload_j*beta^j`, with one global maximum width `W` and a declared width
for each bus. The checked schema makes tags injective in the base field; its dependent key fixes
payload length. A short raw tuple and a longer zero-padded tuple can otherwise encode the same
polynomial. The multi-STARK lookup plan checks agreement across declarations sharing a bus.

Plonky3's denominator is `alpha + (bus+1)*beta^W - descendingPayload`. Expressing it as
`alpha - canonicalFingerprint` requires both a reversed payload and canonical tag `-(bus+1)`.
Stwo's shown ascending payload-minus-offset combiner has the opposite denominator sign; its
single-bus translation uses tag zero. OpenVM places the tag at the message's own width `w`:
conversion to the global-width encoding adds `tag*(beta^W-beta^w)`. When `w<W`, these are different
fingerprint families. Zero tags can give cross-width aliases in the own-width family.
SP1's inspected verifier uses supplied multilinear combiner coefficients; its family has a
separate contract from this univariate fingerprint. The acceptance checks pin source revisions
and test these equations; they do not establish Rust implementation equivalence.

Formal polynomial encoding can be injective even though its evaluation at a sampled scalar has
collisions. To preserve one nonzero net weight, it suffices to isolate a fixed key carrying that
weight from the other occurring distinct keys. The selected-key bound in
[`TaggedTupleProbability.lean`](../../../ArkLib/Data/Polynomial/TaggedTupleProbability.lean)
is `(s-1)*W/|E|`. Semantic keys, schema and weights must all be fixed before `beta`; choosing
weights afterward can violate that bound. Balanced fibers remain balanced for every encoding,
including collisions, by finite regrouping.

For row-varying buses, [Tuple/Source.lean](../../../ArkLib/ProofSystem/Logup/Lookup/Tuple/Source.lean)
opens the stored padded coefficient-column multilinear extensions and combines their answers.
An interpolated tag at a field point need not be a registered bus tag, so the source never decodes
a semantic key there. Its realization holds for every retained BASE multiplicity message;
[Tuple/Security.lean](../../../ArkLib/ProofSystem/Logup/Lookup/Tuple/Security.lean) composes this
actual source with the complete native argument.

## Independently derived bounds

The paper's revised soundness sketch states a `K/|F|` contribution for the equality-kernel step.
A nonzero multilinear polynomial in `n` variables has total degree at most `n`; a generic root
bound is `n/|F|`. Multilinearity alone does not give `1/|F|`: over `F_5`, `X_1*X_2` vanishes at
`9/25` of the points. ArkLib proves `n/|E|` for one nonzero
residual selected before the kernel challenge, avoiding a union bound over all groups. It does
not import the printed numerical constants.

ArkLib's grouped proof uses a division-free global clearing implication: if every group residual
is zero and the helper total is zero, the cleared numerator vanishes, including at zero
denominators. [Grouped.lean](../../../ArkLib/ProofSystem/Logup/Algebra/Grouped.lean) proves this
identity; [weighted soundness](../../../ArkLib/ProofSystem/Logup/Security/Weighted.lean) charges
only its roots for outer soundness. The complete weighted bound is
`(T*2^n+n*(ell+3))/|E|`. The tuple argument adds `(s-1)*W/|E|` for one fixed semantic key
among `s` occurring keys, with arbitrary BASE multiplicities fixed before beta. Completeness
separately accounts for honest helpers encountering poles; tuple completeness holds for every
beta and adds no compression-error term.

Plonky3's [security accounting](https://github.com/Plonky3/Plonky3/blob/9734387626cf5a859885de6a6b30dc49532ed96c/security/src/logup.rs)
includes its own fingerprint and pole budgets. Those are bounds for its stated construction and
accounting model; they are not substitutes for a proof about the native grouped protocol.
Fiat–Shamir and grinding terms in implementation security reports are outside the initial
interactive proof's theorem.

## Delivered ArkLib interfaces

| Contract | Owner |
| --- | --- |
| Weighted scalar circuit, individual degree `ell+2`, Boolean sum and pole-safe clearing | [Grouped.lean](../../../ArkLib/ProofSystem/Logup/Algebra/Grouped.lean) |
| Arbitrary-helper realization from retained values, weights and helpers | [Interaction/Source.lean](../../../ArkLib/ProofSystem/Logup/Interaction/Source.lean) |
| Actual prefix/native/terminal execution and arbitrary whole-prover weighted soundness | [Interaction/Execution.lean](../../../ArkLib/ProofSystem/Logup/Interaction/Execution.lean), [Security/Weighted.lean](../../../ArkLib/ProofSystem/Logup/Security/Weighted.lean) |
| Scalar membership, retained BASE histogram, whole-prover security and honest completeness | [Lookup/](../../../ArkLib/ProofSystem/Logup/Lookup/) |
| Checked typed provider, beta compression, original-key security and all-beta honest completeness | [Lookup/Tuple/](../../../ArkLib/ProofSystem/Logup/Lookup/Tuple/) |
| Direct formal coefficient messages and selected measured honest control | [Prover/RoundCoefficients.lean](../../../ArkLib/ProofSystem/Logup/Prover/RoundCoefficients.lean), [ArithmeticControl.lean](../../../ArkLib/ProofSystem/Logup/Prover/ArithmeticControl.lean) |
| Actual weighted/scalar/tuple defaults | [ArithmeticStrategy.lean](../../../ArkLib/ProofSystem/Logup/Prover/ArithmeticStrategy.lean), [scalar ArithmeticProver.lean](../../../ArkLib/ProofSystem/Logup/Lookup/ArithmeticProver.lean), [tuple ArithmeticProver.lean](../../../ArkLib/ProofSystem/Logup/Lookup/Tuple/ArithmeticProver.lean) |

The defaults construct honest helpers termwise with total inversion, including at poles. They
cache denominator, weight, helper and equality tables, stream adjacent affine-row coefficients,
and fold only states needed by later rounds. Proofs establish **formal** polynomial/message
agreement; finite-field pointwise equality is insufficient. Zero rounds still authenticate the
original source, and public abort preserves the prover's actual private continuation effects.

[Computable native Sumcheck](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean)
and its [soundness](../../../ArkLib/ProofSystem/Sumcheck/Interaction/ComputableSoundness.lean)
supply the native core. Its source-routing, final-claim query and terminal-log bridge connect the
complete endpoint to the retained original view. The
[compiled runtime suite](../../../ArkLibTest/ProofSystem/Logup/Interaction/MeasuredRuntime.lean)
executes measured scalar/tuple defaults and actual KoalaBear-to-Ext6 sampler paths alongside the
weighted fixtures. The [design resource table](../../design/logup.md#separate-resource-metrics)
separates selected E instructions, BASE/Nat preprocessing, raw view fanout, dense source backend,
party sampling and logical storage.
[Actual packet laws](../../../ArkLib/ProofSystem/Logup/Interaction/Resources.lean) retain the
whole prefix and actual returned-claim Q query, including final rejection. The
[sampling consumers](../../../ArkLib/ProofSystem/Logup/Interaction/SamplingResources.lean) connect
actual Bool/log endpoints to supported phased paths. Arbitrary draw programs use their actual
supported lengths; selected uniform defaults have total primitive length `c*(1+n+K+s)`, or
`c*(2+n+K+s)` for tuples, using the proved honest private-party count zero. Malicious private
queries are not bounded. These are full supported-result claims, not losslessness or partial-run
counts, and transfer no arithmetic or memory profile. No metric alone is a total machine-time or
heap bound. Fractional GKR, LogUp*, PCS/FRI composition and Fiat–Shamir remain separate protocols.
