# LogUp statements and implementation correspondence

LogUp uses sums of weighted reciprocals to test finite collections of messages. The common
algebraic statement is that every key has net weight zero in a field. Table inclusion and integer
multiset equality are applications with additional hypotheses preventing count wraparound.
The [executable formalization design](../../design/logup.md) specifies ArkLib's planned native
grouped-sumcheck argument and its completion criteria.

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

Current Plonky3, OpenVM, SP1, and Stwo snapshots expose fractional-GKR machinery. This does not
make their complete proof systems identical. In particular, the Plonky3 fractional verifier returns
opening claims for the original numerator and denominator tables, and Stwo names its entry point
`partially_verify_batch`. Their callers owe authentication of the returned claims. A complete
ArkLib verifier must perform its final oracle check or return a reduction whose output relation
states exactly what remains to be checked.

Plonky3's [LogUp* implementation](https://github.com/Plonky3/Plonky3/blob/9734387626cf5a859885de6a6b30dc49532ed96c/multi-stark/src/logup_star/mod.rs)
has an indexed-read statement and challenge-dependent pushforward weights. Its ability to operate
in small characteristic is not a property of ordinary integer-multiplicity LogUp.

## Characteristic and witness contracts

For a lookup, requests have weight one and a table contributes prover-supplied negative weights.
A missing key cannot balance when its positive query count remains nonzero in the field.
An integer count equal to the characteristic does vanish, regardless of the degree or size of an
extension field used for challenges.

Lookup specializations therefore need a count bound, a declared table collection, and a proof
that enabled requests really have the intended integer weights. Permutation specializations need
count-cast injectivity on both sides. General field balance needs neither integer interpretation.
The Plonky3 `Count` wrapper and OpenVM `count_weight` record static budgets; their stated magnitude
and selector obligations still need caller constraints. A budget label alone does not prove them.

For an executable lookup prover, the natural constructive witness is an actual table index for
each query. Histogramming these indices supplies a valid multiplicity assignment even with
duplicates. This avoids runtime classical choice and normalization by duplicate counts.
It changes the paper's normalized honest assignment while preserving the per-key balance
equations under the paper's nonzero-count assumptions. Histogram correctness itself does not
need those assumptions. Equivalence of the equations is the appropriate correspondence statement.

## Compression contracts

Plonky3's per-bus prefix is `alpha + (bus+1)*beta^W`; its payload combiner uses descending powers
within the tuple. One declared payload width per bus is essential: a short tuple and a longer
zero-padded tuple can encode the same polynomial. The multi-STARK lookup plan checks agreement
across declarations sharing a bus. Bus tags must also be distinct in the base field.

Stwo's shown combiner uses ascending payload powers and subtracts a sampled offset. SP1's inspected
verifier samples a multilinear combiner seed. Establish explicit translations for each family;
do not substitute a probability theorem for one family into another.

Formal polynomial encoding can be injective even though its evaluation at a sampled scalar has
collisions. Bus separation participates in this same probabilistic event. To preserve one
nonzero net weight, it suffices to isolate a fixed nonzero key from the other distinct keys before
the challenge. Full pairwise collision avoidance is stronger than the soundness proof needs.

## Bounds that need an independent derivation

The paper's revised soundness sketch states a `K/|F|` contribution for the equality-kernel step.
A nonzero multilinear polynomial in `n` variables has total degree at most `n`; a generic root
bound is `n/|F|`. Multilinearity alone does not give `1/|F|`: over `F_5`, `X_1*X_2` vanishes at
`9/25` of the points. The formalization must derive the kernel bound it actually uses, and must
not claim the printed numerical constants without an additional argument. Selecting one nonzero
residual before the kernel challenge avoids a union bound over all groups.

The proposed ArkLib grouped proof also differs from the old pole-plus-root analysis. If every
group residual is zero and the helper total is zero, the global cleared numerator vanishes by
polynomial regrouping, including at zero denominators. This suggests charging only its roots for
outer soundness. The proof is an explicit early obligation in the design. Completeness still
accounts for the honest helper construction encountering poles.

Plonky3's [security accounting](https://github.com/Plonky3/Plonky3/blob/9734387626cf5a859885de6a6b30dc49532ed96c/security/src/logup.rs)
includes its own fingerprint and pole budgets. Those are bounds for its stated construction and
accounting model; they are not substitutes for a proof about the native grouped protocol.
Fiat–Shamir and grinding terms in implementation security reports are outside the initial
interactive proof's theorem.

## ArkLib ownership

Reusable algebra belongs under `Data/`; the oracle protocol belongs under `ProofSystem/`.
Reuse [computable native Sumcheck](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean),
its [soundness theorem](../../../ArkLib/ProofSystem/Sumcheck/Interaction/ComputableSoundness.lean),
CompPoly evaluation tables, and existing native source-routing and composition laws.
The [toy IOP code-generation gates](../../../ArkLib/ProofSystem/ToyProblem/Codegen.lean) and
[FRI execution theorems](../../../ArkLib/ProofSystem/Fri/Spec/Execution.lean) illustrate executable
roots and reasoning about actual oracle accesses. LogUp additionally needs a complete native
terminal check and table-based round generation without polynomial expansion.
