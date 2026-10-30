# Adding a ring-switching consumer

Use the shared packing kernel to define the consumer's coordinates, then instantiate the
checked protocol. This guide owns that workflow; the
[ring-switching tracker](https://github.com/Verified-zkEVM/ArkLib/issues/1286) owns reviewed
revisions, validation and landing status. The [concept page](../kb/concepts/ring-switching.md)
owns the mathematical overview. The [Flock section](#flock-in-the-interaction-layer-and-acceptance) records
the remaining stage, residual-relation and extraction obligations.

## Choose the algebra and wire

`PackingData B` supplies independent packing and opening algebras `P` and `E`, with finite bases
indexed by `ιP` and `ιE`. Their ranks may differ. A `ClaimLayout data m` describes the source,
original query, component polynomials, retained point and scalar reconstruction. Prove the
identities for the variable order and bases; equal dimensions do not identify a layout.
Choose a commutative challenge algebra `C` with `Algebra B C`, `Algebra P C` and
`IsScalarTower B P C` for the protocol. Injectivity of `P → C` is an extra security premise.

| Owner | Consumer data or obligation |
| --- | --- |
| `PackingData`, `Coordinates`, `Relations` | Coordinate transpose, packed polynomial and same-source evaluation relations. |
| `ClaimLayout`; `ClaimLayout/Quirky` | Reconstruction for the selected variables and query. |
| `BatchingRule C ιE` | Operational challenge type, sampler and weights. |
| `BatchingStrategy C ιE` | A rule together with its collision error and separation proof. |
| `PackedCommitment P m` | Oracle interfaces and the compatibility predicate `commitsTo`. |
| `PackedCommitment.Honest` | A separate constructor covering every packed polynomial. |
| `Head` | Encoded component message, reconstruction guard, batching challenge and derived target. |
| `ProductSumcheck` | Scalar rounds for the multiplier times the same packed polynomial, then its terminal check. |
| `RingSwitch` | The head-plus-product-sumcheck protocol and contextual opening endpoint. |
| `TensorPrefix` | The DP24 instance, preserving its tensor carrier through the column equivalence. |

Choose a message carrier `M` and prove `M ≃ (ιP → E)`. The honest head sends those
component evaluations once. The verifier checks their weighted reconstruction, then samples the
batching challenge and computes the transpose and target itself. There is no second slice
message. `Head` hands the same packed polynomial and oracle family directly to
`ProductSumcheck`; its terminal verifier executes the certified multiplier evaluator.

DP24 uses `TensorPrefix`; new consumers instantiate the current shared phases directly.

## Separate execution, honest coverage and security

The program uses the oracle interfaces and an operational batching rule. The compatibility
relation specifies the statements certified about that program. `pc.Honest` proves honest inputs
exist; it is separate from the program and its security premises. A functional relation may still
be empty. State honest coverage for the original
commitment scheme rather than restricting `commitsTo` to make a proof easier.

`RingSwitch.perfectCompleteness` works over the stated commutative-ring/algebra structures.
A collision certificate is unnecessary for that theorem. Its security theorem
`RingSwitch.rbrKnowledgeSoundness` additionally uses a certified strategy,
`pc.Functional`, injective coefficient transport `P → C`, and a finite sampled challenge ring
`C` with no zero divisors. There is no separate `IsDomain P` premise, although injectivity into
`C` already implies that `P` has no zero divisors. No such condition is required of `E`. The challenge-index error sum is exactly

```text
bat.error + m * (2 / card C).
```

The terminal message contributes no challenge error. The theorem includes `m = 0`; neither a
zero multiplier nor an empty sum-check loop justifies cancelling a factor.

The standalone head admits the weaker premise that compatible polynomials have equal component
evaluations at each fixed query and oracle statement. Its separate fixed-list theorem bounds
the event that some incorrect member of a prechallenge fixed list passes batching by
`L * bat.error` for a list of size at most `L`. The candidate may be selected after the draw
within that fixed list. Cover every compatible packed polynomial; correct candidates are excluded.
These head results do not establish list-valued security for the full continuation: product
sumcheck still uses functionality, and an inherited residual predicate may restrict a list
without proving the required coverage.

## Worked unequal-rank instance

Start from the maintained [unequal-rank suffix fixture][rsg], not a fresh protocol implementation:

1. Set `B = F₂`, `P = F₁₆`, `E = F₈`, `C = F₁₆`. Its packing and opening ranks are four and
   three. `ClaimLayout.packedSuffixLayout` packs two suffix bits and retains one leading variable.
2. Use the nonconstant source `X₀ + X₁X₂`, an identity component-message codec, and
   `BatchingStrategy.gammaPowers F16 3`. Changing the retained coordinate changes evaluation;
   packing is not an identity map.
3. Instantiate `RingSwitch.reduction data 1 layout codec bat.toBatchingRule pc`.
   `honest_input` exhibits the original relation. `full_accepts` checks the full run,
   preserving the original query, batching challenge and commitment. Changing the scalar claim
   rejects for every continuation transcript. The error sum is `1/4 < 1`.

This fixture exposes the entire packed polynomial through its oracle. It demonstrates the
protocol and contracts; it is not a succinct commitment scheme. The [quirky fixture][quirky]
uses the same nontrivial ranks with a different layout. [Coordinate sampling][coordinate] and
[zero variables][zero] exercise different samplers and the empty-loop boundary. The
[two-round fixture][two-rounds] checks successive challenges, full acceptance, rejection of a
corrupted second polynomial and the exact error `3/8`.

## Close the contextual opening

The final relation is `pc.evalRelWithContext (layout.Query × rule.Challenge)`: the original query
and batching challenge accompany an evaluation claim against the same committed polynomial.
Retaining those values does not prove an additional invariant about them. A consumer must
transport its own inherited relation on that context and witness.

`RingSwitch.append_perfectCompleteness` and `append_rbrKnowledgeSoundness` consume an
opening whose input already matches this contextual relation. `OpeningAdapter` converts a general
`MLIOPCS` to this relation through a zero-round context projection and witness wrapper, transporting
completeness and round-by-round knowledge soundness from its `rbrKnowledgeSoundness` field.
Completeness must hold for every
fixed initial state; RBR must cover all inputs in the stated contextual evaluation
relation, not only a selected honest encoding or context. Match the commitment, oracle
interfaces, prover, verifier, witness and extraction transport. Keep strict honest encoding for
completeness distinct from relaxed compatibility used by security.

The [Binius ring switch][binius] instantiates `TensorPrefix` and appends the Binary Basefold
contextual opening. Its bundled
`fullReduction_perfectCompleteness_and_rbrKnowledgeSoundness` theorem includes
completeness, round-by-round knowledge soundness and the total-error bound.
The maintained [composite fixture][composite] uses a nonconstant `GF(16)/GF(2)` source and its
honest codeword encoding. It checks sampled acceptance and a full challenge-error
sum bounded below one. A direct-polynomial opening example alone would not certify this backend.
The same file also exports ordinary knowledge soundness, derived from the round-by-round result
through the proved guarded bridge `Verifier.GuardedForm.knowledgeSoundness_of_rbrKnowledgeSoundness`
in `ArkLib/OracleReduction/Security/GuardedBridges.lean`.
`Binius.FRIBinius.RingSwitch.fullReduction_perfectCompleteness_and_knowledgeSoundness` pairs
perfect completeness on exact encodings (the strict view of the input interface) with
`Binius.FRIBinius.RingSwitch.fullVerifier_knowledgeSoundness` on the relaxed compatibility
relation. The knowledge error is `κ/|L| + ℓ' * (2/|L|)` plus the concrete Binary Basefold knowledge error
`BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ' R γ`.
For the generic packing ring switch,
`RingSwitching.Packing.RingSwitch.perfectCompleteness_and_knowledgeSoundness` gives ordinary
knowledge error `bat.error + m * (2/|C|)` through
`OracleVerifier.knowledgeSoundness_of_rbrKnowledgeSoundness_of_guarded`.

Hachi §3.1 remains a deterministic trace-head consumer of the coordinate and relation layers,
with its [own conformance theorem][hachi]. Its CWSS and weak-opening contract are separate from
this randomized product-sumcheck route.

## Flock in the interaction layer and acceptance

The [ring-switching tracker](https://github.com/Verified-zkEVM/ArkLib/issues/1286) records delivery
status. The early residual-conformance milestone is separate from full Flock security.

### Early residual conformance

- Prove the source-pinned correspondence between Flock's interaction-layer polynomial, variable
  order and bases and the shared layout, and reconstruction through its interaction-layer head.
- Prove honest completeness on the derived wire, with honest commitment coverage and explicit
  preservation of the inherited residual relation `R(ctx, p)`.
- Apply shared fixed-list separation to that residual relation under an explicit prechallenge
  covering-list hypothesis: the fixed list covers every compatible packed polynomial satisfying
  the inherited relation. End at the same-source packed-opening relation `pc.evalRel`.

This milestone is conditional on the stated inherited-relation and covering-list premises. For
Flock it establishes neither full round-by-round security nor ordinary knowledge soundness;
the ordinary knowledge-soundness exports above concern the Binius and packing ring switches.
The quirky fixture proves shared-layout properties; it does not establish Flock conformance.

### Later Flock security and PCS integration

Prove that the interaction-layer zerocheck and lincheck stages produce the required residual relation,
then establish adaptive list transport and joint-list security through subsequent stages.
Joint extraction and a compatible opening protocol with its security theorem are further
obligations. These proofs discharge the early result's premises and connect it to full Flock
security and PCS integration. The staged Frobenius construction has its own maps, challenge
schedule and endpoint.

For each consumer, put universally quantified conformance in an importable library module and
keep concrete controls in `ArkLibTest`. Check a nonconstant honest witness, acceptance,
a false reconstruction or terminal claim, coordinate order, and context/commitment preservation.
Pin the exact challenge-index ledger and transitive axioms of exported endpoints. Obtain
independent adversarial review and validate the final source with its dependencies.
The owning trackers record progress; this guide does not duplicate PR status or review logs.

[rsg]: ../../ArkLibTest/ProofSystem/RingSwitching/Packing/RingSwitch/UnequalRankSuffix.lean
[quirky]: ../../ArkLibTest/ProofSystem/RingSwitching/Packing/RingSwitch/Quirky.lean
[coordinate]: ../../ArkLibTest/ProofSystem/RingSwitching/Packing/RingSwitch/CoordinateSample.lean
[zero]: ../../ArkLibTest/ProofSystem/RingSwitching/Packing/RingSwitch/ZeroVariables.lean
[binius]: ../../ArkLib/ProofSystem/Binius/FRIBinius/RingSwitch.lean
[composite]: ../../ArkLibTest/ProofSystem/RingSwitching/Conformance/BiniusComposition.lean
[hachi]: ../../ArkLib/Commitments/Functional/Hachi/TraceHead/Conformance.lean

[two-rounds]: ../../ArkLibTest/ProofSystem/RingSwitching/Packing/RingSwitch/TwoRounds.lean
