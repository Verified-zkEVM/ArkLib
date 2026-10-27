# LogUp navigation

Start with the variant you want to use. Each row links to its executable protocol, selected
honest prover, and complete endpoint theorems.

| Variant | Protocol and endpoint | Selected honest prover | Soundness | Completeness |
| --- | --- | --- | --- | --- |
| Weighted balance | [Interaction/Protocol](Interaction/Protocol.lean) | [Prover/Default](Prover/Default.lean) | [Security/Soundness](Security/Soundness.lean) | [Security/Completeness](Security/Completeness.lean) |
| Scalar lookup | [Lookup/Protocol](Lookup/Protocol.lean) | [Lookup/Prover](Lookup/Prover.lean) | [Lookup/Security](Lookup/Security.lean) | [Lookup/Completeness](Lookup/Completeness.lean) |
| Tuple/bus lookup | [Lookup/Tuple/Protocol](Lookup/Tuple/Protocol.lean) | [Lookup/Tuple/Prover](Lookup/Tuple/Prover.lean) | [Lookup/Tuple/Security](Lookup/Tuple/Security.lean) | [Lookup/Tuple/Completeness](Lookup/Tuple/Completeness.lean) |

Each protocol module exports `protocol`, `verifier`, `execute` and `uniformExecute`; each
soundness module exports `uniformExecute_soundness`. Their namespaces are `Logup.Interaction`
(weighted), `Logup.Lookup` (scalar) and `Logup.Lookup.Tuple` (tuple/bus). Selected provers are
`Logup.Prover.Honest.prover`, `Logup.Lookup.Honest.prover` and
`Logup.Lookup.Tuple.Honest.prover`, respectively.

For honest success bounds, use `Logup.Prover.Honest.uniformExecute_honestWith_success_ge`
(weighted), `Logup.Lookup.Honest.uniformExecute_proverWith_success_ge_rows` (scalar), or
`Logup.Lookup.Tuple.Honest.uniformExecute_proverWith_success_ge_rows` (tuple/bus).

The completeness theorems take an explicit message builder. Use the selected prover's
`prover_eq_honestWith` (weighted) or `prover_eq_proverWith` (scalar/tuple) together with
`Logup.Prover.Honest.pureBuilder_correct` to specialize them to the defaults.

The [design guide](../../../docs/design/logup.md) explains the protocol equations, assumptions,
bounds and resource metrics. The [reference comparison](../../../docs/kb/concepts/logup.md)
records the paper and implementation correspondence.

## Run a scalar lookup

The compiled [`ArithmeticLookupTests.Small.uniform` fixture](../../../ArkLibTest/ProofSystem/Logup/Lookup/Prover.lean)
shows the complete default call. Its [`LogupScalarHonestTest.Small` prerequisites](../../../ArkLibTest/ProofSystem/Logup/Lookup/Completeness.lean)
provide a `ZMod 17` field, `f`, checked `cfg`, table data, witness indices and the original source
view/handler. It uses one query column, two physical table pieces, two rows and `ell=1`.

1. Check the dimensions, characteristic budget and grouping with `Config.create?`. Here
   `n=1, M=1, P=2` gives two queries and the budget `2<17`.
2. Supply `Data` and actual table-position `indices`. The fixture queries `[5,7]` against pieces
   `[3,3]` and `[5,7]`, with flattened witness indices `[2,3]`; its `ValidIndices` proof certifies
   membership. The default computes the histogram from these indices before alpha.
3. Supply the original `valuesFamily` view and handler. The fixture uses `VirtualOracle.id` and
   `behaviorOfRealizations data`; `realizes` is the source-agreement premise used for completeness.
4. Construct `Honest.prover f cfg data indices unifSpec`, then pass it to
   `Logup.Lookup.uniformExecute f 1 1 2 1 cfg access view impl`. The result is `ProbComp Bool`,
   including the final original-source check. `Small.uniform_failure`, `uniform_success` and
   `uniform_total` specialize completeness to failure at most `3/17`, success at least `14/17`
   and total mass one.

For explicit alpha/joint/round draw programs, use `execute` instead of `uniformExecute`.
For a custom message builder, use the variant's `Prover/Reference.lean` entry point and discharge
its builder-correctness premise. Run the existing compiled examples with `lake exe logup-runtime`.

## Find a definition or proof

| Question | Start here |
| --- | --- |
| What does scalar lookup mean, and what is its witness? | [Lookup/Language.lean](Lookup/Language.lean): `InLanguage`, `ValidIndices`, `multiplicities` |
| Which characteristic and grouping parameters are accepted? | [Lookup/Config.lean](Lookup/Config.lean) and [Interaction/Config.lean](Interaction/Config.lean) |
| How are typed buses, keys and physical table pieces represented? | [Lookup/Tuple/Provider.lean](Lookup/Tuple/Provider.lean) and the reusable [TaggedTuple schema](../../Data/Polynomial/TaggedTuple.lean) |
| How are the original sources and multiplicities queried? | [Lookup/Source.lean](Lookup/Source.lean) and [Lookup/Tuple/Source.lean](Lookup/Tuple/Source.lean) |
| How is the final Sumcheck claim authenticated? | [Interaction/Source.lean](Interaction/Source.lean) and [Interaction/Protocol.lean](Interaction/Protocol.lean) |
| Where is challenge ordering connected to actual execution? | [Interaction/Execution.lean](Interaction/Execution.lean), [Lookup/Protocol.lean](Lookup/Protocol.lean), [Lookup/Tuple/Execution.lean](Lookup/Tuple/Execution.lean) |
| Why does denominator clearing work at poles? | [Algebra/Grouped.lean](Algebra/Grouped.lean) and [Security/InitialSoundness.lean](Security/InitialSoundness.lean) |
| Where is the tuple compression error proved? | [Lookup/Tuple/CompressionSoundness.lean](Lookup/Tuple/CompressionSoundness.lean) |
| How are honest helpers and private tables constructed? | [Prover/Helpers.lean](Prover/Helpers.lean) and [Prover/State.lean](Prover/State.lean) |
| How are formal round-message coefficients constructed? | [Prover/RoundCoefficients.lean](Prover/RoundCoefficients.lean) and [Prover/CoefficientCircuit.lean](Prover/CoefficientCircuit.lean) |
| How do I supply a different round-message builder? | [Prover/Reference.lean](Prover/Reference.lean), [Lookup/Prover/Reference.lean](Lookup/Prover/Reference.lean), [Lookup/Tuple/Prover/Reference.lean](Lookup/Tuple/Prover/Reference.lean) |

`Interaction/` is the common weighted protocol core. Scalar lookup adds its initial multiplicity
message in `Lookup/`; tuple lookup adds typed providers and beta compression in `Lookup/Tuple/`.
Both variants reuse that weighted core and the native [Sumcheck implementation](../Sumcheck/Interaction/Computable.lean).

## Implementation and resource files

The top level of `Prover/` contains the helper/state definitions, coefficient circuit and formal
reference construction. Its subfolders separate measured execution from resource theorems:

| Area | Files |
| --- | --- |
| Selected weighted implementation | [Default.lean](Prover/Default.lean), [Arithmetic/Control.lean](Prover/Arithmetic/Control.lean), [Arithmetic/State.lean](Prover/Arithmetic/State.lean), [Arithmetic/Round.lean](Prover/Arithmetic/Round.lean) |
| Exact call/profile correspondence | [Arithmetic/Ledger.lean](Prover/Arithmetic/Ledger.lean), [Arithmetic/RoundCost.lean](Prover/Arithmetic/RoundCost.lean), [CoefficientCircuitCost.lean](Prover/CoefficientCircuitCost.lean) |
| Private arithmetic bounds | [Prover/Resources/Arithmetic.lean](Prover/Resources/Arithmetic.lean), [Lookup/ArithmeticResources.lean](Lookup/ArithmeticResources.lean), [Lookup/Tuple/ArithmeticResources.lean](Lookup/Tuple/ArithmeticResources.lean) |
| Tuple eager compression | [Lookup/Tuple/ArithmeticCompression.lean](Lookup/Tuple/ArithmeticCompression.lean) and [Lookup/Tuple/Prover.lean](Lookup/Tuple/Prover.lean) |
| Retained logical storage | [Prover/Resources/Storage.lean](Prover/Resources/Storage.lean) |
| Construction buffers | [Prover/Resources/StorageBuffers.lean](Prover/Resources/StorageBuffers.lean) |
| Combined storage categories | [Prover/Resources/StorageLedger.lean](Prover/Resources/StorageLedger.lean) |
| Source openings, source packets and verifier-local profiles | [Interaction/Resources.lean](Interaction/Resources.lean) and [Algebra/ArithmeticReconstruction.lean](Algebra/ArithmeticReconstruction.lean) |
| Ambient sampling | [Interaction/SamplingResources.lean](Interaction/SamplingResources.lean) and [Interaction/HonestSamplingResources.lean](Interaction/HonestSamplingResources.lean) |

These metrics have separate scopes; consult the [design resource table](../../../docs/design/logup.md#separate-resource-metrics)
before combining them.

## Examples and reusable support

[ArkLibTest/ProofSystem/Logup/](../../../ArkLibTest/ProofSystem/Logup/) mirrors the production tree.
Start with [scalar prover examples](../../../ArkLibTest/ProofSystem/Logup/Lookup/Prover.lean),
[tuple prover examples](../../../ArkLibTest/ProofSystem/Logup/Lookup/Tuple/Prover.lean), or
[complete runtime fixtures](../../../ArkLibTest/ProofSystem/Logup/Interaction/MeasuredRuntime.lean).
Run the compiled fixtures with `lake exe logup-runtime`.

For reusable fractions, clearing and histogram lemmas, start with [Fraction.lean](../../Data/Fraction.lean),
[PartialFractions.lean](../../Data/Polynomial/PartialFractions.lean) and
[Data/Vector/](../../Data/Vector/). Fingerprint schemas and collision bounds live in
[TaggedTuple.lean](../../Data/Polynomial/TaggedTuple.lean) and
[TaggedTupleProbability.lean](../../Data/Polynomial/TaggedTupleProbability.lean). Polynomial
operations and their mathematical bridges live under [ToCompPoly/](../../ToCompPoly/); see the
[executable-polynomial guide](../../../docs/wiki/executable-polynomials.md) for representation,
code-generation, arithmetic-profile and logical-builder conventions.
