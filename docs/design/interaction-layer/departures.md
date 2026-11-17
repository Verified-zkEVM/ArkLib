# Departures of the interaction layer from its design records

This page indexes every recorded departure of the interaction layer from the design records in
[`docs/design/`](..). Each entry links to the page that states the departure in full: what the
record said, what the code does, and why. It also records a gap that review found in the legacy
embedding, and how it was closed.

## Interaction core: entries 1–13

These entries are in
[`interaction-rebuild/IMPLEMENTATION-NOTES.md`](../interaction-rebuild/IMPLEMENTATION-NOTES.md).

| Entry | Departure |
| --- | --- |
| 1 | Oracle interfaces in positions; challenges indexed by node occurrences |
| 2 | Observations retain the transcript and output on rejection |
| 3 | Oracle append and split are lawful maps with data round trips |
| 4 | Adversary models are indexed by input and observation types |
| 5 | Errors in `ℝ≥0∞` with measurable observations |
| 6 | Knowledge requires marginal preservation and an access budget |
| 7 | Round-by-round terminal obligations cover every ambient state |
| 8 | Model definitions live in the security files |
| 9 | Oracle append needs output compatibility on accepted prefix results |
| 10 | Root obligations of state functions are guarded by the input promise |
| 11 | The public-coin sampler is presented beside the pure-end sampler |
| 12 | Path-fiber splitting stays in ArkLib |
| 13 | The oracle decision log is recorded in the core |

## Interaction core: later entries

These entries are also in
[`interaction-rebuild/IMPLEMENTATION-NOTES.md`](../interaction-rebuild/IMPLEMENTATION-NOTES.md).
The status is one of equivalent, premise-required, retired or unresolved.

| Entry | Departure | Status |
| --- | --- | --- |
| 19 | Writer instrumentation of the authoritative runner produces per-slot prefix, owner and query provenance with exact log erasure, in `Oracle/SlotTrace.lean`, `Oracle/Provenance.lean` and `Oracle/PrefixResources.lean` | equivalent |
| 19 | P1 retires intermediate verifier queries and their former phase assignments; prover slots and their prefixes remain | premise-required |
| 18 | Input data, input queries and oracle-node queries have independent universes; families specialize the general resource API | equivalent: `Resources` inputs remove the realization/response coupling, and `OracleProtocol.{u, q}` separates node queries from moves |
| 18 | Agreement preserves path-dependent output statements, oracle indices, carriers and interfaces, general resource inputs, and statement-dependent RBR knowledge relations | equivalent: F7 and 3A use the unchanged owner interfaces; see the [Agreement inventory](sumcheck.md#agreement-universes-and-parent-limits) |
| 18 | Run outputs and a prover's ambient index remain in the monad universe `u` | equivalent: the retained D2 runner contract is `m : Type u → Type u`; neither P1 nor P2 changes this contract |
| 18 | The full-log runner returns only small resource-query logs; ambient-log execution supports arbitrary resource-query universes | unresolved: a parent logging interface that returns large query indices through the small computation monad is missing |
| 26 | Full-prefix knowledge composition with independent witness carriers and measured root, step and leaf maps | equivalent; node-indexed bounds specialize full-prefix bounds, see the knowledge inventory below |
| 21 | Round-by-round soundness implies soundness for lawful distribution monads, with prefix-indexed freshness | equivalent; see the soundness disposition record below |

The [resource and node universe inventory](resource-universes-disposition.md) records the frozen
R26, R27 and decoration canaries closed by entry 18.

## Legacy embedding: entries 14–16

These entries continue the numbering for the security transfers of the legacy embedding. They
are in [`legacy-embedding.md`](legacy-embedding.md#departures).

| Entry | Departure |
| --- | --- |
| [14](legacy-embedding.md#14-the-knowledge-transfer-needs-no-extractor-invariance-premise) | The knowledge transfer needs no extractor-invariance premise. |
| [15](legacy-embedding.md#15-round-by-round-transfers-into-the-interaction-layer-assume-all-state-terminal-certificates) | Round-by-round transfers into the interaction layer assume all-state terminal certificates. Full support of `init`, a state-independent verdict, and a guarded verifier each supply them. |
| [16](legacy-embedding.md#16-round-by-round-knowledge-soundness-out-of-the-interaction-layer-goes-through-induced-languages) | Round-by-round knowledge soundness out of the interaction layer goes through induced languages. It needs `Nonempty WitIn` and does not transport the extractor. |

Entries 15 and 16 are the two hypotheses that a client of the round-by-round transfers must
check. Entry 15 applies to the direction into the interaction layer, and entry 16 to the
direction out of it.

## Sumcheck: entry 22

Entry 22 covers Sumcheck in the interaction layer. Its two departures are described in
[`sumcheck.md`](sumcheck.md#departures).

| Entry | Departure |
| --- | --- |
| [22](sumcheck.md#the-transferred-completeness-is-in-its-own-module) | The transferred completeness is in its own module, `LegacyCompleteness`. |
| [22](sumcheck.md#the-verifier-has-no-interval-start) | Full-run verifiers have no interval start; #1488 owns interval endpoints and composition. |

Entry 22 records the full-run verifier interface; #1488 covers interval endpoints and
composition. The [exact-row disposition](sumcheck.md#migration-disposition) records interval
execution, projection and append clients as remaining work, and marks behavior-guarantee
interfaces unresolved. Full-run, committed and randomized soundness in the interaction layer use
the generic round-by-round-to-soundness implication directly over arbitrary indexed domains and lists with
repetitions.

Entry [21](../interaction-rebuild/IMPLEMENTATION-NOTES.md#21-round-by-round-soundness-implies-soundness-for-lawful-distribution-monads)
records the generic soundness implication. The
[soundness disposition record](soundness-implication-disposition.md) compares every ported frozen
statement and test, explains prefix-indexed freshness, and links the classical specialization laws.
The implication applies to lawful distribution monads, including optional computations.

## Interaction-layer migration: entry 20

Entry 18 records the core's universe constraints, entry 26 knowledge composition, and entry 20
state restoration. Under approved premise P2, challenges and oracle messages never select shape.

| Entry | Status and scope |
| --- | --- |
| [20](../interaction-rebuild/IMPLEMENTATION-NOTES.md#20-state-restoration-under-p2-authored-output-selection) | Premise-required: frozen challenge-selected output carriers are retired by P2. A prover-authored Boolean selects the exact `Fin 8`/`Fin 9` statement carriers instead. The [state-restoration disposition record](state-restoration-disposition.md) classifies each frozen production declaration and fixture assertion, including equivalent laws, P1/P2 restrictions and retired mechanisms. It gives the proved support-to-replay bridge and the zero-root/zero-leaf budget specialization. Frozen output oracles stay `Fin 8`; additional fixtures exercise path-dependent output oracle families. Unmeasured restoration predicates and bounds have independent input, intermediate and terminal witness universes; deterministic observations and shared extraction laws accept general move universes. Round samplers, probabilistic outputs and measured stage programs retain the exact small-carrier constraints recorded in entry 20. |

## The oracle correspondence gap and its resolution

**Gap.** The first version of the legacy embedding defined `embedOracleProver` and
`embedOracleVerifier` on the oracle tree, but stated every execution correspondence and every
security transfer for the plain tree and `embedVerifier`. No theorem related a run of the
embedded oracle parties to legacy `OracleReduction.run`, and the oracle tests used hand-supplied
path data and output maps rather than a run.

**Resolution.** The modules `Legacy/OracleExecution.lean`, `Legacy/OracleSecurity.lean` and
`Legacy/OracleKnowledge.lean` state the correspondence and the transfers on the oracle tree:

- `oracleFinalize` reads the legacy result off an oracle-tree observation, including both
  parties' outputs and the verifier's output oracle data.
- `oracleFinalize_observeWith_counterpartFirst` is program equality with legacy
  `OracleReduction.run` under the counterpart-first schedule, for every legacy protocol
  specification. `simulateQ_oracleFinalize_run` gives the default-schedule form for provers with
  pure challenge slots, and `evalDist_experiment_oracleFinalize_run` the distributional form for
  every prover.
- `oracleCompleteness_iff` and `oracleSoundness_iff` transfer completeness and soundness.
  `oracleAcceptanceAgrees` instantiates the generic round-by-round transfers of `Layout`, which
  give `embedOracleVerifier_rbrSoundness`, `rbrSoundness_of_embedOracleVerifier`,
  `embedOracleVerifier_rbrKnowledgeSoundness` and
  `rbrKnowledgeSoundness_of_embedOracleVerifier`.
- `oracleKnowledgeSoundnessWith_iff` and `oracleKnowledgeSoundness_iff` transfer straight-line
  knowledge soundness, with the same relations, error, rejection semantics and explicit
  extraction failure. They rest on the logged form of the oracle correspondence
  (`runEq_ambientLogged_oracleProver`, `oracleExtractionGame_embed`): the decoded transcript,
  outputs, shared-oracle logs and final shared state agree with the legacy knowledge game.
- `OracleMap.ofLegacySimulation` turns a legacy output-oracle simulation into an oracle map, and
  `legacyOutputMap` is defined through it.

The test `ArkLibTest/Interaction/Core/Legacy/OracleExecution.lean` runs the embedded oracle
parties on accepting and rejecting challenges, with distinct prover and verifier outputs, for both
legacy output-oracle representations. The test
`ArkLibTest/Interaction/Core/Legacy/OracleKnowledge.lean` instantiates the knowledge transfers for
a decision that queries the shared oracle, the input oracle and a message, with an extractor that
reads both shared-oracle logs. It runs the oracle extraction game and the legacy knowledge program
to the same witness.

An earlier entry 17 recorded that straight-line knowledge soundness was transferred on the plain
tree only. `Legacy/OracleKnowledge.lean` closes it, and the entry is removed.

## Logged execution and routing acceptance clients

The [source-to-port inventory](logged-execution-disposition.md) lists each frozen acceptance
assertion, its exact port or missing interface, and the assertions retired by the approved passive
verifier and fixed-shape premises. The produced provenance rows are equivalent under the passive
schedule. There is no separate recursive slot executor: instrumented strategies run through `TwoParty.Lens.run`, and ordinary,
full-trace and ambient-trace APIs share `OracleVerifier.executeWith`. Erasure specializes a
general runner naturality law and writer laws. The premise-required rows identify the intermediate
verifier actions and phase assignments retired by P1.

## Knowledge composition and measured extraction

The [assertion disposition record](knowledge-composition-disposition.md) maps the frozen
production laws and acceptance assertions to the composition and measured-extraction port. It
records the public prover selector required by P2, the explicit zero root and leaf budgets that
recover the frozen bound, and VCVio's small-carrier restriction on measured programs. Pure
backward maps accept large terminal and seam witnesses directly. The shared full-prefix sampler
retains earlier public challenges and prover messages in both distributions and local errors.
P1 retires oracle-payload-dependent challenge selection and effectful receiver actions only.
The inventory marks the already constant KC-065 schedule equivalent.
