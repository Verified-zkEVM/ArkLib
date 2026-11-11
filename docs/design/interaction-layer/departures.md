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
The status is one of equivalent, premise-required or unresolved.

| Entry | Departure | Status |
| --- | --- | --- |
| 18 | Run outputs and a prover's ambient index are tied to the monad universe `u`; every other component takes its own universe, including input and output oracle query types. Input oracle data stays in the response universe `Type u`; the full-log oracle runner `runWithLog` keeps the input index and query type in `Type`, while extraction runs on the general ambient-log runner. | Run-output coupling is premise-required: positions live one universe up and the runner is `m : Type u → Type u`. Input-data and full-log restrictions remain unresolved: `OracleInterface` ties data and responses through `ReaderM`, and the full log records input queries. |
| 21 | Round-by-round soundness implies soundness for lawful distribution monads, with prefix-indexed freshness | equivalent; see the soundness disposition record below |

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
| [22](sumcheck.md#full-run-and-interval-verifier-interfaces) | Full-run verifiers keep their interface; interval verifiers add arbitrary endpoints and public interval composition. |

The second departure distinguishes the unchanged full-run interface from the arbitrary interval interface.
The [exact-row disposition](sumcheck.md#migration-disposition) now names native interval,
projection and append targets. The parent's behavior-guarantee interface gaps remain unresolved.
Both full-run and suffix soundness use the parent implication over indexed domains, including
lists with repetitions.

Entry [21](../interaction-rebuild/IMPLEMENTATION-NOTES.md#21-round-by-round-soundness-implies-soundness-for-lawful-distribution-monads)
records the generic soundness implication. The
[soundness disposition record](soundness-implication-disposition.md) compares every ported frozen
statement and test, explains prefix-indexed freshness, and links the classical specialization laws.
The implication applies to lawful distribution monads, including optional computations.

The interval implementation retains arbitrary `start` and `count` rather than replacing them
with the full run. Its boundary, projection and composition equations preserve original behavior
and prover outputs. P1 and P2 explain changed decision timing and public abort shape.

## Sumcheck ports: entry 23

| Entry | Departure |
| --- | --- |
| [23](../interaction-rebuild/IMPLEMENTATION-NOTES.md#23-sumcheck-ports) | Sumcheck ports: arbitrary interval completeness, native suffix soundness, public interval append, projected behavior, generic message interpretation and routing over `Nat`. |

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
verifier and fixed-shape premises. Its unresolved rows remain migration obligations.
