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

## Interaction-layer migration: entry 18

This entry continues the numbering for the migration of the frozen interaction layer into the
interaction core; entry 17 was removed (see the end of this page). It is in
[`interaction-rebuild/IMPLEMENTATION-NOTES.md`](../interaction-rebuild/IMPLEMENTATION-NOTES.md).

| Entry | Departure |
| --- | --- |
| [18](../interaction-rebuild/IMPLEMENTATION-NOTES.md#18-state-restoration-fixes-the-output-type-and-the-decision-ambient) | State restoration fixes the output type and the decision ambient. The verifier has one output statement type, and a rejecting branch is `none` in an `Option` output, not a type with no claim. The decision has the empty ambient oracle `[]ₒ`. A knowledge state function with a transcript-indexed output witness family replaces per-input round extractors; the adversary's witness is read at the completed transcript by a map, not an equivalence, and the output law is an implication from an accepted observation and the output relation. |

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
