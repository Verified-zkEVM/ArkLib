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
The status is one of equivalent, premise-required, retired, unresolved or accepted upstream limit.
An accepted upstream limit comes from a pinned dependency and is documented at its code site. The
rows for entry 19 use the plainer names ported, excluded by P1 or P2, removed and open for the
first four statuses. The [port table](port-logged-execution.md) explains them.

| Entry | Departure | Status |
| --- | --- | --- |
| 19 | Writer instrumentation of the core runner (`TwoParty.Lens.run`) produces one entry per move, with the partial transcript, the querier and the queries. Erasing the entries gives the aggregate logs exactly. The code is in `Oracle/QueriesByMove.lean`, `Oracle/QueriesByMoveLaws.lean` and `Oracle/SentOracles.lean` | ported |
| 19 | P1 excludes intermediate verifier queries and the moves they were assigned to; prover moves and their partial transcripts remain | excluded by P1 |
| 18 | Input data, input queries and oracle-node queries have independent universes; families specialize the general bundle API | equivalent: `OracleBundle` inputs remove the realization/response coupling, and oracle positions carry their own query interface. Since step 5 of the D2 migration, moves, node queries and bundle data all lie in `Type` |
| 18 | Agreement preserves path-dependent output statements, oracle indices, carriers and interfaces, general bundle inputs, and statement-dependent RBR knowledge relations | equivalent: F7 and 3A use the unchanged owner interfaces; see the [Agreement inventory](sumcheck.md#agreement-universes-and-parent-limits) |
| 18 | Run outputs and a prover's ambient index lie in `Type`, the monad's value universe | equivalent: since step 3 of the D2 migration, the prover's monad is `OracleComp ambient : Type → Type`; neither P1 nor P2 changes this contract |
| 18 | The full-log runner returns only small bundle-query logs; ambient-log execution supports arbitrary bundle-query universes | retired: under record D2's universe policy, bundle-query indices lie in `Type`, and since step 4 of its migration `runWithLog` accepts every oracle verifier. Before the policy, VCVio had no logging interface that returns large query indices through the small computation monad, and `runWithAmbientLog` and `runWithAmbientQueriesByMove` were the workaround |
| 26 | Full-prefix knowledge composition with independent witness carriers and measured root, step and leaf maps | equivalent; node-indexed bounds specialize full-prefix bounds, see the knowledge inventory below |
| 21 | Round-by-round soundness implies soundness for lawful distribution monads, with prefix-indexed freshness | equivalent; see the soundness disposition record below |

Record D2's [universe policy](../interaction-rebuild/D2-ownership-and-universes.md#universe-policy)
supersedes the entry-18 rows. Its [migration](../interaction-rebuild/D2-ownership-and-universes.md#migration)
is complete, and the rows describe the current code.

The [oracle-bundle and oracle-node universe port table](port-bundle-universes.md) records
the old-layer R26, R27 and decoration canaries closed by entry 18. The R26/R27 definitions occur
once, in `ArkLibTest/Interaction/Oracle/BundleFamilies.lean`.

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

The second departure distinguishes the unchanged full-run interface from the arbitrary interval
interface. The [exact-row disposition](sumcheck.md#migration-disposition) now names
interaction-layer interval, projection and append targets. The `degreeModel` and
`degreeGuarantee` rows are retired: their only client, `message_degree`, reads the bound from the
message type. Core therefore needs no counterpart of `OracleModel.satisfies_guarantee`. Both full-run and suffix soundness use the generic round-by-round-to-soundness implication
over indexed domains, including lists with repetitions.

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
| [23](../interaction-rebuild/IMPLEMENTATION-NOTES.md#23-sumcheck-ports) | Sumcheck ports: arbitrary interval completeness, interaction-layer suffix soundness, public interval append, projected behavior, generic message interpretation and routing over `Nat`. |

## Computable Sumcheck: entry 24

This entry is in
[`interaction-rebuild/IMPLEMENTATION-NOTES.md`](../interaction-rebuild/IMPLEMENTATION-NOTES.md#24-computable-sumcheck-runtime).

| Entry | Departure |
| --- | --- |
| [24](../interaction-rebuild/IMPLEMENTATION-NOTES.md#24-computable-sumcheck-runtime) | Computable Sumcheck runtime: the run correspondence renames challenge queries, inputs are CompPoly polynomials, and runtime rows 3, 4 and 6 require P1/P2; row 7 checks the zero-round interval verifier, and the new row 8 checks one CompPoly interval round after a challenge prefix. |

## Interaction-layer migration: entry 20

Entry 18 records the core's universe constraints, entry 26 knowledge composition, and entry 20
state restoration. Under approved premise P2, challenges and oracle messages never select shape.

| Entry | Status and scope |
| --- | --- |
| [20](../interaction-rebuild/IMPLEMENTATION-NOTES.md#20-state-restoration-under-p2-authored-output-selection) | Premise-required: frozen challenge-selected output carriers are retired by P2. A prover-authored Boolean selects the exact `Fin 8`/`Fin 9` statement carriers instead. The [state-restoration disposition record](state-restoration-disposition.md) classifies each frozen production declaration and fixture assertion, including equivalent laws, P1/P2 restrictions and retired mechanisms. It gives the proved support-to-replay bridge and the zero-root/zero-leaf budget specialization. Frozen output oracles stay `Fin 8`; additional fixtures exercise path-dependent output oracle families. Unmeasured restoration predicates and bounds take input, intermediate and output witnesses in `Type`, and deterministic verdicts and shared extraction laws take moves in `Type`, as record D2's universe policy requires. Round samplers, probabilistic outputs and measured stage programs retain the exact small-carrier constraints recorded in entry 20. |

## The oracle correspondence gap and its resolution

**Gap.** The first version of the legacy embedding defined `embedOracleProver` and
`embedOracleVerifier` on the oracle tree, but stated every execution correspondence and every
security transfer for the plain tree and `embedVerifier`. No theorem related a run of the
embedded oracle parties to legacy `OracleReduction.run`, and the oracle tests used hand-supplied
path data and output maps rather than a run.

**Resolution.** The modules `Legacy/OracleExecution.lean`, `Legacy/OracleSecurity.lean` and
`Legacy/OracleKnowledge.lean` state the correspondence and the transfers on the oracle tree:

- `oracleFinalize` reads the legacy result off an oracle-tree outcome, including both
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

The test `ArkLibTest/Interaction/Legacy/OracleExecution.lean` runs the embedded oracle
parties on accepting and rejecting challenges, with distinct prover and verifier outputs, for both
legacy output-oracle representations. The test
`ArkLibTest/Interaction/Legacy/OracleKnowledge.lean` instantiates the knowledge transfers for
a decision that queries the shared oracle, the input oracle and a message, with an extractor that
reads both shared-oracle logs. It runs the oracle extraction game and the legacy knowledge program
to the same witness.

An earlier entry 17 recorded that straight-line knowledge soundness was transferred on the plain
tree only. `Legacy/OracleKnowledge.lean` closes it, and the entry is removed.

## Logged execution and routing tests

The [port table](port-logged-execution.md) lists each assertion in the old layer's tests
and where it is ported or what remains. It also lists which assertions the approved
passive-verifier and fixed-shape premises (P1 and P2) exclude. The rows about the queries by move are ported under
the passive schedule. There is no separate step executor. Instrumented strategies run through
`TwoParty.Lens.run`, and the ordinary run, the queries by move and the ambient queries by move
share `OracleVerifier.executeWith`. Erasure follows from a general law about running
instrumented strategies and from the writer laws. The rows excluded by P1 name the intermediate
verifier actions and move assignments that P1 excludes.

## Stage composition and oracle execution acceptance clients

The [stage and execution port table](port-stages.md) lists each old-layer
assertion of the claim, composition, core-run, execution and dependent-reduction clients. It also
lists each replaced ordered-execution law. Each row gives the assertion's exact port, the premise
that excludes part of it, or the removed mechanism it belonged to. The old-layer ordered execution
decided each stage before the next one and skipped the later stages after a rejection. The port
composes passive stages with right-associated appends, runs every interaction before the
decisions, and selects later stages by the prover's public messages only. The table also records
the universe placement of stage chains. The split of a chain at an arbitrary stage is ported on
completed runs: `StageChain.decideOn_then` and `StageChain.outputOn_then` split the decisions and
output data of a concatenation, and `OracleVerifier.append_append_decideOn` and
`OracleVerifier.append_append_outputOn` reassociate `OracleVerifier.append`. These laws do not
transport the prover of the concatenation to the appended protocol.

## Knowledge composition and measured extraction

The [assertion disposition record](knowledge-composition-disposition.md) maps the frozen
production laws and acceptance assertions to the composition and measured-extraction port. It
records the public prover selector required by P2, the explicit zero root and leaf budgets that
recover the frozen bound, and VCVio's small-carrier restriction on measured programs. Pure
backward maps accept large leaf and seam witnesses directly. The shared full-prefix sampler
retains earlier public challenges and prover messages in both distributions and local errors.
Oracle verifiers draw from the verifier view, which erases oracle messages; their errors keep the
full prefix. P1 retires only challenge selection that depends on oracle messages and effectful
receiver actions. The inventory marks the already constant KC-065 schedule equivalent.

## Oracle-access acceptance tests

The [oracle-access port table](port-oracle-access.md) closes DecorationExample row 2 with
the arbitrary-tree decoration test and the independent-universe node and path-family tests. Its
PhasedRun and QueryBounds rows cite the parent's produced assertions directly. These cover
membership of the join and decision entries, node names, and the agreement between the queries by
move and the logged run. The doubled-export fixture applies the decision entry's permission to its
routed program, jointly with its cost-five bound, and checks the actual ordered decision queries
separately. P1 excludes intermediate verifier effects and the moves they were assigned to.
