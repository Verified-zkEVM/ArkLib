# Logged execution and routing: port table

This table compares the old layer's tests with the interaction-layer port on
`feat/interaction-migrate-core`. Line numbers such as L29 are lines of the old-layer file. Each one
identifies a single declaration there. Related extra coverage is linked even where it does not
settle a row.

The two approved premises are:

- **P1 (passive verifier):** verifiers send public-coin challenges only, and resource queries
  happen in the final decision. A challenge cannot be computed from an input or from a previously
  sent oracle.
- **P2 (fixed shape):** neither a challenge nor an oracle message selects the protocol's subtree.

Each row has one of four statuses:

- **ported:** the new tests check the same mathematical observation.
- **excluded by P1** (or **P2**): the row states exactly which assertion P1 (or P2) excludes.
- **removed:** the row names a mechanism that no longer exists.
- **open:** the row names an interface that the parent branch is missing.

The oracle-access tests ([access]) hold the access and cost fixtures cited below. This branch
provides the sent-oracle and queries-by-move interfaces that those fixtures use. Removing an API name does
not by itself remove the mathematical assertions it carried.

This table covers the eight old-layer files that this branch's tests cite. `ExecutionExample.lean`
and `CoreRunExample.lean` supply fixtures to those files. This slice does not claim their other
tests as ports. The table lists the named assertion lemmas in the two query-bound files as well as
their anonymous examples. A reader can then see the remaining access, cost and security
obligations directly, without inferring them from a trace equality.

## LoggedExecutionExample.lean

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| L29, complete trace | excluded by P1 | P1 excludes three verifier tags: 0 after the public receive, 5 after the first oracle receive, and 2 before a challenge derived from an input or an oracle. It also excludes the querier assignments that go with them. [full] keeps all six action tags in a passive client, but **not** this former assignment of queriers. |
| L29, six-action coverage | ported | [full] checks `[0, 1, 5, 2, 4, 3]` across a public send, an oracle send, challenge service, challenge continuation and the final decision, with private output `(777, hidden)` and verdict 37. The draw is independent of resources. |
| L64, ordered source requests and repeats | ported | [source] keeps first 11, input 7, second 19, second 19 in that order. |
| L64, first request between sends | excluded by P1 | P1 excludes the verifier's request to the first message before the second send. [source] is extra coverage of the final decision. |
| L75, source log of the one-send accepting run | ported | [accepted] includes exactly one sent-oracle request, answered 11. Computing exported data adds no query. |
| L79, accepted closure 18 | ported | [closing], first conjunct, and [faults], accepting conjunct. |
| L84, rejection and its source log | ported | [rejected]. [faults] separately keeps rejection as `.ok none`. |
| L89, structural log erasure audit | ported | [erasure] and [audit]. |
| L90, reduction log erasure audit | ported | [erasure] and [audit]. The outcome includes private output and output oracle data. |

## TerminalRun/Examples.lean

Every outcome below comes from the same actual prover, followed by the same final-decision
interpreter ([decideCatching]). The interpreter runs in `ExceptT Nat` over the persistent stateful
history. The state that holds the log of answered queries sits below the exception transformer.
Because a failed request has no answer, it adds no entry to that log, and every earlier answered
request stays in it. The private output comes from the completed interaction before the decision
is interpreted. It is never rebuilt from a constant or from the fault label.

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| L57, fault history `[9, 0, 1, 2]` | ported | [faults], first conjunct. |
| L60, private output and sent-answer log on failure | ported | [faults], first and second conjuncts, for arbitrary old input, message and hidden output. |
| L66, fault label 17 | ported | [faults], first conjunct returns `.error 17`. |
| L68, distinct fault label 23 | ported | [faults], second conjunct returns `.error 23`. |
| L71, rejection and sent-answer log | ported | [faults], third conjunct returns `.ok none` and keeps the same private output and log. |
| L77, input 7/message 11 closes to 18 | ported | [closing], first conjunct. |
| L82, input 13/message 19 closes to 32 | ported | [closing], second conjunct. [faults] proves the stronger closing equation for arbitrary input and message. |
| L86, erasure audit of the final decision | ported | [erasure] and [audit] for the ordinary rejecting and accepting run. |
| Former effectful reception boundary | excluded by P1 | P1 excludes effect 1 as a separate verifier reception move. [faults] keeps the chronological history with that effect in the final decision. |
| L87, closing an optional final verdict | ported | [optionalClosing] proves that embedding any optional verdict with `Except.ok` and then closing with the completed transcript's output map and resources equals closing first and then embedding. This holds for `none` and for every accepted statement. |

The [source and resource port table](oracle-universe-tests.md) numbers these rows TR1–TR7 and
links them here.

The old reception action 1 now belongs to the final decision. Running it between the send and the
decision is excluded by P1. The chronological history above is preserved, but that does not claim
that the former reception move boundary is preserved.

## RuntimeExample.lean

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| L24, private output, final count 10 and three ordered requests | ported | [unitRuntime] keeps the arbitrary private output and requests 0/1/2 in one unit-response runtime execution that starts at 7. |
| L24, ambient `Nat → Unit` responses in the exact runtime trace | ported | [unitRuntime] keeps the actual unit answers in chronological order and final state 10. Both verifier effects happen in the final decision. |

## PhasedRun.lean

[queriesByMove] produces the actual entries, and for each entry the partial transcript before it,
including challenges and oracle messages. The querier comes from the executed participant action.
The final verifier decision is a separate decision entry. [queriesByMoveContract] checks the
passive move groups and the runtime state, and the original aggregate-log check [moveSummary]
remains. `runWithProverSetup` can keep explicit setup as its own entry. Setup fused into a prover's
first move stays in that move's entry.

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| L84, the queriers of the produced entries cannot be replaced | ported | [queriesByMove] derives each entry's querier from the participant action that it logs. No replacement role decoration is an argument. [queriesByMoveContract] checks the produced queriers. |
| L91, verifier effects 2 and 3 before challenge, effect 6 on receive | excluded by P1 | P1 excludes these non-passive verifier actions at those boundaries. It therefore excludes the exact eight-region list and state `2102345678`. |
| L91, setup/prover/decision effects and private output | ported | [moveSummary] keeps `[9, 9, 1, 4, 5]` and `[2, 3, 6, 7]`, oracle message 17, private output 23 and verdict 31. State `2102563478` witnesses the passive order. |
| L91, remaining per-boundary partial-transcript and querier information | ported | [queriesByMoveContract] and [actualPartialTranscripts] observe the actual message, challenge and oracle message partial transcripts and each entry's querier and queries. Explicit setup remains a separate entry through `runWithProverSetup`. |
| L114, setup query 9 has multiplicity two | ported | [moveSummary] asserts the complete prover log, including both 9s. |
| L121, the final transcript has oracle message 17 | ported | [moveSummary] reads 17 from the actual completed transcript. |
| L178, input 7, accepted export 18, sent log and world order | ported | [closing] and [faults] keep all these observations together with arbitrary private output. |
| L178, setup, send, reception and decision entry groups | excluded by P1 | P1 excludes the separate effectful verifier reception group `[1]`. It now runs in the final decision together with `[2]`. |
| L178, queries by move for the remaining allowed groups | ported | [queriesByMoveLaws] keeps explicit setup, the moves' entries and the decision entry, with full-log and ordinary erasure. The reception action that P1 excludes is identified separately above. |
| L194, explicit rejection | ported | [faults], third conjunct. |
| L198, explicit fault 17 | ported | [faults], first conjunct. Rejection is a different constructor. |
| L201, closing audit of the run by moves | ported | `map_fst_runWithQueriesByMove` and `toLog_runWithQueriesByMove` in [queriesByMoveLaws] keep the ordinary outcome, including its closed optional verdict and output resources. |
| L202, closing audit of the decision in the run by moves | ported | [queriesByMoveLaws] keeps the same closed optional verdict under log projection. [optionalClosing] keeps the optional verdict through the labelled final-decision presentation. |

## SourceRoutingExample.lean

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| L140, SR1, verifier message 23 derived from exported resources | excluded by P1 | P1 excludes the assertion that this message is computed by reading the prefix export and the suffix message. The verifier may send only a public-coin challenge. [sourceClosing] keeps the allowed observations with an independent draw. [routePassive] remains extra coverage. |
| L140, SR1, ambient order `[1, 10, 20, 30, 40, 50, 60]` | excluded by P1 | P1 excludes decision effects 10, 30 and 40 happening before the prover's interaction completes. [sourceClosing] and [routePassive] explicitly check the different passive schedule `[1, 20, 50, 10, 30, 40, 60]`. |
| L140, SR1, arbitrary hidden input and private memory, and actual output resources | ported | [sourceClosing] keeps the send/send/challenge order, input 7, messages 11 and 5, private result `secret + 23 + 50`, and claim/export `(23, 23)` computed from those same actual resources. The challenge is drawn independently, so its former dependency on resources is excluded in the rows above. |
| L162, SR2, exactly two ordered raw requests | ported | [rawHidden] quantifies over the old input, hidden input, visible message and private coordinate. The requests are exactly `[0, 2]` and the answer is `old + visible`. In particular, old 7 and message 11 answer 18. |
| L162, SR2, hidden input never queried | ported | [notHidden] proves that request label 1 does not occur in that same raw execution. The handler would record it even if its answer were discarded. |
| L167, SR3, ordinary whole-prover theorem instantiation | ported | [routeWhole] instantiates [appendLaw] on the actual whole prover and input data. |
| L174, composed routing audit | ported | [audit] and the axiom audit beside [routeWhole] include [appendLaw] and [substitution]. |

The [source and resource port table](oracle-universe-tests.md) numbers these rows SR1–SR4 and
links them here. It also links an added worst-case cost check on the same export map.

## Persistent-runtime tests

The old-layer file is named `NativeRuntime.lean`. This heading describes what its tests check.

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| L79, setup, prefix and suffix share one counter, with a dependent private output | ported | [countSetup] keeps both actual answers, the private output in `Fin (first + 1)`, raw decision requests, final state and world trace. |
| L106, direct runtime without setup | ported | [countDirect] keeps the two actual sends and final count 2. |
| L125, direct adapter by moves agrees with the logged runtime | ported | `simulateQ_toLog_runWithQueriesByMove` in [queriesByMoveLaws] preserves the existing logged execution under every lawful interpreter, including the persistent stateful runtime. [queriesByMoveContract] checks the same runtime state. |
| L228, expanded export keeps raw input and both sent answers | ported | [append] keeps private memory, claim 10, the raw input, prefix and suffix requests, state 3 and the ordered world answers. |
| L263, one export request expands to two raw requests | ported | [raw] uses the same logging-after-substitution law and keeps both answers. |
| L276, expanded run by moves and logged runtime agree | ported | [queriesByMoveLaws] commutes with full-log erasure after routing, and its interpreter law preserves the persistent runtime observation. The existing [append] and [raw] tests keep the expanded source queries. |
| L285, direct logged erasure audit | ported | [erasure] and [audit]. |
| L286, runtime erasure audit | ported | [runtimeErasure] and [audit]. |
| L287, logging-after-substitution audit | ported | [raw] and [audit] use `OracleComp.withQueryLog_simulateQ`. |
| L288, outcome audit of the run by moves and the logged run | ported | `toLog_runWithQueriesByMove`, `map_fst_runWithQueriesByMove` and `simulateQ_toLog_runWithQueriesByMove` in [queriesByMoveLaws]. |

## QueryBounds.lean

[sentOracles] identifies the oracle messages sent at a partial transcript, includes them in the
resources of longer partial transcripts, and keeps node names and typed query routing. Its `toPathResources_data` law
connects the family of sent oracles to the same transcript's `pathResources`.
`OracleVerifier.prefixRoute_oracleMessages` connects the append route, whose outputs use
`splitOutputs`, to that prefix's inputs and oracle messages. [joinEntryNode], [joinEntryIsSent] and
[decisionEntryIsSent] exercise the node names on actual produced entries. Typed access and cost certificates remain in the
oracle-access tests.

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| `route_cost`, L96 | ported | The exact double-read export/cost fixture and bound are ported in the oracle-access tests ([access]). |
| `program_cost`, L117 | ported | The authored double-read suffix and its cost bound are ported in the oracle-access tests ([access]). |
| L130, routed weighted cost at most 5 | ported | The exact routed cost-five bound is ported in the oracle-access tests ([access]). |
| `routed_available`, L149 | ported | [sentOracles] provides the proof that an oracle was sent (`IsSent`), `availableMap` and `liftQuery_node`. The access tests supply the routed program certificate. |
| L165, actual raw log old/old/fresh and claim 4 | ported | The exact composed logged execution, including the old/old/fresh log, closure and private output, is ported in the oracle-access tests ([access]). |
| `future_rejected`, L184, typed exclusion of a future move | ported | Typed exclusion for every prefix program, without a budget restriction, is ported in the oracle-access tests ([access]). |
| `future_rejected`, L184, proof of what was sent, from the partial transcript | ported | [sentOracles] defines `IsSent` using only oracle occurrences that were already sent. [joinEntryIsSent] excludes the future move at the actual join. |
| L209, old node name stable, old distinct from fresh | ported | `liftQuery_node` in [sentOracles] preserves node names and query arguments. [joinEntryNode] and [decisionEntryIsSent] check stability and distinctness on produced entries. |
| L225, closed execution keeps old/old/fresh and private output | ported | The exact composed logged execution, closure and private output are ported in the oracle-access tests ([access]). |
| L251, partial transcript of the actual join entry | ported | [joinEntryBefore] reads the partial transcript of the first suffix prover move's entry from the produced execution. P1 excludes the former verifier decision at this seam, not the seam's partial transcript. |
| L252, partial transcript of the actual decision entry | ported | [decisionEntryBefore] reads the complete actual oracle message partial transcript from the produced decision entry. |
| L255, membership of the join entry | ported | [joinEntryMem] proves that the selected actual join entry is one of the run's entries. `QueriesByMove.mem_withDecision` in [queriesByMove] is the general selection law. |
| L257, membership of the decision entry | ported | [decisionEntryMem] and `QueriesByMove.decision_mem_withDecision` in [queriesByMove] prove membership in the produced execution. |
| L266, the decision entry's partial transcript shows the oracle was sent, and cost 5 | ported | [decisionEntryIsSent] shows that the oracles in the actual decision entry's resources were sent. [sentOracles] supplies inclusion and routing. The access tests keep the cost-five certificate. |
| L277, old node name survives inclusion from the join to the end | ported | [joinEntryNode] uses `SentOracleMessageIndex.node_lift` for the actual produced partial transcripts. `firstMovesLe_node` and `availableMap_node` in [sentOracles] give the general laws. |
| L286, no budget makes the fresh oracle sent at the actual join | ported | [joinEntryIsSent] excludes the fresh oracle occurrence independently of any cost budget. [decisionEntryIsSent] identifies that occurrence at the decision entry. |
| L300, raw log of the run by moves is old/old/fresh | ported | [queriesByMoveSourceLog] keeps the exact old/old/fresh log, private output 3 and verdict 4. [queriesByMoveLaws] proves that the full log agrees for every prover. |
| L320, routed cost cannot be bounded by 4 | ported | The inhabited cost-five witness that excludes a bound of four is ported in the oracle-access tests ([access]). |

## RuntimeQueryBounds.lean

The runtime-trace equalities below keep the actual answers and charges. In the passive
informed-prover trace, the reveal comes before the prefix decision's dummy query. The former
order, dummy query before reveal, needs a non-passive prefix verifier. The table states this
difference explicitly and does not hide it by dropping answers or summing costs.

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| `exported_certificate`, L47 | ported | [sentOracles] supplies the family of sent oracle messages at a partial transcript and the `IsSent` predicate. The access tests supply export access and cost two. |
| `source_name`, L57 | ported | `queryNode`, `liftQuery_node` and `sentOracleMessageMap_query` in [sentOracles] give a node name to the same sent oracle occurrence and route it without changing the query argument. |
| `first_returns_exported`, L61 | ported | The exact decision and output-map/data equations are ported in the oracle-access tests ([access]). |
| `suffixAction_eq`, L72 | ported | The exact suffix decision equation is ported in the oracle-access tests ([access]). |
| `suffix_access`, L87 | ported | [sentOracles] supplies `IsSent` and partial-transcript inclusion. The access tests supply typed suffix access. |
| `suffix_budget`, L102 | ported | The suffix cost certificate is ported in the oracle-access tests ([access]). |
| `routed_suffix_budget`, L124 | ported | The routed suffix cost certificate is ported in the oracle-access tests ([access]). |
| `routed_suffix_access`, L145 | ported | [sentOracles] supplies `IsSent`, typed query inclusion and its node-name and routing law. The access tests supply typed routed access. |
| `actual_history`, L167 | ported | [bitPlain] keeps the two ambient requests and charge 4. Its full trace additionally keeps the challenge. |
| `informed_actual_history`, L182 | excluded by P1 | P1 excludes the prefix verifier's dummy request before the prover's reveal at the seam. [bitInformed] checks reveal, dummy request, reveal and charge 7 as extra passive coverage. |
| `setup_budget`, L197 | ported | The imported setup cost theorem is ported in the oracle-access tests ([access]). |
| `native_split_history`, L207, passive schedule | ported | The all-prover charged runtime and history observation of [appendLaw] is ported in the oracle-access tests ([access]). |
| `native_split_history`, L207, effectful prefix order | excluded by P1 | P1 excludes the prefix verifier's dummy request before the prover's suffix interaction. |
| `native_actual_history`, L227 | ported | [bitLog] keeps the actual chronological ambient history, answers, final state and charge 4. |
| `informed_native_history`, L235 | excluded by P1 | The same former order, dummy request before reveal, is excluded under P1. [bitInformed] is extra coverage. |
| `native_import_budget`, L244 | ported | Import-cost reflection is ported in the oracle-access tests ([access]). |
| `fixed_native_resource_bounds`, L258 | ported | [sentOracles] supplies `IsSent` at each partial transcript. The access tests keep the combined access, cost, history and half-bound conjunction. |
| `informed_cost_does_not_give_half`, L289 | ported | Charge seven and success one for the passive schedule are ported together in the oracle-access tests ([access]). |

## Erasure, closing and open interface obligations

[erasure] forgets both logs and keeps the completed oracle outcome. The interpreter and
runtime corollaries combine this law with oracle simulation and runtime-trace erasure.
[substitution] proves routing for an arbitrary ambient interpreter. `OracleMap.simulate_withAmbient`
specializes it with `QueryImpl.id' ambient`.

[decideCatching] interprets final decisions with labelled failures and keeps the log of answered
queries. Its handler has type `QueryImpl ambient (ExceptT ε m)` and it requires only `[Monad m]`.
Its input-statement and output-query universes match the full-decision-log interface.
[optionalClosing] states the optional-closing correspondence for the output map and resources of
any completed transcript, with independent input-index, input-query and output-query universes.

The obligations about the queries by move are ported under the passive schedule. R1 replaces the
separate step executor with writer-instrumented strategies run by `TwoParty.Lens.run`.
`OracleVerifier.executeWith` supplies the single interaction-and-decision sequence for the
ordinary run, the queries by move and the ambient queries by move. Both aggregate log APIs are
projections of these logs. Erasure follows from the general `MoveInstrumentation.run_mapMovesWith`
law and from the writer and monad laws. The law is added next to its use because the pinned PolyFun
lacks it. No row about the queries by move changes status.

[queriesByMoveLaws] supplies ordinary, full-log and ambient-log erasure, ordered per-entry
concatenation and agreement under interpreters. [sentOracles] supplies the `IsSent` predicate and
inclusion. [movedQuery] checks the distinguishing case: identical transcripts, outputs and
aggregate logs, with a query at different actual partial transcripts. These facts do not restore
verifier queries at intermediate boundaries. P1 excludes those actions and their original move
assignments, as the rows marked excluded by P1 say.

The earlier restriction on full logs with large query universes remains recorded in implementation
note 18. `runWithAmbientQueriesByMove` keeps the queries by move at independent input-query and
oracle-node-query universes, with erasure to `runWithAmbientLog` and to the ordinary run.
`toAmbient_runWithQueriesByMove` equates its produced entries with the full queries by move at
small universes. [liftedQueriesByMove] executes an actual `Nat` oracle node with queries in
`Type 1`. Its decision reads the sent oracle message, and the test checks the partial transcript
at the produced decision entry.

Ports held in the oracle-access tests:

- Four tests cover QueryBounds `route_cost`, `program_cost`, L130, L165, L225 and L320:
  - the exact double-read export/cost fixture;
  - the source and routed cost-five bounds;
  - the inhabited witness that excludes bound four;
  - the actual composed old/old/fresh log with closure and private output.
- Typed routing, distinct old and fresh oracle messages, and exclusion of future moves cover the
  expressible parts of `routed_available`, `future_rejected`, L209, L266, L277, L286 and L300.
- The following tests cover the expressible parts of RuntimeQueryBounds `exported_certificate`,
  `source_name`, `first_returns_exported`, `suffixAction_eq`, `suffix_access`, `suffix_budget`,
  `routed_suffix_budget`, `routed_suffix_access`, `setup_budget`, `native_split_history` and
  `native_import_budget`:
  - exact decisions and output-map/data equations;
  - typed source and routed access;
  - export cost two, suffix cost bounds and setup cost;
  - import-cost reflection and charged passive runtime histories.
- The combined expressible access, cost, history and half-bound conjunction and the
  charge-seven/success-one assertion cover the corresponding parts of
  `fixed_native_resource_bounds` and `informed_cost_does_not_give_half`.

[faults]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L221
[closing]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L235
[full]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L587
[moveSummary]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L539
[source]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L398
[accepted]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L156
[rejected]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L168
[runtime]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L274
[countSetup]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L429
[countDirect]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L432
[append]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L704
[repeat]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L713
[raw]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L745
[bitLog]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L759
[bitPlain]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L792
[bitInformed]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L769
[bitSplit]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L785
[audit]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L854
[erasure]: ../../../ArkLib/Interaction/Core/Security/Knowledge.lean#L402
[runtimeErasure]: ../../../ArkLib/Interaction/Core/Oracle/LoggedExecution.lean#L49
[decideCatching]: ../../../ArkLib/Interaction/Core/Oracle/LoggedExecution.lean#L73
[rawHidden]: ../../../ArkLibTest/Interaction/Core/Oracle/Routing.lean#L83
[notHidden]: ../../../ArkLibTest/Interaction/Core/Oracle/Routing.lean#L88
[routePassive]: ../../../ArkLibTest/Interaction/Core/Oracle/Routing.lean#L178
[routeWhole]: ../../../ArkLibTest/Interaction/Core/Oracle/Routing.lean#L275
[oracleMessages]: ../../../ArkLib/Interaction/Core/Oracle/Routing.lean#L100
[appendLaw]: ../../../ArkLib/Interaction/Core/Oracle/Routing.lean#L122
[substitution]: ../../../ArkLib/Interaction/Core/Composition.lean#L335
[sourceClosing]: ../../../ArkLibTest/Interaction/Core/Oracle/Routing.lean#L255
[unitRuntime]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L315
[optionalClosing]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L247
[access]: oracle-access-tests.md

[queriesByMoveLaws]: ../../../ArkLib/Interaction/Core/Oracle/QueriesByMoveLaws.lean
[sentOracles]: ../../../ArkLib/Interaction/Core/Oracle/SentOracles.lean
[queriesByMoveContract]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L924
[actualPartialTranscripts]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L943
[joinEntryBefore]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1071
[decisionEntryBefore]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1077
[joinEntryMem]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1064
[decisionEntryMem]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1067
[joinEntryNode]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1096
[joinEntryIsSent]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1103
[decisionEntryIsSent]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1114
[queriesByMoveSourceLog]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1124
[movedQuery]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1016

[queriesByMove]: ../../../ArkLib/Interaction/Core/Oracle/QueriesByMove.lean

[liftedQueriesByMove]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1199
