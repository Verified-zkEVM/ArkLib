# Logged execution and routing: port table

This table compares the old layer's tests with the interaction-layer port on
`feat/interaction-migrate-core`. Line numbers such as L29 are lines of the old-layer file. Each one
identifies a single declaration there. Related extra coverage is linked even where it does not
settle a row.

The two approved premises are:

- **P1 (passive verifier):** verifiers send public-coin challenges only, and bundle queries
  happen in the final decision. A challenge cannot be computed from an input or from a previously
  sent oracle.
- **P2 (fixed shape):** neither a challenge nor an oracle message selects the protocol's subtree.

Each row has one of four statuses:

- **ported:** the new tests check the same mathematical observation.
- **excluded by P1** (or **P2**): the row states exactly which assertion P1 (or P2) excludes.
- **removed:** the row names a mechanism that no longer exists.
- **open:** the row names an interface that the parent branch is missing.

The oracle-access tests ([access]) use the sent-oracle and queries-by-move interfaces.
They supply the access and cost fixtures cited below.

Of the 88 rows, 74 are ported, 11 are excluded by P1 and 3 are removed.

This table covers the eight old-layer files that this branch's tests cite. `ExecutionExample.lean`
and `CoreRunExample.lean` supply fixtures to those files. This slice does not claim their other
tests as ports. The table lists the named assertion lemmas in the two query-bound files as well as
their anonymous examples. A reader can then see the remaining access, cost and security
obligations directly, without inferring them from a trace equality.

## LoggedExecutionExample.lean

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| L29, complete trace | excluded by P1 | P1 excludes three verifier tags: 0 after the public receive, 5 after the first oracle receive, and 2 before a challenge derived from an input or an oracle. It also excludes the querier assignments that go with them. [full] keeps all six tags in a passive client, but **not** this former assignment of queriers. |
| L29, six-tag trace | ported | [full] checks the six-tag trace `[0, 1, 5, 2, 4, 3]` across a public send, an oracle send, one challenge draw, the challenge continuation and the final decision. Tags 5 and 2 both come from that one draw. It also checks private output `(777, hidden)` and verdict 37. The draw is independent of the bundles. |
| L64, ordered source requests and repeats | ported | [source] keeps first 11, input 7, second 19, second 19 in that order. |
| L64, first request between sends | excluded by P1 | P1 excludes the verifier's request to the first message before the second send. [source] is extra coverage of the final decision. |
| L75, source log of the one-send accepting run | ported | [accepted] includes exactly one sent-oracle request, answered 11. Computing exported data adds no query. |
| L79, accepted closure 18 | ported | [closing], first conjunct, and [faults], accepting conjunct. |
| L84, rejection and its source log | ported | [rejected]. [faults] separately keeps rejection as `.ok none`. |
| L89, structural log erasure audit | ported | [erasure] and [audit]. |
| L90, reduction log erasure audit | ported | [erasure] and [audit]. The outcome includes private output and output oracle data. |

## TerminalRun/Examples.lean

Every outcome below comes from the same actual prover. The test adapter `decisionObserved` then
interprets the final decision with [decideCatching] at the completed transcript's path, view and
bundle data. The adapter runs in `ExceptT Nat` over the persistent stateful history. The state that
holds the log of answered queries sits below the exception transformer. Because a failed request has
no answer, it adds no entry to that log, and every earlier answered request stays in it. The private
output comes from the completed interaction before the decision is interpreted. It is never rebuilt
from a constant or from the fault label.

The fault labels come from the handler: `decisionHandler` fails on requests 17 and 23. A core
verdict is an `Option`, so the verifier itself cannot return a fault. [totalFaults] checks that
modes 1 and 2 reject under a total handler.

The adapter and the ordinary erasure law have different scopes. [erasure] and [audit] cover the
ordinary logged run `runWithLog`. No theorem relates [decideCatching] to the ordinary logged
decision at the same path, view and bundle data.

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| L57, fault history `[9, 0, 1, 2]` | ported | Under handler failure: [faults], first conjunct. |
| L60, private output and sent-answer log on failure | ported | Under handler failure: [faults], first and second conjuncts, for arbitrary old input, message and hidden output. |
| L66, fault label 17 | removed | The old verifier returned `.fault 17` itself. A core verdict is an `Option`, so a verifier cannot return a fault. [totalFaults] shows that mode 1 rejects under a total handler. Label 17 survives only as a handler failure, in [faults]. |
| L68, distinct fault label 23 | removed | The old verifier returned `.fault 23` itself. A core verdict is an `Option`, so a verifier cannot return a fault. [totalFaults] shows that mode 2 rejects under a total handler. Label 23 survives only as a handler failure, in [faults]. |
| L71, rejection and sent-answer log | ported | [faults], third conjunct returns `.ok none` and keeps the same private output and log. |
| L77, input 7/message 11 closes to 18 | ported | [closing], first conjunct. |
| L82, input 13/message 19 closes to 32 | ported | [closing], second conjunct. [faults] proves the stronger closing equation for arbitrary input and message. |
| L86, erasure audit of the final decision | ported | [erasure] and [audit] for the ordinary rejecting and accepting run. They do not cover [decideCatching]. |
| Former effectful reception boundary | excluded by P1 | P1 excludes effect 1 as a separate verifier reception move. [faults] keeps the chronological history with that effect in the final decision. |
| L87, closing an optional final verdict | ported | [faults], fourth conjunct, checks the closed output `.ok (some (message, old + message))` of an actual accepting run, and [closing] checks two more. [optionalClosing] is only an equation about `Except.map`: for the closing map of any completed transcript, `Except.ok` of an optional verdict mapped by `Option.map` equals `Except.ok` of the closed verdict. It mentions no actual run. |

The [oracle bundle port table](port-oracle-bundles.md) numbers these rows TR1–TR7 and
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
| L194, explicit rejection | ported | [accessTerminal] keeps the actual transcript, arbitrary private output, prover log, decision source log and world history with `.ok none`. |
| L198, explicit fault 17 | removed | The old verifier returned `.fault 17` itself, as in TerminalRun L66. A core verdict is an `Option`, so a verifier cannot return a fault. Label 17 survives only as a handler failure, in [faults]. |
| L201, closing audit of the run by moves | ported | `map_fst_runWithQueriesByMove` and `toLog_runWithQueriesByMove` in [queriesByMoveLaws] keep the ordinary outcome, including its closed optional verdict and output oracles. |
| L202, closing audit of the decision in the run by moves | ported | [queriesByMoveLaws] preserves the closed optional verdict of the actual run under log projection. [optionalClosing] gives the separate `Except.map` equation for closing an optional verdict. |

## SourceRoutingExample.lean

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| L140, SR1, verifier message 23 derived from exported resources | excluded by P1 | P1 excludes the assertion that this message is computed by reading the prefix export and the suffix message. The verifier may send only a public-coin challenge. [sourceClosing] keeps the allowed observations with an independent draw. [routePassive] remains extra coverage. |
| L140, SR1, ambient order `[1, 10, 20, 30, 40, 50, 60]` | excluded by P1 | P1 excludes decision effects 10, 30 and 40 happening before the prover's interaction completes. [sourceClosing] and [routePassive] explicitly check the different passive schedule `[1, 20, 50, 10, 30, 40, 60]`. |
| L140, SR1, arbitrary hidden input and private memory, and actual output resources | ported | [sourceClosing] keeps the send/send/challenge order, input 7, messages 11 and 5, private result `secret + 23 + 50`, and claim/export `(23, 23)` computed from those same actual bundles. The challenge is drawn independently, so its former dependency on the bundles is excluded in the rows above. |
| L162, SR2, exactly two ordered raw requests | ported | [rawHidden] quantifies over the old input, hidden input, visible message and private coordinate. The requests are exactly `[0, 2]` and the answer is `old + visible`. In particular, old 7 and message 11 answer 18. |
| L162, SR2, hidden input never queried | ported | [notHidden] proves that request label 1 does not occur in that same raw execution. The handler would record it even if its answer were discarded. |
| L167, SR3, ordinary whole-prover theorem instantiation | ported | [routeWhole] instantiates [appendLaw] on the actual whole prover and input data. |
| L174, composed routing audit | ported | [audit] and the axiom audit beside [routeWhole] include [appendLaw] and [substitution]. |

The [oracle bundle port table](port-oracle-bundles.md) numbers these rows SR1–SR4 and
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
bundles of longer partial transcripts, and keeps node names and typed query routing. Its `toPathBundle_data` law
connects the bundle of sent oracles to the same transcript's `pathBundle`.
`OracleVerifier.prefixRoute_oracleMessages` connects the append route, whose outputs use
`splitOutputs`, to that prefix's inputs and oracle messages. [joinEntryNode], [joinEntryIsSent] and
[decisionEntryIsSent] exercise the node names on actual produced entries. The [oracle-access
tests][access] supply the typed access and cost certificates.

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| `route_cost`, L96 | ported | The exact double-read export/cost fixture and bound are ported in the oracle-access tests ([access]). |
| `program_cost`, L117 | ported | The authored double-read suffix and its cost bound are ported in the oracle-access tests ([access]). |
| L130, routed weighted cost at most 5 | ported | The exact routed cost-five bound is ported in the oracle-access tests ([access]). |
| `routed_available`, L149 | ported | [sentOracles] provides the proof that an oracle was sent (`IsSent`), `availableMap` and `liftQuery_node`. [routedAvailable] applies the produced decision entry's permission to the exact routed program. |
| L165, actual raw log old/old/fresh and claim 4 | ported | The exact composed logged execution, including the old/old/fresh log, closure and private output, is ported in the oracle-access tests ([access]). |
| `future_rejected`, L184, typed exclusion of a future move | ported | Typed exclusion for every prefix program, without a budget restriction, is ported in the oracle-access tests ([access]). |
| `future_rejected`, L184, proof of what was sent, from the partial transcript | ported | [sentOracles] defines `IsSent` using only oracle occurrences that were already sent. [joinEntryIsSent] excludes the future move at the actual join. |
| L209, old node name stable, old distinct from fresh | ported | `liftQuery_node` in [sentOracles] preserves node names and query arguments. [joinEntryNode] and [decisionEntryIsSent] check stability and distinctness on produced entries. |
| L225, closed execution keeps old/old/fresh and private output | ported | The exact composed logged execution, closure and private output are ported in the oracle-access tests ([access]). |
| L251, partial transcript of the actual join entry | ported | [joinEntryBefore] reads the partial transcript of the first suffix prover move's entry from the produced execution. P1 excludes the former verifier decision at this seam, not the seam's partial transcript. |
| L252, partial transcript of the actual decision entry | ported | [decisionEntryBefore] reads the complete actual oracle message partial transcript from the produced decision entry. |
| L255, membership of the join entry | ported | [joinEntryMem] proves that the selected actual join entry is one of the run's entries. `QueriesByMove.mem_withDecision` in [queriesByMove] is the general selection law. |
| L257, membership of the decision entry | ported | [decisionEntryMem] and `QueriesByMove.decision_mem_withDecision` in [queriesByMove] prove membership in the produced execution. |
| L266, the decision entry's partial transcript shows the oracle was sent, and cost 5 | ported | [decisionEntryIsSent] shows that the oracles in the actual decision entry's bundle were sent. [availableCost] pairs that permission for the exact doubled-export route with its cost-five bound. |
| L277, old node name survives inclusion from the join to the end | ported | [joinEntryNode] uses `SentOracleMessageIndex.node_lift` for the actual produced partial transcripts. `firstMovesLe_node` and `availableMap_node` in [sentOracles] give the general laws. |
| L286, no budget makes the fresh oracle sent at the actual join | ported | [joinEntryIsSent] excludes the fresh oracle occurrence independently of any cost budget. [decisionEntryIsSent] identifies that occurrence at the decision entry. |
| L300, raw log of the run by moves is old/old/fresh | ported | [queriesByMoveSourceLog] keeps the exact old/old/fresh log, private output 3 and verdict 4. [queriesByMoveLaws] proves that the full log agrees for every prover. |
| L320, routed cost cannot be bounded by 4 | ported | The inhabited cost-five witness that excludes a bound of four is ported in the oracle-access tests ([access]). |

## RuntimeQueryBounds.lean

The [runtime table of the access port table][access-runtime] holds the complete port entries and
exact counterparts. P1 excludes the old order in the prefix, dummy query before reveal. It does not
exclude the proofs that an oracle was sent at a partial transcript. `PartialTranscript.queryNode`
and `availableMap_node` supply node names and inclusion for input queries. The access port table
links those laws next to the concrete permission and cost assertions.

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
| `native_split_history`, L207, passive schedule | ported | `OracleVerifier.run_append` ([appendLaw]) proves the narrower passive law: both interactions run first, then the decisions. The old lemma split the runtime execution of every prover. [bitSplit] instantiates the passive law on the hidden-bit fixture. |
| `native_split_history`, L207, effectful prefix order | excluded by P1 | P1 excludes the prefix verifier's dummy request before the prover's suffix interaction. |
| `native_actual_history`, L227 | ported | [bitLog] keeps the actual chronological ambient history, answers, final state and charge 4. |
| `informed_native_history`, L235 | excluded by P1 | The same former order, dummy request before reveal, is excluded under P1. [bitInformed] is extra coverage. |
| `native_import_budget`, L244 | ported | Import-cost reflection is ported in the oracle-access tests ([access]). |
| `fixed_native_resource_bounds`, L258 | ported | [sentOracles] supplies `IsSent` at each partial transcript. The access tests keep the combined access, cost, history and half-bound conjunction. |
| `informed_cost_does_not_give_half`, L289, charge and success | ported | Charge seven and success one for the passive schedule are ported together in the oracle-access tests ([access]). |
| `informed_cost_does_not_give_half`, L289, query order | excluded by P1 | The old history has the prefix verifier's dummy request before both reveals. P1 excludes that order, as for L182 and L235. The passive port has reveal, dummy request, reveal. |

## Erasure, closing and open interface obligations

[erasure] forgets both logs and keeps the completed oracle outcome. The interpreter and
runtime corollaries combine this law with oracle simulation and runtime-trace erasure.
[substitution] proves routing for an arbitrary ambient interpreter. `OracleMap.simulate_withAmbient`
specializes it with `QueryImpl.id' ambient`.

[decideCatching] interprets a final decision at a supplied path, view and bundle data, with
labelled failures, and keeps the log of answered queries. It prepends each answer and reverses the
log once at the end. Its handler has type `QueryImpl ambient (ExceptT ε m)` and it requires only `[Monad m]`.
Its input statements and output queries lie in `Type`, as in the full-decision-log interface.
[optionalClosing] states the optional-closing correspondence for the output map and bundle of
any completed transcript, with input indices, input queries and output queries in `Type`.

The obligations about the queries by move are ported under the passive schedule. The runner
instruments both strategies before calling `TwoParty.Lens.run`. `OracleVerifier.executeWith`
supplies the single interaction-and-decision sequence for the ordinary run, both aggregate logged
runs, the queries by move and the ambient queries by move. The aggregate logged runs `runWithLog`
and `runWithAmbientLog` log directly with `withLogging` and build no partial transcripts.
`toLog_runWithQueriesByMove` and `toLog_runWithAmbientQueriesByMove` in [queriesByMoveLaws] prove
that forgetting the move boundaries gives them. Erasure follows from the general `MoveInstrumentation.run_mapMovesWith`
law and from the writer and monad laws. The law is added next to its use because the pinned PolyFun
lacks it. No row about the queries by move changes status.

[queriesByMoveLaws] supplies ordinary, full-log and ambient-log erasure, ordered per-entry
concatenation and agreement under interpreters. [sentOracles] supplies the `IsSent` predicate and
inclusion. Its general laws are weaker than the concrete checks:
`runWithQueriesByMove_before_le` proves that the partial transcript of each recorded entry extends
to the completed transcript, and `isSent_at_decision` carries the proof that an oracle was sent
along that extension. Neither law fixes an entry's exact partial transcript. The concrete tests
[queriesByMoveContract], [actualPartialTranscripts] and [movedQuery] check the exact partial
transcript of each entry in their fixtures. [movedQuery] checks the distinguishing case: identical transcripts, outputs and
aggregate logs, with a query at different actual partial transcripts. These facts do not restore
verifier queries at intermediate boundaries. P1 excludes those actions and their original move
assignments, as the rows marked excluded by P1 say.

Step 4 of the D2 migration retired the earlier restriction on full logs with large query
universes, which implementation note 18 records: every bundle query index now lies in `Type`.
`runWithAmbientQueriesByMove` keeps the queries by move, with erasure to `runWithAmbientLog` and to
the ordinary run.
`toAmbient_runWithQueriesByMove` equates its produced entries with the full queries by move at
small universes. [liftedQueriesByMove] executed an actual `Nat` oracle node with queries in
`Type 1` until step 3 of the D2 migration, which pins the node-query universe of the verifier APIs
at `0` and removed that test.

The rows above link the access port table for their full statements, exact targets and the
qualifications from P1. Proofs that an oracle was sent use [sentOracles]. Observations of produced
entries use [queriesByMove] and [queriesByMoveLaws]. Typed access and whole-run logs remain extra checks.

[faults]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L224
[totalFaults]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L251
[closing]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L238
[full]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L603
[moveSummary]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L556
[source]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L417
[accepted]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L154
[rejected]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L166
[runtime]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L294
[countSetup]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L448
[countDirect]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L451
[append]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L719
[repeat]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L728
[raw]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L760
[bitLog]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L774
[bitPlain]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L807
[bitInformed]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L784
[bitSplit]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L800
[audit]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L869
[erasure]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/Knowledge.lean#L419
[runtimeErasure]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Oracle/LoggedExecution.lean#L49
[decideCatching]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Oracle/LoggedExecution.lean#L78
[rawHidden]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/Routing.lean#L84
[notHidden]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/Routing.lean#L89
[routePassive]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/Routing.lean#L179
[routeWhole]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/Routing.lean#L277
[oracleMessages]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Oracle/Routing.lean#L100
[appendLaw]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Oracle/Routing.lean#L123
[substitution]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Composition.lean#L502
[sourceClosing]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/Routing.lean#L257
[unitRuntime]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L334
[optionalClosing]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L267
[access]: port-oracle-access.md
[access-runtime]: port-oracle-access.md#runtimequerybounds-17-assertions
[accessTerminal]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenSendRun.lean#L140
[routedAvailable]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/RoutedAccess.lean#L295
[availableCost]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L84

[queriesByMoveLaws]: ../../../ArkLib/Interaction/Oracle/QueriesByMoveLaws.lean
[sentOracles]: ../../../ArkLib/Interaction/Oracle/SentOracles.lean
[queriesByMoveContract]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L944
[actualPartialTranscripts]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L963
[joinEntryBefore]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1090
[decisionEntryBefore]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1096
[joinEntryMem]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1083
[decisionEntryMem]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1086
[joinEntryNode]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1115
[joinEntryIsSent]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1122
[decisionEntryIsSent]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1133
[queriesByMoveSourceLog]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1143
[movedQuery]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1036

[queriesByMove]: ../../../ArkLib/Interaction/Oracle/QueriesByMove.lean

[liftedQueriesByMove]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1211
