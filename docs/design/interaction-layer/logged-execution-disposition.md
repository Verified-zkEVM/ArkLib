# Logged execution and routing: source-to-port inventory

This inventory compares the frozen acceptance clients with the interaction-layer port on
`feat/interaction-migrate-core`. Source line numbers identify individual declarations.
Related additional coverage is linked even where it does not discharge a row.

The two approved premises are:

- **P1 (passivity):** verifiers send public-coin challenges only, and resource queries occur in
  the final decision. A challenge cannot be computed from an input or previously sent oracle.
- **P2 (shape):** neither a challenge nor an oracle payload selects the protocol's subtree.

Each row has one of four statuses. An **equivalent** row preserves the stated mathematical
observation. A **premise-required** row states exactly which assertion P1 or P2 retires. A
**retired** row names a removed mechanism. An **unresolved** row names a missing parent interface.
The oracle-access tests ([access]) own the access and cost fixtures cited below; this branch
provides their prefix-resource and phase interfaces. Retiring an API name alone does not retire
its mathematical assertions.

The files inventoried here are the eight frozen files cited by this branch's acceptance clients.
`ExecutionExample.lean` and `CoreRunExample.lean` supply fixtures to those files; their other
clients are not claimed as ports by this slice. Named assertion lemmas in the two query-bound
files are included as well as their anonymous examples, so an inventory reader can see the
remaining access, cost and security obligations rather than infer them from a trace equality.

## LoggedExecutionExample.lean

| Source assertion | Status | Exact target or remaining obligation |
| --- | --- | --- |
| L29, complete trace | premise-required | P1 retires verifier tag 0 after the public receive, tag 5 after the first oracle receive, tag 2 before an input/oracle-derived challenge, and their owner assignments. [full] retains all six action tags in a passive client, **not** this former ownership. |
| L29, six-action coverage | equivalent | [full] checks `[0, 1, 5, 2, 4, 3]` across a public send, oracle send, challenge service, challenge continuation and terminal decision, with private output `(777, hidden)` and verdict 37. The draw is independent of resources. |
| L64, ordered source requests and repeats | equivalent | [source] retains first 11, input 7, second 19, second 19 in that order. |
| L64, first request between sends | premise-required | P1 retires the verifier's request to the first message before the second send. [source] is additional final-decision coverage. |
| L75, source log of the one-send accepting run | equivalent | [accepted] includes exactly one sent-oracle request, answered 11; computing exported data adds no query. |
| L79, accepted closure 18 | equivalent | [closing], first conjunct, and [faults], accepting conjunct. |
| L84, rejection and its source log | equivalent | [rejected]; [faults] separately retains rejection as `.ok none`. |
| L89, structural log erasure audit | equivalent | [erasure] and [audit]. |
| L90, reduction log erasure audit | equivalent | [erasure] and [audit]; the observation includes private output and output oracle data. |

## TerminalRun/Examples.lean

Every outcome below is produced by the same actual prover followed by the same final-decision
interpreter [terminalAPI]. Its target uses `ExceptT Nat` over the persistent stateful history.
The state holding the answered-query log is below the exception transformer. A failed request
has no answer, so it adds no query-answer entry; every earlier answered request remains recorded.
The private output is obtained from the completed interaction before interpreting the decision.
It is never reconstructed from a constant or the fault label.

| Source assertion | Status | Exact target or remaining obligation |
| --- | --- | --- |
| L57, fault history `[9, 0, 1, 2]` | equivalent | [faults], first conjunct. |
| L60, private output and sent-answer log on failure | equivalent | [faults], first and second conjuncts, for arbitrary old input, message and hidden output. |
| L66, fault label 17 | equivalent | [faults], first conjunct returns `.error 17`. |
| L68, distinct fault label 23 | equivalent | [faults], second conjunct returns `.error 23`. |
| L71, rejection and sent-answer log | equivalent | [faults], third conjunct returns `.ok none`, retaining the same private output and log. |
| L77, input 7/message 11 closes to 18 | equivalent | [closing], first conjunct. |
| L82, input 13/message 19 closes to 32 | equivalent | [closing], second conjunct; [faults] proves the stronger arbitrary-input/message closing equation. |
| L86, terminal erasure audit | equivalent | [erasure] and [audit] for the ordinary rejecting/accepting run. |
| Former effectful reception boundary | premise-required | P1 retires effect 1 as a separate verifier reception phase; [faults] retains the chronological history with that effect in the final decision. |
| L87, closing an optional terminal verdict | equivalent | [optionalClosing] proves that embedding any optional verdict with `Except.ok` and closing with the completed transcript's output map and resources equals closing first and then embedding, including `none` and every accepted statement. |

The old reception action 1 now belongs to the decision. Its execution between send and terminal
is a **premise-required** retirement under P1; preservation of the chronological history above
does not assert preservation of the former reception phase boundary.

## RuntimeExample.lean

| Source assertion | Status | Exact target or remaining obligation |
| --- | --- | --- |
| L24, private output, final count 10 and three ordered requests | equivalent | [unitRuntime] retains the arbitrary private output and requests 0/1/2 in one unit-response runtime execution starting at 7. |
| L24, ambient `Nat → Unit` responses in the exact runtime trace | equivalent | [unitRuntime] retains the actual unit answers in chronological order and final state 10; both verifier effects occur in the final decision. |

## PhasedRun.lean

[slots] produces the actual slots and their accumulated full prefixes, including challenges
and oracle payloads. The owner comes from the executed participant slot, and the final verifier
decision is a distinct terminal phase. [tracePhases] checks the passive phase groups and runtime
state; the original aggregate-log [phases] check remains. Explicit setup can be retained as its
own slot by `runWithSetupTrace`; setup fused into a prover's first slot stays in that slot.

| Source component | Status | Full disposition |
| --- | --- | --- |
| L84, produced phase owners cannot be replaced | equivalent | [slots] derives each phase owner from its slot constructor; no replacement role decoration is an argument. [tracePhases] checks the produced owners. |
| L91, verifier effects 2 and 3 before challenge, effect 6 on receive | premise-required | P1 retires these non-passive verifier actions at those boundaries. It consequently retires the exact eight-region list and state `2102345678`. |
| L91, setup/prover/decision effects and private output | equivalent | [phases] retains `[9, 9, 1, 4, 5]` and `[2, 3, 6, 7]`, payload 17, private output 23 and verdict 31. The passive order is witnessed by state `2102563478`. |
| L91, remaining per-boundary prefix/owner information | equivalent | [tracePhases] and [actualPrefixes] observe the actual message, challenge and payload prefixes and each slot's owner and queries. Explicit setup remains a separate slot through `runWithSetupTrace`. |
| L114, setup query 9 has multiplicity two | equivalent | [phases] asserts the complete prover log, including both 9s. |
| L121, final prefix has payload 17 | equivalent | [phases] reads 17 from the actual completed transcript. |
| L178, input 7, accepted export 18, sent log and world order | equivalent | [closing] and [faults] retain all these observations together with arbitrary private output. |
| L178, setup/send/reception/terminal phase groups | premise-required | P1 retires the separate effectful verifier reception group `[1]`; it now executes in the final decision with `[2]`. |
| L178, phase artifact for the remaining allowed groups | equivalent | [trace] retains explicit setup, prover slots and the terminal decision, with full-log and ordinary erasure. P1's retired reception action is identified separately above. |
| L194, explicit rejection | equivalent | [accessTerminal] retains the actual transcript, arbitrary private output, prover log, decision source log and world history with `.ok none`. |
| L198, explicit fault 17 | equivalent | [accessTerminal] retains those same observations with `.error 17`, distinct from rejection. |
| L201, phased closing audit | equivalent | `runWithTrace_erase` and `runWithTrace_logView` in [trace] retain the ordinary observation, including its closed optional verdict and output resources. |
| L202, phased terminal closing audit | equivalent | [trace] preserves the same closed optional verdict under log projection; [optionalClosing] preserves the optional verdict through the labelled terminal presentation. |

## SourceRoutingExample.lean

| Source assertion | Status | Exact target or remaining obligation |
| --- | --- | --- |
| L140, SR1, exported-resource-derived verifier message 23 | premise-required | P1 retires the assertion that this message is computed by reading the prefix export and suffix message; the verifier may send only a public-coin challenge. [sourceClosing] preserves the allowed observations with an independent draw; [routePassive] remains additional coverage. |
| L140, SR1, ambient order `[1, 10, 20, 30, 40, 50, 60]` | premise-required | P1 retires decision effects 10, 30 and 40 occurring before completion of the prover's interaction. [sourceClosing] and [routePassive] explicitly check the different passive schedule `[1, 20, 50, 10, 30, 40, 60]`. |
| L140, SR1, arbitrary hidden input/private memory and actual output resources | equivalent | [sourceClosing] preserves the send/send/challenge order, input 7, messages 11 and 5, private result `secret + 23 + 50`, and claim/export `(23, 23)` computed from those same actual resources. The challenge is drawn independently; its former resource dependency is retired above. |
| L162, SR2, exact two ordered raw requests | equivalent | [rawHidden] quantifies the old input, hidden input, visible message and private coordinate; requests are exactly `[0, 2]`, and the answer is `old + visible`. In particular old 7/message 11 answers 18. |
| L162, SR2, hidden slot never queried | equivalent | [notHidden] proves request label 1 absent from that same raw execution. The handler would record it even if its answer were discarded. |
| L167, SR3, ordinary whole-prover theorem instantiation | equivalent | [routeWhole] instantiates [appendLaw] on the actual whole prover and input data. |
| L174, composed routing audit | equivalent | [audit] and the axiom audit beside [routeWhole] include [appendLaw] and [substitution]. |

## Persistent-runtime acceptance file

The frozen filename is `NativeRuntime.lean`; this heading describes its mathematical role.

| Source assertion | Status | Exact target or remaining obligation |
| --- | --- | --- |
| L79, setup/prefix/suffix share one counter and dependent private output | equivalent | [countSetup] retains both actual answers, the private output in `Fin (first + 1)`, raw decision requests, final state and world trace. |
| L106, direct runtime without setup | equivalent | [countDirect] retains the two actual sends and final count 2. |
| L125, direct phased adapter agrees with logged runtime | equivalent | `simulateQ_runWithTrace_logView` in [trace] preserves the existing logged execution under every lawful interpreter, including the persistent stateful runtime. [tracePhases] checks the same runtime state. |
| L228, expanded export keeps raw input and both sent answers | equivalent | [append] retains private memory, claim 10, the raw input/prefix/suffix requests, state 3 and the ordered world answers. |
| L263, one export request expands to two raw requests | equivalent | [raw] uses the same logging-after-substitution law and retains both answers. |
| L276, expanded phased/logged runtime correspondence | equivalent | [trace] commutes with full-log erasure after routing, and its interpreter law preserves the persistent runtime observation. Existing [append] and [raw] tests retain expanded source queries. |
| L285, direct logged erasure audit | equivalent | [erasure] and [audit]. |
| L286, runtime erasure audit | equivalent | [runtimeErasure] and [audit]. |
| L287, logging-after-substitution audit | equivalent | [raw] and [audit] use `OracleComp.withQueryLog_simulateQ`. |
| L288, phased/logged observation audit | equivalent | `runWithTrace_logView`, `runWithTrace_erase` and `simulateQ_runWithTrace_logView` in [trace]. |

## QueryBounds.lean

[prefixResources] identifies the available payloads at a full prefix, includes their resources
in longer prefixes, and preserves canonical names and typed query routing. Its
`pathResourcesInclusion_data` law connects the canonical family to the same transcript's
`pathResources`. `OracleVerifier.prefixRoute_payload` connects the append route, whose outputs
use `splitOutputs`, to that prefix's inputs and payloads. [joinName], [joinAvailable] and
[terminalAvailable] exercise the canonical names on actual produced phases. Typed access and cost
certificates remain in the oracle-access tests.

| Source component | Status | Full disposition |
| --- | --- | --- |
| `route_cost`, L96 | equivalent | The exact double-read export/cost fixture and bound are ported in the oracle-access tests ([access]). |
| `program_cost`, L117 | equivalent | The authored double-read suffix and its cost bound are ported in the oracle-access tests ([access]). |
| L130, routed weighted cost at most 5 | equivalent | The exact routed cost-five bound is ported in the oracle-access tests ([access]). |
| `routed_available`, L149 | equivalent | [prefixResources] provides canonical availability, `contextInclusion`, and `includeQuery_name`; [routedAvailable] certifies the exact routed program at its produced terminal phase. |
| L165, actual raw log old/old/fresh and claim 4 | equivalent | The exact composed logged execution, including the old/old/fresh log, closure and private output, is ported in the oracle-access tests ([access]). |
| `future_rejected`, L184, typed future-slot exclusion | equivalent | Typed exclusion for every prefix program, without a budget restriction, is ported in the oracle-access tests ([access]). |
| `future_rejected`, L184, canonical prefix-context certificate | equivalent | [prefixResources] defines availability using only already sent oracle occurrences. [joinAvailable] excludes the future slot at the actual join. |
| L209, old canonical name stable, old distinct from fresh | equivalent | `includeQuery_name` in [prefixResources] preserves names and query arguments. [joinName] and [terminalAvailable] check stability and distinctness on produced phases. |
| L225, closed execution retains old/old/fresh and private output | equivalent | The exact composed logged execution, closure and private output are ported in the oracle-access tests ([access]). |
| L251, actual join-phase prefix | equivalent | [joinPrefix] reads the first suffix prover slot from the produced execution. P1 retires the former verifier decision at this seam, not the seam prefix. |
| L252, actual terminal-phase prefix | equivalent | [terminalPrefix] reads the complete actual payload prefix from the produced terminal decision. |
| `joinPhase_mem`, L255 | equivalent | [joinMember] proves membership of the selected actual join phase; `TracedRun.phase_mem` in [slots] is the general selection law. |
| `terminalPhase_mem`, L257 | equivalent | [terminalMember] and `TracedRun.terminalPhase_mem` in [slots] prove membership in the produced execution. |
| L266, terminal prefix certifies availability and cost 5 | equivalent | [terminalAvailable] certifies the actual terminal resources; [availableCost] couples canonical availability to cost five for the exact doubled-export route. |
| L277, old query name survives join-to-terminal inclusion | equivalent | [joinName] uses `includeIndex_name` for the actual produced prefixes. `joinToTerminal_name` and `contextInclusion_name` in [prefixResources] give the general laws. |
| L286, no budget makes fresh slot available at actual join | equivalent | [joinAvailable] excludes the fresh occurrence independently of any cost budget; [terminalAvailable] identifies that occurrence at the terminal boundary. |
| L300, phased raw log is old/old/fresh | equivalent | [phaseSource] retains the exact old/old/fresh log, private output 3 and verdict 4. [trace] proves full-log correspondence for every prover. |
| L320, routed cost cannot be bounded by 4 | equivalent | The inhabited cost-five witness excluding a bound of four is ported in the oracle-access tests ([access]). |

## RuntimeQueryBounds.lean

The [access ledger's runtime table][access-runtime] holds the complete dispositions and exact
counterparts. Passivity excludes the old dummy-before-reveal prefix order; it does not exclude
canonical prefix certificates. `FullPrefix.queryName` and `contextInclusion_name` supply
canonical input naming and inclusion; the access ledger links those laws alongside the concrete
permission and cost assertions.

| Source component | Status | Full disposition |
| --- | --- | --- |
| `exported_certificate`, L47 | equivalent | [prefixResources] supplies the canonical prefix family and its availability predicate. The access tests supply export access and cost two. |
| `source_name`, L57 | equivalent | `queryName`, `includeQuery_name` and `familyInclusion_query` in [prefixResources] name and route the same available occurrence without changing the query argument. |
| `first_returns_exported`, L61 | equivalent | The exact decision and output-map/data equations are ported in the oracle-access tests ([access]). |
| `suffixAction_eq`, L72 | equivalent | The exact suffix decision equation is ported in the oracle-access tests ([access]). |
| `suffix_access`, L87 | equivalent | [prefixResources] supplies canonical availability and prefix inclusion; the access tests supply typed suffix access. |
| `suffix_budget`, L102 | equivalent | The suffix cost certificate is ported in the oracle-access tests ([access]). |
| `routed_suffix_budget`, L124 | equivalent | The routed suffix cost certificate is ported in the oracle-access tests ([access]). |
| `routed_suffix_access`, L145 | equivalent | [prefixResources] supplies canonical availability, typed query inclusion and its naming/routing law; the access tests supply typed routed access. |
| `actual_history`, L167 | equivalent | [bitPlain] retains the two ambient requests and charge 4; its full trace additionally retains the challenge. |
| `informed_actual_history`, L182 | premise-required | P1 retires the prefix verifier's dummy request before the prover's reveal at the seam. [bitInformed] checks reveal/dummy/reveal and charge 7 as additional passive coverage. |
| `setup_budget`, L197 | equivalent | The imported setup cost theorem is ported in the oracle-access tests ([access]). |
| `native_split_history`, L207, passive schedule | equivalent | The all-prover charged runtime/history observation of [appendLaw] is ported in the oracle-access tests ([access]). |
| `native_split_history`, L207, effectful prefix order | premise-required | P1 excludes the prefix verifier's dummy request before the prover's suffix interaction. |
| `native_actual_history`, L227 | equivalent | [bitLog] retains the actual chronological ambient history, answers, final state and charge 4. |
| `informed_native_history`, L235 | premise-required | Same retired dummy-before-reveal order under P1; [bitInformed] is additional coverage. |
| `native_import_budget`, L244 | equivalent | Import-cost reflection is ported in the oracle-access tests ([access]). |
| `fixed_native_resource_bounds`, L258 | equivalent | [prefixResources] supplies canonical prefix availability. The access tests retain the integrated access, cost, history and half-bound conjunction. |
| `informed_cost_does_not_give_half`, L289 | equivalent | Charge seven and success one for the passive schedule are ported together in the oracle-access tests ([access]). |

## Erasure, closing and open interface obligations

[erasure] forgets both logs while retaining the completed oracle observation. The interpreter
and runtime corollaries compose this law with oracle simulation and runtime trace erasure.
[substitution] proves routing for an arbitrary ambient interpreter;
`OracleMap.simulate_withAmbient` specializes it with `QueryImpl.id' ambient`.

[terminalAPI] interprets final decisions with labelled failures and retained answered-query logs.
Its handler has type `QueryImpl ambient (ExceptT ε m)` and it requires only `[Monad m]`.
Its input statement and output-query universes match the full-decision-log interface.
[optionalClosing] states the optional-closing correspondence for the output map and resources
of any completed transcript, with independent input-index, input-query and output-query universes.

The produced provenance obligations are equivalent under the passive schedule. R1 replaces the
separate slot executor with writer-instrumented strategies executed by `TwoParty.Lens.run`.
`OracleVerifier.executeWith` supplies the single interaction/decision sequence for ordinary,
full-trace and ambient-trace execution; both aggregate log APIs project these traces. The
general `SlotInstrumentation.run_natural` law, added next to its use because pinned PolyFun
lacks it, and writer/monad laws give erasure. No provenance disposition changes status.
[trace] supplies ordinary, full-log and ambient-log erasure, ordered per-slot concatenation and interpreter
correspondence. [prefixResources] supplies canonical availability and inclusion. [movedQuery]
checks the distinguishing case: identical transcripts, outputs and aggregate logs, with a query
at different actual prefixes. These facts do not restore verifier queries at intermediate
boundaries. P1 retires those actions and their original phase assignments, as the corresponding
premise-required rows state.

The pre-existing large-query full-log restriction remains recorded in implementation note 18;
`runWithAmbientTrace` retains provenance at independent input-query and oracle-node-query
universes, with erasure to `runWithAmbientLog` and the ordinary run.
`runWithTrace_ambientView` equates its produced slots with the full trace at small universes.
[largeTrace] executes an actual `Nat` oracle node with queries in `Type 1`, reads its sent
payload in the decision, and checks the produced terminal prefix.

The rows above link the access ledger for their full statements, exact targets and passivity
qualifications. Canonical availability uses [prefixResources]; produced phase observations use
[slots] and [trace]. Typed access and whole-run logs remain additional checks.

[faults]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L220
[closing]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L234
[full]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L563
[phases]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L515
[source]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L375
[accepted]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L156
[rejected]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L167
[runtime]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L251
[countSetup]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L406
[countDirect]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L409
[append]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L680
[repeat]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L689
[raw]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L721
[bitLog]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L735
[bitPlain]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L768
[bitInformed]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L745
[bitSplit]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L761
[audit]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L830
[erasure]: ../../../ArkLib/Interaction/Core/Security/Knowledge.lean#L402
[runtimeErasure]: ../../../ArkLib/Interaction/Core/Oracle/LoggedExecution.lean#L49
[terminalAPI]: ../../../ArkLib/Interaction/Core/Oracle/LoggedExecution.lean#L73
[rawHidden]: ../../../ArkLibTest/Interaction/Core/Oracle/Routing.lean#L83
[notHidden]: ../../../ArkLibTest/Interaction/Core/Oracle/Routing.lean#L88
[routePassive]: ../../../ArkLibTest/Interaction/Core/Oracle/Routing.lean#L178
[routeWhole]: ../../../ArkLibTest/Interaction/Core/Oracle/Routing.lean#L275
[payload]: ../../../ArkLib/Interaction/Core/Oracle/Routing.lean#L97
[appendLaw]: ../../../ArkLib/Interaction/Core/Oracle/Routing.lean#L119
[substitution]: ../../../ArkLib/Interaction/Core/Composition.lean#L335
[sourceClosing]: ../../../ArkLibTest/Interaction/Core/Oracle/Routing.lean#L255
[unitRuntime]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L292
[optionalClosing]: ../../../ArkLib/Interaction/Core/Oracle/LoggedExecution.lean#L93
[access]: oracle-access-tests.md

[trace]: ../../../ArkLib/Interaction/Core/Oracle/Provenance.lean
[prefixResources]: ../../../ArkLib/Interaction/Core/Oracle/PrefixResources.lean
[tracePhases]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L901
[actualPrefixes]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L919
[joinPrefix]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1043
[terminalPrefix]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1047
[joinMember]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1036
[terminalMember]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1039
[joinName]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1064
[joinAvailable]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1069
[terminalAvailable]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1080
[phaseSource]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1090
[movedQuery]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L989

[slots]: ../../../ArkLib/Interaction/Core/Oracle/SlotTrace.lean

[largeTrace]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1163

[accessTerminal]: ../../../ArkLibTest/Interaction/Core/Oracle/PhasedRun.lean#L133

[routedAvailable]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L282
[availableCost]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L83

[access-runtime]: oracle-access-tests.md#runtimequerybounds-17-assertions
