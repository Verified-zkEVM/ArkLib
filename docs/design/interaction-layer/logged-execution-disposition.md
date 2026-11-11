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
**child-owned** row is fully expressible with the current interfaces and is ported in the
oracle-access tests ([access]), not here. An **unresolved** row needs a parent interface that
does not exist yet, and names it. Retiring an API name alone does not retire its mathematical
assertions.

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

The base's [erasure] theorem describes a log of the prover interaction and a log of the final
decision. It does not return a list of per-slot phase artifacts. [phases] tests every available
log, the completed prefix's public message/challenge/payload, private output, verdict and digit
state together. It keeps duplicate setup requests. It is additional passive coverage, not a
claim that the old phase list is returned by this API.

| Source assertion | Status | Exact target or remaining obligation |
| --- | --- | --- |
| L84, produced phase owners cannot be replaced | unresolved | Missing Core artifact with intrinsic per-slot owner and prefix fields; the base runner has two query logs but no `phases` field. [phases] does not fill that gap. |
| L91, verifier effects 2 and 3 before challenge, effect 6 on receive | premise-required | P1 retires these non-passive verifier actions at those boundaries. It consequently retires the exact eight-region list and state `2102345678`. |
| L91, setup/prover/decision effects and private output | equivalent | [phases] retains `[9, 9, 1, 4, 5]` and `[2, 3, 6, 7]`, payload 17, private output 23 and verdict 31. The passive order is witnessed by state `2102563478`. |
| L91, remaining per-boundary prefix/owner information | unresolved | Missing Core phase artifact that associates each actual slot with its accumulated full prefix. [phases] only checks the two produced log regions and completed prefix. |
| L114, setup query 9 has multiplicity two | equivalent | [phases] asserts the complete prover log, including both 9s. |
| L121, final prefix has payload 17 | equivalent | [phases] reads 17 from the actual completed transcript. |
| L178, input 7, accepted export 18, sent log and world order | equivalent | [closing] and [faults] retain all these observations together with arbitrary private output. |
| L178, setup/send/reception/terminal phase groups | premise-required | P1 retires the separate effectful verifier reception group `[1]`; it now executes in the final decision with `[2]`. |
| L178, phase artifact for the remaining allowed groups | unresolved | Missing the same produced-prefix phase interface; [terminalAPI] returns terminal query logs, not a per-slot artifact. |
| L194, explicit rejection | equivalent | [faults], third conjunct. |
| L198, explicit fault 17 | equivalent | [faults], first conjunct; rejection is a different constructor. |
| L201, phased closing audit | unresolved | No phase-artifact closing correspondence exists in Core. [audit] checks the available log erasure laws, not that missing correspondence. |
| L202, phased terminal closing audit | unresolved | Same missing phase-artifact terminal correspondence; [terminalAPI] supplies only the terminal failure/log interpreter. |

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
| L125, direct phased adapter agrees with logged runtime | unresolved | Missing Core per-slot phase artifact and its runtime/log correspondence. [runtimeErasure] is not a replacement for this equality. |
| L228, expanded export keeps raw input and both sent answers | equivalent | [append] retains private memory, claim 10, the raw input/prefix/suffix requests, state 3 and the ordered world answers. |
| L263, one export request expands to two raw requests | equivalent | [raw] uses the same logging-after-substitution law and retains both answers. |
| L276, expanded phased/logged runtime correspondence | unresolved | Same missing phase-artifact correspondence; [append] is logged execution only. |
| L285, direct logged erasure audit | equivalent | [erasure] and [audit]. |
| L286, runtime erasure audit | equivalent | [runtimeErasure] and [audit]. |
| L287, logging-after-substitution audit | equivalent | [raw] and [audit] use `OracleComp.withQueryLog_simulateQ`. |
| L288, phased/logged observation audit | unresolved | Missing the phase-artifact log-view law. |

## QueryBounds.lean

Canonical prefix certificates identify available queries and their inclusion across accumulated
contexts. The [payload] law supplies same-run routing evidence. Canonical query names and
join-prefix availability certificates require the open Core interfaces listed below. Typed
access, exact double-read fixtures and cost certificates are ported in the oracle-access tests.

| Source assertion | Status | Exact target or remaining obligation |
| --- | --- | --- |
| `route_cost`, L96 | child-owned | The exact double-read export/cost fixture and bound are ported in the oracle-access tests ([access]). |
| `program_cost`, L117 | child-owned | The authored double-read suffix and its cost bound are ported in the oracle-access tests ([access]). |
| L130, routed weighted cost at most 5 | child-owned | The exact routed cost-five bound is ported in the oracle-access tests ([access]). |
| `routed_available`, L149 | unresolved | Missing Core canonical accumulated-prefix query names, availability and inclusion. The typed routing part is ported in the oracle-access tests. |
| L165, actual raw log old/old/fresh and claim 4 | child-owned | The exact composed logged execution, including the old/old/fresh log, closure and private output, is ported in the oracle-access tests ([access]). |
| `future_rejected`, L184, typed future-slot exclusion | child-owned | Typed exclusion for every prefix program, without a budget restriction, is ported in the oracle-access tests ([access]). |
| `future_rejected`, L184, canonical prefix-context certificate | unresolved | Missing Core canonical prefix query names and context-availability certificates. |
| L209, old canonical name stable, old distinct from fresh | unresolved | Missing Core canonical query names and accumulated-context inclusion. Distinct typed old/fresh slots and repeated use of the old slot are ported in the oracle-access tests. |
| L225, closed execution retains old/old/fresh and private output | child-owned | The exact composed logged execution, closure and private output are ported in the oracle-access tests ([access]). |
| L251, actual join-phase prefix | unresolved | Missing produced per-slot phase prefixes. |
| L252, actual terminal-phase prefix | unresolved | Missing produced per-slot phase prefixes. |
| `joinPhase_mem`, L255 | unresolved | Missing actual phase membership interface. |
| `terminalPhase_mem`, L257 | unresolved | Missing actual phase membership interface. |
| L266, terminal prefix certifies availability and cost 5 | unresolved | Missing Core canonical phase-prefix availability certificates. The cost-five part is ported in the oracle-access tests. |
| L277, old query name survives join-to-terminal inclusion | unresolved | Missing Core canonical names under phase-prefix inclusion. Typed routing is ported in the oracle-access tests. |
| L286, no budget makes fresh slot available at actual join | unresolved | Missing Core availability certificates at produced phase prefixes. Typed exclusion without a budget restriction is ported in the oracle-access tests. |
| L300, phased raw log is old/old/fresh | unresolved | Missing Core phased/logged correspondence. The exact raw log part is ported in the oracle-access tests. |
| L320, routed cost cannot be bounded by 4 | child-owned | The inhabited cost-five witness excluding a bound of four is ported in the oracle-access tests ([access]). |

## RuntimeQueryBounds.lean

The trace equalities below retain actual answers and charges. The passive informed-prover trace
has its reveal before the prefix decision's dummy query. The former dummy-before-reveal schedule
requires a non-passive prefix verifier; this distinction is explicit rather than hidden by
forgetting answers or summing costs.

| Source assertion | Status | Exact target or remaining obligation |
| --- | --- | --- |
| `exported_certificate`, L47 | unresolved | Missing Core canonical prefix availability. Export access and the cost-two certificate are ported in the oracle-access tests. |
| `source_name`, L57 | unresolved | Missing Core canonical accumulated-prefix query names. The actual input index is ported in the oracle-access tests. |
| `first_returns_exported`, L61 | child-owned | The exact decision and output-map/data equations are ported in the oracle-access tests ([access]). |
| `suffixAction_eq`, L72 | child-owned | The exact suffix decision equation is ported in the oracle-access tests ([access]). |
| `suffix_access`, L87 | unresolved | Missing Core canonical prefix availability. Typed source access is ported in the oracle-access tests. |
| `suffix_budget`, L102 | child-owned | The suffix cost certificate is ported in the oracle-access tests ([access]). |
| `routed_suffix_budget`, L124 | child-owned | The routed suffix cost certificate is ported in the oracle-access tests ([access]). |
| `routed_suffix_access`, L145 | unresolved | Missing Core canonical prefix availability. Typed routed access is ported in the oracle-access tests. |
| `actual_history`, L167 | equivalent | [bitPlain] retains the two ambient requests and charge 4; its full trace additionally retains the challenge. |
| `informed_actual_history`, L182 | premise-required | P1 retires the prefix verifier's dummy request before the prover's reveal at the seam. [bitInformed] checks reveal/dummy/reveal and charge 7 as additional passive coverage. |
| `setup_budget`, L197 | child-owned | The imported setup cost theorem is ported in the oracle-access tests ([access]). |
| `native_split_history`, L207, passive schedule | child-owned | The all-prover charged runtime/history observation of [appendLaw] is ported in the oracle-access tests ([access]). |
| `native_split_history`, L207, effectful prefix order | premise-required | P1 excludes the prefix verifier's dummy request before the prover's suffix interaction. |
| `native_actual_history`, L227 | equivalent | [bitLog] retains the actual chronological ambient history, answers, final state and charge 4. |
| `informed_native_history`, L235 | premise-required | Same retired dummy-before-reveal order under P1; [bitInformed] is additional coverage. |
| `native_import_budget`, L244 | child-owned | Import-cost reflection is ported in the oracle-access tests ([access]). |
| `fixed_native_resource_bounds`, L258 | unresolved | Missing Core canonical prefix availability. The integrated expressible access/cost/history/half-bound conjunction is ported in the oracle-access tests. |
| `informed_cost_does_not_give_half`, L289 | child-owned | Charge seven and success one for the passive schedule are ported together in the oracle-access tests ([access]). |

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

Open interface obligations:

- A produced per-slot artifact with intrinsic owners, accumulated full prefixes and membership
  is needed by PhasedRun L84, L91 and L178, and QueryBounds L251, L252, `joinPhase_mem` and
  `terminalPhase_mem`.
- Closing, terminal-closing and logged-runtime correspondences for that phase artifact are
  needed by PhasedRun L201/L202, the persistent-runtime file L125/L276/L288, and QueryBounds L300.
- Canonical accumulated-prefix query names, context availability and inclusion certificates
  are needed by QueryBounds `routed_available`, the canonical-context part of `future_rejected`,
  L209, L266, L277 and L286; and RuntimeQueryBounds `exported_certificate`, `source_name`,
  `suffix_access`, `routed_suffix_access` and `fixed_native_resource_bounds`.

Ports owned by the oracle-access tests:

- The exact double-read export/cost fixture, source and routed cost-five bounds, inhabited
  witness excluding bound four, and actual composed old/old/fresh log with closure and private
  output cover QueryBounds `route_cost`, `program_cost`, L130, L165, L225 and L320. Typed routing,
  distinct old/fresh slots and future-slot exclusion cover the expressible parts of
  `routed_available`, `future_rejected`, L209, L266, L277, L286 and L300.
- Exact decisions and output-map/data equations, typed source/routed access, export cost two,
  suffix cost bounds, setup cost, import-cost reflection and charged passive runtime histories
  cover the expressible parts of RuntimeQueryBounds `exported_certificate`, `source_name`,
  `first_returns_exported`, `suffixAction_eq`, `suffix_access`, `suffix_budget`,
  `routed_suffix_budget`, `routed_suffix_access`, `setup_budget`, `native_split_history` and
  `native_import_budget`. The integrated expressible access/cost/history/half-bound conjunction
  and charge-seven/success-one assertion cover the corresponding parts of
  `fixed_native_resource_bounds` and `informed_cost_does_not_give_half`.

[faults]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L218
[closing]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L231
[full]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L557
[phases]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L510
[source]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L367
[accepted]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L155
[rejected]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L160
[runtime]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L248
[countSetup]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L398
[countDirect]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L401
[append]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L672
[repeat]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L681
[raw]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L713
[bitLog]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L727
[bitPlain]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L760
[bitInformed]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L737
[bitSplit]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L755
[audit]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L825
[erasure]: ../../../ArkLib/Interaction/Core/Security/Knowledge.lean#L388
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
[unitRuntime]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L288
[optionalClosing]: ../../../ArkLib/Interaction/Core/Oracle/LoggedExecution.lean#L93
[access]: oracle-access-tests.md
