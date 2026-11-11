# Logged execution and routing: source-to-port inventory

This inventory compares the frozen acceptance clients with the interaction-layer port on
`feat/interaction-migrate-core`. Source line numbers identify individual declarations, including
assertions formerly grouped under one inline row label. No row labelled unresolved is counted
as a completed port. Related additional coverage is linked even where it does not discharge
that row.

The two approved premises are:

- **P1 (passivity):** verifiers send public-coin challenges only, and resource queries occur in
  the final decision. A challenge cannot be computed from an input or previously sent oracle.
- **P2 (shape):** neither a challenge nor an oracle payload selects the protocol's subtree.

An equivalent row preserves the stated mathematical observation. A premise-required row states
exactly which assertion P1 or P2 retires. An unresolved row names the interface or outstanding
port it needs. Retiring an API name alone does not retire its mathematical assertions.

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
| L87, closing an optional terminal verdict | unresolved | The base has no `TerminalRun.closed_of_ofOption` counterpart relating returned explicit terminal faults to its optional runner. [terminalAPI] retains target-monad failures, but does not claim that missing generic correspondence. |

The old reception action 1 now belongs to the decision. Its execution between send and terminal
is a **premise-required** retirement under P1; preservation of the chronological history above
does not assert preservation of the former reception phase boundary.

## RuntimeExample.lean

| Source assertion | Status | Exact target or remaining obligation |
| --- | --- | --- |
| L24, private output, final count 10 and three ordered requests | equivalent | [runtime] retains the arbitrary private output and the full counted trace. |
| L24, ambient `Nat → Unit` responses in the exact runtime trace | unresolved | [runtime] uses `Nat → Nat` counter answers. The unit-response fixture itself has not been ported; no response-erasing adapter is counted as its port. |

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

These entries prevent the earlier inline labels from counting result equality as a port of a
resource-availability certificate. The relevant VCVio cost laws exist; the missing pieces for
prefix certificates are in Core. The [payload] law is useful same-run routing evidence, but
it does not produce canonical query names or a join-prefix availability certificate.

| Source assertion | Status | Exact target or remaining obligation |
| --- | --- | --- |
| `route_cost`, L96 | unresolved | The exact double-read export/cost fixture is not ported; [repeat] uses one prefix decision read and one export read instead. |
| `program_cost`, L117 | unresolved | Requires the same unported authored double-read suffix and its cost model. |
| L130, routed weighted cost at most 5 | unresolved | Same missing fixture port; VCVio's generic cost-substitution theorem alone is not this assertion. |
| `routed_available`, L149 | unresolved | Missing accumulated-prefix canonical query names/availability and their inclusion law in Core. |
| L165, actual raw log old/old/fresh and claim 4 | unresolved | [repeat] has that source projection and claim, but a different authored export and an extra ambient request 3; not counted equivalent. |
| `future_rejected`, L184 | unresolved | Missing the typed join-prefix availability/cost certificate interface; [payload] cannot certify rejection of a future slot. |
| L209, old canonical name stable, old distinct from fresh | unresolved | Missing Core canonical query names and accumulated-context inclusion. |
| L225, closed execution retains old/old/fresh and private output | unresolved | Same unported exact double-read fixture as L165; [repeat] is additional coverage. |
| L251, actual join-phase prefix | unresolved | Missing produced per-slot phase prefixes. |
| L252, actual terminal-phase prefix | unresolved | Missing produced per-slot phase prefixes. |
| `joinPhase_mem`, L255 | unresolved | Missing actual phase membership interface. |
| `terminalPhase_mem`, L257 | unresolved | Missing actual phase membership interface. |
| L266, terminal prefix certifies availability and cost 5 | unresolved | Missing canonical phase-prefix certificates and the exact double-read cost fixture. |
| L277, old query name survives join-to-terminal inclusion | unresolved | Missing Core canonical names and phase-prefix inclusion; [payload] preserves actual payloads but not this assertion. |
| L286, no budget makes fresh slot available at actual join | unresolved | Missing phase-prefix availability certificate; no narrowing to a particular budget is claimed. |
| L300, phased raw log is old/old/fresh | unresolved | Missing phased/logged correspondence and the exact double-read fixture. |
| L320, routed cost cannot be bounded by 4 | unresolved | Exact double-read route/cost witness remains unported. |

## RuntimeQueryBounds.lean

The trace equalities below retain actual answers and charges. The passive informed-prover trace
has its reveal before the prefix decision's dummy query. The former dummy-before-reveal schedule
requires a non-passive prefix verifier; this distinction is explicit rather than hidden by
forgetting answers or summing costs.

| Source assertion | Status | Exact target or remaining obligation |
| --- | --- | --- |
| `exported_certificate`, L47 | unresolved | Missing Core canonical prefix availability; the exact authored export/cost certificate remains unported. |
| `source_name`, L57 | unresolved | Missing canonical accumulated-prefix query naming. |
| `first_returns_exported`, L61 | unresolved | [appendLaw] keeps the same-run output map but no equality for this exact authored export is yet tested. |
| `suffixAction_eq`, L72 | unresolved | The passive final decision exists in the fixture, but this exact source-program equality is not ported. |
| `suffix_access`, L87 | unresolved | Missing canonical prefix availability. |
| `suffix_budget`, L102 | unresolved | The exact suffix-program cost certificate remains unported; [bitLog] only checks actual costs. |
| `routed_suffix_budget`, L124 | unresolved | The exact routed cost certificate remains unported; [substitution] is semantic routing, not a cost bound. |
| `routed_suffix_access`, L145 | unresolved | Missing canonical prefix availability. |
| `actual_history`, L167 | equivalent | [bitPlain] retains the two ambient requests and charge 4; its full trace additionally retains the challenge. |
| `informed_actual_history`, L182 | premise-required | P1 retires the prefix verifier's dummy request before the prover's reveal at the seam. [bitInformed] checks reveal/dummy/reveal and charge 7 as additional passive coverage. |
| `setup_budget`, L197 | unresolved | The exact imported setup cost-bound theorem remains unported. |
| `native_split_history`, L207 | unresolved | [appendLaw] is generic open-program equality, but the all-prover charged runtime observation of this exact fixture has not been stated. |
| `native_actual_history`, L227 | equivalent | [bitLog] retains the actual chronological ambient history, answers, final state and charge 4. |
| `informed_native_history`, L235 | premise-required | Same retired dummy-before-reveal order under P1; [bitInformed] is additional coverage. |
| `native_import_budget`, L244 | unresolved | Missing this fixture's imported cost-reflection certificate, not supplied by the trace observation alone. |
| `fixed_native_resource_bounds`, L258 | unresolved | Missing canonical prefix availability, fixture cost certificates, and the integrated exact-experiment half-bound theorem on this branch. None is replaced by a trace equality. |
| `informed_cost_does_not_give_half`, L289 | unresolved | The actual passive trace/charge is tested by [bitInformed]; the exact integrated success-one/security assertion has not been ported here. |

## Ownership and open obligations

The duplicate `OracleVerifier.runWithLog_erase` was removed. Both interpreter and runtime
corollaries now use [erasure] directly. The per-query routing proof lives in [substitution];
`OracleMap.simulate_withAmbient` specializes it with `QueryImpl.id' ambient`.

[terminalAPI] is new and imposes no lawful-monad or inhabited-error premise. Its input statement
and output-query universes match the base's full-decision-log interface. It interprets existing
`OracleVerifier.decide` programs; it does not introduce a competing ambient-log runner or law.
No existing public signature was narrowed. The generic `simulate_withAmbient` signature is
unchanged; its proof is now a specialization. The interpreter/runtime erasure corollaries retain
their previous signatures. The removed alias had exactly the base erasure law
`Sigma.fst <$> V.runWithLog stmt data prover = V.run stmt data prover`.

The new signature is
`decideWithFailureLog V handler stmt p view data :
m (Except ε (Option (T p)) × QueryLog (ambient + (pathResources inputs s p).spec))`.
Here `handler : QueryImpl ambient (ExceptT ε m)` and only `[Monad m]` is needed.

The migration remains **blocked**. In particular, the produced phase-prefix/owner artifact and
canonical prefix-availability interfaces are absent from the stack parent. The exact weighted
query clients and integrated resource/security certificates listed above also remain unported.
They must be supplied or explicitly descoped by a maintainer decision; final payload routing,
flattened traces, and a changed fixture are not counted as proofs of them. No generic prefix or
phase dependency has been stubbed or re-proved locally.

[faults]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L218
[closing]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L231
[full]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L508
[phases]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L461
[source]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L318
[accepted]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L155
[rejected]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L160
[runtime]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L248
[countSetup]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L349
[countDirect]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L352
[append]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L623
[repeat]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L632
[raw]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L664
[bitLog]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L678
[bitPlain]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L711
[bitInformed]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L688
[bitSplit]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L706
[audit]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L776
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
