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
**child-owned** row delegates its expressible contract to the exact row of the
oracle-access ledger ([access]), which supplies the test or stronger owner theorem. The target
may reuse a parent-owned law. For compound assertions the unresolved component is indexed
separately; delegation never counts that component as ported. An **unresolved** row names the
parent interface that is still missing. Retiring an API name alone does not retire its mathematical
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

The [access ledger's PhasedRun table][access-phases] is the authoritative disposition for the
seven frozen assertions L84–L198. The index below separates expressible observations,
passivity-required scheduling changes and unresolved phase artifacts; each entry links its
full disposition and exact target. The base's two query logs are not a per-slot phase artifact.

| Source component | Status | Full disposition |
| --- | --- | --- |
| L84, intrinsic phase owners | unresolved | Produced owner/prefix artifact: [row 1][ap1]. |
| L91, non-passive verifier placements | premise-required | [Row 2][ap2]. |
| L91, passive effects and outputs | equivalent | [Row 2][ap2]. |
| L91, allowed slot prefixes/owners | unresolved | Produced owner/prefix artifact: [row 2][ap2]. |
| L114, duplicate setup queries | child-owned | [Row 3][ap3]. |
| L114, separately selectable setup phase | unresolved | Produced phase artifact: [row 3][ap3]. |
| L121, retained final payload | child-owned | [Row 4][ap4]. |
| L178, closure and query histories | equivalent | [Row 5][ap5]. |
| L178, former effectful reception group | premise-required | [Row 5][ap5]. |
| L178, allowed phase groups | unresolved | Produced owner/prefix artifact: [row 5][ap5]. |
| L194, explicit rejection | child-owned | [Row 6][ap6]. |
| L198, fault 17 distinct from rejection | child-owned | [Row 7][ap7]. |

The two diagnostic closing audits are outside the access ledger's seven assertion rows:

| Source audit | Status | Remaining interface |
| --- | --- | --- |
| L201, phased closing audit | unresolved | Phase artifact and closing law. |
| L202, phased terminal closing audit | unresolved | Phase artifact and terminal-closing law. |

The existing [terminal interpreter][terminalAPI] preserves labelled faults and answered-query
logs, while the linked child port additionally retains the actual transcript and prover log.
It does not supply the unresolved per-slot phase artifact or its closing laws.

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

The [access ledger's QueryBounds table][access-queries] holds the complete dispositions,
including every exact test/theorem target. This index records ownership and the missing
interface for each unresolved component, without repeating that full account.

| Source component | Status | Full disposition |
| --- | --- | --- |
| L96, route_cost | child-owned | [Row 1][aq1]. |
| L117, program_cost | child-owned | [Row 2][aq2]. |
| L130, routed cost five | child-owned | [Row 3][aq3]. |
| L149, typed routed access | child-owned | [Row 4][aq4]. |
| L149, canonical availability | unresolved | Prefix names/availability/inclusion: [row 4][aq4]. |
| L165, actual old/old/fresh log and claim | child-owned | [Row 5][aq5]. |
| L184, typed future exclusion | child-owned | [Row 6][aq6]. |
| L184, canonical prefix certificate | unresolved | Prefix names and availability: [row 6][aq6]. |
| L209, typed old/fresh identity | child-owned | [Row 7][aq7]. |
| L209, canonical old/fresh names | unresolved | Prefix names and inclusion: [row 7][aq7]. |
| L225, closed output and repeated log | child-owned | [Row 8][aq8]. |
| L251, actual join prefix | unresolved | Produced per-slot prefix artifact: [row 9][aq9]. |
| L252, actual terminal prefix | unresolved | Produced per-slot prefix artifact: [row 10][aq10]. |
| L255, joinPhase_mem | unresolved | Produced phase membership: [row 11][aq11]. |
| L257, terminalPhase_mem | unresolved | Produced phase membership: [row 12][aq12]. |
| L266, typed access and cost five | child-owned | [Row 13][aq13]. |
| L266, actual terminal availability | unresolved | Phase-prefix availability: [row 13][aq13]. |
| L277, typed old-slot routing | child-owned | [Row 14][aq14]. |
| L277, canonical name under inclusion | unresolved | Prefix names/inclusion: [row 14][aq14]. |
| L286, typed future exclusion | child-owned | [Row 15][aq15]. |
| L286, actual join availability | unresolved | Produced prefix and availability: [row 15][aq15]. |
| L300, exact raw log | child-owned | [Row 16][aq16]. |
| L300, phased/logged equality | unresolved | Phase/log correspondence: [row 16][aq16]. |
| L320, cost four impossible | child-owned | [Row 17][aq17]. |

## RuntimeQueryBounds.lean

The [access ledger's runtime table][access-runtime] holds the complete dispositions and exact
counterparts. Passivity excludes the old dummy-before-reveal prefix order; it does not exclude
canonical prefix certificates. The latter components remain unresolved in both ledgers.

| Source component | Status | Full disposition |
| --- | --- | --- |
| L47, typed export access/cost | child-owned | [Row 1][ar1]. |
| L47, canonical export availability | unresolved | Canonical prefix availability: [row 1][ar1]. |
| L57, actual input query | child-owned | [Row 2][ar2]. |
| L57, canonical source name | unresolved | Canonical prefix names: [row 2][ar2]. |
| L61, decision and output-map equations | child-owned | [Row 3][ar3]. |
| L72, suffix equation | child-owned | [Row 4][ar4]. |
| L87, typed suffix permission | child-owned | [Row 5][ar5]. |
| L87, canonical suffix availability | unresolved | Canonical prefix availability: [row 5][ar5]. |
| L102, suffix cost | child-owned | [Row 6][ar6]. |
| L124, routed suffix cost | child-owned | [Row 7][ar7]. |
| L145, typed raw access | child-owned | [Row 8][ar8]. |
| L145, canonical raw availability | unresolved | Canonical prefix availability: [row 8][ar8]. |
| L167, actual guessing history | equivalent | [Row 9][ar9]. |
| L182, old informed ordering | premise-required | [Row 10][ar10]. |
| L197, setup cost | child-owned | [Row 11][ar11]. |
| L207, all-prover passive split | child-owned | [Row 12][ar12]. |
| L207, effectful prefix ordering | premise-required | [Row 12][ar12]. |
| L227, logged guessing history | equivalent | [Row 13][ar13]. |
| L235, old informed ordering | premise-required | [Row 14][ar14]. |
| L244, import-cost reflection | child-owned | [Row 15][ar15]. |
| L258, expressible joint half bound | child-owned | [Row 16][ar16]. |
| L258, canonical joint availability | unresolved | Canonical prefix availability: [row 16][ar16]. |
| L289, passive charge seven/success one | child-owned | [Row 17][ar17]. |
| L289, old informed ordering | premise-required | [Row 17][ar17]. |

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

The delegated rows above link the access ledger for their full statements, exact targets,
passivity qualifications and unresolved components. No typed-access test is counted as the
missing canonical prefix-availability interface, and no whole-run log is counted as a produced
per-slot phase artifact.

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

[access-phases]: oracle-access-tests.md#phasedrun-7-assertions
[access-queries]: oracle-access-tests.md#querybounds-17-assertions
[access-runtime]: oracle-access-tests.md#runtimequerybounds-17-assertions
[ap1]: oracle-access-tests.md#p1
[ap2]: oracle-access-tests.md#p2
[ap3]: oracle-access-tests.md#p3
[ap4]: oracle-access-tests.md#p4
[ap5]: oracle-access-tests.md#p5
[ap6]: oracle-access-tests.md#p6
[ap7]: oracle-access-tests.md#p7
[aq1]: oracle-access-tests.md#q1
[aq2]: oracle-access-tests.md#q2
[aq3]: oracle-access-tests.md#q3
[aq4]: oracle-access-tests.md#q4
[aq5]: oracle-access-tests.md#q5
[aq6]: oracle-access-tests.md#q6
[aq7]: oracle-access-tests.md#q7
[aq8]: oracle-access-tests.md#q8
[aq9]: oracle-access-tests.md#q9
[aq10]: oracle-access-tests.md#q10
[aq11]: oracle-access-tests.md#q11
[aq12]: oracle-access-tests.md#q12
[aq13]: oracle-access-tests.md#q13
[aq14]: oracle-access-tests.md#q14
[aq15]: oracle-access-tests.md#q15
[aq16]: oracle-access-tests.md#q16
[aq17]: oracle-access-tests.md#q17
[ar1]: oracle-access-tests.md#r1
[ar2]: oracle-access-tests.md#r2
[ar3]: oracle-access-tests.md#r3
[ar4]: oracle-access-tests.md#r4
[ar5]: oracle-access-tests.md#r5
[ar6]: oracle-access-tests.md#r6
[ar7]: oracle-access-tests.md#r7
[ar8]: oracle-access-tests.md#r8
[ar9]: oracle-access-tests.md#r9
[ar10]: oracle-access-tests.md#r10
[ar11]: oracle-access-tests.md#r11
[ar12]: oracle-access-tests.md#r12
[ar13]: oracle-access-tests.md#r13
[ar14]: oracle-access-tests.md#r14
[ar15]: oracle-access-tests.md#r15
[ar16]: oracle-access-tests.md#r16
[ar17]: oracle-access-tests.md#r17
