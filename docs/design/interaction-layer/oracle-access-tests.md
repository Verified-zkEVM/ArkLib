# Oracle test dispositions

This reference accounts for all 89 frozen assertions in the seven files below. The eight
interaction layer modules port these files; `QueryCost.lean` collects cost and profile assertions
from `QueryBounds`, `RuntimeQueryBounds` and `PhasedRun`, rather than porting an eighth source file.
Row numbers follow frozen declaration order, including the universe canaries. Helper definitions
and diagnostic axiom-print commands are not additional assertions.

This document holds the full dispositions for the overlapping PhasedRun, QueryBounds and
RuntimeQueryBounds rows. The [parent inventory][parent-inventory] indexes the same contracts.
Each row has exactly one status: **equivalent**, **premise-required**, **retired**, or
**unresolved**. Equivalent preserves the observation and its quantifiers. Premise-required names
P1 or P2 and the assertion it retires. Retired names a removed mechanism. Unresolved names a
missing parent interface. Parent-owned results are linked directly rather than copied.

The approved premises are **P1**, public-coin challenges with resource queries confined to the
final decision, and **P2**, subtree selection independent of challenges and oracle payloads.
P1 permits distributions depending on earlier public challenges and prover messages.

## PhasedRun: 7 assertions

| Frozen row | Contract | Disposition and evidence |
|---|---|---|
| <a id="p1"></a>[1][fp1] | Intrinsic phase owners | equivalent: [produced slots][slot-api] derive owners from the executed participant; [phase_trace_contract][p-trace] checks them. |
| <a id="p2"></a>[2][fp2] | State, owners, order | premise-required: P1 retires verifier actions 2/3 before the challenge and 6 at reception. [phase_trace_contract][p-trace] retains all tags, passive groups and state; [actual_phase_prefixes][p-prefixes] retains the actual moves. |
| <a id="p3"></a>[3][fp3] | Setup count | equivalent: [setup_phase_trace_contract][p-setup-trace] records a separate setup slot with both query 9 entries. |
| <a id="p4"></a>[4][fp4] | Final payload | equivalent: [run][p-accept], [lookup][p-payload], [actual_phase_prefixes][p-prefixes]. |
| <a id="p5"></a>[5][fp5] | Closing, log, groups | premise-required: P1 retires reception effect 1 as a separate verifier group. [closure/log][p-close] and [terminal outcomes][p-terminal] retain the actual outputs and histories; [trace erasure and setup/log laws][trace-api] preserve the remaining groups and closing. |
| <a id="p6"></a>[6][fp6] | Explicit rejection | equivalent: [terminal outcomes][p-terminal]. |
| <a id="p7"></a>[7][fp7] | Fault 17, not rejection | equivalent: [terminal outcomes][p-terminal]. |

The parent's produced trace supplies the phase artifact, including owners, full prefixes,
membership and ordered query groups. `OracleVerifier.executeWith` runs the interaction and final
decision; `observeInteraction` instruments strategies run by `TwoParty.Lens.run`.
`runWithSetupTrace` preserves independently selectable setup, and `runWithSetupTrace_logView`
relates its log to the ordinary logged execution. These are parent declarations, not a second
executor in these tests.

For row 2, passivity changes ambient order `[9, 9, 1, 2, 3, 4, 5, 6, 7]` to
`[9, 9, 1, 4, 5, 2, 3, 6, 7]`. [phase_trace_contract][p-trace] checks state `2102563478`
and the produced passive groups; [actual_phase_prefixes][p-prefixes] checks the challenge and
payload values in their actual prefixes. The local [accepting run][p-accept] independently
quantifies payload, private output and challenge.

Row 5 retains input 7, accepted target 11, materialized answer 18, sent-answer log and ambient
history `[9, 0, 1, 2]`. P1 moves reception effect 1 into the final decision with effect 2.
The remaining phase observations are equivalent through `runWithTrace_logView`,
`runWithTrace_erase` and `simulateQ_runWithTrace_logView` in [Provenance][trace-api]. The closing
audits at L201/L202 have those same exact targets in the [parent inventory][parent-phase-audits].

Rows 6–7 use the same actual closing prover and final decision interpreter. The new port first
runs the prover and captures the completed transcript, private output and prover query log,
then calls `OracleVerifier.decideWithFailureLog` on those actual payloads and input data.
The ambient handler returns fault 17 as `Except.error 17`; rejection is `Except.ok none`, and
acceptance is `Except.ok (some (message, old + message))`. All three outcomes retain the same
transcript, arbitrary hidden private output, prover log, decision query-answer log and history
`[9, 0, 1, 2]`. The unanswered failing request adds no query-answer entry. The sent answer is
read before that failure, and acceptance closes with the same run's actual input and message.
No fault is encoded as an accepted value, and `OracleVerifier.decide` is unchanged.

## Prefix: 8 assertions

| Frozen row | Contract | Disposition and evidence |
|---|---|---|
| [1][fx1] | Shared structural cursor | equivalent: [shared spine][x-cursor]. |
| [2][fx2] | Different execution prefixes | equivalent: [distinct full moves][x-distinct]. |
| [3][fx3] | The crossed send is available | equivalent: [crossed-send query][x-query]; `FullPrefix.Index`, `name` and `Available` in [PrefixResources][prefix-api] identify the crossed occurrence. |
| [4][fx4] | The root cannot access that send | equivalent: [empty prefix has no slot][x-no-slot]; `FullPrefix.Index` at `.here` is empty in [PrefixResources][prefix-api]. |
| [5][fx5] | An empty-payload send permits a root prefix | equivalent: [root moves][x-empty-root]. |
| [6][fx6] | No realization crosses an empty send | equivalent: [crossed moves][x-empty-moves]. |
| [7][fx7] | Prefix length two | equivalent: [length][x-length], [completion][x-complete]. |
| [8][fx8] | The first hidden realization is true | equivalent: [full prefix payload][x-payload]. |

Rows 3–4 use the parent's canonical `FullPrefix` interface in [PrefixResources][prefix-api].
`Index` at an empty prefix is empty, while crossing an oracle send adds its canonical occurrence;
`Available` is existence of an index with that occurrence's `name`. `Available.mono` preserves
availability under full-prefix extension. The [prefix append identity][x-prefix] identifies the
boundary immediately after the send, and [crossed-send query][x-query] reads its own payload
without choosing the future public message. [Completed-path lookup][x-sent] checks that payload
for every later choice. [AccessExample 3][a-unsent] and [4][a-sent] check the typed access boundary.

## QueryBounds: 17 assertions

| Frozen row | Contract | Disposition and evidence |
|---|---|---|
| <a id="q1"></a>[1][fq1] | Per-query cost | equivalent: [route_cost][c-route]. |
| <a id="q2"></a>[2][fq2] | Source cost five | equivalent: [program_cost][c-program]. |
| <a id="q3"></a>[3][fq3] | Routed cost five | equivalent: [routed_cost][c-routed]. |
| <a id="q4"></a>[4][fq4] | Available queries | equivalent: [routed_available][q-available] certifies canonical availability at the actual terminal phase. |
| <a id="q5"></a>[5][fq5] | Old/old/fresh log | equivalent: [actual logged run][q-log]. |
| <a id="q6"></a>[6][fq6] | Future exclusion | equivalent: [exclusion][q-future] for every prefix program; [joinPhase_availability][q-join-available] excludes the canonical future occurrence at the produced join. |
| <a id="q7"></a>[7][fq7] | Old/fresh identities | equivalent: [typed identity][q-repeat], [joinPhase_name][q-join-name] and [terminalPhase_availability][q-terminal-available]. |
| <a id="q8"></a>[8][fq8] | Closing keeps the log | equivalent: [closed run log][q-log]. |
| <a id="q9"></a>[9][fq9] | Produced join prefix | equivalent: [joinPhase_prefix][q-join-prefix]. |
| <a id="q10"></a>[10][fq10] | Terminal prefix | equivalent: [terminalPhase_prefix][q-terminal-prefix]. |
| <a id="q11"></a>[11][fq11] | Join membership | equivalent: [joinPhase_mem][q-join-member]. |
| <a id="q12"></a>[12][fq12] | Terminal membership | equivalent: [terminalPhase_mem][q-terminal-member]. |
| <a id="q13"></a>[13][fq13] | Availability/cost | equivalent: [routed_available_and_cost][q-available-cost] certifies the same routed program at the produced terminal phase with cost five. |
| <a id="q14"></a>[14][fq14] | Name inclusion | equivalent: [joinPhase_name][q-join-name]; `contextInclusion_name`, `includeQuery_name` and `familyInclusion_query` in [PrefixResources][prefix-api] preserve names, query arguments and routing. |
| <a id="q15"></a>[15][fq15] | Join exclusion | equivalent: [joinPhase_availability][q-join-available] excludes the future occurrence regardless of budget; [exclusion][q-future] proves the typed program law. |
| <a id="q16"></a>[16][fq16] | Phased log | equivalent: [phase_source_log_contract][q-phase-source] and `simulateQ_runWithTrace_logView` in [Provenance][trace-api]. |
| <a id="q17"></a>[17][fq17] | Four is insufficient | equivalent: [cost-five path][c-lower]. |

Rows 5 and 8 use the actual `composed.runWithLog`. For every `a` and `b`, the doubled export
records two prefix-slot entries with answer `a`, then the suffix-slot entry with answer `b`.
The same assertion checks private output `a + b` and verdict `some (a + a + b)`.
The [one/two specialization][q-concrete-log] recovers private output 3 and accepted result 4.
Output closing uses those same resources; this fixture's output family is empty.

Rows 9–12, 14–16 reuse the parent's `LoggedExecutionTests` produced two-oracle execution.
Its `joinPhase_mem`, `terminalPhase_mem`, `joinPhase_prefix`, `terminalPhase_prefix`,
`phase_intrinsic_owners`, `joinPhase_name`, `joinPhase_availability`,
`terminalPhase_availability` and `phase_source_log_contract` already prove the frozen
observations. The join is the first suffix prover slot. P1 retires the old verifier decision
at that seam, while preserving its prefix and membership. No duplicate assertions or executor
are introduced here. `runWithTrace_logView` and `simulateQ_runWithTrace_logView` give the
phase/log correspondence for every prover, including this branch's composed verifier.

The additional [routed_available][q-available] and [joint certificate][q-available-cost] cover
this branch's exact doubled-export program. `traced a b` comes from `composed.runWithTrace`;
`rawAvailable` matches each raw query's canonical completed-prefix name with a resource in that
execution's actual terminal phase. This couples availability to the same program as the cost-five
bound. The [run transcript][q-run], [split payloads][q-split], [prefix payload][q-prefix-payload]
and [suffix payload][q-suffix-payload] remain additional checks.

## RuntimeQueryBounds: 17 assertions

| Frozen row | Contract | Disposition and evidence |
|---|---|---|
| <a id="r1"></a>[1][fr1] | Export access | equivalent: [access][r-export], [cost][c-input-cost], and the input case of `FullPrefix.queryName` in [PrefixResources][prefix-api]. |
| <a id="r2"></a>[2][fr2] | Source name | equivalent: [typed input query][r-input]; `FullPrefix.queryName` names every input query by its input index. |
| <a id="r3"></a>[3][fr3] | Dummy and export | equivalent: [decision][r-pre], [map][r-map]. |
| <a id="r4"></a>[4][fr4] | Suffix equation | equivalent: [decision][r-decide], [data][r-output]. |
| <a id="r5"></a>[5][fr5] | Suffix permissions | equivalent: [typed][r-access] and the input naming/inclusion laws in [PrefixResources][prefix-api]. |
| <a id="r6"></a>[6][fr6] | Suffix cost five | equivalent: [suffix_budget][c-suffix]. |
| <a id="r7"></a>[7][fr7] | Routed cost five | equivalent: [routed bound][c-suffix-routed]. |
| <a id="r8"></a>[8][fr8] | Raw permissions | equivalent: [typed][r-raw-access] and `contextInclusion_name` in [PrefixResources][prefix-api]. |
| <a id="r9"></a>[9][fr9] | Guess history | equivalent: ambient history, [charged run][c-history]. |
| <a id="r10"></a>[10][fr10] | Informed order | premise-required: P1 retires dummy-before-reveal order; [passive split][p-informed-split]. |
| <a id="r11"></a>[11][fr11] | Setup import cost | equivalent: [setup_budget][c-setup]. |
| <a id="r12"></a>[12][fr12] | Generic runtime split | premise-required: P1 retires effectful-prefix order; [all-prover passive law][run-append]. |
| <a id="r13"></a>[13][fr13] | Logged guess history | equivalent: ambient projection, [log][p-guess-log]. |
| <a id="r14"></a>[14][fr14] | Logged informed order | premise-required: P1 retires dummy-before-reveal order; [passive log][p-informed-log]. |
| <a id="r15"></a>[15][fr15] | Run import cost | equivalent: [import_budget][c-import]. |
| <a id="r16"></a>[16][fr16] | Joint half bound | equivalent: [joint][c-joint] with the input naming/inclusion laws in [PrefixResources][prefix-api]. |
| <a id="r17"></a>[17][fr17] | Charge 7, success 1 | premise-required: P1 retires dummy-before-reveal order; [passive charge and success][c-informed]. |

Rows 1, 2, 5, 8 and 16 use the input case of the parent's `FullPrefix.queryName`,
`contextInclusion_name` and `includeName` in [PrefixResources][prefix-api]. The prefix has no
sent oracle: its export reads only its input, whose canonical name is `.inl` of that same input
index at every prefix. The inclusion keeps that input index unchanged. The linked access and
cost tests quantify over every relevant path and view and use precisely that input query.

Row 3's decision performs the dummy request and accepts the unit statement; its output map is
exactly the input projection. Row 4 checks the entire effectful decision and the output map on
arbitrary resource data. The [routed export query][r-route] identifies the input slot used by
the cost theorem. Thus the delegated exact-decision and output-map obligations have actual
counterparts, with canonical input naming supplied by the parent.

For rows 9 and 13, the full trace includes a challenge event. Its ambient projection is exactly
`[false ↦ false, true ↦ hidden]`, final state is `(hidden, 2)` and charge is four. The
[parent split check][p-guess-split] and direct logged check retain that same ambient history.
Row 12's passive-schedule counterpart is the general whole-prover
`OracleVerifier.run_append`, with its [ordinary-import client][p-general-split]. It quantifies
over arbitrary whole provers, not just the guessing and informed examples. Applying runtime
execution and the pure state/trace/charge observation to this open-program equality proves the
charged runtime/history equality for every such prover. The exact target is the stronger
[open-program split law][run-append]; no two-prover specialization is counted as the all-prover
port. Its frozen effectful-prefix order is separately excluded by passivity.

For rows 10, 14 and 17, the informed prover reveals at the seam before the passive prefix's
dummy request. Ambient order is `[true ↦ hidden, false ↦ false, true ↦ hidden]`; frozen order
was `[false ↦ false, true ↦ hidden, true ↦ hidden]`. Both have final state `(hidden, 3)` and
charge seven. The old dummy-before-reveal order requires a non-passive prefix verifier and is
premise-required to change; it is not an unresolved allowed-phase interface. The additional
passive history is not an equivalent assertion of the former order.

The row-16 conjunction includes the exact prefix decision and export, typed access and cost
certificates, import budget, charged history and the half bound for every fixed guess and
secret. [Actual answers][r-guess-answers] retain the materialized output oracle and target;
[guess_success][r-guess-success] proves probability exactly one half. This expressible
conjunction uses the parent's canonical input naming and inclusion laws described above.
The row-17 passive conjunction retains charge seven and [success one][r-informed-success],
with its different order explicit and its [actual answer observation][r-informed-answers].
Neither theorem derives arbitrary-prover security from access/cost certificates alone.

## AccessExample: 18 assertions

| Frozen row | Contract | Disposition and evidence |
|---|---|---|
| [1][fa1] | Before false send: inputs only | equivalent: [no sent slot][a-before-f]. |
| [2][fa2] | Before true send: inputs only | equivalent: [no sent slot][a-before-t]. |
| [3][fa3] | Unsent query rejected by typing | equivalent: [negative client][a-unsent]. |
| [4][fa4] | Same resource available after send | equivalent: [positive client][a-sent]. |
| [5][fa5] | False-branch response is Bool | equivalent: [response type][a-bool]. |
| [6][fa6] | True-branch response is Fin 3 | equivalent: [response type][a-fin]. |
| [7][fa7] | Inputs and one sent slot | retired: literal `Access.extend` index layout; [slot indices][a-slots] retain the input-plus-one-payload count. |
| [8][fa8] | Access restriction/rebuild | retired: stored `AccessDecoration.restrict_build`; [independent future][a-future] retains payload-independent shape. |
| [9][fa9] | Different full execution paths | equivalent: [distinct payloads][a-distinct]. |
| [10][fa10] | Access depends only on shape | equivalent: [shape][a-shape], [family][a-family]. |
| [11][fa11] | Terminal send available | retired: literal `Access.extend` index layout; [terminal slots][a-terminal] retain terminal availability. |
| [12][fa12] | Non-faithful terminal response is Nat | equivalent: [response type][a-nat]. |
| [13][fa13] | Route input 7 and sent 11 | equivalent: [sum eighteen][a-route], all hidden values. |
| [14][fa14] | Hidden pair coordinate is unobservable | equivalent: [handler equality][a-hidden]. |
| [15][fa15] | Second send unavailable | equivalent: [negative client][a-missing-second]. |
| [16][fa16] | Second slot after two sends | equivalent: [second answer][a-second]. |
| [17][fa17] | Large message universe | equivalent: [independent universes][a-large-data]. |
| [18][fa18] | Large query universe | equivalent: [independent universes][a-large-query]. |

Rows 7 and 11 retain the input-plus-one-payload slot count. They do not assert literal equality
with the old `Access.extend` query-index layout `Unit ⊕ Unit`: the interaction layer uses family
indices and sigma-indexed interface queries, and heterogeneous resources keep their data as a
pair. The [one-slot uniqueness test][a-single] rules out an extra sent slot. Row 8 retains
payload-independent future selection, but `AccessDecoration.restrict_build` was an identity of
stored per-node access decorations. There is no such decoration to restrict or rebuild now;
`pathResources` computes resources from a completed shape and composition routes them explicitly.

Rows 17–18 quantify over every message type, interface and initial polynomial at the exact
frozen instantiations. Row 17 uses `OracleInterface.{1, 0}` on `Messages : Type 1` and initial
and result `PFunctor.{0, 1}`. Row 18 uses `OracleInterface.{0, 1}` on `Messages : Type` and
initial and result `PFunctor.{1, 0}`. [Resources.sum][resource-sum] extends an arbitrary prior
query handler with the given interface and its message realization. Neither test restricts the
prior polynomial, replaces a family with a constant, or uses a universe lift. These tests cover
resource extension; DecorationExample 2 separately checks interfaces inside protocol oracle nodes.

## DecorationExample: 13 assertions

| Frozen row | Contract | Disposition and evidence |
|---|---|---|
| [1][fd1] | Role decorations at arbitrary tree universe | retired: no authored role decoration. |
| [2][fd2] | Raw oracle/query universes | equivalent: [independent universes][d-protocol], [actual unequal-universe node and path resources][d-node]. |
| [3][fd3] | Protocol bundle at arbitrary universe | equivalent: [protocol canary][d-protocol]. |
| [4][fd4] | Receiver-owned branching root | premise-required: P2 retires receiver-owned subtree selection; [sender root][d-root] makes the choice prover-authored. |
| [5][fd5] | False future owner | equivalent: [position][d-false-pos], [owner][d-false-owner]. |
| [6][fd6] | True future owner | equivalent: [position][d-true-pos], [owner][d-true-owner]. |
| [7][fd7] | False oracle has Unit queries | equivalent: [query type][d-query]. |
| [8][fd8] | False oracle subtree | retired: restriction of stored oracle decorations; [interface][d-false-interface] and [cursor][d-false-cursor] retain the subtree. |
| [9][fd9] | True oracle subtree | retired: restriction of stored oracle decorations; [interface][d-true-interface] and [cursor][d-true-cursor] retain the subtree. |
| [10][fd10] | After false marker | equivalent: [cursor][d-false-cursor], [owner][d-false-owner]. |
| [11][fd11] | After true marker | equivalent: [cursor][d-true-cursor], [owner][d-true-owner]. |
| [12][fd12] | Oracle node's implicit owner is sender | equivalent: [node owner][d-oracle-owner]. |
| [13][fd13] | Owner after erasure | retired: conversion to a second runtime tree; [owner][d-oracle-owner] retains intrinsic ownership. |

The true future is a constant-continuation `.challenge Bool`, while the false future is a
`.message (Fin 2)`. Each cursor crosses its branch's oracle marker, and each future position and
owner is checked separately, and the [future positions are distinct][d-distinct].
Both oracle nodes remain sender-owned. The root remains a
prover-authored message: only public messages select shape branches in
[oracleSig][oracle-signature].
A receiver-owned choice that changes the next oracle type is therefore not represented by this
fixture. Row 4 records that changed authoring model, rather than calling the sender test an
equivalent receiver-ownership test.

Rows 1, 8–9 and 13 used separate role/oracle decorations, restriction of those stored objects,
and conversion to a second runtime tree with a second role assignment. Oracle positions now
carry their interfaces, the signature fixes ownership, and the runtime follows that signature
on the same tree. Interface restriction and runtime role-conversion identities have no such
objects in Core. The linked cursor types also select the complete corresponding oracle subtree,
including its future, but are not equations between removed decorations.

Row 2 quantifies message and query universes independently through
`UniverseProtocol.{uProtocol, uQuery}` and `universeNode`. The small-node canary attaches an
arbitrary `OracleInterface.{0, 1} Nat` to a real oracle position and checks the query type of
its path family. It does not merely install the interface as an input resource. The parent's
[lifted_trace_contract][d-node-run] additionally executes such a node, queries its payload and
checks its terminal prefix. The optional leaf parameter makes the message universe visible in
the alias's domain, as in the parent `OracleProtocol`; it is an actual tree return type.

## MixedExample: 9 assertions

| Frozen row | Contract | Disposition and evidence |
|---|---|---|
| [1][fm1] | Arbitrary position universe | equivalent: [position canary][m-position]. |
| [2][fm2] | Arbitrary tree universe | equivalent: [tree canary][m-tree]. |
| [3][fm3] | Arbitrary branch-path universe | equivalent: [branch canary][m-branch]. |
| [4][fm4] | Arbitrary execution-path universe | equivalent: [execution canary][m-execution]. |
| [5][fm5] | Distinct hidden payloads give distinct paths | equivalent: [inequality][m-distinct]. |
| [6][fm6] | Equal public choices give equal shapes | equivalent: [projection equality][m-shared]. |
| [7][fm7] | False branch retains public choice only | equivalent: [false shape][m-false]. |
| [8][fm8] | True branch erases Fin 3 payload | equivalent: [true shape][m-true]. |
| [9][fm9] | Complete runtime message | equivalent: [full transcript][m-runtime]. |

The branch selector is re-authored as a prover message, and row 9 no longer converts to a second
generic runtime tree. `PathAlong oracleSig` is already the full runtime transcript. The new
assertion checks the complete transcript, including the public branch and payload; the separate
[payload lookup][m-payload] and [view-erasure test][m-view] also preserve the observable boundary.
The position canary alone does not establish independent oracle-query universes;
DecorationExample row 2 now checks that distinct contract.

## Parent interfaces and remaining universe restriction

The merged parent supplies the formerly missing phase and canonical-prefix interfaces.
[SlotTrace][slot-api] produces slots with actual full prefixes, intrinsic owners and query groups;
[Provenance][trace-api] supplies closing, ordinary erasure and log correspondence;
[PrefixResources][prefix-api] supplies canonical names, availability and inclusion, together with
query routing. The [parent inventory][parent-inventory] and the tables above identify their exact
assertion targets. P1 retires intermediate verifier effects, not produced prover prefixes.

`OraclePos.{u, q}`, `OraclePoly`, `oracleSig`, `viewSig`, `OracleProtocol`, `pathFamily` and
`pathResources` retain independent node-query universes. General `Resources.{u, uI, dI}` also
separates response, resource-query and data universes without changing the shared
`OracleInterface`; families are a specialization. Thus the earlier node and input-data coupling
entries are closed by the parent, as recorded in [implementation note 18][universes].

The **unresolved** restriction is the full-log runner's large-query result interface.
[OracleVerifier.runWithLog][logged-runner] returns resource-query entries through a small
computation monad. Returning large query indices in that complete heterogeneous log needs a
parent logging interface with a sufficiently large result universe. `runWithAmbientLog` and
`runWithAmbientTrace` preserve independent input-data, input-query and node-query universes by
returning only ambient decision queries. The full-log [loggedSummary][q-log-summary] keeps the
strongest supported output-query universe. P1 and P2 impose no universe restrictions.
Run outputs continue to follow the parent monad's value universe, as documented in note 18.

## Definition-site transparency

The only retained definition-site attribute added by this branch is `@[instance_reducible]` on
`Interaction.Core.AccessExampleTests.firstInterface`. It declares a value of the class
`OracleInterface`; ordinary semireducibility triggers Lean's class-definition transparency
warning. The attribute gives this declaration the expected instance transparency, with no
command modifying another declaration. The former `@[reducible]` is replaced by that narrower
choice. All 18 other definition-site fixture attributes were removed and the ordinary-import
clients are checked without them. No added local/global `attribute [...]` transparency command
or `set_option respectTransparency` remains.

[fp1]: ../../../ArkLibTest/Interaction/Oracle/PhasedRun.lean#L84
[fp2]: ../../../ArkLibTest/Interaction/Oracle/PhasedRun.lean#L91
[fp3]: ../../../ArkLibTest/Interaction/Oracle/PhasedRun.lean#L114
[fp4]: ../../../ArkLibTest/Interaction/Oracle/PhasedRun.lean#L121
[fp5]: ../../../ArkLibTest/Interaction/Oracle/PhasedRun.lean#L178
[fp6]: ../../../ArkLibTest/Interaction/Oracle/PhasedRun.lean#L194
[fp7]: ../../../ArkLibTest/Interaction/Oracle/PhasedRun.lean#L198
[fx1]: ../../../ArkLibTest/Interaction/Oracle/Prefix.lean#L26
[fx2]: ../../../ArkLibTest/Interaction/Oracle/Prefix.lean#L28
[fx3]: ../../../ArkLibTest/Interaction/Oracle/Prefix.lean#L35
[fx4]: ../../../ArkLibTest/Interaction/Oracle/Prefix.lean#L40
[fx5]: ../../../ArkLibTest/Interaction/Oracle/Prefix.lean#L47
[fx6]: ../../../ArkLibTest/Interaction/Oracle/Prefix.lean#L49
[fx7]: ../../../ArkLibTest/Interaction/Oracle/Prefix.lean#L55
[fx8]: ../../../ArkLibTest/Interaction/Oracle/Prefix.lean#L58
[fq1]: ../../../ArkLibTest/Interaction/Oracle/QueryBounds.lean#L96
[fq2]: ../../../ArkLibTest/Interaction/Oracle/QueryBounds.lean#L117
[fq3]: ../../../ArkLibTest/Interaction/Oracle/QueryBounds.lean#L130
[fq4]: ../../../ArkLibTest/Interaction/Oracle/QueryBounds.lean#L149
[fq5]: ../../../ArkLibTest/Interaction/Oracle/QueryBounds.lean#L165
[fq6]: ../../../ArkLibTest/Interaction/Oracle/QueryBounds.lean#L184
[fq7]: ../../../ArkLibTest/Interaction/Oracle/QueryBounds.lean#L209
[fq8]: ../../../ArkLibTest/Interaction/Oracle/QueryBounds.lean#L225
[fq9]: ../../../ArkLibTest/Interaction/Oracle/QueryBounds.lean#L251
[fq10]: ../../../ArkLibTest/Interaction/Oracle/QueryBounds.lean#L252
[fq11]: ../../../ArkLibTest/Interaction/Oracle/QueryBounds.lean#L255
[fq12]: ../../../ArkLibTest/Interaction/Oracle/QueryBounds.lean#L257
[fq13]: ../../../ArkLibTest/Interaction/Oracle/QueryBounds.lean#L266
[fq14]: ../../../ArkLibTest/Interaction/Oracle/QueryBounds.lean#L277
[fq15]: ../../../ArkLibTest/Interaction/Oracle/QueryBounds.lean#L286
[fq16]: ../../../ArkLibTest/Interaction/Oracle/QueryBounds.lean#L300
[fq17]: ../../../ArkLibTest/Interaction/Oracle/QueryBounds.lean#L320
[fr1]: ../../../ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L47
[fr2]: ../../../ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L57
[fr3]: ../../../ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L61
[fr4]: ../../../ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L72
[fr5]: ../../../ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L87
[fr6]: ../../../ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L102
[fr7]: ../../../ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L124
[fr8]: ../../../ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L145
[fr9]: ../../../ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L167
[fr10]: ../../../ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L182
[fr11]: ../../../ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L197
[fr12]: ../../../ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L207
[fr13]: ../../../ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L227
[fr14]: ../../../ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L235
[fr15]: ../../../ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L244
[fr16]: ../../../ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L258
[fr17]: ../../../ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L289
[fa1]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L42
[fa2]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L44
[fa3]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L47
[fa4]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L53
[fa5]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L55
[fa6]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L57
[fa7]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L64
[fa8]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L67
[fa9]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L79
[fa10]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L87
[fa11]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L109
[fa12]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L111
[fa13]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L121
[fa14]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L126
[fa15]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L133
[fa16]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L141
[fa17]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L147
[fa18]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L152
[fd1]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L25
[fd2]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L28
[fd3]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L32
[fd4]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L78
[fd5]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L81
[fd6]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L84
[fd7]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L87
[fd8]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L109
[fd9]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L114
[fd10]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L119
[fd11]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L124
[fd12]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L129
[fd13]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L133
[fm1]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L23
[fm2]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L26
[fm3]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L29
[fm4]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L32
[fm5]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L55
[fm6]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L60
[fm7]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L64
[fm8]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L68
[fm9]: ../../../ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L72
[a-before-f]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L54
[a-before-t]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L59
[a-unsent]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L65
[a-sent]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L74
[a-bool]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L78
[a-fin]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L82
[a-slots]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L87
[a-future]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L97
[a-distinct]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L105
[a-shape]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L110
[a-family]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L113
[a-terminal]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L134
[a-nat]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L138
[a-route]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L149
[a-hidden]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L154
[a-single]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L164
[a-missing-second]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L171
[a-second]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L187
[a-large-data]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L191
[a-large-query]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean#L202
[d-protocol]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L23
[d-root]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L106
[d-false-cursor]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L115
[d-true-cursor]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L119
[d-false-pos]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L123
[d-true-pos]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L127
[d-false-owner]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L130
[d-true-owner]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L134
[d-query]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L80
[d-false-interface]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L87
[d-true-interface]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L94
[d-oracle-owner]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L101
[m-position]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/MixedExample.lean#L23
[m-tree]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/MixedExample.lean#L27
[m-branch]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/MixedExample.lean#L31
[m-execution]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/MixedExample.lean#L35
[m-runtime]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/MixedExample.lean#L87
[m-distinct]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/MixedExample.lean#L57
[m-shared]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/MixedExample.lean#L63
[m-false]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/MixedExample.lean#L68
[m-true]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/MixedExample.lean#L72
[m-payload]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/MixedExample.lean#L77
[m-view]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/MixedExample.lean#L81
[x-cursor]: ../../../ArkLibTest/Interaction/Core/Oracle/Prefix.lean#L37
[x-distinct]: ../../../ArkLibTest/Interaction/Core/Oracle/Prefix.lean#L40
[x-sent]: ../../../ArkLibTest/Interaction/Core/Oracle/Prefix.lean#L54
[x-no-slot]: ../../../ArkLibTest/Interaction/Core/Oracle/Prefix.lean#L61
[x-empty-root]: ../../../ArkLibTest/Interaction/Core/Oracle/Prefix.lean#L69
[x-empty-moves]: ../../../ArkLibTest/Interaction/Core/Oracle/Prefix.lean#L74
[x-length]: ../../../ArkLibTest/Interaction/Core/Oracle/Prefix.lean#L88
[x-complete]: ../../../ArkLibTest/Interaction/Core/Oracle/Prefix.lean#L90
[x-payload]: ../../../ArkLibTest/Interaction/Core/Oracle/Prefix.lean#L93
[p-accept]: ../../../ArkLibTest/Interaction/Core/Oracle/PhasedRun.lean#L90
[p-payload]: ../../../ArkLibTest/Interaction/Core/Oracle/PhasedRun.lean#L93
[p-reject]: ../../../ArkLibTest/Interaction/Core/Oracle/PhasedRun.lean#L102
[q-route]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L136
[q-future]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L173
[q-log]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L240
[q-log-summary]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L232
[q-repeat]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L143
[q-fresh]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L149
[q-distinct]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L153
[q-untyped]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L167
[q-run]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L208
[q-split]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L217
[q-prefix-payload]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L221
[q-suffix-payload]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L225
[q-concrete-log]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L247
[c-route]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L48
[c-program]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L69
[c-routed]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L78
[c-suffix]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L173
[c-suffix-routed]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L186
[c-setup]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L200
[c-history]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L206
[c-import]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L220
[c-joint]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L230
[c-informed]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L261
[c-prover-log]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L292
[c-joint-cost]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L83
[c-lower]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L116
[c-input-cost]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L166
[c-count]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L296
[r-export]: ../../../ArkLibTest/Interaction/Core/Oracle/RuntimeQueryBounds.lean#L45
[r-decide]: ../../../ArkLibTest/Interaction/Core/Oracle/RuntimeQueryBounds.lean#L60
[r-access]: ../../../ArkLibTest/Interaction/Core/Oracle/RuntimeQueryBounds.lean#L84
[r-route]: ../../../ArkLibTest/Interaction/Core/Oracle/RuntimeQueryBounds.lean#L106
[r-raw-access]: ../../../ArkLibTest/Interaction/Core/Oracle/RuntimeQueryBounds.lean#L121
[r-guess-answers]: ../../../ArkLibTest/Interaction/Core/Oracle/RuntimeQueryBounds.lean#L144
[r-informed-answers]: ../../../ArkLibTest/Interaction/Core/Oracle/RuntimeQueryBounds.lean#L154
[r-guess-success]: ../../../ArkLibTest/Interaction/Core/Oracle/RuntimeQueryBounds.lean#L165
[r-informed-success]: ../../../ArkLibTest/Interaction/Core/Oracle/RuntimeQueryBounds.lean#L185
[r-input]: ../../../ArkLibTest/Interaction/Core/Oracle/RuntimeQueryBounds.lean#L36
[r-map]: ../../../ArkLibTest/Interaction/Core/Oracle/RuntimeQueryBounds.lean#L51
[r-pre]: ../../../ArkLibTest/Interaction/Core/Oracle/RuntimeQueryBounds.lean#L54
[r-output]: ../../../ArkLibTest/Interaction/Core/Oracle/RuntimeQueryBounds.lean#L70
[p-order]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L518
[p-close]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L222
[p-parent-reject]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L218
[p-guess-log]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L727
[p-informed-log]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L737
[p-guess-split]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L760
[p-informed-split]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L771
[p-general-split]: ../../../ArkLibTest/Interaction/Core/Oracle/Routing.lean#L354
[run-append]: ../../../ArkLib/Interaction/Core/Oracle/Routing.lean#L119
[oracle-position]: ../../../ArkLib/Interaction/Core/Signature.lean#L45
[oracle-signature]: ../../../ArkLib/Interaction/Core/Signature.lean#L57
[resource-sum]: ../../../ArkLib/Interaction/Core/OracleVerifier.lean#L133
[logged-runner]: ../../../ArkLib/Interaction/Core/Security/Knowledge.lean#L332

[universes]:
    ../interaction-rebuild/IMPLEMENTATION-NOTES.md#18-run-outputs-are-tied-to-the-monad-universe

[x-query]: ../../../ArkLibTest/Interaction/Core/Oracle/Prefix.lean#L108

[x-prefix]: ../../../ArkLibTest/Interaction/Core/Oracle/Prefix.lean#L100

[d-distinct]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L138

[p-terminal]: ../../../ArkLibTest/Interaction/Core/Oracle/PhasedRun.lean#L133

[parent-inventory]: logged-execution-disposition.md
[parent-phase-audits]: logged-execution-disposition.md#phasedrunlean

[trace-api]: ../../../ArkLib/Interaction/Core/Oracle/Provenance.lean
[slot-api]: ../../../ArkLib/Interaction/Core/Oracle/SlotTrace.lean
[prefix-api]: ../../../ArkLib/Interaction/Core/Oracle/PrefixResources.lean
[p-trace]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L901
[p-prefixes]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L919
[p-setup-trace]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L944
[q-join-prefix]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1043
[q-terminal-prefix]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1047
[q-join-member]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1036
[q-terminal-member]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1039
[q-join-name]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1064
[q-join-available]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1069
[q-terminal-available]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1080
[q-phase-source]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1090
[d-node-run]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1163

[d-node]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L33

[q-available]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L282

[q-available-cost]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L83
