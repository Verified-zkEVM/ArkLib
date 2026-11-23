# Oracle access tests: port table

This table covers all 89 assertions in the seven old-layer test files below. Eight modules in the
interaction layer port them. `QueryCost.lean` is the eighth: it collects the cost and query-profile
assertions from `QueryBounds`, `RuntimeQueryBounds` and `PhasedRun` instead of porting an eighth
old file. Row numbers follow the old declaration order, including the universe canaries. Helper
definitions and the diagnostic axiom-print commands are not counted as assertions.

This document holds the full entries for the overlapping PhasedRun, QueryBounds and
RuntimeQueryBounds rows. The [parent port table][parent-port-table] lists the same contracts.

Each row has exactly one of four statuses:

- **ported:** the new test keeps the observation and its quantifiers.
- **excluded by P1** (or **P2**): the row names the premise and the assertion it rules out.
- **removed:** the row names a mechanism that no longer exists.
- **open:** the row names an interface that the parent is missing.

A result that the parent already proves is linked directly instead of being copied.

The two premises are **P1**, public-coin challenges with resource queries confined to the final
decision, and **P2**, subtree selection independent of challenges and oracle payloads. P1 allows
distributions that depend on earlier public challenges and prover messages.

## PhasedRun: 7 assertions

| Old-layer row | Contract | Status and where it is ported |
|---|---|---|
| <a id="p1"></a>[1][fp1] | Intrinsic step actors | ported: [produced steps][step-api] derive each actor from the executed participant; [step_log_contract][p-step-log] checks them. |
| <a id="p2"></a>[2][fp2] | State, actors, order | excluded by P1: P1 rules out verifier actions 2 and 3 before the challenge and action 6 at reception. [step_log_contract][p-step-log] keeps all tags, passive groups and state; [actual_step_prefixes][p-prefixes] keeps the moves of the transcript prefixes. |
| <a id="p3"></a>[3][fp3] | Setup count | ported: [setup_step_log_contract][p-setup-step] records a separate setup step with both query 9 entries. |
| <a id="p4"></a>[4][fp4] | Final payload | ported: [run][p-accept], [lookup][p-payload], [actual_step_prefixes][p-prefixes]. |
| <a id="p5"></a>[5][fp5] | Closing, log, groups | excluded by P1: P1 rules out reception effect 1 as a separate verifier group. [closure/log][p-close] and [decision outcomes][p-decision] keep the outputs and histories of the run; [log erasure and setup/log laws][laws-api] keep the remaining groups and closing. |
| <a id="p6"></a>[6][fp6] | Explicit rejection | ported: [decision outcomes][p-decision]. |
| <a id="p7"></a>[7][fp7] | Fault 17, not rejection | ported: [decision outcomes][p-decision]. |

The parent's step log supplies the step data: actors, transcript prefixes, membership and the
ordered query groups. `OracleVerifier.executeWith` runs the interaction and the final decision.
`runLoggingSteps` instruments strategies that the core runner `TwoParty.Lens.run` runs.
`runWithSetupStep` keeps the setup as an independently selectable step, and
`toLog_runWithSetupStep` relates its log to the ordinary logged execution. These are parent
declarations, and the tests here add no second executor.

For row 2, passivity changes the ambient order `[9, 9, 1, 2, 3, 4, 5, 6, 7]` to
`[9, 9, 1, 4, 5, 2, 3, 6, 7]`. [step_log_contract][p-step-log] checks state `2102563478` and the
produced passive groups. [actual_step_prefixes][p-prefixes] checks the challenge and payload values
in the transcript prefixes. The local [accepting run][p-accept] quantifies over payload, private
output and challenge independently.

Row 5 keeps input 7, accepted target 11, materialized answer 18, the sent-answer log and the
ambient history `[9, 0, 1, 2]`. P1 moves reception effect 1 into the final decision together with
effect 2. The remaining step observations are ported through `toLog_runWithStepLog`,
`map_fst_runWithStepLog` and `simulateQ_toLog_runWithStepLog` in [StepLogLaws][laws-api]. The
closing audits at L201 and L202 have those same exact targets in the
[parent port table][parent-phase-audits].

Rows 6–7 use the same closing prover and final-decision interpreter. The new test first runs the
prover and captures the completed transcript, the private output and the prover query log. It then
calls `OracleVerifier.decideCatching` on that transcript and the input data. The ambient handler
returns fault 17 as `Except.error 17`. Rejection is `Except.ok none`, and acceptance is
`Except.ok (some (message, old + message))`. All three outcomes keep the same transcript, an
arbitrary hidden private output, the prover log, the decision's log of answered queries and the
history `[9, 0, 1, 2]`. The unanswered failing request adds no entry to the log of answered
queries. The sent answer is read before that failure, and acceptance closes with the same run's
input and message. No fault is encoded as an accepted value, and `OracleVerifier.decide` is
unchanged.

## Prefix: 8 assertions

| Old-layer row | Contract | Status and where it is ported |
|---|---|---|
| [1][fx1] | Shared structural cursor | ported: [shared spine][x-cursor]. |
| [2][fx2] | Different transcript prefixes | ported: [distinct full moves][x-distinct]. |
| [3][fx3] | The crossed send gives a sent oracle | ported: [crossed-send query][x-query]; `SentOracle`, `SentOracle.node` and `IsSent` in [SentOracles][sent-api] identify the crossed oracle. |
| [4][fx4] | The root has no sent oracle for that send | ported: [empty prefix has no sent oracle][x-no-sent]; `SentOracle` at `.here` is empty in [SentOracles][sent-api]. |
| [5][fx5] | An empty-payload send permits a root prefix | ported: [root moves][x-empty-root]. |
| [6][fx6] | No realization crosses an empty send | ported: [crossed moves][x-empty-moves]. |
| [7][fx7] | Prefix length two | ported: [length][x-length], [completion][x-complete]. |
| [8][fx8] | The first hidden realization is true | ported: [transcript prefix payload][x-payload]. |

Rows 3–4 use the parent's `TranscriptPrefix` interface in [SentOracles][sent-api]. `SentOracle` at
an empty prefix is empty, while crossing an oracle send adds the sent oracle for that node.
`IsSent` says that some sent oracle has a given node name, and `IsSent.mono` keeps that true when
the transcript prefix is extended. The [prefix append identity][x-prefix] identifies the boundary
immediately after the send, and the [crossed-send query][x-query] reads its own payload without
choosing the future public message. [Completed-path lookup][x-sent] checks that payload for every
later choice. [AccessExample 3][a-unsent] and [4][a-sent] check the typed access boundary.

## QueryBounds: 17 assertions

| Old-layer row | Contract | Status and where it is ported |
|---|---|---|
| <a id="q1"></a>[1][fq1] | Per-query cost | ported: [route_cost][c-route]. |
| <a id="q2"></a>[2][fq2] | Source cost five | ported: [program_cost][c-program]. |
| <a id="q3"></a>[3][fq3] | Routed cost five | ported: [routed_cost][c-routed]. |
| <a id="q4"></a>[4][fq4] | Queried oracles were sent | ported: [routed_available][q-available] proves that every oracle the routed program queries was sent at the produced decision step. |
| <a id="q5"></a>[5][fq5] | Old/old/fresh log | ported: [logged run][q-log]. |
| <a id="q6"></a>[6][fq6] | Future exclusion | ported: [exclusion][q-future] for every prefix program; [joinStep_isSent][q-join-sent] excludes the node of the future oracle at the produced join step. |
| <a id="q7"></a>[7][fq7] | Old/fresh identities | ported: [typed identity][q-repeat], [joinStep_node][q-join-node] and [decisionStep_isSent][q-decision-sent]. |
| <a id="q8"></a>[8][fq8] | Closing keeps the log | ported: [closed run log][q-log]. |
| <a id="q9"></a>[9][fq9] | Produced join prefix | ported: [joinStep_before][q-join-before]. |
| <a id="q10"></a>[10][fq10] | Decision-step prefix | ported: [decisionStep_before][q-decision-before]. |
| <a id="q11"></a>[11][fq11] | Join membership | ported: [joinStep_mem][q-join-member]. |
| <a id="q12"></a>[12][fq12] | Decision-step membership | ported: [decisionStep_mem][q-decision-member]. |
| <a id="q13"></a>[13][fq13] | Sent oracles and cost | ported: [routed_available_and_cost][q-available-cost] proves the same routed program at the produced decision step, with cost five. |
| <a id="q14"></a>[14][fq14] | Node-name inclusion | ported: [joinStep_node][q-join-node]; `availableMap_node`, `liftQuery_node` and `sentFamilyMap_query` in [SentOracles][sent-api] keep node names, query arguments and routing. |
| <a id="q15"></a>[15][fq15] | Join exclusion | ported: [joinStep_isSent][q-join-sent] excludes the future oracle regardless of budget; [exclusion][q-future] proves the typed program law. |
| <a id="q16"></a>[16][fq16] | Step log | ported: [step_source_log_contract][q-step-source] and `simulateQ_toLog_runWithStepLog` in [StepLogLaws][laws-api]. |
| <a id="q17"></a>[17][fq17] | Four is insufficient | ported: [cost-five path][c-lower]. |

Rows 5 and 8 use `composed.runWithLog`. For every `a` and `b`, the doubled export records two
entries for the prefix oracle with answer `a`, then the entry for the suffix oracle with answer
`b`. The same assertion checks private output `a + b` and verdict `some (a + a + b)`. The
[one/two specialization][q-concrete-log] recovers private output 3 and accepted result 4. Output
closing uses those same resources; this fixture's output family is empty.

Rows 9–12 and 14–16 reuse the parent's `LoggedExecutionTests` two-oracle execution. Its
`joinStep_mem`, `decisionStep_mem`, `joinStep_before`, `decisionStep_before`,
`step_intrinsic_actors`, `joinStep_node`, `joinStep_isSent`, `decisionStep_isSent` and
`step_source_log_contract` already prove the old observations. The join is the first suffix prover
step. P1 rules out the old verifier decision at that seam, and the new tests keep its transcript
prefix and membership. They add no duplicate assertions or executor. `toLog_runWithStepLog` and
`simulateQ_toLog_runWithStepLog` relate steps and log for every prover, including this branch's
composed verifier.

The additional [routed_available][q-available] and [joint proof][q-available-cost] cover this
branch's exact doubled-export program. `composedStepLog a b` comes from `composed.runWithStepLog`.
`rawAvailable` matches each raw query's node name, computed from the completed transcript, with an
oracle that was sent at the decision step of that execution. This ties the proof that an oracle was
sent to the same program as the cost-five bound. The [run transcript][q-run],
[split payloads][q-split], [prefix payload][q-prefix-payload] and
[suffix payload][q-suffix-payload] stay as additional checks.

## RuntimeQueryBounds: 17 assertions

| Old-layer row | Contract | Status and where it is ported |
|---|---|---|
| <a id="r1"></a>[1][fr1] | Export access | ported: [access][r-export], [cost][c-input-cost], and the input case of `queryNode` in [SentOracles][sent-api]. |
| <a id="r2"></a>[2][fr2] | Source node name | ported: [typed input query][r-input]; `queryNode` gives every input query the node name of its input index. |
| <a id="r3"></a>[3][fr3] | Dummy and export | ported: [decision][r-pre], [map][r-map]. |
| <a id="r4"></a>[4][fr4] | Suffix equation | ported: [decision][r-decide], [data][r-output]. |
| <a id="r5"></a>[5][fr5] | Suffix permissions | ported: [typed][r-access] and the input node-name and inclusion laws in [SentOracles][sent-api]. |
| <a id="r6"></a>[6][fr6] | Suffix cost five | ported: [suffix_budget][c-suffix]. |
| <a id="r7"></a>[7][fr7] | Routed cost five | ported: [routed bound][c-suffix-routed]. |
| <a id="r8"></a>[8][fr8] | Raw permissions | ported: [typed][r-raw-access] and `availableMap_node` in [SentOracles][sent-api]. |
| <a id="r9"></a>[9][fr9] | Guess history | ported: ambient history, [charged run][c-history]. |
| <a id="r10"></a>[10][fr10] | Informed order | excluded by P1: P1 rules out the dummy-before-reveal order; [passive split][p-informed-split]. |
| <a id="r11"></a>[11][fr11] | Setup import cost | ported: [setup_budget][c-setup]. |
| <a id="r12"></a>[12][fr12] | Generic runtime split | excluded by P1: P1 rules out the effectful-prefix order; [all-prover passive law][run-append]. |
| <a id="r13"></a>[13][fr13] | Logged guess history | ported: ambient projection, [log][p-guess-log]. |
| <a id="r14"></a>[14][fr14] | Logged informed order | excluded by P1: P1 rules out the dummy-before-reveal order; [passive log][p-informed-log]. |
| <a id="r15"></a>[15][fr15] | Run import cost | ported: [import_budget][c-import]. |
| <a id="r16"></a>[16][fr16] | Joint half bound | ported: [joint][c-joint] with the input node-name and inclusion laws in [SentOracles][sent-api]. |
| <a id="r17"></a>[17][fr17] | Charge 7, success 1 | excluded by P1: P1 rules out the dummy-before-reveal order; [passive charge and success][c-informed]. |

Rows 1, 2, 5, 8 and 16 use the input case of the parent's `queryNode`, `availableMap_node` and
`liftNode` in [SentOracles][sent-api]. The prefix has no sent oracle: its export reads only its
input, whose node name is `.inl` of that same input index at every prefix. The inclusion keeps that
input index unchanged. The linked access and cost tests quantify over every relevant path and view,
and use precisely that input query.

Row 3's decision performs the dummy request and accepts the unit statement, and its output map is
exactly the input projection. Row 4 checks the entire effectful decision and the output map on
arbitrary resource data. The [routed export query][r-route] identifies the input oracle that the
cost theorem uses. The delegated exact-decision and output-map obligations therefore have
counterparts here, with the node names of the inputs supplied by the parent.

For rows 9 and 13, the full trace includes a challenge event. Its ambient projection is exactly
`[false ↦ false, true ↦ hidden]`, the final state is `(hidden, 2)` and the charge is four. The
[parent split check][p-guess-split] and the direct logged check keep that same ambient history.
Under the passive schedule, row 12 is ported by the general whole-prover `OracleVerifier.run_append`
with its [ordinary-import client][p-general-split]. It quantifies over arbitrary whole provers, not
just the guessing and informed examples. Applying runtime execution and the pure
state/trace/charge observation to this open-program equality proves the charged runtime/history
equality for every such prover. The exact target is the stronger
[open-program split law][run-append]. No two-prover specialization counts as the all-prover port.
P1 separately excludes the old effectful-prefix order.

For rows 10, 14 and 17, the informed prover reveals at the seam before the passive prefix's dummy
request. The ambient order is `[true ↦ hidden, false ↦ false, true ↦ hidden]`. The old order was
`[false ↦ false, true ↦ hidden, true ↦ hidden]`. Both have final state `(hidden, 3)` and charge
seven. The old dummy-before-reveal order needs a non-passive prefix verifier, so P1 excludes it. It
is not an open question about which steps are allowed. The extra passive history does not port the
former order.

The row-16 conjunction includes the exact prefix decision and export, the typed access and cost
certificates, the import budget, the charged history and the half bound for every fixed guess and
secret. [Answers][r-guess-answers] keep the materialized output oracle and target, and
[guess_success][r-guess-success] proves probability exactly one half. This conjunction uses the
parent's node names for inputs and the inclusion laws described above. The row-17 passive
conjunction keeps charge seven and [success one][r-informed-success], with its different order
stated explicitly, and its [answer observation][r-informed-answers]. Neither theorem derives
arbitrary-prover security from access and cost certificates alone.

## AccessExample: 18 assertions

| Old-layer row | Contract | Status and where it is ported |
|---|---|---|
| [1][fa1] | Before false send: inputs only | ported: [no sent oracle][a-before-f]. |
| [2][fa2] | Before true send: inputs only | ported: [no sent oracle][a-before-t]. |
| [3][fa3] | Unsent query rejected by typing | ported: [negative client][a-unsent]. |
| [4][fa4] | The oracle can be queried after its send | ported: [positive client][a-sent]. |
| [5][fa5] | False-branch response is Bool | ported: [response type][a-bool]. |
| [6][fa6] | True-branch response is Fin 3 | ported: [response type][a-fin]. |
| [7][fa7] | Inputs and one sent oracle | removed: literal `Access.extend` index layout; [oracle indices][a-slots] keep the input-plus-one-payload count. |
| [8][fa8] | Access restriction/rebuild | removed: stored `AccessDecoration.restrict_build`; [independent future][a-future] keeps payload-independent shape. |
| [9][fa9] | Different execution paths | ported: [distinct payloads][a-distinct]. |
| [10][fa10] | Access depends only on shape | ported: [shape][a-shape], [family][a-family]. |
| [11][fa11] | Terminal send can be queried | removed: literal `Access.extend` index layout; [terminal oracles][a-terminal] keep the terminal send queryable. |
| [12][fa12] | Non-faithful terminal response is Nat | ported: [response type][a-nat]. |
| [13][fa13] | Route input 7 and sent 11 | ported: [sum eighteen][a-route], all hidden values. |
| [14][fa14] | Hidden pair coordinate is unobservable | ported: [handler equality][a-hidden]. |
| [15][fa15] | Second send cannot be queried | ported: [negative client][a-missing-second]. |
| [16][fa16] | Second oracle after two sends | ported: [second answer][a-second]. |
| [17][fa17] | Large message universe | ported: [independent universes][a-large-data]. |
| [18][fa18] | Large query universe | ported: [independent universes][a-large-query]. |

Rows 7 and 11 keep the count of input oracles plus one payload. They do not assert literal equality
with the old `Access.extend` query-index layout `Unit ⊕ Unit`: the interaction layer uses family
indices and sigma-indexed interface queries, and heterogeneous resources keep their data as a pair.
The [one-oracle uniqueness test][a-single] rules out an extra sent oracle. Row 8 keeps
payload-independent future selection, but `AccessDecoration.restrict_build` was an identity about
stored per-node access decorations. There is no such decoration to restrict or rebuild now.
`pathResources` computes resources from a completed shape, and composition routes them explicitly.

Rows 17–18 quantify over every message type, interface and initial polynomial at the exact
universe instantiations of the old tests. Row 17 uses `OracleInterface.{1, 0}` on
`Messages : Type 1` and initial and result `PFunctor.{0, 1}`. Row 18 uses
`OracleInterface.{0, 1}` on `Messages : Type` and initial and result `PFunctor.{1, 0}`.
[Resources.sum][resource-sum] extends an arbitrary prior query handler with the given interface and
its message realization. Neither test restricts the prior polynomial, replaces a family with a
constant, or uses a universe lift. These tests cover resource extension; DecorationExample 2
separately checks interfaces inside protocol oracle nodes.

## DecorationExample: 13 assertions

| Old-layer row | Contract | Status and where it is ported |
|---|---|---|
| [1][fd1] | Role decorations at arbitrary tree universe | removed: no authored role decoration. |
| [2][fd2] | Raw oracle/query universes | ported: [arbitrary-tree decoration][d-decoration] at independent message and query universes; [unequal-universe node and path resources][d-node]. |
| [3][fd3] | Protocol bundle at arbitrary universe | ported: [protocol canary][d-protocol]. |
| [4][fd4] | Branching root chosen by the receiver | excluded by P2: P2 rules out subtree selection by the receiver; [sender root][d-root] makes the choice prover-authored. |
| [5][fd5] | False future actor | ported: [position][d-false-pos], [actor][d-false-actor]. |
| [6][fd6] | True future actor | ported: [position][d-true-pos], [actor][d-true-actor]. |
| [7][fd7] | False oracle has Unit queries | ported: [query type][d-query]. |
| [8][fd8] | False oracle subtree | removed: restriction of stored oracle decorations; [interface][d-false-interface] and [cursor][d-false-cursor] keep the subtree. |
| [9][fd9] | True oracle subtree | removed: restriction of stored oracle decorations; [interface][d-true-interface] and [cursor][d-true-cursor] keep the subtree. |
| [10][fd10] | After false marker | ported: [cursor][d-false-cursor], [actor][d-false-actor]. |
| [11][fd11] | After true marker | ported: [cursor][d-true-cursor], [actor][d-true-actor]. |
| [12][fd12] | The actor at an oracle node is the sender | ported: [node actor][d-oracle-actor]. |
| [13][fd13] | Actor after erasure | removed: conversion to a second runtime tree; [actor][d-oracle-actor] keeps the intrinsic actor. |

The true future is a constant-continuation `.challenge Bool`, while the false future is a
`.message (Fin 2)`. Each cursor crosses its branch's oracle marker. The test checks each future's
position and actor separately, and the [future positions are distinct][d-distinct]. The sender is
the actor at both oracle nodes. The root remains a prover-authored message: only public messages
select shape branches in [oracleSig][oracle-signature]. A choice by the receiver that changes the
next oracle type is therefore not represented by this fixture. Row 4 records that change of
authoring model instead of calling the sender test a port of the receiver test.

Rows 1, 8–9 and 13 used separate role and oracle decorations, restriction of those stored objects,
and conversion to a second runtime tree with a second role assignment. Oracle positions now carry
their interfaces, the signature fixes the actor, and the runtime follows that signature on the same
tree. The identities for restricting interfaces and converting runtime roles have no such objects
in Core to apply to. The linked cursor types also select the complete corresponding oracle
subtree, including its future, but they are not equations between removed decorations.

Row 2 quantifies message and query universes independently. The old alias has the form
`tree.OracleDecoration.{uOracle, uQuery}` for an arbitrary tree. Oracle positions in the
interaction layer carry their interfaces, so the decoration of an arbitrary tree is read off the
tree. [UniverseOracleDecoration][d-decoration] takes any
`tree : OracleProtocol.{uProtocol, uQuery}` and a path and returns the tree's path family, and its
example instantiates it at `.{0, 1}` on an arbitrary tree. `UniverseProtocol.{uProtocol, uQuery}`
and `universeNode` add a constructed node. The small-node canary attaches an arbitrary
`OracleInterface.{0, 1} Nat` to a real oracle position and checks the query type of its path
family. It does not merely install the interface as an input resource. The parent's
[lifted_step_log_contract][d-node-run] also runs such a node, queries its payload and checks the
transcript prefix at its decision step. The optional leaf parameter makes the message universe
visible in the alias's domain, as in the parent `OracleProtocol`; it is an actual tree return type.

## MixedExample: 9 assertions

| Old-layer row | Contract | Status and where it is ported |
|---|---|---|
| [1][fm1] | Arbitrary position universe | ported: [position canary][m-position]. |
| [2][fm2] | Arbitrary tree universe | ported: [tree canary][m-tree]. |
| [3][fm3] | Arbitrary branch-path universe | ported: [branch canary][m-branch]. |
| [4][fm4] | Arbitrary execution-path universe | ported: [execution canary][m-execution]. |
| [5][fm5] | Distinct hidden payloads give distinct paths | ported: [inequality][m-distinct]. |
| [6][fm6] | Equal public choices give equal shapes | ported: [projection equality][m-shared]. |
| [7][fm7] | False branch keeps the public choice only | ported: [false shape][m-false]. |
| [8][fm8] | True branch erases Fin 3 payload | ported: [true shape][m-true]. |
| [9][fm9] | Complete runtime message | ported: [full transcript][m-runtime]. |

The branch selector is re-authored as a prover message, and row 9 no longer converts to a second
generic runtime tree. `PathAlong oracleSig` is already the full transcript. The new test checks the
complete transcript, including the public branch and payload. The separate
[payload lookup][m-payload] and [view-erasure test][m-view] also keep the observable boundary. The
position canary alone does not establish independent oracle-query universes, and DecorationExample
row 2 now checks that separate contract.

## Parent interfaces and remaining universe restriction

The merged parent supplies the step and sent-oracle interfaces that earlier versions of this table
listed as missing. [StepLog][step-api] produces steps with their transcript prefixes, actors and
query groups. [StepLogLaws][laws-api] supplies closing, ordinary erasure and the correspondence
with the log. [SentOracles][sent-api] supplies node names, the proof that an oracle was sent and
inclusion, together with query routing. The [parent port table][parent-port-table] and the tables
above identify their exact assertion targets. P1 rules out intermediate verifier effects, not the
produced prover prefixes.

`OraclePos.{u, q}`, `OraclePoly`, `oracleSig`, `viewSig`, `OracleProtocol`, `oracleMessageFamily` and
`pathResources` keep independent node-query universes. General `Resources.{u, uI, dI}` also
separates response, resource-query and data universes without changing the shared
`OracleInterface`; families are a specialization. The earlier node-universe and input-data
coupling entries are therefore closed by the parent, as recorded in
[implementation note 18][universes].

The **open** item is the large-query result interface of the full-log runner.
[OracleVerifier.runWithLog][logged-runner] returns resource-query entries through a small
computation monad. Returning large query indices in that complete heterogeneous log needs a parent
logging interface with a sufficiently large result universe. `runWithAmbientLog` and
`runWithAmbientStepLog` keep independent input-data, input-query and node-query universes by
returning only ambient decision queries. The full-log [loggedSummary][q-log-summary] keeps the
strongest supported output-query universe. P1 and P2 impose no universe restrictions. Run outputs
continue to follow the parent monad's value universe, as documented in note 18.

## Definition-site transparency

The only definition-site attribute this branch keeps is `@[instance_reducible]` on
`Interaction.Core.AccessExampleTests.firstInterface`. It declares a value of the class
`OracleInterface`, and ordinary semireducibility triggers Lean's class-definition transparency
warning. The attribute gives this declaration the expected instance transparency, with no command
modifying another declaration. It replaces the former `@[reducible]` with a narrower choice. All 18
other definition-site fixture attributes were removed, and the ordinary-import clients are checked
without them. No added local or global `attribute [...]` transparency command and no
`set_option respectTransparency` remains.

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
[d-decoration]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L45
[d-root]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L117
[d-false-cursor]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L126
[d-true-cursor]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L130
[d-false-pos]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L134
[d-true-pos]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L138
[d-false-actor]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L141
[d-true-actor]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L145
[d-query]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L91
[d-false-interface]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L98
[d-true-interface]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L105
[d-oracle-actor]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L112
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
[x-no-sent]: ../../../ArkLibTest/Interaction/Core/Oracle/Prefix.lean#L61
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
[c-prover-log]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L293
[c-joint-cost]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L83
[c-lower]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L116
[c-input-cost]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L166
[c-count]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L297
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
[p-order]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L542
[p-close]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L223
[p-parent-reject]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L219
[p-guess-log]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L759
[p-informed-log]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L769
[p-guess-split]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L792
[p-informed-split]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L803
[p-general-split]: ../../../ArkLibTest/Interaction/Core/Oracle/Routing.lean#L355
[run-append]: ../../../ArkLib/Interaction/Core/Oracle/Routing.lean#L119
[oracle-position]: ../../../ArkLib/Interaction/Core/Signature.lean#L45
[oracle-signature]: ../../../ArkLib/Interaction/Core/Signature.lean#L57
[resource-sum]: ../../../ArkLib/Interaction/Core/OracleVerifier.lean#L133
[logged-runner]: ../../../ArkLib/Interaction/Core/Security/Knowledge.lean#L332

[universes]:
    ../interaction-rebuild/IMPLEMENTATION-NOTES.md#18-run-outputs-are-tied-to-the-monad-universe

[x-query]: ../../../ArkLibTest/Interaction/Core/Oracle/Prefix.lean#L108

[x-prefix]: ../../../ArkLibTest/Interaction/Core/Oracle/Prefix.lean#L100

[d-distinct]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L149

[p-decision]: ../../../ArkLibTest/Interaction/Core/Oracle/PhasedRun.lean#L133

[parent-port-table]: logged-execution-disposition.md
[parent-phase-audits]: logged-execution-disposition.md#phasedrunlean

[laws-api]: ../../../ArkLib/Interaction/Core/Oracle/StepLogLaws.lean
[step-api]: ../../../ArkLib/Interaction/Core/Oracle/StepLog.lean
[sent-api]: ../../../ArkLib/Interaction/Core/Oracle/SentOracles.lean
[p-step-log]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L925
[p-prefixes]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L944
[p-setup-step]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L970
[q-join-before]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1072
[q-decision-before]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1077
[q-join-member]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1064
[q-decision-member]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1067
[q-join-node]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1096
[q-join-sent]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1102
[q-decision-sent]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1113
[q-step-source]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1124
[d-node-run]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1199

[d-node]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L33

[q-available]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L286

[q-available-cost]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L83
