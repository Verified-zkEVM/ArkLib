# Oracle access tests: port table

This table covers all 89 assertions in the seven old-layer test files below, in 90 rows: 75 ported,
6 excluded by P1, 1 excluded by P2, 8 removed and none open. RuntimeQueryBounds row 17 has two
rows, one for its charge and success and one for its query order. Eight modules in the interaction
layer port the assertions. `QueryCost.lean` is the eighth: it collects the cost and query-profile
assertions from `QueryBounds`, `RuntimeQueryBounds` and `PhasedRun` instead of porting an eighth
old file. Row numbers follow the old declaration order, including the universe canaries. Helper
definitions and the diagnostic axiom-print commands are not counted as assertions.

This document holds the full entries for the overlapping PhasedRun, QueryBounds and
RuntimeQueryBounds rows. The [parent port table][parent-port-table] lists the same contracts.

The two approved premises are:

- **P1 (passive verifier):** P1 restricts execution. The verifier's bundle queries happen only in
  the final decision. Each challenge comes from the supplied challenge implementation, which answers
  a `challengeSpec` query indexed by the challenge node. That index records only the challenge's
  structural location: the query carries no input and no sent oracle message. The runtime that
  answers it may have ambient state. Fresh independent public coins are an additional assumption on
  the chosen interpretation, and the types do not impose them. For example,
  [WARP §3.2](https://eprint.iacr.org/2025/753) specifies a uniformly random verifier message in
  each round.
- **P2 (fixed shape):** neither a challenge nor an oracle message directly selects the protocol's
  subtree. Only the prover's public messages select the continuation. A prover can choose those
  messages after seeing a challenge, so a challenge can still affect the continuation through the
  prover.

Each row has one of four statuses:

- **ported:** the new tests check the same mathematical observation, with the same quantifiers.
- **excluded by P1** (or **P2**): the row states exactly which assertion P1 (or P2) excludes.
- **removed:** the row names a mechanism that no longer exists.
- **open:** the row names an interface that the parent branch is missing.

A result that the parent already proves is linked directly instead of being copied.

## PhasedRun: 7 assertions

| Old-layer row | Contract | Status and where it is ported |
|---|---|---|
| <a id="p1"></a>[1][fp1] | Intrinsic queriers | ported: [produced entries][step-api] derive each querier from the executed participant; [queries_by_move_contract][p-step-log] checks them. |
| <a id="p2"></a>[2][fp2] | State, queriers, order | excluded by P1: P1 excludes verifier actions 2 and 3 before the challenge and action 6 at reception. The [queries_by_move_contract][p-step-log] test keeps all tags, passive groups and state. [actual_partial_transcripts][p-prefixes] keeps the moves of the partial transcripts. |
| <a id="p3"></a>[3][fp3] | Setup count | ported: [setup_queries_by_move_contract][p-setup-step] records a separate setup entry with both query 9 entries. |
| <a id="p4"></a>[4][fp4] | Final oracle message | ported: [run][p-accept], [lookup][p-payload], [actual_partial_transcripts][p-prefixes]. |
| <a id="p5"></a>[5][fp5] | Closing, log, groups | excluded by P1: P1 excludes reception effect 1 as a separate verifier group. The [closure/log][p-close] and [decision outcomes][p-decision] tests keep the outputs and histories of the run. [log erasure and setup/log laws][laws-api] keep the remaining groups and closing. |
| <a id="p6"></a>[6][fp6] | Explicit rejection | ported: [decision outcomes][p-decision]. |
| <a id="p7"></a>[7][fp7] | Fault 17, not rejection | removed: the old verifier returned `.fault 17` itself. A core verdict is an `Option`, so a verifier cannot return a fault. [answerAll_rejects][p-total] shows that mode 1 returns `.ok none` when the handler answers every request. |

The parent's queries by move supply the entry data: queriers, partial transcripts, membership and
the ordered query groups. `OracleVerifier.executeWith` runs the interaction and the final decision.
`runLoggingMoves` instruments strategies that the core runner `TwoParty.Lens.run` runs.
`runWithProverSetup` keeps the setup as an independently selectable entry, and
`toLog_runWithProverSetup` relates its log to the ordinary logged execution. These are parent
declarations, and the tests here add no second executor.

For row 2, passivity changes the ambient order. The old order is `[9, 9, 1, 2, 3, 4, 5, 6, 7]`.
The passive order is `[9, 9, 1, 4, 5, 2, 3, 6, 7]`. The [queries_by_move_contract][p-step-log]
test checks state `2102563478` and the produced passive groups. The
[actual_partial_transcripts][p-prefixes] test checks the challenge and oracle message values in
the partial transcripts. The local [accepting run][p-accept] quantifies
over oracle message, private output and challenge independently.

Row 5 keeps input 7, accepted target 11, materialized answer 18, the sent-answer log and the
ambient history `[9, 0, 1, 2]`. P1 moves reception effect 1 into the final decision together with
effect 2. The remaining observations by move are ported through `toLog_runWithQueriesByMove`,
`map_fst_runWithQueriesByMove` and `simulateQ_toLog_runWithQueriesByMove` in
[QueriesByMoveLaws][laws-api]. The
closing audits at L201 and L202 have those same exact targets in the
[parent port table][parent-phase-audits].

Row 6 uses the closing prover and the final-decision interpreter. The test first runs the prover
and captures the completed transcript, the private output and the prover query log. It then calls
`OracleVerifier.decideCatching` on that transcript and the input data. Rejection is
`Except.ok none`, and acceptance is `Except.ok (some (message, old + message))`. Both keep the same
transcript, an arbitrary hidden private output, the prover log, the decision's log of answered
queries and the history `[9, 0, 1, 2]`. Acceptance closes with the same run's input and message.

Row 7 is removed. The old verifier's terminal action returned `.fault 17` itself. In the port,
mode 1 requests tag 17, and the ambient handler `decisionHandler` throws 17. When the handler
answers every request, [answerAll_rejects][p-total] shows that mode 1 returns `.ok none` and that
the history records request 17 after `[9, 0, 1, 2]`.

**Handler failure.** The first conjunct of [decision_outcomes][p-decision] checks that a handler
failure keeps its label 17, the transcript, the private output, the prover log and the queries
answered before the failure. The failed request has no answer, so it adds no entry to the log of
answered queries. This check is additional coverage: no old PhasedRun assertion runs a failing
handler. No fault is encoded as an accepted value, and `OracleVerifier.decide` is unchanged.

## Prefix: 8 assertions

| Old-layer row | Contract | Status and where it is ported |
|---|---|---|
| [1][fx1] | Shared structural cursor | ported: [shared spine][x-cursor]. |
| [2][fx2] | Different partial transcripts | ported: [distinct full moves][x-distinct]. |
| [3][fx3] | The crossed send gives a sent oracle | ported: [root_sent_after_send][x-root-sent] shows that the root oracle node of `mixed` is sent after the Boolean is sent, for either Boolean. The [crossed-send query][x-query] reads the answer from that oracle message. |
| [4][fx4] | The root has no sent oracle for that send | ported: [root_not_sent_empty][x-root-empty] shows that the root oracle node of `mixed` is not sent at `PartialTranscript.empty`. |
| [5][fx5] | A send of an empty oracle message type permits a root partial transcript | ported: [root moves][x-empty-root]. |
| [6][fx6] | No realization crosses an empty send | ported: [crossed moves][x-empty-moves]. |
| [7][fx7] | Prefix length two | ported: [length][x-length], [completion][x-complete]. |
| [8][fx8] | The first hidden realization is true | ported: [oracle message in the partial transcript][x-payload]. |

Rows 3–4 use the parent's `PartialTranscript` interface in [SentOracles][sent-api] on the original
`mixed` protocol. `IsSent` says that some sent oracle message has a given node name.
`SentOracleMessageIndex` at an empty partial transcript is empty, while crossing an oracle send
adds the sent oracle message for that node. `IsSent.mono` keeps `IsSent` true when the partial
transcript is extended. The crossed-send query runs on a standalone prefix protocol: the
[prefix append identity][x-prefix] identifies it as `mixed` up to the send, and the
[crossed-send query][x-query] reads its own oracle message without choosing the future public
message. [Completed-path lookup][x-sent] checks that oracle message for every later choice. [AccessExample 3][a-unsent] and [4][a-sent] check the typed access boundary.

## QueryBounds: 17 assertions

| Old-layer row | Contract | Status and where it is ported |
|---|---|---|
| <a id="q1"></a>[1][fq1] | Per-query cost | ported: [route_cost][c-route]. |
| <a id="q2"></a>[2][fq2] | Source cost five | ported: [program_cost][c-program]. |
| <a id="q3"></a>[3][fq3] | Routed cost five | ported: [routed_cost][c-routed]. |
| <a id="q4"></a>[4][fq4] | Queried oracles were sent | ported: [raw_available][q-raw-available] proves that every query in the completed bundle has a matching node at the produced decision entry. [routed_available][q-available] applies that permission to the routed program. [loggedSummary_eq][q-log] and [composed_decisionQueries][q-decision-queries] check the actual ordered queries separately. |
| <a id="q5"></a>[5][fq5] | Old/old/fresh log | ported: [loggedSummary_eq][q-log]. |
| <a id="q6"></a>[6][fq6] | Future exclusion | ported: [exclusion][q-future] for every prefix program; [joinEntry_isSent][q-join-sent] excludes the node of the future oracle at the produced join entry. |
| <a id="q7"></a>[7][fq7] | Old/fresh identities | ported: [typed identity][q-repeat], [joinEntry_node][q-join-node] and [decisionEntry_isSent][q-decision-sent]. |
| <a id="q8"></a>[8][fq8] | Closing keeps the log | ported: [loggedSummary_eq][q-log]. |
| <a id="q9"></a>[9][fq9] | Produced join partial transcript | ported: [joinEntry_before][q-join-before]. |
| <a id="q10"></a>[10][fq10] | Decision-entry partial transcript | ported: [decisionEntry_before][q-decision-before]. |
| <a id="q11"></a>[11][fq11] | Join membership | ported: [joinEntry_mem][q-join-member]. |
| <a id="q12"></a>[12][fq12] | Decision-entry membership | ported: [decisionEntry_mem][q-decision-member]. |
| <a id="q13"></a>[13][fq13] | Sent oracles and cost | ported: [routed_available_and_cost][q-available-cost] applies the decision entry's permission to the routed program and proves its structural cost bound of five. [composed_decisionQueries][q-decision-queries] checks the actual ordered queries of the same queries-by-move result. |
| <a id="q14"></a>[14][fq14] | Node-name inclusion | ported: [joinEntry_node][q-join-node]; `availableMap_node`, `liftQuery_node` and `sentOracleMessageMap_query` in [SentOracles][sent-api] keep node names, query arguments and routing. |
| <a id="q15"></a>[15][fq15] | Join exclusion | ported: [joinEntry_isSent][q-join-sent] excludes the future oracle regardless of budget; [exclusion][q-future] proves the typed program law. |
| <a id="q16"></a>[16][fq16] | Queries by move | ported: [queries_by_move_source_log_contract][q-step-source] and `simulateQ_toLog_runWithQueriesByMove` in [QueriesByMoveLaws][laws-api]. |
| <a id="q17"></a>[17][fq17] | Four is insufficient | ported: [cost-five path][c-lower]. |

Rows 5 and 8 use `composed.runWithLog`. For every `a` and `b`, the doubled export records two
entries for the prefix oracle with answer `a`. The entry for the suffix oracle with answer `b`
follows. The same assertion checks private output `a + b` and verdict `some (a + a + b)`. The
[one/two specialization][q-concrete-log] recovers private output 3 and accepted result 4. Output
closing uses that same bundle; this fixture's output family is empty.

Rows 9–12 and 14–16 reuse the parent's `LoggedExecutionTests` two-oracle execution. Its
`joinEntry_mem`, `decisionEntry_mem`, `joinEntry_before`, `decisionEntry_before`,
`entry_intrinsic_queriers`, `joinEntry_node`, `joinEntry_isSent`, `decisionEntry_isSent` and
`queries_by_move_source_log_contract` already prove the old observations. The join is the entry of
the first suffix prover move. P1 excludes the old verifier decision at that seam, and the new tests
keep its partial transcript and membership. They add no duplicate assertions or executor.
`toLog_runWithQueriesByMove` and `simulateQ_toLog_runWithQueriesByMove` relate entries and log for
every prover, including this branch's composed verifier.

Rows 4 and 13 use `composedQueriesByMove a b`, which comes from `composed.runWithQueriesByMove`.
`rawAvailable` matches a raw query's node name, computed from the completed transcript, with an
oracle that was sent at the decision entry of that execution. That entry's partial transcript is
the whole transcript, so [raw_available][q-raw-available] holds for every query in the completed
bundle, not only for the queries the program makes. [routed_available][q-available] applies this
permission to the routed program, and [routed_available_and_cost][q-available-cost] pairs it with
the cost-five bound. The actual ordered queries are checked separately. [loggedSummary_eq][q-log]
checks them on the logged run. [composed_decisionQueries][q-decision-queries] checks the
`decisionQueries` field of the same queries-by-move result: two reads of the prefix oracle with
answer `a`, then one read of the suffix oracle with answer `b`. The `decision` entry's own `queries`
field holds only the ambient projection. The [run transcript][q-run],
[split oracle messages][q-split], [prefix oracle message][q-prefix-payload] and
[suffix oracle message][q-suffix-payload] stay as additional checks.

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
| <a id="r10"></a>[10][fr10] | Informed order | excluded by P1: P1 excludes the dummy-before-reveal order; [passive split][p-informed-split]. |
| <a id="r11"></a>[11][fr11] | Setup import cost | ported: [setup_budget][c-setup]. |
| <a id="r12"></a>[12][fr12] | Generic runtime split | excluded by P1: P1 excludes the effectful-prefix order; [all-prover passive law][run-append]. |
| <a id="r13"></a>[13][fr13] | Logged guess history | ported: ambient projection, [log][p-guess-log]. |
| <a id="r14"></a>[14][fr14] | Logged informed order | excluded by P1: P1 excludes the dummy-before-reveal order; [passive log][p-informed-log]. |
| <a id="r15"></a>[15][fr15] | Run import cost | ported: [import_budget][c-import]. |
| <a id="r16"></a>[16][fr16] | Joint half bound | ported: [joint][c-joint] with the input node-name and inclusion laws in [SentOracles][sent-api]. |
| <a id="r17"></a>[17][fr17] | Charge 7, success 1 | ported: [charge seven and success one][c-informed] for the passive schedule, and the [answer outcome][r-informed-answers]. |
| [17][fr17] | Dummy-before-reveal order | excluded by P1: the old history has the prefix verifier's dummy request before both reveals. P1 excludes that order, as for rows 10 and 14. The passive [trace][c-informed] has reveal, dummy request, reveal. |

Rows 1, 2, 5, 8 and 16 use the input case of the parent's `queryNode`, `availableMap_node` and
`liftNode` in [SentOracles][sent-api]. The prefix has no sent oracle: its export reads only its
input, whose node name is `.inl` of that same input index at every partial transcript. The inclusion keeps that
input index unchanged. The linked access and cost tests quantify over every relevant path and view,
and use precisely that input query.

Row 3's decision performs the dummy request and accepts the unit statement, and its output map is
exactly the input projection. Row 4 checks the entire effectful decision and the output map on
arbitrary bundle data. The [routed export query][r-route] identifies the input oracle that the
cost theorem uses. The delegated exact-decision and output-map obligations therefore have
counterparts here, with the node names of the inputs supplied by the parent.

For rows 9 and 13, the full trace includes a challenge event. Its ambient projection is exactly
`[false ↦ false, true ↦ hidden]`, the final state is `(hidden, 2)` and the charge is four. The
[parent split check][p-guess-split] and the direct logged check keep that same ambient history.
Under the passive schedule, row 12 is ported by the general whole-prover `OracleVerifier.run_append`
with its [ordinary-import client][p-general-split]. It quantifies over arbitrary whole provers, not
just the guessing and informed examples. Applying runtime execution and the pure
state/trace/charge outcome to this open-program equality proves the charged runtime/history
equality for every such prover. The exact target is the stronger
[open-program split law][run-append]. No two-prover specialization counts as the all-prover port.
P1 separately excludes the old effectful-prefix order.

For rows 10 and 14 and the order part of row 17, the informed prover reveals at the seam before
the passive prefix's dummy request. The ambient order is `[true ↦ hidden, false ↦ false, true ↦ hidden]`. The old order was
`[false ↦ false, true ↦ hidden, true ↦ hidden]`. Both have final state `(hidden, 3)` and charge
seven. The old dummy-before-reveal order needs a non-passive prefix verifier, so P1 excludes it. It
is not an open question about which steps are allowed. The extra passive history does not port the
former order.

The row-16 conjunction holds for every fixed guess and secret. It includes the exact prefix
decision and export, the typed access and cost certificates, the import budget, the charged
history and the half bound. [Answers][r-guess-answers] keep the materialized output oracle and target, and
[guess_success][r-guess-success] proves probability exactly one half. This conjunction uses the
parent's node names for inputs and the inclusion laws described above. The row-17 passive
conjunction keeps charge seven and [success one][r-informed-success], with its different order
stated explicitly, and its [answer outcome][r-informed-answers]. Neither theorem derives
arbitrary-prover security from access and cost certificates alone.

These fixtures measure three different quantities, with different interfaces and prices. The
doubled export's routed suffix has a completed path of cost five, which excludes a bound of four
(QueryBounds row 17). In the hidden-bit runtime, both runs import one coin, and their ambient
histories cost four for a fixed guess and seven for the informed prover. The success event
compares the exported oracle answer with the accepted target. The half bound holds for the fixed
guess because of that prover's behavior. It is not a soundness premise, and these fixture bounds
are not a general resource contract.

[routed_suffix_budget][c-suffix-routed] uses `OracleMap.withAmbient_worstCaseCost` to transfer
the suffix decision's bound through the route. Each routed bundle query costs at most the
corresponding source query's charge.

## AccessExample: 18 assertions

| Old-layer row | Contract | Status and where it is ported |
|---|---|---|
| [1][fa1] | Before false send: inputs only | ported: [no sent oracle][a-before-f]. |
| [2][fa2] | Before true send: inputs only | ported: [no sent oracle][a-before-t]. |
| [3][fa3] | Unsent query rejected by typing | ported: [negative client][a-unsent]. |
| [4][fa4] | The oracle can be queried after its send | ported: [positive client][a-sent]. |
| [5][fa5] | False-branch response is Bool | ported: [response type][a-bool]. |
| [6][fa6] | True-branch response is Fin 3 | ported: [response type][a-fin]. |
| [7][fa7] | Inputs and one sent oracle | removed: literal `Access.extend` index layout; [oracle indices][a-slots] keep the count of inputs plus one oracle message. |
| [8][fa8] | Access restriction/rebuild | removed: stored `AccessDecoration.restrict_build`; [independent future][a-future] keeps a future that does not depend on the oracle message. |
| [9][fa9] | Different execution paths | ported: [distinct oracle messages][a-distinct]. |
| [10][fa10] | Access depends only on the path | ported: [path][a-shape], [family][a-family]. |
| [11][fa11] | Terminal send can be queried | removed: literal `Access.extend` index layout; [terminal oracles][a-terminal] keep the terminal send queryable. |
| [12][fa12] | Non-faithful terminal response is Nat | ported: [response type][a-nat]. |
| [13][fa13] | Route input 7 and sent 11 | ported: [sum eighteen][a-route], all hidden values. |
| [14][fa14] | Hidden pair coordinate is unobservable | ported: [handler equality][a-hidden]. |
| [15][fa15] | Second send cannot be queried | ported: [negative client][a-missing-second]. |
| [16][fa16] | Second oracle after two sends | ported: [second answer][a-second]. |
| [17][fa17] | Large message universe | ported: [independent universes][a-large-data]. |
| [18][fa18] | Large query universe | ported: [independent universes][a-large-query]. |

Rows 7 and 11 keep the count of input oracles plus one oracle message. They do not assert literal equality
with the old `Access.extend` query-index layout `Unit ⊕ Unit`. The interaction layer uses family
indices and sigma-indexed interface queries, and heterogeneous bundles keep their data as a pair.
The [one-oracle uniqueness test][a-single] excludes an extra sent oracle. Row 8 keeps
future selection that does not depend on the oracle message, but `AccessDecoration.restrict_build` was an identity about
stored per-node access decorations. There is no such decoration to restrict or rebuild now.
`pathBundle` computes the bundle of a completed path, and composition routes it explicitly.

Rows 17–18 quantify over every message type, interface and initial polynomial at the exact
universe instantiations of the old tests. Row 17 uses `OracleInterface.{1, 0}` on
`Messages : Type 1` and initial and result `PFunctor.{0, 1}`. Row 18 uses
`OracleInterface.{0, 1}` on `Messages : Type` and initial and result `PFunctor.{1, 0}`.
[OracleBundle.sum][bundle-sum] extends an arbitrary prior query handler with the given interface and
its message realization. Neither test restricts the prior polynomial, replaces a family with a
constant, or uses a universe lift. These tests cover bundle extension; DecorationExample 2
separately checks interfaces inside protocol oracle nodes.

## DecorationExample: 13 assertions

| Old-layer row | Contract | Status and where it is ported |
|---|---|---|
| [1][fd1] | Role decorations at arbitrary tree universe | removed: no authored role decoration. |
| [2][fd2] | Raw oracle/query universes | ported: [arbitrary-tree decoration][d-decoration] at independent message and query universes; [unequal-universe node and path bundles][d-node]. |
| [3][fd3] | Protocol bundle at arbitrary universe | ported: [protocol canary][d-protocol]. |
| [4][fd4] | Branching root chosen by the receiver | excluded by P2: P2 excludes subtree selection by the receiver; [sender root][d-root] makes the choice prover-authored. |
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
select branches in [oracleSig][oracle-signature]. A choice by the receiver that changes the
next oracle type is therefore not represented by this fixture. Row 4 records that change of
authoring model instead of calling the sender test a port of the receiver test.

Rows 1, 8–9 and 13 used separate role and oracle decorations and restricted those stored objects.
They also converted to a second runtime tree with a second role assignment. Oracle positions now carry
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
family. It does not merely install the interface in the input bundle. The parent's
[lifted_queries_by_move_contract][d-node-run] also runs such a node, queries its oracle message and
checks the partial transcript at its decision entry. The optional leaf parameter makes the message universe
visible in the alias's domain, as in the parent `OracleProtocol`; it is an actual tree return type.

## MixedExample: 9 assertions

| Old-layer row | Contract | Status and where it is ported |
|---|---|---|
| [1][fm1] | Arbitrary position universe | ported: [position canary][m-position]. |
| [2][fm2] | Arbitrary tree universe | ported: [tree canary][m-tree]. |
| [3][fm3] | Arbitrary branch-path universe | ported: [branch canary][m-branch]. |
| [4][fm4] | Arbitrary execution-path universe | ported: [execution canary][m-execution]. |
| [5][fm5] | Distinct hidden oracle messages give distinct full transcripts | ported: [inequality][m-distinct]. |
| [6][fm6] | Equal public choices give equal structural paths | ported: [path equality][m-shared] checks that the two full transcripts have equal structural paths. |
| [7][fm7] | False branch keeps the public choice only | ported: [false path][m-false]. |
| [8][fm8] | True branch erases the Fin 3 oracle message | ported: [true path][m-true]. |
| [9][fm9] | Complete runtime message | ported: [full transcript][m-runtime]. |

The branch selector is re-authored as a prover message, and row 9 no longer converts to a second
generic runtime tree. `PathAlong oracleSig` is already the full transcript. The new test checks the
complete transcript, including the public branch and oracle message. The separate
[oracle message lookup][m-payload] and [view-erasure test][m-view] also keep the observable boundary. The
position canary alone does not establish independent oracle-query universes, and DecorationExample
row 2 now checks that separate contract.

## Parent interfaces and remaining universe restriction

The merged parent supplies the queries-by-move and sent-oracle interfaces that earlier versions of
this table listed as missing. [QueriesByMove][step-api] produces entries with their partial
transcripts, queriers and query groups. [QueriesByMoveLaws][laws-api] supplies closing, ordinary erasure and the correspondence
with the log. [SentOracles][sent-api] supplies node names, the proof that an oracle was sent and
inclusion, together with query routing. The [parent port table][parent-port-table] and the tables
above identify their exact assertion targets. P1 excludes intermediate verifier effects, not the
produced prover moves.

`OraclePos.{u, q}`, `OraclePoly`, `oracleSig`, `viewSig`, `OracleProtocol`, `oracleMessageFamily` and
`pathBundle` keep independent node-query universes. General `OracleBundle.{u, uI, dI}` also
separates response, bundle-query and data universes without changing the shared
`OracleInterface`; families are a specialization. The earlier node-universe and input-data
coupling entries are therefore closed by the parent, as recorded in
[implementation note 18][universes].

The remaining item is the large-query result interface of the full-log runner. ArkLib accepts it
as an upstream limit (departures entry 18); [VCVio#1236](https://github.com/Verified-zkEVM/VCVio/pull/1236)
adds `OracleComp.subst`, which aims to lift it.
[OracleVerifier.runWithLog][logged-runner] returns bundle-query entries through a small
computation monad. Returning large query indices in that complete heterogeneous log needs a parent
logging interface with a sufficiently large result universe. `runWithAmbientLog` and
`runWithAmbientQueriesByMove` keep independent input-data, input-query and node-query universes by
returning only ambient decision queries. The full-log [loggedSummary][q-log-summary] keeps the
strongest supported output-query universe. P1 and P2 impose no universe restrictions. Run outputs
continue to follow the parent monad's value universe, as documented in note 18.

## Definition-site transparency

The only definition-site attribute this branch keeps is `@[instance_reducible]` on
`Interaction.AccessTypingTests.firstInterface`. It declares a value of the class
`OracleInterface`, and ordinary semireducibility triggers Lean's class-definition transparency
warning. The attribute gives this declaration the expected instance transparency, with no command
modifying another declaration. It replaces the former `@[reducible]` with a narrower choice. All 18
other definition-site fixture attributes were removed, and the ordinary-import clients are checked
without them. No added local or global `attribute [...]` transparency command and no
`set_option respectTransparency` remains.

[fp1]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/PhasedRun.lean#L84
[fp2]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/PhasedRun.lean#L91
[fp3]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/PhasedRun.lean#L114
[fp4]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/PhasedRun.lean#L121
[fp5]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/PhasedRun.lean#L178
[fp6]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/PhasedRun.lean#L194
[fp7]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/PhasedRun.lean#L198
[fx1]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Prefix.lean#L26
[fx2]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Prefix.lean#L28
[fx3]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Prefix.lean#L35
[fx4]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Prefix.lean#L40
[fx5]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Prefix.lean#L47
[fx6]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Prefix.lean#L49
[fx7]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Prefix.lean#L55
[fx8]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Prefix.lean#L58
[fq1]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/QueryBounds.lean#L96
[fq2]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/QueryBounds.lean#L117
[fq3]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/QueryBounds.lean#L130
[fq4]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/QueryBounds.lean#L149
[fq5]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/QueryBounds.lean#L165
[fq6]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/QueryBounds.lean#L184
[fq7]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/QueryBounds.lean#L209
[fq8]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/QueryBounds.lean#L225
[fq9]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/QueryBounds.lean#L251
[fq10]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/QueryBounds.lean#L252
[fq11]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/QueryBounds.lean#L255
[fq12]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/QueryBounds.lean#L257
[fq13]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/QueryBounds.lean#L266
[fq14]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/QueryBounds.lean#L277
[fq15]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/QueryBounds.lean#L286
[fq16]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/QueryBounds.lean#L300
[fq17]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/QueryBounds.lean#L320
[fr1]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L47
[fr2]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L57
[fr3]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L61
[fr4]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L72
[fr5]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L87
[fr6]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L102
[fr7]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L124
[fr8]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L145
[fr9]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L167
[fr10]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L182
[fr11]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L197
[fr12]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L207
[fr13]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L227
[fr14]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L235
[fr15]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L244
[fr16]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L258
[fr17]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean#L289
[fa1]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L42
[fa2]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L44
[fa3]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L47
[fa4]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L53
[fa5]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L55
[fa6]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L57
[fa7]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L64
[fa8]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L67
[fa9]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L79
[fa10]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L87
[fa11]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L109
[fa12]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L111
[fa13]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L121
[fa14]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L126
[fa15]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L133
[fa16]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L141
[fa17]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L147
[fa18]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean#L152
[fd1]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L25
[fd2]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L28
[fd3]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L32
[fd4]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L78
[fd5]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L81
[fd6]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L84
[fd7]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L87
[fd8]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L109
[fd9]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L114
[fd10]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L119
[fd11]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L124
[fd12]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L129
[fd13]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean#L133
[fm1]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L23
[fm2]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L26
[fm3]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L29
[fm4]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L32
[fm5]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L55
[fm6]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L60
[fm7]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L64
[fm8]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L68
[fm9]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean#L72
[a-before-f]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L54
[a-before-t]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L59
[a-unsent]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L65
[a-sent]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L74
[a-bool]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L78
[a-fin]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L82
[a-slots]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L87
[a-future]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L97
[a-distinct]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L105
[a-shape]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L110
[a-family]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L113
[a-terminal]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L134
[a-nat]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L138
[a-route]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L149
[a-hidden]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L154
[a-single]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L164
[a-missing-second]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L171
[a-second]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L187
[a-large-data]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L191
[a-large-query]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/AccessTyping.lean#L202
[d-protocol]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/PositionsAndOwners.lean#L23
[d-decoration]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/PositionsAndOwners.lean#L45
[d-root]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/PositionsAndOwners.lean#L118
[d-false-cursor]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/PositionsAndOwners.lean#L127
[d-true-cursor]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/PositionsAndOwners.lean#L131
[d-false-pos]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/PositionsAndOwners.lean#L135
[d-true-pos]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/PositionsAndOwners.lean#L139
[d-false-actor]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/PositionsAndOwners.lean#L142
[d-true-actor]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/PositionsAndOwners.lean#L146
[d-query]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/PositionsAndOwners.lean#L91
[d-false-interface]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/PositionsAndOwners.lean#L99
[d-true-interface]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/PositionsAndOwners.lean#L106
[d-oracle-actor]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/PositionsAndOwners.lean#L113
[m-position]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/MixedTranscripts.lean#L23
[m-tree]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/MixedTranscripts.lean#L27
[m-branch]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/MixedTranscripts.lean#L31
[m-execution]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/MixedTranscripts.lean#L35
[m-runtime]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/MixedTranscripts.lean#L87
[m-distinct]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/MixedTranscripts.lean#L57
[m-shared]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/MixedTranscripts.lean#L63
[m-false]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/MixedTranscripts.lean#L68
[m-true]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/MixedTranscripts.lean#L72
[m-payload]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/MixedTranscripts.lean#L77
[m-view]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/MixedTranscripts.lean#L81
[x-cursor]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/PartialTranscripts.lean#L39
[x-distinct]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/PartialTranscripts.lean#L42
[x-sent]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/PartialTranscripts.lean#L54
[x-empty-root]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/PartialTranscripts.lean#L85
[x-empty-moves]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/PartialTranscripts.lean#L90
[x-length]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/PartialTranscripts.lean#L104
[x-complete]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/PartialTranscripts.lean#L106
[x-payload]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/PartialTranscripts.lean#L109
[p-accept]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenSendRun.lean#L90
[p-payload]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenSendRun.lean#L93
[q-future]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/RoutedAccess.lean#L174
[q-log]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/RoutedAccess.lean#L243
[q-log-summary]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/RoutedAccess.lean#L235
[q-repeat]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/RoutedAccess.lean#L143
[q-run]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/RoutedAccess.lean#L209
[q-split]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/RoutedAccess.lean#L218
[q-prefix-payload]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/RoutedAccess.lean#L222
[q-suffix-payload]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/RoutedAccess.lean#L227
[q-concrete-log]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/RoutedAccess.lean#L250
[c-route]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L49
[c-program]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L70
[c-routed]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L79
[c-suffix]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L174
[c-suffix-routed]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L187
[c-setup]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L203
[c-history]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L209
[c-import]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L223
[c-joint]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L233
[c-informed]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L264
[c-lower]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L117
[c-input-cost]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L167
[r-export]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenBitAccess.lean#L45
[r-decide]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenBitAccess.lean#L60
[r-access]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenBitAccess.lean#L84
[r-route]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenBitAccess.lean#L106
[r-raw-access]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenBitAccess.lean#L121
[r-guess-answers]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenBitAccess.lean#L144
[r-informed-answers]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenBitAccess.lean#L154
[r-guess-success]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenBitAccess.lean#L165
[r-informed-success]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenBitAccess.lean#L185
[r-input]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenBitAccess.lean#L36
[r-map]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenBitAccess.lean#L51
[r-pre]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenBitAccess.lean#L54
[r-output]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenBitAccess.lean#L70
[p-close]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L239
[p-guess-log]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L774
[p-informed-log]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L784
[p-guess-split]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L807
[p-informed-split]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L818
[p-general-split]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/Routing.lean#L357
[run-append]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Oracle/Routing.lean#L123
[oracle-signature]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Signature.lean#L58
[bundle-sum]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/OracleVerifier.lean#L135
[logged-runner]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/Knowledge.lean#L338

[universes]:
    ../interaction-rebuild/IMPLEMENTATION-NOTES.md#18-run-outputs-are-tied-to-the-monad-universe

[x-query]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/PartialTranscripts.lean#L124
[x-root-sent]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/PartialTranscripts.lean#L69
[x-root-empty]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/PartialTranscripts.lean#L63

[x-prefix]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/PartialTranscripts.lean#L116

[d-distinct]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/PositionsAndOwners.lean#L150

[p-decision]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenSendRun.lean#L140
[p-total]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/HiddenSendRun.lean#L161

[parent-port-table]: port-logged-execution.md
[parent-phase-audits]: port-logged-execution.md#phasedrunlean

[laws-api]: ../../../ArkLib/Interaction/Oracle/QueriesByMoveLaws.lean
[step-api]: ../../../ArkLib/Interaction/Oracle/QueriesByMove.lean
[sent-api]: ../../../ArkLib/Interaction/Oracle/SentOracles.lean
[p-step-log]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L945
[p-prefixes]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L965
[p-setup-step]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L991
[q-join-before]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1092
[q-decision-before]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1097
[q-join-member]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1084
[q-decision-member]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1087
[q-join-node]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1117
[q-join-sent]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1123
[q-decision-sent]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1134
[q-step-source]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1145
[d-node-run]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L1213

[d-node]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/ProtocolTree/PositionsAndOwners.lean#L33

[q-available]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/RoutedAccess.lean#L295
[q-raw-available]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/RoutedAccess.lean#L277
[q-decision-queries]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/RoutedAccess.lean#L263

[q-available-cost]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L84
