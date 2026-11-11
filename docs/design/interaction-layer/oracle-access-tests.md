# Oracle test dispositions

This reference accounts for all 89 frozen assertions in the seven files below. The eight
interaction layer modules port these files; `QueryCost.lean` collects cost and profile assertions
from `QueryBounds`, `RuntimeQueryBounds` and `PhasedRun`, rather than porting an eighth source file.
Row numbers follow frozen declaration order, including the universe canaries. Helper definitions
and diagnostic axiom-print commands are not additional assertions.

This document holds the full dispositions for the overlapping PhasedRun, QueryBounds and
RuntimeQueryBounds rows. The [parent inventory][parent-inventory] links these rows rather than
maintaining a second disposition. Its `child-owned` status identifies these delegated ports;
it does not imply that unresolved parts of a compound frozen assertion have been discharged.

Each row links the frozen assertion and the exact replacement test, theorem, or explicit
retirement. **Preserved** means the indicated semantic contract and its quantifiers are retained.
**Partial** names a retained part and any unresolved dimension; it is not an equivalence.
**Changed** identifies a different behavior. **Retired** means the tested object or operation no
longer exists. **Unresolved** names a restriction requiring an owner change. Parent-owned results
are linked directly; they are not duplicated to increase a coverage count.

## PhasedRun: 7 assertions

| Frozen row | Contract | Disposition and evidence |
|---|---|---|
| <a id="p1"></a>[1][fp1] | Intrinsic phase owners | Unresolved: produced phase artifact. |
| <a id="p2"></a>[2][fp2] | State, owners, order | Partial: [passive run][p-order]; see below. |
| <a id="p3"></a>[3][fp3] | Setup count | Partial: [count][c-count]; unresolved phase artifact. |
| <a id="p4"></a>[4][fp4] | Final payload | Preserved: [run][p-accept], [lookup][p-payload]. |
| <a id="p5"></a>[5][fp5] | Closing, log, groups | Partial: [closure/log][p-close]; see below. |
| <a id="p6"></a>[6][fp6] | Explicit rejection | Preserved: [terminal outcomes][p-terminal]. |
| <a id="p7"></a>[7][fp7] | Fault 17, not rejection | Preserved: [terminal outcomes][p-terminal]. |

Rows 1, 2, 3 and 5 still need a produced per-slot phase artifact with intrinsic owners,
accumulated full prefixes and membership. The two logs of `runWithLog` do not supply that
interface. This missing allowed-phase information is **unresolved**, not retired merely because
the old `PhasedRun.phases` field is absent. Row 3 retains setup multiplicity in the
[whole prover log][c-prover-log], but not an independently selectable setup-phase artifact.

Passivity does require changing row 2's verifier chronology. Its ambient order
`[9, 9, 1, 2, 3, 4, 5, 6, 7]` becomes `[9, 9, 1, 4, 5, 2, 3, 6, 7]` when the verifier effects
move to the end decision. The [parent runtime check][p-order] retains every action tag, payload,
private output and verdict and witnesses the changed order by its digit state. The local
[accepting run][p-accept] independently quantifies payload, private output and challenge.
The non-passive verifier placements are premise-required changes; the remaining per-boundary
owner/prefix information is still unresolved.

Row 5 retains input 7, accepted target 11, materialized oracle answer 18, the sent-answer log and
ambient history `[9, 0, 1, 2]`. Passivity moves reception effect 1 into the final decision with
effect 2. It excludes that former effectful reception boundary, but does not justify dropping
phase artifacts for the remaining allowed slots. Their owner/prefix interface is unresolved.
The frozen closing audits at L201/L202 are inventoried separately in the
[parent's phase section][parent-phase-audits]; they need that phase artifact's closing laws.

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
| [1][fx1] | Shared structural cursor | Preserved: [shared spine][x-cursor]. |
| [2][fx2] | Different execution prefixes | Preserved: [distinct full moves][x-distinct]. |
| [3][fx3] | The crossed send is available | Partial: [crossed-send query][x-query]; see below. |
| [4][fx4] | The root cannot access that send | Partial: [empty prefix has no slot][x-no-slot]. |
| [5][fx5] | An empty-payload send permits a root prefix | Preserved: [root moves][x-empty-root]. |
| [6][fx6] | No realization crosses an empty send | Preserved: [crossed moves][x-empty-moves]. |
| [7][fx7] | Prefix length two | Preserved: [length][x-length], [completion][x-complete]. |
| [8][fx8] | The first hidden realization is true | Preserved: [full prefix payload][x-payload]. |

Rows 3–4 used `ExecutionPrefix.Available`, a predicate on cursor occurrences and accumulated
contexts. A corresponding canonical prefix-availability interface in Core remains unresolved.
The replacement reads a crossed payload from full prefix moves and indexes resource queries
by the completed shape of the decision's protocol.
The [prefix append identity][x-prefix] identifies the actual stage ending immediately after the
send. Its query is answered from that stage's own payload without choosing the future public
message. The [completed-path lookup][x-sent] also checks the payload for every later choice. The
partial tests do not supply that unresolved prefix-availability interface. The before/after query
rejection and acceptance clients in [AccessExample 3][a-unsent] and [4][a-sent] retain the
corresponding typed-access boundary. No independent availability annotation can authorize an
unsent slot.

## QueryBounds: 17 assertions

| Frozen row | Contract | Disposition and evidence |
|---|---|---|
| <a id="q1"></a>[1][fq1] | Per-query cost | Preserved: [route_cost][c-route]. |
| <a id="q2"></a>[2][fq2] | Source cost five | Preserved: [program_cost][c-program]. |
| <a id="q3"></a>[3][fq3] | Routed cost five | Preserved: [routed_cost][c-routed]. |
| <a id="q4"></a>[4][fq4] | Available queries | Partial: [typed route][q-route]; unresolved names. |
| <a id="q5"></a>[5][fq5] | Old/old/fresh log | Preserved: [actual logged run][q-log]. |
| <a id="q6"></a>[6][fq6] | Future exclusion | Partial: [exclusion][q-future]; unresolved names. |
| <a id="q7"></a>[7][fq7] | Old/fresh identities | Partial: [typed identity][q-repeat]; see below. |
| <a id="q8"></a>[8][fq8] | Closing keeps the log | Preserved: [closed run log][q-log]. |
| <a id="q9"></a>[9][fq9] | Produced join prefix | Unresolved: per-slot prefix artifact. |
| <a id="q10"></a>[10][fq10] | Terminal prefix | Unresolved: per-slot prefix artifact. |
| <a id="q11"></a>[11][fq11] | Join membership | Unresolved: phase artifact membership. |
| <a id="q12"></a>[12][fq12] | Terminal membership | Unresolved: phase artifact membership. |
| <a id="q13"></a>[13][fq13] | Availability/cost | Partial: [typed cost five][c-joint-cost]. |
| <a id="q14"></a>[14][fq14] | Name inclusion | Partial: [typed][q-repeat]; unresolved names. |
| <a id="q15"></a>[15][fq15] | Join exclusion | Partial: [typed][q-future]; unresolved prefix. |
| <a id="q16"></a>[16][fq16] | Phased log | Partial: [raw log][q-log]; unresolved phase API. |
| <a id="q17"></a>[17][fq17] | Four is insufficient | Preserved: [cost-five path][c-lower]. |

Rows 5 and 8 use the actual `composed.runWithLog`, not an isolated export simulation. For every
`a` and `b`, a query to the doubled export records two prefix-slot entries with answer `a`, then
the suffix-slot entry with answer `b`. The same assertion checks private output `a + b` and
verdict `some (a + a + b)`. The [one/two specialization][q-concrete-log] recovers private output
3, accepted result 4 and the frozen three answers. The log precedes answering the resource
queries, detecting dropped or coalesced expansion entries. Row 8 needs no separate closing
executor: `runWithLog` returns materialized output data; this fixture's output family is empty.

Rows 4, 6, 7, 13, 14 and 15 need canonical accumulated-prefix query names, availability and
inclusion certificates. That mathematical interface is **unresolved**. Typed routing does not
replace the missing certificates: [both old reads][q-repeat] use the literal same prefix slot,
[fresh routing][q-fresh] uses the [distinct suffix slot][q-distinct], and the
[negative client][q-untyped] rejects a suffix query in prefix resources. The exclusion theorem
holds for every prefix program without a budget restriction. These are the expressible parts
of rows 4, 6, 7, 13–15, not a proof of canonical naming at the produced join.

Rows 9–12 and 16 need a produced per-slot phase artifact with accumulated full prefixes,
intrinsic owners and membership, plus its logged-run correspondence. These interfaces remain
**unresolved**. The existing [run transcript][q-run], [split payloads][q-split],
[prefix payload][q-prefix-payload] and [suffix payload][q-suffix-payload] retain same-run data;
they do not prove that a join or terminal prefix is a member of an actual phase collection.
Row 13 retains the routed cost-five bound and typed access but still needs canonical phase-prefix
availability. Row 14 retains typed identity under routing but still needs canonical names under
join-to-terminal inclusion. Row 15 retains typed future exclusion but still needs availability
at the actual produced join. Row 16 retains the exact raw log but still needs the phase/log law.
All these missing components require the corresponding parent Core interfaces; changing an API
name alone does not discharge them.

## RuntimeQueryBounds: 17 assertions

| Frozen row | Contract | Disposition and evidence |
|---|---|---|
| <a id="r1"></a>[1][fr1] | Export access | Partial: [access][r-export], [cost][c-input-cost]. |
| <a id="r2"></a>[2][fr2] | Source name | Unresolved names; [typed input query][r-input] retained. |
| <a id="r3"></a>[3][fr3] | Dummy and export | Preserved: [decision][r-pre], [map][r-map]. |
| <a id="r4"></a>[4][fr4] | Suffix equation | Preserved: [decision][r-decide], [data][r-output]. |
| <a id="r5"></a>[5][fr5] | Suffix permissions | Partial: [typed][r-access]; unresolved names. |
| <a id="r6"></a>[6][fr6] | Suffix cost five | Preserved: [suffix_budget][c-suffix]. |
| <a id="r7"></a>[7][fr7] | Routed cost five | Preserved: [routed bound][c-suffix-routed]. |
| <a id="r8"></a>[8][fr8] | Raw permissions | Partial: [typed][r-raw-access]; unresolved names. |
| <a id="r9"></a>[9][fr9] | Guess history | Preserved ambient history: [charged run][c-history]. |
| <a id="r10"></a>[10][fr10] | Informed order | P1 order: [split][p-informed-split]. |
| <a id="r11"></a>[11][fr11] | Setup import cost | Preserved: [setup_budget][c-setup]. |
| <a id="r12"></a>[12][fr12] | Generic runtime split | [All-prover law][run-append]; see below. |
| <a id="r13"></a>[13][fr13] | Logged guess history | Preserved ambient: [log][p-guess-log]. |
| <a id="r14"></a>[14][fr14] | Logged informed order | P1 order: [log][p-informed-log]. |
| <a id="r15"></a>[15][fr15] | Run import cost | Preserved: [import_budget][c-import]. |
| <a id="r16"></a>[16][fr16] | Joint half bound | Partial: [joint][c-joint]; unresolved names. |
| <a id="r17"></a>[17][fr17] | Charge 7, success 1 | [Passive theorem][c-informed]; order changed. |

Rows 1, 2, 5, 8 and 16 need canonical accumulated-prefix names, availability and inclusion.
Those components remain **unresolved**, even though the typed permission and cost parts are
ported. The current assertions quantify over every relevant path and view and identify exact
input/export indices. The prefix has no sent oracle, so its export reads only its input. These
facts do not supply the missing canonical prefix-context certificates.

Row 3's decision performs the dummy request and accepts the unit statement; its output map is
exactly the input projection. Row 4 checks the entire effectful decision and the output map on
arbitrary resource data. The [routed export query][r-route] identifies the input slot used by
the cost theorem. Thus the delegated exact-decision and output-map obligations have actual
counterparts, independently of the unresolved canonical naming interface.

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
conjunction does not supply the unresolved canonical availability certificates of the full row.
The row-17 passive conjunction retains charge seven and [success one][r-informed-success],
with its different order explicit and its [actual answer observation][r-informed-answers].
Neither theorem derives arbitrary-prover security from access/cost certificates alone.

## AccessExample: 18 assertions

| Frozen row | Contract | Disposition and evidence |
|---|---|---|
| [1][fa1] | Before false send: inputs only | Preserved: [no sent slot][a-before-f]. |
| [2][fa2] | Before true send: inputs only | Preserved: [no sent slot][a-before-t]. |
| [3][fa3] | Unsent query rejected by typing | Preserved: [negative client][a-unsent]. |
| [4][fa4] | Same resource available after send | Preserved: [positive client][a-sent]. |
| [5][fa5] | False-branch response is Bool | Preserved: [response type][a-bool]. |
| [6][fa6] | True-branch response is Fin 3 | Preserved: [response type][a-fin]. |
| [7][fa7] | Inputs and one sent slot | Partial: [slot indices][a-slots]; layout retired. |
| [8][fa8] | Access restriction/rebuild | Partial: [independent future][a-future]. |
| [9][fa9] | Different full execution paths | Preserved: [distinct payloads][a-distinct]. |
| [10][fa10] | Access depends only on shape | Preserved: [shape][a-shape], [family][a-family]. |
| [11][fa11] | Terminal send available | Partial: [terminal slots][a-terminal]; layout retired. |
| [12][fa12] | Non-faithful terminal response is Nat | Preserved: [response type][a-nat]. |
| [13][fa13] | Route input 7 and sent 11 | Preserved: [sum eighteen][a-route], all hidden values. |
| [14][fa14] | Hidden pair coordinate is unobservable | Preserved: [handler equality][a-hidden]. |
| [15][fa15] | Second send unavailable | Preserved: [negative client][a-missing-second]. |
| [16][fa16] | Second slot after two sends | Preserved: [second answer][a-second]. |
| [17][fa17] | Large message universe | Preserved: [independent universes][a-large-data]. |
| [18][fa18] | Large query universe | Preserved: [independent universes][a-large-query]. |

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
resource extension, not independently quantified interfaces inside protocol oracle nodes.

## DecorationExample: 13 assertions

| Frozen row | Contract | Disposition and evidence |
|---|---|---|
| [1][fd1] | Role decorations at arbitrary tree universe | Retired: no authored role decoration. |
| [2][fd2] | Raw oracle/query universes | Unresolved: [node coupling][oracle-position]. |
| [3][fd3] | Protocol bundle at arbitrary universe | Preserved: [protocol canary][d-protocol]. |
| [4][fd4] | Receiver-owned branching root | Changed: [sender root][d-root]. |
| [5][fd5] | False future owner | Preserved: [position][d-false-pos], [owner][d-false-owner]. |
| [6][fd6] | True future owner | Preserved: [position][d-true-pos], [owner][d-true-owner]. |
| [7][fd7] | False oracle has Unit queries | Preserved: [query type][d-query]. |
| [8][fd8] | False oracle subtree | Partial: [interface][d-false-interface]; restriction retired. |
| [9][fd9] | True oracle subtree | Partial: [interface][d-true-interface]; restriction retired. |
| [10][fd10] | After false marker | Preserved: [cursor][d-false-cursor], [owner][d-false-owner]. |
| [11][fd11] | After true marker | Preserved: [cursor][d-true-cursor], [owner][d-true-owner]. |
| [12][fd12] | Oracle node's implicit owner is sender | Preserved: [node owner][d-oracle-owner]. |
| [13][fd13] | Owner after erasure | Partial: [owner][d-oracle-owner]; erasure retired. |

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

Row 2 is specifically unresolved. The one-universe protocol alias and AccessExample 17–18 are
not replacements for independent message/query universes at a protocol oracle node. The owning
change is specified below.

## MixedExample: 9 assertions

| Frozen row | Contract | Disposition and evidence |
|---|---|---|
| [1][fm1] | Arbitrary position universe | Preserved: [position canary][m-position]. |
| [2][fm2] | Arbitrary tree universe | Preserved: [tree canary][m-tree]. |
| [3][fm3] | Arbitrary branch-path universe | Preserved: [branch canary][m-branch]. |
| [4][fm4] | Arbitrary execution-path universe | Preserved: [execution canary][m-execution]. |
| [5][fm5] | Distinct hidden payloads give distinct paths | Preserved: [inequality][m-distinct]. |
| [6][fm6] | Equal public choices give equal shapes | Preserved: [projection equality][m-shared]. |
| [7][fm7] | False branch retains public choice only | Preserved: [false shape][m-false]. |
| [8][fm8] | True branch erases Fin 3 payload | Preserved: [true shape][m-true]. |
| [9][fm9] | Complete runtime message | Preserved: [full transcript][m-runtime]. |

The branch selector is re-authored as a prover message, and row 9 no longer converts to a second
generic runtime tree. `PathAlong oracleSig` is already the full runtime transcript. The new
assertion checks the complete transcript, including the public branch and payload; the separate
[payload lookup][m-payload] and [view-erasure test][m-view] also preserve the observable boundary.
The position canary does not establish independent oracle-query universes; that is the distinct
unresolved DecorationExample row 2.

## Shared unresolved parent interfaces

A produced per-slot phase artifact must associate actual execution slots with intrinsic owners,
accumulated full prefixes and membership, with closing and log-correspondence laws. Its owners
are the interaction runner and `Observation` in `Core/Execution.lean` and logged execution in
`Core/Security/Knowledge.lean`. The two existing query logs cannot serve as that artifact.

Canonical accumulated-prefix query names need availability and inclusion certificates that
identify the same source across a genuine join and its terminal context. This requires a prefix
resource interface beside `PrefixMoves`/`pathResources` in `Core/Protocol.lean` and
`Core/OracleVerifier.lean`, with the inclusion/routing laws in `Core/Composition.lean`.
Typed resource indices do not supply these certificates. These gaps are shared with the
[parent inventory][parent-inventory] and remain unresolved; they do not block the fault port.

## Unresolved universe restrictions and owner changes

1. **Protocol oracle nodes couple message and query universes.**
   `OraclePos.oracle` in `ArkLib/Interaction/Core/Signature.lean` requires
   `OracleInterface.{u, u} X`. Restoring frozen DecorationExample 2 requires a second query
   universe in `OraclePos`, `OraclePoly`, `oracleSig`, `viewSig` and `OracleProtocol`, then
   carrying it through `pathFamily` and `pathResources` in `Core/OracleVerifier.lean` and their
   consumers. Positions may need the maximum of the two type-containing universes; moves and
   responses can still stay in `Type u`. This is an owner change to the parent Core signature
   and oracle family machinery, outside these test ports. It is not solved by `Resources.sum`.
2. **Oracle data and responses remain coupled.**
   As [implementation note 18][universes] records, `OracleInterface` in
   `ArkLib/OracleReduction/OracleInterface.lean` stores an `OracleContext` over `ReaderM Message`.
   Separating realization and response universes requires generalizing that owner to independently
   typed data, queries and responses with an answer function on the data, and then generalizing
   `OracleFamily` and `Resources.ofFamily`. AccessExample 17–18 preserve the frozen coupling;
   they do not claim to remove it.
3. **The full-log runner keeps input indices and query types in `Type`.**
   [OracleVerifier.runWithLog][logged-runner] returns logs containing those queries inside the
   small runner monad. The existing `runWithAmbientLog` logs only ambient queries while answering
   input/message queries without storing them. Preserving the complete heterogeneous log instead
   requires a runner/monad result universe large enough to return it. The owning changes are in
   `Core/Security/Knowledge.lean`, the log-erasure laws in `Core/Oracle/LoggedExecution.lean`,
   and extraction interfaces consuming the log. This slice keeps the strongest supported
   output-query universe in [loggedSummary][q-log-summary] and the prover-log client. These input
   restrictions are unresolved, not a consequence of a test's choice of scalar fixture.

The run's returned output statements, data, output indices and private outputs still share the
move/response universe as required by the monadic runner. Those premise-required ties are
separate from the unresolved restrictions above.

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
[d-protocol]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L24
[d-root]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L90
[d-false-cursor]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L99
[d-true-cursor]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L103
[d-false-pos]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L107
[d-true-pos]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L111
[d-false-owner]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L114
[d-true-owner]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L118
[d-query]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L64
[d-false-interface]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L71
[d-true-interface]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L78
[d-oracle-owner]: ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L85
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
[q-log]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L239
[q-log-summary]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L231
[q-repeat]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L143
[q-fresh]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L149
[q-distinct]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L153
[q-untyped]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L167
[q-run]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L207
[q-split]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L216
[q-prefix-payload]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L220
[q-suffix-payload]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L224
[q-concrete-log]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryBounds.lean#L246
[c-route]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L48
[c-program]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L69
[c-routed]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L78
[c-suffix]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L169
[c-suffix-routed]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L182
[c-setup]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L196
[c-history]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L202
[c-import]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L216
[c-joint]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L226
[c-informed]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L257
[c-prover-log]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L288
[c-joint-cost]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L84
[c-lower]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L112
[c-input-cost]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L162
[c-count]: ../../../ArkLibTest/Interaction/Core/Oracle/QueryCost.lean#L292
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
[p-order]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L510
[p-close]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L218
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

[d-distinct]:
    ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L122

[p-terminal]: ../../../ArkLibTest/Interaction/Core/Oracle/PhasedRun.lean#L133

[parent-inventory]: logged-execution-disposition.md
[parent-phase-audits]: logged-execution-disposition.md#phasedrunlean
