# Oracle test dispositions

This reference accounts for all 89 frozen assertions in the seven files below. The eight
interaction layer modules port these files; `QueryCost.lean` collects cost and profile assertions
from `QueryBounds`, `RuntimeQueryBounds` and `PhasedRun`, rather than porting an eighth source file.
Row numbers follow frozen declaration order, including the universe canaries. Helper definitions
and diagnostic axiom-print commands are not additional assertions.

Each row links the frozen assertion and the exact replacement test, theorem, or explicit
retirement. **Preserved** means the indicated semantic contract and its quantifiers are retained.
**Partial** names a retained part and a removed or unresolved dimension; it is not an equivalence.
**Changed** identifies a different behavior. **Retired** means the tested object or operation no
longer exists. **Unresolved** names a restriction requiring an owner change. Parent-owned results
are linked directly; they are not duplicated to increase a coverage count.

## PhasedRun: 7 assertions

| Frozen row | Contract | Disposition and evidence |
|---|---|---|
| [1][fp1] | A run cannot be relabeled | Retired: no phase artifact or supplied role decoration. |
| [2][fp2] | State, owners and chronology | Changed: [runtime check][parent-phase-runtime]. |
| [3][fp3] | Setup query 9 counts twice | Partial: [count two][c-count]; phase grouping retired. |
| [4][fp4] | The final prefix retains payload 17 | Preserved: [arbitrary payload][p-payload]. |
| [5][fp5] | Input, closure, log and phases | Partial: [closure/log][parent-closed]. |
| [6][fp6] | Explicit rejection | Preserved: [rejected run and retained log][parent-reject]. |
| [7][fp7] | Fault 17 differs from rejection | Retired: the verdict has no fault constructor. |

The interaction layer obtains owners from the signature, and its runner produces a transcript,
private output and verdict. There is no `PhasedRun.phases` list or role decoration to relabel.
The two logs of `runWithLog` are prover ambient queries and decision queries, not participant
phase groups. Thus rows 1 and the grouping parts of rows 2, 3 and 5 have no current operation to
check. Row 3 still checks multiplicity in the [whole prover log][c-prover-log].

Row 2 also changes chronology: the frozen verifier's interleaved effects move to the passive end
decision. Its ambient order `[9, 9, 1, 2, 3, 4, 5, 6, 7]` becomes
`[9, 9, 1, 4, 5, 2, 3, 6, 7]`. The linked parent check tests the new runtime state and trace;
it is not an equivalent execution of the frozen schedule. The local [accepting run][p-accept]
quantifies the payload, private output and challenge independently.

Row 5 retains the input argument 7, accepted target 11, materialized oracle answer 18, sent-answer
log and ambient trace `[9, 0, 1, 2]`. It does not retain the four separate phase groups. Row 7's
three-way terminal outcome was removed: `OracleVerifier.decide` uses `OptionT`, distinguishing
acceptance from rejection only. A rejection test does not replace the lost fault distinction.
Restoring faults would require a fault-bearing verdict in the verifier, runner and security
observations, rather than encoding a fault as an accepted value.

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
contexts. Those objects were removed. The replacement reads a crossed payload from full prefix
moves and indexes resource queries by the completed shape of the decision's protocol.
The [prefix append identity][x-prefix] identifies the actual stage ending immediately after the
send. Its query is answered from that stage's own payload without choosing the future public
message. The [completed-path lookup][x-sent] also checks the payload for every later choice. The
partial tests do not claim a theorem about the removed predicate. The before/after query
rejection and acceptance clients in [AccessExample 3][a-unsent] and [4][a-sent] retain the
corresponding typed-access boundary. No independent availability annotation can authorize an
unsent slot.

## QueryBounds: 17 assertions

| Frozen row | Contract | Disposition and evidence |
|---|---|---|
| [1][fq1] | Cost of each routed query | Preserved: [route_cost][c-route]. |
| [2][fq2] | Source cost at most five | Preserved: [program_cost][c-program]. |
| [3][fq3] | Routed cost at most five | Preserved: [routed_cost][c-routed]. |
| [4][fq4] | Routed available slots | Partial: [typed program][q-route]; names retired. |
| [5][fq5] | Integrated log repeats the old read | Preserved: [loggedSummary_eq][q-log]. |
| [6][fq6] | Future slot at any cost | Partial: [exclusion][q-future], [ill-typed][q-untyped]. |
| [7][fq7] | Old/fresh identities | Preserved: [repeat][q-repeat], [distinct][q-distinct]. |
| [8][fq8] | Closing keeps output and repeated log | Preserved: [closed run log][q-log]. |
| [9][fq9] | Join prefix | Partial: [run][q-run], [payload][q-prefix-payload]. |
| [10][fq10] | Terminal prefix | Partial: [run][q-run], [split payloads][q-split]. |
| [11][fq11] | The join belongs to the phase list | Retired: no phase list or phase membership. |
| [12][fq12] | Terminal phase membership | Retired: no phase list or phase membership. |
| [13][fq13] | Availability and cost on one route | Partial: [typed cost five][c-joint-cost]. |
| [14][fq14] | Old name under inclusion | Partial: [prefix query][q-repeat]; names retired. |
| [15][fq15] | Future slot at actual join | Partial: [exclusion][q-future]; phases retired. |
| [16][fq16] | Phase adapter source log | Partial: [exact raw log][q-log]; adapter retired. |
| [17][fq17] | Four is not a cost bound | Preserved: [inhabited cost-five path][c-lower]. |

Rows 5 and 8 use the actual `composed.runWithLog`, not an isolated simulation of the export.
For every `a` and `b`, one query to the doubled export records two raw prefix-slot entries with
answer `a`, followed by the suffix-slot entry with answer `b`. The same assertion checks private
output `a + b` and verdict `some (a + a + b)`. The [one/two specialization][q-concrete-log]
recovers private output 3, accepted result 4 and the frozen three answers. The log is before
resource queries are answered; it detects dropped or coalesced expansion entries. The parent's
different single-export-read fixture is not counted as covering these rows.

Rows 4, 6, 13–15 used canonical cursor names, `availableContext` and context inclusion. These
were replaced by typed input/message resource indices and `prefixRoute`/`suffixRoute`.
[Fresh routing][q-fresh] uses the distinct suffix slot; both old reads use the literal same
prefix slot. A prefix program cannot name the future suffix slot, regardless of a cost bound.
These facts preserve resource separation but are not identities about the removed name encoding.
The documentation therefore marks those compound rows partial.

Rows 9–12 and 16 also used an actual phase list. The current runner has structural splitting
and transcript payloads, not a temporal phase collection. The tests retain the executed
transcript, its [payload][q-prefix-payload] and [suffix payload][q-suffix-payload]. They do
not establish membership in a nonexistent phase list or a correspondence with a removed phase
adapter. Row 8 needs no separate closing executor: `runWithLog` already returns materialized
output-oracle data; this fixture's output family is empty.

## RuntimeQueryBounds: 17 assertions

| Frozen row | Contract | Disposition and evidence |
|---|---|---|
| [1][fr1] | Export access and cost two | Partial: [access][r-export], [cost][c-input-cost]. |
| [2][fr2] | Canonical input source name | Partial: [input-slot query][r-input]; names retired. |
| [3][fr3] | Dummy and export | Preserved: [decision][r-prefix-decision], [map][r-export-map]. |
| [4][fr4] | Suffix queries and outputs | Preserved: [decision][r-decide], [data][r-output]. |
| [5][fr5] | Suffix permissions | Partial: [suffix_access][r-access]; boundary names retired. |
| [6][fr6] | Suffix cost five | Preserved: [suffix_budget][c-suffix]. |
| [7][fr7] | Routed suffix cost five | Preserved: [routed_suffix_budget][c-suffix-routed]. |
| [8][fr8] | Routed raw permissions | Partial: [raw access][r-raw-access]; names retired. |
| [9][fr9] | Guessing split history | Preserved ambient: [history][c-history]. |
| [10][fr10] | Informed split history | Changed: [split run][parent-informed-split]. |
| [11][fr11] | Setup costs one import query | Preserved: [setup_budget][c-setup]. |
| [12][fr12] | Generic runtime split | Changed: [general law][run-append]. |
| [13][fr13] | Direct logged guessing history | Preserved ambient: [parent log][parent-guess-log]. |
| [14][fr14] | Direct logged informed history | Changed: [parent log][parent-informed-log]. |
| [15][fr15] | Whole-run import cost one | Preserved: [import_budget][c-import]. |
| [16][fr16] | Joint half certificate | Partial: [joint theorem][c-joint]; names retired. |
| [17][fr17] | Charge seven; success one | Partial: [joint theorem][c-informed]; order changed. |

Rows 1, 2, 5, 8 and 16 previously quantified an `ExportedBoundary` whose prefix supplied
canonical resource names. The current access assertions quantify over every relevant path and
view, use the exact input/export query indices and prove both the allowed queries and their
costs. The prefix protocol has no sent oracle, so its export reads only its input. This retains
the source-permission facts; it does not recreate the removed cursor-name/context API.

Row 3's verifier decision performs its dummy request and accepts the unit statement. Its
separate output map is exactly the input projection. Row 4 checks the entire effectful decision
and the output map on arbitrary resource data, rather than assuming the output is constant.
The [routed export query][r-route] identifies the same input slot used in the cost proof.

For rows 9 and 13 the full-surface trace includes a challenge event; its `QueryLog.fst` is exactly
`[false ↦ false, true ↦ hidden]`, with final state `(hidden, 2)` and ambient charge four.
The [parent split check][parent-guess-split] and direct logged check retain this same ambient
history. Row 12's replacement is the general, whole-prover `OracleVerifier.run_append`, with
its [ordinary-import client][parent-general-split]; it is not restricted to the two example
provers. Applying runtime execution and a history observation to that equality preserves the
new scheduler's entire trace and state. It does not recover the frozen active-prefix scheduler.

For rows 10, 14 and 17, the informed prover queries at the seam before the passive prefix
decision. The ambient order is `[true ↦ hidden, false ↦ false, true ↦ hidden]`; the frozen order
was `[false ↦ false, true ↦ hidden, true ↦ hidden]`. Both have final state `(hidden, 3)` and
charge seven, but they are different histories. Restoring the old chronology would require
executing the prefix verifier's decision before the suffix interaction, a change to Core's
passive-verifier execution/composition model. These rows are not equivalent ports.

The new row-16 conjunction includes the prefix decision and export, access and cost certificates,
import budget, charged runtime history and the half bound for every fixed guess and secret.
The [answer observation][r-guess-answers] uses the actual materialized output oracle and target;
[guess_success][r-guess-success] proves probability exactly one half. The informed conjunction
retains charge seven and [success exactly one][r-informed-success], with its different order
stated explicitly. Its [answer observation][r-informed-answers] comes from the same actual run.
Neither theorem claims security against arbitrary provers from access/cost certificates alone.

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
   small runner monad. A small-result alternative would log only ambient queries while answering
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
[p-accept]: ../../../ArkLibTest/Interaction/Core/Oracle/PhasedRun.lean#L89
[p-payload]: ../../../ArkLibTest/Interaction/Core/Oracle/PhasedRun.lean#L92
[p-reject]: ../../../ArkLibTest/Interaction/Core/Oracle/PhasedRun.lean#L101
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
[r-export-map]: ../../../ArkLibTest/Interaction/Core/Oracle/RuntimeQueryBounds.lean#L51
[r-prefix-decision]: ../../../ArkLibTest/Interaction/Core/Oracle/RuntimeQueryBounds.lean#L54
[r-output]: ../../../ArkLibTest/Interaction/Core/Oracle/RuntimeQueryBounds.lean#L70
[parent-phase-runtime]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L374
[parent-closed]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L181
[parent-reject]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L165
[parent-guess-log]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L559
[parent-informed-log]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L570
[parent-guess-split]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L594
[parent-informed-split]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L605
[parent-general-split]: ../../../ArkLibTest/Interaction/Core/Oracle/Routing.lean#L257
[run-append]: ../../../ArkLib/Interaction/Core/Oracle/Routing.lean#L119
[oracle-position]: ../../../ArkLib/Interaction/Core/Signature.lean#L45
[oracle-signature]: ../../../ArkLib/Interaction/Core/Signature.lean#L57
[resource-sum]: ../../../ArkLib/Interaction/Core/OracleVerifier.lean#L133
[logged-runner]: ../../../ArkLib/Interaction/Core/Security/Knowledge.lean#L311

[universes]:
    ../interaction-rebuild/IMPLEMENTATION-NOTES.md#18-run-outputs-are-tied-to-the-monad-universe

[x-query]: ../../../ArkLibTest/Interaction/Core/Oracle/Prefix.lean#L108

[x-prefix]: ../../../ArkLibTest/Interaction/Core/Oracle/Prefix.lean#L100

[d-distinct]:
    ../../../ArkLibTest/Interaction/Core/Oracle/TypeTree/DecorationExample.lean#L122
