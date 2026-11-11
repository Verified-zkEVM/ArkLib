# Implementation notes for the interaction core

These notes record where `ArkLib/Interaction/Core/` departs from the design records in this
directory. The records themselves are unchanged. Each entry states what the record said, what the
code does and why. Entries 1–8 were identified by the review of the first implementation; entries
9–12 were introduced while addressing that review, and entry 13 by core additions that the oracle
migration needs. The final section records later core changes that keep to the records; they are
not departures.

## 1. Oracle interfaces in positions; challenges indexed by node occurrences

Records D1 and D4 left open where an oracle payload's query interface lives and how challenges are
named. The code carries the interface in the oracle position (`OraclePos.oracle X interface` in
`Signature.lean`) and indexes challenges by structural node occurrences (`Node`, `ChallengeNode`
in `Protocol.lean`). This resolves the open choice without a separate decoration, and node
occurrences name each challenge independently of any transcript. Position universes remain
separate from moves and the monad; entry 18 records the independent oracle-query universe.

## 2. Observations retain the transcript and output on rejection

Records D4 and D7 describe a run that either outputs a statement or rejects. The code's
`Observation` keeps the full transcript and prover output together with an optional verdict
(`Execution.lean`), and `Reduction.run` gives the accepting `OptionT` presentation. Rejection is
therefore a returned observation, distinct from missing probability mass. In the classical
experiment every program is an `OracleComp`, which cannot fail, so rejection is the only way a run
can fail to accept; the security tests check that half the mass of a one-challenge run is a returned
rejection and that the total mass is one.

## 3. Oracle append and split are lawful maps with data round trips

Record D6 sketches routing through an equivalence of oracle signatures. The code represents
append and split by lawful `OracleMap`s with round-trip laws on the materialized data
(`OracleVerifier.lean`), with `payloadImpl_append` as the handler law. This is enough for both
materialization and query routing. It does not claim syntactic equality of query traces, which
the agreement law would not imply.

## 4. Adversary models are indexed by input and observation types

Record D7 attaches the adversary model to a verifier. The code's `AdversaryModel` is parameterized
by input and observation types, with an input-indexed adversary class; `OutputJudgement` decodes
the verdict and witness, and `StatementProblem` packages public context into the statement. The
generalization lets the same predicates serve plain and oracle verifiers and other models. A client
claiming correspondence with the legacy layer must choose the actual verdict and decode the actual
prover witness. Plain completeness and soundness have classical convenience predicates; oracle
security and knowledge assemble the generic predicate explicitly.

## 5. Errors in `ℝ≥0∞` with measurable observations

The legacy layer uses `ℝ≥0` errors. The code uses `ℝ≥0∞`, measurable observation spaces and
outer-measure upper bounds for general models; the classical wrappers use discrete observations,
so every event is measurable. The bounds are uninformative at error one or more, as usual.

## 6. Knowledge requires marginal preservation and an access budget

Record D9 section 4 asks knowledge soundness to preserve the run. The code requires the
extraction experiment's observation marginal to equal the model's outcome, adds an access-cost
budget counting adversary re-entry, and returns an optional witness, with an explicit `none`
counted as bad (`Knowledge.lean`). This prevents an extractor from deleting accepted mass. For a
general interface whose extractor can lose mass it is stronger than legacy `knowledgeSoundnessWith`,
whose bad event simply drops the missing mass, so a transfer from the legacy layer needs a
non-loss premise or a chosen failure-completion semantics. For the classical straight-line and
transcript-only interfaces the qualification is moot: `classicalStraightline_marginal` and
`classicalTranscriptOnly_marginal` prove that marginal preservation always holds, since the
extractor runs after the observation is fixed and `OracleComp` cannot lose mass.

## 7. Round-by-round terminal obligations cover every ambient state

The legacy terminal experiment starts from a fresh `init`. The code's `validAcceptance` asks for
positive acceptance probability from some ambient state (`RoundByRound.lean`). The interaction can
change shared state before the decision, so a fresh-state check could be evaded; the stronger
obligation needs suitable hypotheses for a transfer to the legacy layer. Structural spines with
full-move decorations give the state function and extractor the full prefix, including oracle
payloads.

## 8. Model definitions live in the security files

Record D9 sketches an optional `Model.lean`. The code defines models and extraction interfaces in
`Security/Completeness.lean` and `Security/Knowledge.lean`, and moves the `OracleFamily` helpers
to the neutral owner `ArkLib/Relation/Basic.lean`. Rewinding and quantum models, security
composition theorems, legacy execution and transfer theorems, and the focal-first to
counterpart-first exchange in distribution are outside this slice.

## 9. Oracle append needs output compatibility on accepted prefix results

Records D5 and D6 compose an oracle verifier by running the prefix decision and then the suffix
decision on the routed oracles, with the output map composed through the prefix output map and no
side condition. A composite output map, however, depends only on the statement, path and view,
whereas the suffix output map depends on the intermediate statement that the prefix decision
returns, possibly after ambient queries. The code therefore takes an `OutputCompatibility`
certificate. Its `agrees` field requires equality only for intermediate statements in the support
of `OracleVerifier.decideWith`, the prefix decision with its resource queries answered from the
routed input data and every ambient answer allowed. `OutputCompatibility.ofStatement` builds the
certificate when every accepted prefix result equals one public statement, and
`append_decideWith` states the routing law: the composed decision is the prefix decision followed
by the suffix decision on the routed data. Some condition is necessary: a prefix that returns an
ambient random bit, followed by a suffix whose output oracle exposes that bit, admits no
certificate, which a test checks. Compatibility depends on both verifiers: the same prefix
followed by a suffix whose output map ignores the bit does admit one. `ofStatement` gives a
sufficient condition, every accepted prefix result being one public statement; a test composes an
accepting zero-round prefix that returns `false` with the bit-dependent constant-oracle suffix,
and the composite accepts and returns the zero oracle.

## 10. Root obligations of state functions are guarded by the input promise

Record D7 sketches `toFun_root : ∀ stmt, toFun stmt root ⟨⟩ → stmt ∈ langIn` with no promise.
In the code both `StateFunction.root` and `KnowledgeStateFunction.root` assume
`admissible stmt`, and `KnowledgeStateFunction` takes the promise as a parameter. The error
obligations already quantify only over admissible inputs, and terminal knowledge soundness is also
promise-restricted. Without the guard, a zero-round protocol with promise `b = true` and
immediate extraction has no knowledge state function at all, because the terminal obligation on
the excluded input `false` forces the root relation on it.

## 11. The public-coin sampler is presented beside the pure-end sampler

Record D4 describes the sampler as the public-coin counterpart determined by the signature, with
replay from PolyFun. The code keeps `samplerEnd` and `sampler`, the pure-end form on which the
runner, `appendSampler` and the composition run laws are stated, and adds `publicCoinSampler` as a
PolyFun `PublicCoinCounterpart`. `toCounterpart_publicCoinSampler` and
`toCounterpart_publicCoinOracleSampler` prove that its conversion is the runner's sampler, and
`replay_publicCoinSampler` and `replay_publicCoinOracleSampler` that its replay draws nothing. The
bridge theorems are stated for `plainSig` and `oracleSig` rather than an arbitrary lens: the
definition casts along the owner of each position, and that cast reduces only once the signature
fixes the owner.

## 12. Path-fiber splitting stays in ArkLib

Record D5 splits paths and views at the seam with PolyFun's path operations and adds nothing to
ArkLib for it. `Fiber`,
`project_split` and `splitFiber` in `Composition.lean` are generic in the polynomial and the lens
but remain in ArkLib, marked as candidates for PolyFun; `project_split` is now derived from
PolyFun's `projectPathAlong_append`, `append_split` and `split_append` laws. The same holds for
`Node.appendEquiv` and `ChallengeNode.appendEquiv` in `Protocol.lean`, which split the node
occurrences and challenge nodes of an appended protocol into prefix and suffix-fibre parts. They
stay local to avoid a further PolyFun API change and repin beyond the merged lens work this slice
pins to; moving them to PolyFun is a follow-up.

## 13. The oracle decision log is recorded in the core

Record D6 assigns logged execution to the later oracle migration. The core's
`OracleVerifier.runWithLog` already logs the decision over the ambient oracles and the input and
message oracle families, before the resource queries are routed to the materialized data, so the
migration can read the resource queries without a second logged runner. Extractors still receive
only the ambient part, as record D7 requires: `OracleVerifier.runWithLog_fst` proves that the
`QueryLog.fst` of the decision log is the log of a run that records ambient queries alone, and the
oracle extraction game passes that projection.

## Continuation

Entries 14–16 record the departures of the legacy embedding. They are in
[`legacy-embedding.md`](../interaction-layer/legacy-embedding.md#departures), and
[`departures.md`](../interaction-layer/departures.md) indexes every entry, including 1–13 and 18.
Entry 18 below is a later core entry; number 17 belonged to an entry that was removed.

## 18. Run outputs are tied to the monad universe

**Status: equivalent for independent input data and query universes; unresolved for the
full-log oracle runner's large-query interface.** Record D2's ledger puts moves and participant
outputs in `Type u` and leaves the other components of a verifier unstated. The code gives every
component that is not a run output its own universe as far as the definitions allow: the ambient
index of a verifier, the input resource index and data, the output oracle index `J p` of an
oracle verifier, the query types of the input and output oracle interfaces, the input statement, the
input witness and the intermediate witnesses of a knowledge state function.

**Retained runner contract.** Run outputs stay in `Type u`: the output statement `StmtOut p`, the output
oracle data `B p j` returned by a run, the output index `J p` once a run returns `∀ j, B p j`,
prover outputs, extracted witnesses and the state `σ` of a security experiment. Positions live one
universe up for plain protocols (`PlainPos : Type (u+1)`) and in
`Type (max (u+1) (q+1))` for oracle protocols, because an oracle position names both a payload
type and a query type. Moves and returned values stay in `Type u`, and the runner is
`m : Type u → Type u`
(`OracleComp ambient` with responses in `Type u`). `simulateQ`, which answers the decision's
resource queries in a run and in `decideWith`, also needs the value universe to equal the response
universe. A run output in another universe would need a `ULift` adapter or a monad on a larger
universe, which record D2 rejects. A prover's ambient index is in `Type u` for the same reason:
`OracleComp ambient : Type u → Type (max uι u)` is the prover's monad, so `Reduction`, `Prover`,
both runs and the classical security models fix it.

`OracleProtocol` takes the tree's actual leaf type as a parameter, defaulting to `PUnit`.
All execution, path-resource and security APIs use those default trivial leaves, preserving their
previous carriers by definitional equality. An explicit leaf type describes return values in the
authored `FreeM` tree. The parameter is used by the tree representation and is not a phantom:
the universe canary constructs and reads a natural-number leaf. Exposing that parameter also
lets the pinned universe linter distinguish the move universe in the alias's type; the query
universe remains independent, without a linter suppression or source-policy exception.

**Query types are separated.** The decision no longer reads one homogeneous family
`sumFamily inputs (pathFamily s p)`. It reads `pathResources inputs s p`, the disjoint sum of the
input specification and the path's specification, with their data kept as a pair
(`Resources.sum`). `OracleSpec` addition allows the two index types to lie in different universes,
and the input queries (`Resources.{u, uI, dI}`), oracle-node queries (`OracleProtocol.{u, q}`)
and output queries (`OracleFamily.{uJ, u, wJ}`) take their own universes through routing, append
and `decideWith`. `splitFamily` was already generic in the polynomial position universe;
`splitOutputs` and both path-routing directions now carry the independent node-query universe.
The query types never become values of the runner: they are answered by `simulateQ`, which
returns only responses.

**Equivalent: independent input data.** `OracleVerifier`, `pathResources`, `decideWith`, `run`,
append, the ambient-log runner and the security wrappers accept general
`Resources.{u, uI, dI}` inputs. Their data is `inputs.Data : Type dI`; only responses lie in
`Type u`. The R26 and R27 canaries retain the exact named query and realization carriers with
response universe `e` independent of realization universe `a`. No encoding or lift of a
realization is needed. `Resources.ofFamily` remains the specialization for existing
`OracleFamily` clients. Its `OracleInterface` uses `ReaderM`, which still ties that
specialization's data and response universes together. This no longer restricts the verifier
input API, and the shared interface is unchanged. Output families and oracle-node payload
interfaces still use `OracleInterface`; a run returns their data in the move/response universe.

**Equivalent: Agreement output and witness families (F7 and 3A).** `Security/Agreement.lean`
now preserves path-dependent `T p`, `J p`, `B p j` and `outputs p` in every agreement and tree
transport law. The output type is `OracleVerifier.Output T B`. Agreement itself and the decision
and output-map cast laws retain independent ambient and output-index universes; the ordinary
run laws retain the owner's general move/response universe. Probability laws keep only their
owners' small returned-value constraints. General resource inputs keep data and query universes
independent. The full-log law retains the parent's small resource-query indices.

Round-by-round knowledge agreement and transport quantify over `Win stmt` and `W stmt tr`,
with independent input, intermediate and output witness universes. The output relation receives
the input statement, completed transcript, output and witness in that order. The owner definition
in `Security/RoundByRound.lean` is unchanged. Prefix-dependent draws and local errors remain
available; Sumcheck specializes them through `rbrKnowledgeSoundnessOfNodes`. The
[Agreement inventory](../interaction-layer/sumcheck.md#agreement-universes-and-parent-limits)
marks both reviewed contracts equivalent and records the ordinary-import universe clients.
Neither P1 nor P2 retires an Agreement output or witness contract.

**Unresolved: the full-log oracle runner.** `OracleVerifier.runWithLog` returns the decision's
full query log, which records resource queries. Its input query index and oracle-node query
type must remain in `Type`. A large-query full-log API needs a parent logging interface whose
log can be returned by the small computation monad. Input data has its independent universe
even in this API, because the log never stores realizations. Only this full-log API keeps the
restriction, for clients that need the resource queries. Extraction does not use it. `OracleVerifier.runWithAmbientLog` puts the logger on the
ambient handler before adding the pure resource handler, so its result holds only two ambient
logs, and it takes the input statement, the input index and the input and output query types in
any universe, including input data and oracle-node queries.
`map_runWithLog_eq_runWithAmbientLog` proves that, at small input universes, it is
the full-log run with the decision log restricted to its ambient entries, and
`map_fst_runWithAmbientLog` proves at the general signature that forgetting both logs gives
`OracleVerifier.run`. The oracle extraction game, the classical oracle extraction models and their
marginal lemmas run on it at the general signature. `Extractor.OracleStraightline` and
`Extractor.OracleTranscriptOnly` take a statement in any universe and have no input-family
parameter, so they never had the restriction.

**Security wrappers.** The input statement `S`, the honest input witness `W` and the input oracle
data and query index are arguments of a run, so the security wrappers take them in any universe:
`Verifier.classicalModel`, `OracleVerifier.classicalModel` (statement and input index),
`Reduction.completeness`, `Verifier.soundness`, `StateFunction`, `rbrSoundness`,
`Verifier.validAcceptance`, `KnowledgeStateFunction`, `rbrKnowledgeSoundness`, the plain
straight-line and transcript-only extractors and extraction game, and the oracle extraction game
and classical oracle extraction models (statement, input index, input and output query types).
The intermediate witnesses of a `KnowledgeStateFunction` take their own universe `uK`. Its
extractors are plain functions, not computations of the runner, so the root extractor may map an
intermediate witness in one universe to an input witness in another. `rbrKnowledgeSoundness`,
`Verifier.rbrKnowledgeSoundness` and `OracleVerifier.rbrKnowledgeSoundness` take `uK` as an
explicit universe parameter and pass it to the existential, so elaboration does not specialize
it. `KnowledgeStateFunction.lift` moves a knowledge state function to a larger witness universe
by lifting each intermediate witness, and `rbrKnowledgeSoundness.lift` transports the bound from
`uK` to `max uK v` at the same error. A legacy intermediate witness lies in `Type`, which fixes
the universe of the certificate that the legacy-to-interaction theorems construct but not the
universe of their conclusions: they lift that certificate and hold for every `uK`. The
interaction-to-legacy theorems drop the witnesses and hold for every `uK` as well. Extracted
witnesses returned by the extraction games are values of the runner and stay in `Type`. The
restrictions that remain are the retained runner contracts above (ambient index and experiment state
in `Type`, output data, output index and extracted witnesses in `Type`) and the unresolved
large-query full-log interface. Neither P1 nor P2 retires any of these universe contracts; both premises concern scheduling and shape rather than universes.

`ArkLibTest/Interaction/Core/UniverseCanary.lean` instantiates the independent universes against
`Verifier`, `OracleVerifier`, `Reduction`, both appends, the routing law `append_decideWith`,
`OracleMap.simulate_eq`, two oracle runs, the classical security models, the oracle extraction
game and the classical extraction models with their marginal laws. One input interface is an
`OracleInterface.{0, 1} Nat` whose queries are types, and an append routes it through a middle
family with queries in `Type 1` to an output family with queries in `Type 0`. A knowledge state
function with intermediate witnesses in `Type 1` and the input witness `Unit` certifies
round-by-round knowledge for the core definition and both verifier wrappers. The same module
now constructs an actual oracle node carrying `OracleInterface.{0, 1} Nat`, runs a verifier
that queries its payload, and checks the returned value by `rfl`. Its R26/R27 resource
constructors quantify independently over `a` and `e`, and an R26 verifier and run consume
the original realization family directly.


## Changes that keep to the records

### Verifier outputs are indexed by the shape path

Record D6 fixed the output family for the first milestone. Both verifiers now index their outputs
by the public shape path: `Verifier ambient s StmtIn StmtOut` takes `StmtOut : Path s → Type u`,
and `OracleVerifier ambient s S T inputs outputs` takes `T : Path s → Type u` and
`outputs : (p : Path s) → OracleFamily (J p) (B p)`. The decision returns `T p` and the output map
targets `outputs p`; `OracleVerifier.Output T B p := T p × ∀ j, B p j` is the accepted claim of a
run. In an append the composite's output at a path of `s₁.append s₂` is the suffix's output at the
split path (`splitFamily`, `OracleVerifier.splitOutputs`), so composed decisions return the
suffix's output without a cast. `Observation` takes the indexed family, and the security
definitions take output problems over the path context (`PathProblem s T`), with acceptance
predicates typed at the transcript's path (`validAcceptance impl stmt tr (event : T p → Prop)`).
Constant families `fun _ => T` recover every earlier user; the legacy embedding and the sumcheck
core use them, so their statements are unchanged. Record D6 is updated accordingly, and
`ArkLibTest/Interaction/Core/Oracle/DependentRouting.lean` ports the frozen layer's dependent
routing example.

### Output witnesses are indexed by the transcript

The round-by-round and straight-line knowledge interfaces took a constant output witness type,
although the prover's output `Out : PathAlong l s → Type` and the intermediate witnesses
`Witness sp history` of a knowledge state function were already indexed by the transcript. A
protocol whose output witness depends on a message, such as an index `Fin (payload + 1)` bounded
by a sent `payload`, had to encode that carrier into a constant type and track its compatibility
with the transcript separately. The old interfaces could not expose the transcript-indexed carrier
directly.

**Round-by-round knowledge** (`Security/RoundByRound.lean`). The output witness of
`KnowledgeStateFunction` and `rbrKnowledgeSoundness` is a family `W : PathAlong l s → Type`.
`validOutput` takes `(stmt : S) → (tr : PathAlong l s) → W tr → Prop`, and
`extractLeaf sp history stmt` takes `W (PrefixMoves.complete l sp history)`. The input witness
type `Win` stays a plain type. The verifier forms take the family implicitly, with output
relations

- `Verifier.rbrKnowledgeSoundness`: `relOut : (tr : PathAlong plainSig s) → T → W tr → Prop`;
- `OracleVerifier.rbrKnowledgeSoundness`:
  `relOut : (tr : PathAlong oracleSig s) → (T × ∀ j, B j) → W tr → Prop`, where the second
  argument pairs the output statement with the output oracle data.

**Straight-line knowledge** (`Security/Knowledge.lean`). The extractor interfaces
`Extractor.Straightline`, `Extractor.TranscriptOnly`, `Extractor.OracleStraightline` and
`Extractor.OracleTranscriptOnly` take an output witness family `Wout : PathAlong plainSig s → Type`
or `Wout : PathAlong oracleSig s → Type`. Their arguments are ordered
`(stmt : S) → (tr : PathAlong _ s) → Wout tr → …`, so the witness is typed at the transcript passed
with it. The extraction games read the prover output through `readOut : ∀ tr, Out tr → Wout tr`;
the identity is a valid `readOut` when `Wout = Out`. The `withLogs` adapters, both extraction
games, `mem_support_extractionGame`, the classical interfaces and their marginal lemmas carry the
family. `Prover`, the generic `knowledgeSoundnessWith` and `knowledgeSoundness`, and the input
witness types are unchanged.

There is one theory for each notion. Constant witness types are the constant family `fun _ => W`
at the use site. The legacy round-by-round transfers in `Legacy/Security.lean` and
`Legacy/OracleSecurity.lean` use `fun _ => WitOut` and the output relation
`fun _ t w => (t, w) ∈ relOut`. The legacy extractor lifts `liftExtractor` and
`liftOracleExtractor` use `fun _ => WitOut` and only reorder the transcript and witness arguments.
Relations, errors and extractor behavior are as before.

The tests in `ArkLibTest/Interaction/Core/Security.lean` use the carrier `Fin (payload + 1)`
directly. In `payloadKnowledge` it is the leaf witness, and the input relation follows from its
bound together with the acceptance equality `payload = stmt`; `payloadKnowledge_extract` gives
the extraction equation for every payload. In `payload_extractionGame` a prover outputs
`w : Fin 8` after sending `7`, the identity `readOut` passes it to the extractor, and the accepting
run extracts `w.val`.

This keeps to record D7, whose problems already index witness types by the claim; D7 fixes no
constant output witness type for either notion.

## 19. Produced per-slot provenance under the passive schedule

**Status: equivalent for produced prefix, owner, query-group and log correspondence assertions;
premise-required for intermediate verifier actions retired by P1.**
`Oracle/SlotTrace.lean` instruments participant strategies with a list-valued writer layer;
`TwoParty.Lens.run` remains the sole recursive executor. `OracleVerifier.executeWith` owns the
interaction, terminal decision and output-closing sequence. The ordinary runner, full trace
and ambient trace specialize this mechanism without narrowing the ordinary runner's universes.
`Oracle/Provenance.lean` supplies erasure and interpretation laws. Each executed
participant slot records the actual preceding moves and ordered query/answer log. Ownership is
derived from the slot constructor. The final verifier decision is its own terminal phase;
`runWithSetupTrace` also retains an explicitly separate prover setup action.

`SlotInstrumentation.run_natural` supplies the general runner naturality law missing from the
pinned PolyFun interface. It works for arbitrary polynomials, ownership lenses, environments
and PolyFun's existing `MonadHom` morphisms. `observeInteraction_log` specializes it to concatenation of slot query
logs in the writer layer. Erasure uses this general law and monad laws, without an independent
recursive execution algorithm or a protocol-specific execution equivalence induction.
`runWithLog` is the full-log projection of the trace runner.
`runWithTrace_logView`, `runWithTrace_ambientLog` and `runWithTrace_erase` recover the existing
full logged, ambient logged and ordinary executions exactly. `phases_queries` states ordered
ambient-log concatenation, and `simulateQ_runWithTrace_logView` preserves the correspondence under
lawful interpreters, including stateful runtimes. The existing full-log universe restriction in
entry 18 applies to the full-log trace result. `runWithAmbientTrace` uses the same instrumented
strategies and shared sequencing mechanism, returning only ambient decision queries and preserving
independent input-data, input-query and
oracle-node-query universes. `runWithAmbientLog` is its aggregate projection;
`runWithAmbientTrace_erase` gives ordinary erasure. `runWithTrace_ambientView` identifies the
full trace with this ambient view at small query universes, including every slot prefix and owner.

`Oracle/PrefixResources.lean` defines available payload families at actual prefixes, intrinsic
node names, prefix-resource inclusion and typed query inclusion. `includeQuery_name` and
`familyInclusion_query` relate canonical naming to actual query routing;
`pathResourcesInclusion_data` identifies completed-prefix data with the payloads used by the
verifier. `runWithTrace_prefixes` certifies that each produced phase precedes the actual completed
transcript, and `available_at_terminal` transports its availability certificate.
`runWithAmbientTrace_prefixes` gives the same provenance certificate for independent query
universes. A compile-time acceptance canary checks these universe parameters directly. `joinToTerminal_name` preserves names from an appended protocol's actual seam to its
terminal prefix. The append route continues to use `prefixRoute_payload` and `splitOutputs`.

The acceptance client keeps the aggregate tests and adds per-slot runtime observations, actual
join and terminal membership, canonical availability and future-slot exclusion. Its distinguishing
test moves one ambient request across a fixed public message: ordinary observations and aggregate
logs remain equal, while the traced query prefixes differ. P1 retires intermediate effectful
verifier actions and their former query groups; it does not retire prover slots or their prefixes.
The disposition inventory records those qualifications separately.

## 19. Knowledge composition and measured extraction

The [assertion disposition record](../interaction-layer/knowledge-composition-disposition.md)
compares this branch's frozen production laws and acceptance assertions with their exact targets.
[Entry 18](#18-run-outputs-are-tied-to-the-monad-universe) describes inherited protocol, runner,
output-family and oracle interfaces. The inventory below covers only this branch's additions.

### Backward maps and composition

`Security/KnowledgeComposition/Extraction.lean` owns full transcript cursors, backward extraction,
certificate composition and the deterministic extraction-failure theorem. The public
`Security/KnowledgeComposition.lean` imports it and supplies local-bound, relation-level and
plain verifier composition theorems.

| API | Change on this branch |
| --- | --- |
| `KnowledgeStateFunction` | `Win stmt`, `Witness stmt sp history` and `W stmt tr` retain the input statement. Statements, input witnesses, intermediate witnesses and terminal witnesses have independent universes `uS`, `uW`, `uK`, `uO`. |
| `extractFrom`, `extractAlong`, `terminalWitness` | Pure backward maps accept large terminal witnesses directly. The root map returns `Win stmt`; no terminal or seam carrier is encoded into a small type. |
| `child`, `withRootWitness`, `extractFromMaps` | Restrict to a first move, expose the actual root witness internally and factor extraction through its computational fields. These support recursion with an independently large input witness. |
| `append` and its extraction/state laws | The prefix's terminal family `Wmid stmt tr₁ : Type uM` is the suffix's input family. The final family has its own universe `uO`; the seam states that the suffix root extractor returns a valid prefix witness. |
| `guard`, `condition`, `comap` and their local bounds | Restrict states to admissible inputs, conjoin a statement predicate, or pull back statements and map dependent input/output witnesses. The source and target terminal families have independent universes. |
| `BadChallengeFrom`, `BadChallengeAlong` | Follow the actual suffix extraction of the supplied terminal witness. `extraction_failure_implies_badChallengeAlong` identifies a receiver transition without choosing a different witness. |
| `rbrKnowledgeSoundness` and both verifier wrappers | Pass the terminal universe through to the certificate. Both lift operations raise only `uK`, keeping the terminal and input carriers. Legacy wrappers specialize to their original small terminal families. |
| `rbrKnowledgeSoundness_append`, `_of_mid` | Compose local errors and dependent middle relations on every prefix transcript, including false middle claims. `_of_mid` accepts explicit input and output witness maps. |
| Plain/oracle `simulateQ_append_run`, `support_append`, `validAcceptance_append` | Decompose the two decisions with the same intermediate ambient state and, for oracle verifiers, actual routed suffix data. The support laws work in any lawful monad with lawful support. |
| `Verifier.rbrKnowledgeSoundness_append`, `_of_pure` | Compose standalone plain verifier hypotheses. The supported prefix result must equal the named middle statement; `_of_pure` derives that law for a pure prefix decision. |

The plain verifier proof conditions suffix states on possible prefix acceptance. The suffix has
its own output relation. No theorem identifies two independently existential acceptance events
with composite acceptance. `splitFiber_pair` and `Verifier.append_decide_pathAlong` expose the
transports in the decision fold; heterogeneous equality identifies equal-path output fibers.

The oracle fixture instead uses `rbrKnowledgeSoundness_append` and `_of_mid` with
`composed_validAcceptance_iff` as an explicit relation-level bridge. It does not instantiate a
generic standalone oracle verifier composition theorem. The plain `indexed_composed` client does
instantiate the standalone plain verifier theorem. The disposition record keeps these claims
separate.

### Full-prefix distributions and local errors

The shared `PrefixDraw` and `PrefixError` interfaces index draws and errors by the same receiver
cursor and full history. The public `rbrKnowledgeSoundness` predicate and both verifier forms use
these interfaces. `combinePrefixDraw` retains the first error before the seam. After the seam,
it selects the second error family by the complete first transcript and evaluates it at the
second prefix history. `appendPrefixSampler_eq_combinePrefixDraw` proves the matching sampler law.

The `_prefix` composition theorems accept these families. The node-indexed predicates end in
`OfNodes`; the established node composition theorems follow from the general laws by ignoring
history. There is one local-bound and composition proof development. P1 removes challenge
selection from oracle payloads and effectful receiver actions only. Earlier public challenges and
prover messages may select later distributions and local errors. The fixed two-bit zero-error
certificate in `ArkLibTest/Interaction/Core/Security/PrefixKnowledge.lean` checks this distinction
without inserting a prover message. The inventory records the corrected schedule correspondences,
including KC-065 as equivalent because its frozen schedule was already constant.

### Measured extraction

`Security/MeasuredResources.lean` names one VCVio `BudgetedProgram` for each root, step and leaf
map. `programAlong` composes those programs using VCVio's `BudgetedProgram.comp` and `contramap`.
`BudgetAtMost rootBound stepBound leafBound` gives
`leafBound + (completeSpine l tr).length • stepBound + rootBound`.
The frozen `length • bound` result is recovered by explicitly supplying zero root and leaf
bounds to `programAlong_budget_le_nsmul` and `programAlong_costAtMost_nsmul`.
The empty-protocol fixture quantifies all state functions and stage programs with those zero
bounds. It does not assume an arbitrary root or leaf program has budget zero.

The cursor induction counts full moves, including oracle messages. PolyFun's node-dependent
charges do not directly replace it: the stage programs depend on the statement and full earlier
moves, and the root and leaf budgets require separate accounting. Instruction budgets leave pure
work, views, handlers, carrier identification and intermediate witness sizes uncharged. The zero
program exists for every state function; the ordered and unbounded-depth tests use named charged
programs to test actual instruction cost as well as budgets.

The measured API retains these small carriers because of pinned VCVio declarations:

| Restricted carrier | Forcing declaration at VCVio `fc54dd3d7691d6f5db7dc829e321a727f095bc2d` |
| --- | --- |
| Input witnesses `Win stmt : Type` and root-stage result | `OracleComp.BudgetedProgram {Input Result : Type}` in `VCVio/OracleComp/QueryTracking/MeasuredProgram.lean:156`; the root program realizes `extractRoot`. |
| Intermediate witnesses and `StageInput : Type` | The same `BudgetedProgram` input/result binders force each step's dependent input pair and result to be small. |
| Terminal witnesses `W stmt tr : Type` | The same `BudgetedProgram` input binder forces the leaf program's argument to be small. This restriction also applies to `programAlong` and `MeasuredKnowledgeStateFunction`. |
| Cost type `ω : Type`, instruction names and views | `OracleComp.MeasuredProgram (Input Result ω : Type)` at line 66, with fields `View : Type` and `Op : Type`; `BudgetedProgram` bundles this program. |

The statement universe remains arbitrary. The pure `PrefixMoves`, `KnowledgeStateFunction`,
lifting, extraction, extraction failure, append and restriction laws accept
`P : PFunctor.{uA, u}` and a lens to `rolePoly.{u}`, with leaves `PUnit.{u + 1}`.
The move, statement and witness universes are independent; branches and leaves share the move
universe. KC-318 and KC-322 now send the frozen `ULift.{1} Nat` oracle payload, retain
`ULift.{2} (Fin (payload.down + 1))` witnesses and prove extraction returns six.

Probability bounds use the small-move instance of this general certificate. Pinned VCVio's
`ProbComp : Type → Type` (`VCVio/OracleComp/ProbComp/Basic.lean:31`) forces `sampleAt` to return
a small move. `challengeSpec` (`Core/Protocol.lean:65–67`) returns `Move l`, whose universe is
shared by challenges and public/oracle messages. The disposition record's PROB-031 names this
remaining probabilistic limitation. It does not restrict pure backward maps or large terminal
and seam witnesses in the verifier wrappers.

### Acceptance evidence

The composition fixture sends a public prover selector after the Boolean challenge. That selector
chooses a public unit-message suffix or an oracle-message suffix under P2. Both challenge values
remain available on each selected shape. Payload-dependent `Fin (n + 1)` carriers, extraction
composition, terminal relations and the exported oracle from the same execution are checked on
both shapes. The selector change is premise-required under P2, not missing parent support.

The ordinary-import universe canary composes with `Type` itself as the terminal and seam carrier,
both in `Type 1`, and tests both verifier wrappers and lifting with large terminal witnesses.
Separate clients retain statement-indexed witnesses at unequal universes, empty carriers,
standalone plain verifier composition and the actual shared ambient state at the seam.
The axiom collectors check the new laws against `propext`, `Classical.choice` and `Quot.sound`.

### Restoration under P2

The frozen restoration fixture's `Out` chooses `Fin 8` or `Fin 9` from a Boolean challenge.
Its replacement is **premise-required under P2**: challenges cannot select output shape.
The child restoration branch (#1483) selects `Fin 8` versus `Fin 9` by a public prover message.
It must retain the plain replay's payload return on both challenge values and keep oracle
rejection separate. This branch corrects the disposition; the child owns the restoration fixture.
No challenge-indexed parent output interface is required.

### Validation

The required targeted reverse-dependency build and guard commands are the acceptance checks for
this branch. The disposition record gives their scope. No whole-library validation is requested.

### `combineDraw` combines errors

The composite error is `combineDraw (m := fun _ => ℝ≥0∞) l s₁ s₂ ε₁ ε₂`: the combinator that
combines the prefix and suffix draws, at a constant result family. Prefix challenge nodes keep the
prefix error, and suffix challenge nodes keep the error of the suffix at their prefix path. No
separate error traversal is added.

## 20. State restoration under P2: authored output selection

Approved premise P2 says that challenges and oracle messages never select protocol shape.
`Path s` therefore retains public prover messages and erases challenges. The frozen fixtures'
challenge-selected `Fin 8`/`Fin 9` statement carriers are **premise-required and retired under P2**.
They are not a missing parent dependency, as entry 19 also records.

The replacement fixture prepends a prover-authored Boolean `b` to the original one- or two-round
protocol. That public message selects the exact statement carriers `Fin 8` and `Fin 9`. The
challenge remains independent and continues to control acceptance, rejection and knowledge-state
transitions. The fixtures quantify over both selectors and every original challenge, statement,
message and output witness. In particular the diagonal selectors reproduce the numerical frozen
replays, while all four selector/challenge combinations are checked by universal theorems.
The frozen output oracle stays `PUnit → Fin 8`, with the original interface and payload. A
separate `varyingVerifier`/`varyingGame` fixture additionally checks genuinely path-dependent
output oracle carriers and interfaces; it does not replace the frozen rows.

### Games and execution

`selectedPlainGame`, `selectedClosedGame` and the two-round `PublicSelection.game` restore the
original adversary and evaluate the full verifier on the public-selector-prefixed transcript.
Their output is dependent on that returned transcript. The public selector makes no restoration
oracle query, so the original salted keys, adaptive repeated query, query counts and error
charges are unchanged. The suffix verifier at each fixed selector is used to instantiate the
generic soundness theorem. Observation equations and party-run correspondence identify its
output with the full verifier's output; the game is not a manually predicted verdict.

`plainScriptedRun_eq` and `replayResult_eq` return payload seven on every Boolean challenge, in
both exact statement carriers. `selectedScriptedRun_eq` and `oracleReplayResult_eq` separately
retain rejection on a false challenge. The one-round `selectedGame_eval_run` and two-round
`PublicSelection.game_eval_run` connect restored games to actual `OracleVerifier.run` executions.
The one-round `selected_fresh` checks the complete interaction's uniform challenge marginal,
independently of input, authored selector and oracle payload.

### Branch-specific interfaces

The [disposition record](../interaction-layer/state-restoration-disposition.md) gives exact frozen
and target declarations, endpoint correspondences and the P1/P2 classification for each port.
This branch adds the following restoration interfaces on the parent's state functions:

| Interface | Restoration-specific contract |
| --- | --- |
| `verificationGame`, `closedVerificationGame` | Complete the adaptive selection, then return the transcript and its path-indexed passive observation. |
| `complete_support_matches`, `run_scriptedProver_of_mem_support` | Every supported open completion carries the selected messages and replays through the actual interpreted party runner. |
| Uniform, private-coin and nonuniform knowledge bounds | Read the supplied adversary witness at the completed transcript; retain `(Q + rounds.length) * error` or `Q * max + sum`. |
| `programAlong_budget_le_protocol`, `programAlong_budget_le_protocol_zero` | Count message/challenge stages per round, with explicit root/leaf terms and the frozen zero-endpoint specialization. |
| Authored-selector fixtures | A public prover Boolean selects exact `Fin 8`/`Fin 9` statement carriers; challenges still control acceptance and knowledge transitions. |

Unmeasured restoration retains independent input, intermediate and terminal witness universes.
Probabilistic game outputs remain small; deterministic observations accept general move universes.
The record explains these constraints and the change from arbitrary terminal results to optional
passive decisions and explicit output-law implications.

### Shared extraction laws and carrier constraints

This branch adds root-failure localization and child restriction laws beside the parent's
extraction definitions in `Security/KnowledgeComposition/Extraction.lean`. The keyed conclusion
`BadChallengeOnCompletion F stmt messages table w key` retains the witness extracted from the
actual suffix and supplied output witness. Only `BadChallengeOnCompletion.mem_badChallenge`
forgets that witness for the probability bound. The [parent inventory](../interaction-layer/knowledge-composition-disposition.md)
describes the shared certificate signatures; the [restoration record](../interaction-layer/state-restoration-disposition.md)
identifies this branch's consumers and source assertions.

The remaining small carriers follow these exact declarations at VCVio pin
`fc54dd3d7691d6f5db7dc829e321a727f095bc2d`:

- `SampleableType (β : Type)` in
  `VCVio/OracleComp/Constructions/SampleableType/Basic.lean:51` forces
  `Round.sampleChallenge` to sample small challenges. `protocol` uses `OraclePoly.{0}`,
  whose messages and challenges share the move universe. Round-specific pure keyed laws
  therefore remain on this small protocol; the shared extraction laws are general.
- `ProbComp : Type → Type` in `VCVio/OracleComp/ProbComp/Basic.lean:31` keeps random
  outputs small in the restoration games and bounds. It does not restrict `readOut`
  or the certificate's input, intermediate or terminal witness universes.
- `OracleComp.BudgetedProgram {Input Result : Type}` in
  `VCVio/OracleComp/QueryTracking/MeasuredProgram.lean:156` fixes root results, step
  inputs/results and leaf inputs to `Type`. `KnowledgeStateFunction.MeasuredStages`
  (`Core/Security/MeasuredResources.lean:99`) applies this interface to the actual extraction
  maps. Its restoration budget theorems and the packaged measured game theorem retain
  small input, intermediate and terminal witnesses. `OracleComp.MeasuredProgram` at line 66
  also fixes the cost carrier `ω` to `Type`.

### Frozen-source dispositions

The [state-restoration disposition record](../interaction-layer/state-restoration-disposition.md)
contains one table per frozen production or test file. It covers 86 production declarations,
all 53 frozen fixture assertions, and six proof-bearing measured fixture definitions. It replaces
the one-round and two-round tables previously kept here, with exact file/line references and one
status per row. The record distinguishes P1/P2 restrictions, retired adapters and equivalent laws;
it includes the proved support-to-replay bridge and zero-endpoint budget specialization.

### Validation

On 2026-11-11, the ancestry check against `feat/interaction-migrate-core-3` passed, and both
prescribed checks exited zero from this worktree:

```sh
~/claude-work/restack-1110/check.sh feat/interaction-migrate-core-3 build
DOC_BASE=feat/interaction-migrate-core-3 ~/claude-work/restack-1110/check.sh \
    feat/interaction-migrate-core-3 guards
```

The build includes both restoration test modules, their executable replay assertions, and the
transitive axiom checks on the new game and replay theorems. The guards cover documentation,
frozen paths, forbidden proof escapes, headers, imports and Lean source style. The parent's
ancestry, build and guards were also rerun successfully from its worktree. Every changed Lean
file has fewer than 1500 lines and no line exceeds 100 characters.

Independent statement review checked the P2 dispositions, all original non-carrier quantifiers,
actual party runs, keyed witnesses, nonuniform errors and measured costs. Blind read-back of the
production declarations independently confirmed their dependent output types and witness
universes.

## 21. Round-by-round soundness implies soundness for lawful distribution monads

The probability-free escape theory is polymorphic in protocol positions and moves. Only the
probability bounds require small moves. `Security/RoundByRound.lean` owns the shared full-prefix
interface `PrefixDraw`, its oracle-program form `PrefixChallengePrograms`, `prefixSampleAt`,
and `prefixSampler` with its execution laws. Node-indexed draws embed through
`PrefixDraw.ofNodes`, which ignores history and agrees with `sampleAt`.

`Security/Implications.lean` bounds actual flip events at full prefixes. Its passive sampler
retains history-dependent challenge programs, and an exact equation identifies its execution
with the ordinary Core runner. Encoded event marginals transport prefix-indexed challenge models
into that bound. The plain and oracle verifier implications give the corresponding bound for
structural draws.
All forms allow missing probability mass in any lawful distribution monad.

`soundnessUsing` interprets the whole computation. Exact specialization laws retain the
classical initial state distribution and the existential terminal state of `validAcceptance`.
The generic and classical implications share their run-to-decision and acceptance proof.
The path supremum is bounded by arbitrary finite rank-indexed sums, as well as the existing
all-node sum and uniform-error corollaries.

The [disposition record](../interaction-layer/soundness-implication-disposition.md) gives the
source-to-target inventory, the freshness argument, failure tests, and limits of the correspondence.
Inherited universe constraints remain in [entry 18](#18-run-outputs-are-tied-to-the-monad-universe).

## Sumcheck migration

### 22. Sumcheck domain multiplicity and routing laws


`Sumcheck.Core.Soundness` now proves full-run soundness in the interaction layer for every map
`D : Fin d → R`, with indexed sums that retain repeated points. `Indexed` proves the local
false-to-true bound and constructs the round-by-round state function. It applies #1486's
`OracleVerifier.soundness_of_rbrSoundness_uniform` and counts one challenge per round to obtain
`n * (deg / |R|)` for the actual core run of every prover. `Soundness` derives arbitrary-list
and injective corollaries, plus committed and possibly failing randomized one-round bounds in
probability and measure form. These interaction layer security theorems do not use the legacy
embedding.

`Types`, `Tree` and `Domain` define the interaction layer statements, fixed protocol and
indexed arithmetic.
`DomainEquivalence` keeps the separate injective comparison with `Spec`; `LegacySoundness` keeps
the previous transferred bound as a comparison check. The arithmetic holds for commutative
semirings. The probabilistic bounds add `IsDomain`, finiteness and uniform sampling. Tests check
that constant one sums to two over `[0, 0]`, to one over `[0]`, and passes the
interaction layer final decision with repeated points and target two. The interaction layer tests audit the theorem axioms.

#1488 implements interval endpoints with `intervalVerifier`, built from the interaction-layer
`foldVerifier`.
The exact-row Sumcheck disposition gives interval execution, projection and append targets;
their full-run corollaries preserve the parent statements. P1 and P2 explain changed abort and shape assertions.
The generic `OracleModel.satisfies_guarantee` interface has no Core counterpart and is tracked as a
separate gap.

`Interaction.Core.Prover.simulate_joinSlot` belongs beside `Prover.simulate` in
`Interaction/Core/Reduction.lean`. It now covers every protocol tree, lens, dependent prover
output family and lawful target monad, including terminal trees. The Sumcheck tests use this law.
`decodeTranscript_succ` is a simplification equation beside `decodeTranscript` in
`Sumcheck/Core/Execution.lean`. The four local transparency attributes added by the Sumcheck
migration have been removed.

The affine message construction, evaluation law and oracle-answer law in `Effects` now quantify
over every commutative semiring. Their natural-number instances use `2 * X + 1`, and an actual
routed query at `2` returns `5`. These deterministic assertions require no sampling instance.
The other `ZMod 17` fixtures correspond to frozen `Protocol`, `Sequential`, `ArbitraryRounds`
and soundness fixtures over that same field. Uniform sampling is used in the probabilistic
soundness statements.

## 23. Sumcheck ports

**Plan.** The frozen assertions quantify over interval endpoints, projected input behavior and
composition through exported oracles. This entry follows the parent's entries through 22.

**Code.** `Sumcheck/Core/Fold.lean` implements passive interaction-layer checks. `Interval`
specializes those checks to every `start + count ≤ n`. `IntervalCompleteness` proves support,
perfect and measure completeness for that full range. `IntervalAdaptive` supplies current-statement
challenge callbacks through an actual shared-state handler. `IntervalSoundness` proves
interaction-layer round-by-round suffix soundness for exactly `start + count = n`, then applies the
parent's uniform implication with `count` challenges and error `count * (deg / |R|)`. Lists retain
all repetitions; embeddings specialize the same proofs. `intervalVerifier_full_run` identifies the
zero-start full interval with the parent's interaction-layer indexed verifier without changing its
theorems.

`FoldComposition.run_append_public_intervalVerifier` compares actual public one-round and suffix
interval verifier runs. It transports the midpoint and endpoint statements explicitly, retains the
transcript, original polynomial and private output, and permits arbitrary effectful provers.
`Projection` constructs the interaction-layer projected oracle map and its derived query handler.
`projectedExecute_closed` identifies returned behavior with that handler; `projectedExecute_related`
proves its evaluation claim. `Behavior` handles arbitrary original input behavior at the empty
interval and proves its final remaining-sum relation is evaluation.
`BehaviorComposition.run_append_behaviorIntervalVerifier` extends the public append equation to
arbitrary original evaluation behavior. `IntervalRoundSoundness` proves the actual one-round
probability and measure bounds at every variable position, including intermediate endpoints.
`ComputableProjection` computes indexed CompPoly projections, retaining repeated domain points.
`ComputableInterval` constructs the honest computational strategy and proves its interpretation,
actual execution equality and completeness. `ComputableSoundness` transfers the interaction-layer
suffix bound to every computational-message prover with shared ambient state. `Interpreted` and
`InterpretedExecution` provide generic message interfaces and preserve both prover slots, each
public draw and the terminal computation under evaluation-preserving message interpretation. Legacy
`Spec` projections and honest prover comparisons are isolated in `LegacyProjection` and
`LegacyProtocol`; interaction-layer security does not depend on them.

The routing fixture uses `Nat`, with semiring-general polynomial export and routing laws.
Explicit deterministic handlers produce query order `[1, 3, 2, 4]`, accepted claim `(10, 10)` and
private output `hidden + 110`. A prefix rejection still runs both interactions under P1, then
skips the suffix decision. It therefore retains the full trace and output rather than the
frozen early-abort trace `[3]` and output `hidden + 50`. Suffix rejection also retains the full
trace. Interval tests cover nonzero starts, zero counts, repeated domains and rejection.

**Premises.** P1 moves all resource queries to the final decision and restricts verifier moves
to public coins. P2 prevents challenges and oracle messages from selecting shape. The
[exact disposition table](../interaction-layer/sumcheck.md#migration-disposition) names these
premises on changed abort and shape rows. It records the full endpoint ranges and exact targets;
a full-run theorem does not replace an arbitrary interval theorem.

The merged parent supplies generic routing and soundness implications. Constructor, projection
and transport equations replace this branch's added transparency commands. Existing parent
transparency settings remain unchanged. Mathematical polynomial projections remain
noncomputable; the generic interface and deterministic execution use computable carriers.

## 24. Computable Sumcheck runtime

**Migration.** The migration list ports the frozen computable Sumcheck to the interaction core:
`execute_eq_native`, the frozen `ComputableCompleteness` and `ComputableSoundness`, and the seven
rows of `scripts/SumcheckRuntime.lean`. Rows 3, 4 and 6 are premise-required under P1/P2; row 7 now checks the verifier.

**Code.** `Sumcheck.Core.Computable` instantiates the carrier-generic protocol and verifier of
`Sumcheck.Core` (open question OQ17) at CompPoly messages and CompPoly multivariate inputs; see
[`sumcheck.md`](../interaction-layer/sumcheck.md#the-computable-instance).

- `run_eq_interpret` replaces `execute_eq_native`. It equates the runs only after the challenge
  queries are renamed (`renameQueries`): the challenge nodes of the protocol at two carriers are
  different types. Challenge implementations move between the carriers by
  `Interpreted.transportDraw`, which keeps uniform sampling.
- The input oracle is a CompPoly multivariate polynomial with the individual degree bound,
  answered by direct evaluation, rather than an arbitrary behavior. The relations and languages
  are the legacy ones on the input read by `toOracleStatement`.
- `verifierOn` and the Core `pathLift` are `@[macro_inline]`, so the verifier at the noncomputable
  Mathlib input family stays executable, and the computable verifier shares its decision.
- `support_completeness` keeps the frozen supported-run guarantee without a probability or
  normalization assumption. `perfectCompleteness` follows for every challenge implementation,
  and `soundness` keeps the mathematical core error for every prover. The indexed CompPoly
  interval results cover every bounded endpoint; suffix soundness has the interval verifier's
  `count * (deg / |R|)` bound.
- Runtime rows. The challenges are drawn from the challenge oracle, not from a prover event, and
  the log records each draw.
  - Row 3 expects the log `[p0, c0, p2, c1, p3]` instead of `[0, 1, 2, 1, 3]`.
  - Row 4 had a public abort that stopped before the challenge, with the log `[0, 2]`. The
    verifier is passive, so a failed first check still runs every round: rejection with the log
    `[p0, c0, p2, c1, p3]`.
  - Row 6 expects the log `[c0, c1]` instead of `[1, 1]`.
  - Row 7 runs the zero-round interval verifier from the final round state. Its optional verdict
    is `some (16, 4, 4, 16)` and its trace is empty. The prover-only observation is an additional
    check.

**Why.** The interaction core has one protocol per message carrier and a passive verifier, and
names challenges by node occurrences. The restated rows check the same values and effect order
under those rules.

## 25. Routing owners and transparency

**Code.** The remaining forwarding subexpressions in the interaction layer and Sumcheck Core
use `OracleMap.fst`, `OracleMap.snd`, `OracleMap.embedding`, `Interaction.Core.pathLift` and
VCVio's `QueryImpl.id'` restrictions (or `QueryImpl.ofLift` for universe-polymorphic sums). Legacy index elimination, equality transport, path
elimination, export arithmetic and surrounding effects are preserved. `OracleMap.par` uses the
resource projections. The parent's `OracleMap.sum` already composes `par` and the family/resource
representation maps. `oracles_split` delegates its empty-prefix family routing to `embedding`.
The ordinary and traced runners forward ambient queries and challenge requests through the
identity handler, without substituting a sampler. Legacy `decisionImpl` retains its substantive
resource translation and delegates only the outer sum routing to identity restrictions.

**Parent fixes retained.** `Interpreted.headQuery` and `tailLift` already use `embedding`.
`Execution.verifier.outputMap` already uses `fst`; its carrier-generic `verifierOn` now does too.
`roundRoute` already specializes `roundRouteOn`; the latter now delegates to `headQuery`.
The Sumcheck `Routing` test already uses identity restrictions and projection handlers throughout
its export map. `OracleVerifier.runWithLog` and `runWithAmbientLog` already specialize traced
runners; the forwarding implementations in `Oracle/SlotTrace` now use identity restrictions.

**Transparency.** The Core layers and their tests carry no local transparency overrides.
Imported replication and path projection algorithms retain their definition-site transparency;
proofs use explicit reduction and their equations where needed. The existing definition-site
annotations on `PlainPoly`, `plainSig`, `OraclePoly`, `oracleSig`, `viewSig`, `oracleIdx`,
`OracleData`, `sumFamily`, `singletonFamily`, `pathFamily`, `PrefixMoves` and Sumcheck `round`
use `reducible`. Their docstrings explain the dependent constructor or query types exposed by
reduction. `OracleMap.fst` is `macro_inline` so the carrier-generic verifier can project its
inputs without computing the mathematical input family's interpreter. No attribute command
changes another declaration's transparency.

**Disposition.** No ledger row changes status. P1 still permits challenge distributions that
depend on earlier public moves and confines resource queries to the final decision. P2 still
prevents challenges and payloads from selecting shape. No statement or premise changes.
