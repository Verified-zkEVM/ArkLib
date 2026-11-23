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
`Outcome` keeps the full transcript and prover output together with an optional verdict
(`Execution.lean`), and `Reduction.run` gives the accepting `OptionT` presentation. Rejection is
therefore a returned observation, distinct from missing probability mass. In the classical
experiment every program is an `OracleComp`, which cannot fail, so rejection is the only way a run
can fail to accept; the security tests check that half the mass of a one-challenge run is a returned
rejection and that the total mass is one.

## 3. Oracle append and split are lawful maps with data round trips

Record D6 sketches routing through an equivalence of oracle signatures. The code represents
append and split by lawful `OracleMap`s with round-trip laws on the materialized data
(`OracleVerifier.lean`), with `oracleMessageImpl_append` as the handler law. This is enough for both
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
transcript-only interfaces the qualification is moot: `classicalStraightLine_marginal` and
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
of `OracleVerifier.decideWith`, the prefix decision with its bundle queries answered from the
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

Record D5 splits paths and views at the seam with PolyFun's path operations, reached through
`Transcript.split` and `Transcript.append` (`Core/Transcript.lean`, where `TranscriptAt` is also
defined). `project_split` and `TranscriptAt.split` in `Composition.lean` are generic in the
polynomial and the lens but remain in ArkLib, marked as candidates for PolyFun; `project_split` is
derived from `Transcript.path_append`, `Transcript.append_split` and `Transcript.split_append`,
which restate PolyFun's laws of the same names. The same holds for
`Node.appendEquiv` and `ChallengeNode.appendEquiv` in `Protocol.lean`, which split the node
occurrences and challenge nodes of an appended protocol into prefix and suffix-fibre parts. They
stay local to avoid a further PolyFun API change and repin beyond the merged lens work this slice
pins to; moving them to PolyFun is a follow-up.

## 13. The oracle decision log is recorded in the core

Record D6 assigns logged execution to the later oracle migration. The core's
`OracleVerifier.runWithLog` already logs the decision over the ambient oracles and the input and
message oracle families, before the bundle queries are routed to the materialized data, so the
migration can read the bundle queries without a second logged runner. Extractors still receive
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
index of a verifier, the input bundle's index and data, the output oracle index `J p` of an
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
bundle queries in a run and in `decideWith`, also needs the value universe to equal the response
universe. A run output in another universe would need a `ULift` adapter or a monad on a larger
universe, which record D2 rejects. A prover's ambient index is in `Type u` for the same reason:
`OracleComp ambient : Type u → Type (max uι u)` is the prover's monad, so `Reduction`, `Prover`,
both runs and the classical security models fix it.

`OracleProtocol` takes the tree's actual leaf type as a parameter, defaulting to `PUnit`.
All execution, path-bundle and security APIs use those default trivial leaves, preserving their
previous carriers by definitional equality. An explicit leaf type describes return values in the
authored `FreeM` tree. The parameter is used by the tree representation and is not a phantom:
the universe canary constructs and reads a natural-number leaf. Exposing that parameter also
lets the pinned universe linter distinguish the move universe in the alias's type; the query
universe remains independent, without a linter suppression or source-policy exception.

**Query types are separated.** The decision no longer reads one homogeneous family
`sumFamily inputs (oracleMessageFamily s p)`. It reads `pathBundle inputs s p`, the disjoint sum of the
input specification and the path's specification, with their data kept as a pair
(`OracleBundle.sum`). `OracleSpec` addition allows the two index types to lie in different universes,
and the input queries (`OracleBundle.{u, uI, dI}`), oracle-node queries (`OracleProtocol.{u, q}`)
and output queries (`OracleFamily.{uJ, u, wJ}`) take their own universes through routing, append
and `decideWith`. `splitFamily` was already generic in the polynomial position universe;
`splitOutputs` and both path-routing directions now carry the independent node-query universe.
The query types never become values of the runner: they are answered by `simulateQ`, which
returns only responses.

**Equivalent: independent input data.** `OracleVerifier`, `pathBundle`, `decideWith`, `run`,
append, the ambient-log runner and the security wrappers accept general
`Resources.{u, uI, dI}` inputs. Their data is `inputs.Data : Type dI`; only responses lie in
`Type u`. The R26 and R27 canaries in `ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean`
keep the exact named query and realization carriers with
response universe `e` independent of realization universe `a`. No encoding or lift of a
realization is needed. `OracleBundle.ofFamily` remains the specialization for existing
`OracleFamily` clients. Its `OracleInterface` uses `ReaderM`, which still ties that
specialization's data and response universes together. This no longer restricts the verifier
input API, and the shared interface is unchanged. Output families and oracle-node payload
interfaces still use `OracleInterface`; a run returns their data in the move/response universe.

**Unresolved: the full-log oracle runner.** `OracleVerifier.runWithLog` returns the decision's
full query log, which records bundle queries. Its input query index and oracle-node query
type must remain in `Type`. A large-query full-log API needs a parent logging interface whose
log can be returned by the small computation monad. Input data has its independent universe
even in this API, because the log never stores realizations. Only this full-log API keeps the
restriction, for clients that need the bundle queries. Extraction does not use it. `OracleVerifier.runWithAmbientLog` puts the logger on the
ambient handler before adding the pure bundle handler, so its result holds only two ambient
logs, and it takes the input statement, the input index and the input and output query types in
any universe, including input data and oracle-node queries.
`map_runWithLog_eq_runWithAmbientLog` proves that, at small input universes, it is
the full-log run with the decision log restricted to its ambient entries, and
`map_fst_runWithAmbientLog` proves at the general signature that forgetting both logs gives
`OracleVerifier.run`. The oracle extraction game, the classical oracle extraction models and their
marginal lemmas run on it at the general signature. `Extractor.OracleStraightLine` and
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
that queries its oracle message, and checks the returned value by `rfl`. The R26/R27 resource
constructors in the imported `ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean`
quantify independently over `a` and `e`. `viewVerifier`, its identity-view specialization
`namedVerifier` and a shared run example consume the original realization family directly.

## Changes that keep to the records

### Verifier outputs are indexed by the shape path

Record D6 fixed the output family for the first milestone. Both verifiers now index their outputs
by the public shape path: `Verifier ambient s StmtIn StmtOut` takes `StmtOut : Path s → Type u`,
and `OracleVerifier ambient s S T inputs outputs` takes `T : Path s → Type u` and
`outputs : (p : Path s) → OracleFamily (J p) (B p)`. The decision returns `T p` and the output map
targets `outputs p`; `OracleVerifier.Output T B p := T p × ∀ j, B p j` is the accepted claim of a
run. In an append the composite's output at a path of `s₁.append s₂` is the suffix's output at the
split path (`splitFamily`, `OracleVerifier.splitOutputs`), so composed decisions return the
suffix's output without a cast. `Outcome` takes the indexed family, and the security
definitions take output problems over the path context (`PathProblem s T`), with acceptance
predicates typed at the transcript's path (`validAcceptance impl stmt tr (event : T p → Prop)`).
Constant families `fun _ => T` recover every earlier user; the legacy embedding and the sumcheck
core use them, so their statements are unchanged. Record D6 is updated accordingly, and
`ArkLibTest/Interaction/Core/Oracle/DependentRouting.lean` ports the frozen layer's dependent
routing example.

### Output witnesses are indexed by the transcript

The round-by-round and straight-line knowledge interfaces took a constant output witness type,
although the prover's output `Out : Transcript l s → Type` and the intermediate witnesses
`Witness sp history` of a knowledge state function were already indexed by the transcript. A
protocol whose output witness depends on a message, such as an index `Fin (payload + 1)` bounded
by a sent `payload`, had to encode that carrier into a constant type and track its compatibility
with the transcript separately. The old interfaces could not expose the transcript-indexed carrier
directly.

**Round-by-round knowledge** (`Security/RoundByRound.lean`). The output witness of
`KnowledgeStateFunction` and `rbrKnowledgeSoundness` is a family `W : Transcript l s → Type`.
`validOutput` takes `(stmt : S) → (tr : Transcript l s) → W tr → Prop`, and
`extractLeaf sp history stmt` takes `W (PartialTranscriptAt.complete l sp history)`. The input witness
type `Win` stays a plain type. The verifier forms take the family implicitly, with output
relations

- `Verifier.rbrKnowledgeSoundness`: `relOut : (tr : Transcript plainSig s) → T → W tr → Prop`;
- `OracleVerifier.rbrKnowledgeSoundness`:
  `relOut : (tr : Transcript oracleSig s) → (T × ∀ j, B j) → W tr → Prop`, where the second
  argument pairs the output statement with the output oracle data.

**Straight-line knowledge** (`Security/Knowledge.lean`). The extractor interfaces
`Extractor.StraightLine`, `Extractor.TranscriptOnly`, `Extractor.OracleStraightLine` and
`Extractor.OracleTranscriptOnly` take an output witness family `Wout : Transcript plainSig s → Type`
or `Wout : Transcript oracleSig s → Type`. Their arguments are ordered
`(stmt : S) → (tr : Transcript _ s) → Wout tr → …`, so the witness is typed at the transcript passed
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

## 19. The queries by move under the passive schedule

**Status: ported for the partial transcript, querier, query-group and log assertions of the produced
entries; excluded by P1 for the intermediate verifier actions that P1 excludes.**
`Oracle/QueriesByMove.lean` wraps the participants' strategies in a list-valued writer layer.
`TwoParty.Lens.run` remains the only recursive executor. `OracleVerifier.executeWith` runs the
interaction, the final decision and the output closing in sequence. The ordinary runner, the
queries by move and the ambient queries by move all specialize it, and the ordinary runner's
universes stay as wide as before. `Oracle/QueriesByMoveLaws.lean` supplies the erasure and
interpreter laws. Each executed participant action records an entry (`QueriesAt`): the actual
earlier moves (the partial transcript, `PartialTranscript` in `Core/Transcript.lean`), the querier
and the ordered query/answer log. The querier comes from the participant action that the entry
logs. The final verifier decision is its own decision entry. `runWithProverSetup` also keeps a
separately run prover setup as an entry.

`MoveInstrumentation.run_mapMovesWith` is the general naturality law for the runner that the pinned
PolyFun interface lacks. It holds for arbitrary polynomials, role lenses, environments and
PolyFun's existing `MonadHom` morphisms. `runLoggingMoves_log` specializes it to concatenating the
entries' query logs in the writer layer. Erasure uses this law and the monad laws. It needs no
separate recursive execution algorithm and no induction on a protocol-specific execution
equivalence. `runWithLog` is the full-log projection of `runWithQueriesByMove`.
`toLog_runWithQueriesByMove`, `toAmbientLog_runWithQueriesByMove` and
`map_fst_runWithQueriesByMove` recover the existing full-log, ambient-log and ordinary executions
exactly. `withDecision_queries` states that the ambient logs concatenate in order, and
`simulateQ_toLog_runWithQueriesByMove` keeps this agreement under lawful interpreters, including
stateful runtimes. The universe restriction on full logs in entry 18 applies to the full-log
queries by move. `runWithAmbientQueriesByMove` uses the same instrumented strategies and the same
sequencing. It returns only the ambient decision queries and keeps the input-data, input-query and
oracle-node-query universes independent. `runWithAmbientLog` is its aggregate projection, and
`map_fst_runWithAmbientQueriesByMove` gives ordinary erasure. `toAmbient_runWithQueriesByMove`
identifies the full queries by move with this ambient view at small query universes, including
every entry's partial transcript and querier.

`Oracle/SentOracles.lean` defines the family of sent oracle messages at each partial transcript
and their node names. It also includes the bundle available at a shorter partial transcript, and its
typed queries, into the bundle available at a longer one. `liftQuery_node` and
`sentOracleMessageMap_query` relate node names to the routing of actual queries.
`toPathBundle_data` identifies the data of a completed partial transcript with the oracle
messages that the verifier uses. `runWithQueriesByMove_before_le` shows that each produced entry
comes before the actual completed transcript, and `isSent_at_decision` carries the proof that an
oracle was sent over to the decision entry. `runWithAmbientQueriesByMove_before_le` gives the same
guarantee about the ambient queries by move for independent query universes. A compile-time test
checks these universe parameters directly. `firstMovesLe_node` keeps node names from the seam of an
appended protocol to its final partial transcript. The append route still uses
`prefixRoute_oracleMessages` and `splitOutputs`.

The test file `ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean` keeps the aggregate tests.
It adds per-entry runtime observations, membership of the actual join and decision entries, proofs
that oracles were sent, and exclusion of future moves. Its distinguishing test moves one ambient
request across a fixed public message. The ordinary outcomes and aggregate logs stay equal, while
the partial transcripts of the queries differ. P1 excludes intermediate effectful verifier
actions and their former query groups. It does not exclude prover moves or their partial
transcripts. The [port table](../interaction-layer/port-logged-execution.md) records these
qualifications separately.
