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

### Finite heterogeneous stage composition

The interaction layer had no replacement for the frozen ordered execution of a finite family of
closed stages (`ExecutionInterface`, `ClosedStage`, `OrderedExecution.run` in
`ArkLib/Interaction/Oracle/Composition.lean`). `ArkLib/Interaction/Core/Stages.lean` adds an n-ary
composition through the passive append `OracleVerifier.append` (record D5).

- `Stages ambient S inputs` is the plan of a finite chain of passive oracle verifiers from the
  statement type `S` and the oracle family `inputs`. `Stages.nil` has no stages.
  `Stages.cons s V draw rest` has a first stage with protocol `s`, verifier `V` and challenge
  draws `draw`, followed at each shape path `p` of `s` by the chain `rest p`, whose inputs are
  `V`'s output statement type and output family at `p`. Statement types and families may change
  at every boundary and may depend on the shape paths. Statements live in the computation
  universe `u`.
- `Stages.Compatibility c` is the evidence: at every boundary, an
  `OracleVerifier.OutputCompatibility` certificate between the stage's verifier and the composed
  verifier of the stages after it. `Stages.compose` computes the evidence type and the composed
  verifier together by recursion on the plan, and `Stages.verifier c e` is the composed verifier.
  The plan does not store its verifiers' certificates, because the certificate at a boundary
  refers to the composed verifier of the rest; storing it in the constructor would need an
  inductive-recursive definition. The certificates are general, so an output map may read its
  input statement, for example through `OutputCompatibility.ofStatement` when the intermediate
  statement is public. `Stages.StatementFree c` is the special case in which no output map reads
  its input statement; `Stages.StatementFree.certify` builds its evidence with
  `OutputCompatibility.ofStatementFree`.
- Inside a chain, the oracle families share one query universe `w`, because a recursive
  occurrence of an inductive type keeps the type's universe parameters. Families from other query
  universes enter and leave through `OracleFamily.liftQueries` and the verifier adapters
  `OracleVerifier.liftInputs`, `OracleVerifier.liftOutputs` and `OracleVerifier.lowerOutputs`,
  instances of `OracleVerifier.comapInputs` and `OracleVerifier.mapOutputs`. The recovery laws
  (`liftInputs_decideWith`, `liftInputs_outputData`, `liftOutputs_outputData`,
  `lowerOutputs_outputData`, `comapInputs_run`) state that the adapters keep the decision, the
  output data and the run.
- `Stages.protocol`, `Stages.draw` and `Stages.run` are the composed protocol, the combined draws
  and the core run `OracleVerifier.run` of the composed verifier with the challenges answered by
  the draws. `Stages.verifier_cons` and `Stages.draw_cons` state that a chain with a first stage
  composes by `OracleVerifier.append` and `combineDraw`, and `Stages.run_cons` states that its
  run is the run of the binary append of the first stage and the composed rest, which
  `OracleVerifier.run_append` splits into both interactions and both decisions.
- The decision laws are `Stages.decideWith_nil` (no stages accept the input statement, and
  `Stages.outputData_nil` forwards the input data), `Stages.decideWith_one` (one stage decides as
  that stage) and `Stages.decideWith_cons_of_reject` (a rejecting first decision rejects).
- The chain laws derive a property of the composed decision from one hypothesis per stage
  boundary, with predicates whose types may differ at every boundary and which may depend on the
  shape paths up to it (`Stages.Boundaries`): deterministic acceptance
  (`Stages.decideWith_accepts` from `Stages.DeterministicSteps`), the support
  (`Stages.decideWith_preserves_support` from `Stages.SupportSteps`) and almost-sure acceptance
  (`Stages.decideWith_preserves_measure` from `Stages.MeasureSteps`, with each boundary event a
  `Stages.DiscreteEvent` that carries the discrete measurable structure of its statement type).
  They concern the fold of the decisions after all interactions, and each is proved by induction
  on the chain from the binary law `OracleVerifier.append_decideWith_of_accept`,
  `OracleVerifier.append_decideWith_preserves_support` or
  `OracleVerifier.append_decideWith_preserves_measure`.

The composition runs the interactions of all stages and then folds the decisions. A rejecting
decision makes the composite reject and skips the later decisions, but no interaction. A later
stage is selected only by the shape path of the earlier stages, which records the prover's public
messages: neither a challenge, nor an oracle payload, nor an earlier verdict selects it (premises
P1 and P2 of the
[stage and execution inventory](../interaction-layer/stage-execution-disposition.md)).

The frozen executor decided each stage before the next one started, so a rejection skipped the
later interactions, and selected each stage's protocol by the statement the previous stage had
accepted. P1 and P2 retire both. `ArkLibTest/Interaction/Core/Oracle/StagesExample.lean` ports the
frozen two-stage tests with the history `[0, 2, 1, 3]` and the rejection history `[0, 2, 1]`, runs
three stages with a sampled challenge (`[0, 2, 4, 5, 1, 3, 6]`, and `[0, 2, 4, 5, 1]` when the
first decision rejects), and selects a second stage by the first stage's prover message. It also
composes a stage whose output map reads its input statement, alone and followed by a second stage;
composes stages whose families have their queries in `Type` and `Type 1`; and derives a property
of a three-stage decision from one hypothesis per boundary.

The split of a composition at an arbitrary middle stage is not ported. The protocol part exists:
PolyFun's `PFunctor.FreeM.append_assoc`, with the inverse laws of `Path.append` and `Path.split`,
and the concatenation `Chain.then` with `Chain.toTypeTree_then`. The missing part is a
reassociation law for `OracleVerifier.append`, which must transport paths and views along the
protocol associativity, reconcile `prefixRoute` and `suffixRoute`, and reassociate the
compatibility certificates. The split after the first stage is `Stages.run_cons`.

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
