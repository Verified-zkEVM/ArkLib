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
occurrences name each challenge independently of any transcript. Positions stay one universe above
moves and the monad, as D2 requires.

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

**Status: premise-required for run outputs and a prover's ambient index; unresolved for input
oracle data and for the full-log oracle runner.** Record D2's ledger puts moves and participant
outputs in `Type u` and leaves the other components of a verifier unstated. The code gives every
component that is not a run output its own universe as far as the definitions allow: the ambient
index of a verifier, the input oracle index `I`, the output oracle index `J p` of an oracle
verifier, the query types of the input and output oracle interfaces, the input statement, the
input witness and the intermediate witnesses of a knowledge state function.

**Premise-required.** Run outputs stay in `Type u`: the output statement `StmtOut p`, the output
oracle data `B p j` returned by a run, the output index `J p` once a run returns `∀ j, B p j`,
prover outputs, extracted witnesses and the state `σ` of a security experiment. Positions live one
universe up (`PlainPos`, `OraclePos : Type (u+1)`), because a position names a type, so the moves
and returned values of a run are in `Type u`, and the runner is `m : Type u → Type u`
(`OracleComp ambient` with responses in `Type u`). `simulateQ`, which answers the decision's
resource queries in a run and in `decideWith`, also needs the value universe to equal the response
universe. A run output in another universe would need a `ULift` adapter or a monad on a larger
universe, which record D2 rejects. A prover's ambient index is in `Type u` for the same reason:
`OracleComp ambient : Type u → Type (max uι u)` is the prover's monad, so `Reduction`, `Prover`,
both runs and the classical security models fix it.

**Query types are separated.** The decision no longer reads one homogeneous family
`sumFamily inputs (pathFamily s p)`. It reads `pathResources inputs s p`, the disjoint sum of the
input specification and the path's specification, with their data kept as a pair
(`Resources.sum`). `OracleSpec` addition allows the two index types to lie in different universes,
so the input queries (`OracleFamily.{uI, u, wI}`) and the output queries
(`OracleFamily.{uJ, u, wJ}`) take their own universes through routing, append and `decideWith`.
The query types never become values of the runner: they are answered by `simulateQ`, which
returns only responses.

**Unresolved: input oracle data.** The data `A i` of an input oracle is still in `Type u`, the
universe of the responses. This is not required by the runner: a realization `a : A` in a larger
universe can answer small queries with small responses through a function
`(a : A) → (q : Q) → Response q`, and a run never returns it. The coupling comes from
`OracleInterface` (`ArkLib/OracleReduction/OracleInterface.lean:55`), which stores an
`OracleContext Query (ReaderM Message)`. The pinned `ReaderM Message` is a monad
`Type v → Type v` on the universe of `Message`, so an interface's responses lie in the universe of
its data. Separating the data universe needs a generalization of `OracleInterface` to separate
realization and response universes. That file is outside this slice, so the dependency is open.
The same coupling ties the output oracle data `B p j` of an oracle verifier to `Type u` outside a
run.

**Unresolved: the full-log oracle runner.** `OracleVerifier.runWithLog` returns the decision's
full query log, which records input queries, so its input index `I` and its input query type stay
in `Type`. Only this full-log API keeps the restriction, for clients that need the resource
queries. Extraction does not use it. `OracleVerifier.runWithAmbientLog` puts the logger on the
ambient handler before adding the pure resource handler, so its result holds only two ambient
logs, and it takes the input statement, the input index and the input and output query types in
any universe. `map_runWithLog_eq_runWithAmbientLog` proves that, at small input universes, it is
the full-log run with the decision log restricted to its ambient entries, and
`map_fst_runWithAmbientLog` proves at the general signature that forgetting both logs gives
`OracleVerifier.run`. The oracle extraction game, the classical oracle extraction models and their
marginal lemmas run on it at the general signature. `Extractor.OracleStraightline` and
`Extractor.OracleTranscriptOnly` take a statement in any universe and have no input-family
parameter, so they never had the restriction.

**Security wrappers.** The input statement `S`, the honest input witness `W` and the input oracle
index `I` are arguments of a run, so the security wrappers take them in any universe:
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
restrictions that remain are the premise-required ones above (ambient index and experiment state
in `Type`, output data, output index and extracted witnesses in `Type`) and the two unresolved
ones (input oracle data in `Type`, and the full-log runner).

`ArkLibTest/Interaction/Core/UniverseCanary.lean` instantiates the independent universes against
`Verifier`, `OracleVerifier`, `Reduction`, both appends, the routing law `append_decideWith`,
`OracleMap.simulate_eq`, two oracle runs, the classical security models, the oracle extraction
game and the classical extraction models with their marginal laws. One input interface is an
`OracleInterface.{0, 1} Nat` whose queries are types, and an append routes it through a middle
family with queries in `Type 1` to an output family with queries in `Type 0`. A knowledge state
function with intermediate witnesses in `Type 1` and the input witness `Unit` certifies
round-by-round knowledge for the core definition and both verifier wrappers.

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

### Signature inventory

| API | Before this restack | After this restack |
| --- | --- | --- |
| `terminalObservation` | Only `protocol rounds`, fixed `T`, small inputs | Any `s`, `S : Type uS`, input index `I : Type uI`, independent query universes; result `Option (T (projectPathAlong _ _ tr))` |
| `closedTerminalObservation` | Fixed statement and output oracle carriers | Statement and oracle data at the transcript's path; output index may have its own universe outside a run |
| `verificationGame`, `closedVerificationGame` and their equality/evaluation laws | Product of transcript and a fixed observation type | Input paired with a dependent pair of transcript and observation at that path, plus the unchanged adversary witness |
| Uniform, private-coin, per-round and measured game relations | `relOut stmt tr out w` at a fixed output carrier | Same arguments, with `out : T (projectPathAlong _ _ tr)` or the closed path-indexed output |
| `verificationGame_eval_run` | Separate path equality and output equality in a fixed carrier | Equality of the dependent pair containing the path and its correctly typed observation |
| `run_scriptedProver` | Small statement and input-index types | Independent statement, input-index and query universes; run output constraints remain those of entry 18 |
| Unmeasured keyed predicates and restoration bounds | `Win stmt` and intermediate witnesses in `Type` | Independent input-witness universe `uW` and certificate universe `uK`, retaining statement-indexed carriers and every original relation |
| Measured node-kind budgets and stage bounds | Small statement index | Independent statement universe; program input/result carriers retain pinned VCVio's small-universe scope |
| Plain replay | Constant statement carrier | Prover-authored `b` selects `Fin 8`/`Fin 9`, with all original challenge quantifiers and returned values |

The probabilistic restoration games return the selected input and oracle data; these are run
outputs and remain small under entry 18. Input witnesses are not returned by the game and take
universe `uW`. Intermediate certificate witnesses take universe `uK` independently. Deterministic
observations and the scripted-run theorem have the larger argument universes listed above.

### Shared extraction laws and merge resolution

The merge conflicted in `Security/KnowledgeComposition.lean` and this notes file. The parent's
composition module and entries 1–19 were kept. The root-failure theorem and the two child
restriction laws contributed by state restoration were moved beside the definitions in
`Security/KnowledgeComposition/Extraction.lean`, retaining independent universes.
`badChallengeFromMaps` factors the same bad-transition recursion through the certificate's actual
states and extraction maps, so unused root obligations do not affect it. Keyed recursive helpers
use `withRootWitness` internally, as the parent composition does; their public signatures retain
the original input carrier.

`exists_badChallenge_of_extraction_failure` still concludes
`BadChallengeOnCompletion F stmt messages table w key`. Every transition keeps the witness
extracted from the actual remaining transcript and the supplied `w`. Only the explicitly named
`BadChallengeOnCompletion.mem_badChallenge` forgets that witness for the probability bound.
The larger-certificate canary checks keyed localization after lifting the certificate to `Type 1`.

### Frozen one-round rows

Locations below refer to the existing row annotations in
`ArkLibTest/Interaction/Core/Security/StateRestoration.lean` and the corresponding frozen file.

| Row | P2 disposition and ported assertion |
| --- | --- |
| 1, input law | Unchanged: every input and witness satisfies exactly the original root relation. |
| 2, plain output law | Challenge-selected carrier retired by P2. `selectedPlainOutputLaw_iff` retains the full equivalence for every authored selector, input, transcript and witness. |
| 3–5, preservation and local bound | Shape-independent and retained unchanged, including both challenge values and the exact `1/2` bound. |
| 6, extraction | Unchanged value thirteen from witness six and payload seven, on every challenge; the selector does not enter extraction. |
| 7, freshness | Shape-independent uniform sampling retained; `selected_fresh` checks the full selected interaction for every input, selector and payload. |
| 8, plain game bound | Authored carrier replacement; `selected_actual_game_bound` retains the always-returning terminal, challenge-based relation and error `1/2`. |
| 9–11, replay and evaluations | Challenge-selected carrier retired by P2. `plainScriptedRun_eq`, `replayResult_eq` and the two evaluations retain payload seven on both challenges in the selected carriers. |
| 12, extraction evaluation | Unchanged value thirteen. |
| 13–14, oracle observations | `selectedObservation` retains every input and payload, exact accepted claim on true and rejection on false; only the statement-carrier selector changes. |
| 15, oracle output law | `selectedOracleOutputLaw` retains the complete terminal-state equivalence, including every supplied witness. Output oracles remain `Fin 8`. |
| 16, closed game bound | `selected_actual_oracle_game_bound` retains `1/2` in both authored carriers, with a general bounded-adversary theorem underneath it. |
| 17, rejecting relation | The selected false-branch assertion retains arbitrary relations and excludes every related claim. |
| 18–19, closed evaluations | The selected oracle replay evaluates to `some (7, 7)` on true and `none` on false. |
| 20, private coins | `selected_actual_coin_game_bound` retains the two original coin-selected adversaries and `1/2`. |
| 21, failed coins | The selected-game failure assertion retains probability zero. |

### Frozen two-round rows

The row annotations are in `ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean`.

| Row | P2 disposition and ported assertion |
| --- | --- |
| 1–3, input law, preservation, local bounds | Shape-independent and retained, including the distinct challenge alphabets and round errors `1/8` and `1/16`. |
| 4–5, observation and output law | Challenge-selected carrier retired by P2. `PublicSelection.observation` and `outputLaw` retain every input, both messages, both challenges and every witness, with the original acceptance disjunction. |
| 6, query bound | The original adversary still queries the later salted key twice before completion; query bound two is unchanged. |
| 7, extraction | Unchanged extraction eighteen on every pair of challenges. |
| 8–9, error arithmetic | Unchanged maximum error `1/8` and error sum `3/16`. |
| 10, nonuniform game bound and charge | `PublicSelection.actual_nonuniform_game_bound` retains the same adaptive adversary and `7/16` in both authored carriers; the original round-charge theorem remains unchanged. |
| 11, strict improvement | Unchanged comparison with the coarser uniform bound. |
| 12, reachable bad execution | The selected accepting claim with witness six still extracts eighteen and fails the input relation. |
| 13, accepting/rejecting observation evaluations | Selected evaluations retain `some (7, 7)` and `none`. |
| 14, extraction evaluation | Unchanged extracted value eighteen. |
| 15–30, measured extraction | Shape-independent stage maps, budgets, execution results, empty carriers and program equalities remain unchanged, with every original path and witness quantifier. |
| 31, packaged measured game | `PublicSelection.measured_game_bound` instantiates the packaged theorem for each selected carrier and retains all statement/path/witness quantifiers and cost two. |
| 32, program-result event | `PublicSelection.program_run_game_bound` states failure on the actual program result, with error `7/16` and cost two. |

The one- and two-round closed games also have table-evaluation and actual-party replay laws. No
challenge-selected output carrier is asserted inside the P2 core, and no approved row is left
pending path-indexed outputs.

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
