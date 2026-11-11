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

## 21. Round-by-round soundness implies soundness for lawful distribution monads

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


`Sumcheck.Core.Soundness` now proves full-run soundness natively for every map
`D : Fin d → R`, with indexed sums that retain repeated points. `Indexed` proves the local
false-to-true bound and constructs the round-by-round state function. It applies #1486's
`OracleVerifier.soundness_of_rbrSoundness_uniform` and counts one challenge per round to obtain
`n * (deg / |R|)` for the actual core run of every prover. `Soundness` derives arbitrary-list
and injective corollaries, plus committed and possibly failing randomized one-round bounds in
probability and measure form. No native security theorem imports or uses the legacy embedding.

`Types`, `Tree` and `Domain` own the native statements, fixed protocol and indexed arithmetic.
`DomainEquivalence` keeps the separate injective comparison with `Spec`; `LegacySoundness` keeps
the previous transferred bound as a comparison check. The arithmetic holds for commutative
semirings. The probabilistic bounds add `IsDomain`, finiteness and uniform sampling. Tests check
that constant one sums to two over `[0, 0]`, to one over `[0]`, and passes the native final
decision with repeated points and target two. The native tests audit the theorem axioms.

#1488 implements interval endpoints with `intervalVerifier` built from native `foldVerifier`.
The exact-row Sumcheck disposition gives interval execution, projection and append targets;
their full-run corollaries preserve the parent statements. P1 and P2 explain changed abort and shape assertions.
Behavior-guarantee assertions remain unresolved pending the corresponding parent interface.

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

**Code.** `Sumcheck/Core/Fold.lean` implements passive native checks. `Interval` specializes
those checks to every `start + count ≤ n`. `IntervalCompleteness` proves support, perfect and
measure completeness for that full range. `IntervalAdaptive` supplies current-statement
challenge callbacks through an actual shared-state handler. `IntervalSoundness` proves native
round-by-round suffix soundness for exactly `start + count = n`, then applies the parent's
uniform implication with `count` challenges and error `count * (deg / |R|)`. Lists retain all
repetitions; embeddings specialize the same proofs. `intervalVerifier_full_run` identifies the
zero-start full interval with the parent's native indexed verifier without changing its theorems.

`FoldComposition.run_append_public_intervalVerifier` compares actual public one-round and
suffix interval verifier runs. It transports the midpoint and endpoint statements explicitly,
retains the transcript, original polynomial and private output, and permits arbitrary effectful
provers. `Projection` constructs the native projected oracle map and its derived query handler.
`projectedExecute_closed` identifies returned behavior with that handler;
`projectedExecute_related` proves its evaluation claim. `Behavior` handles arbitrary original
input behavior at the empty interval and proves its final remaining-sum relation is evaluation.
`BehaviorComposition.run_append_behaviorIntervalVerifier` extends the public append equation
to arbitrary original evaluation behavior. `IntervalRoundSoundness` proves the actual one-round
probability and measure bounds at every variable position, including intermediate endpoints.
`ComputableProjection` computes indexed CompPoly projections, retaining repeated domain points.
`ComputableInterval` constructs the honest computational strategy and proves its interpretation,
actual execution equality and completeness. `ComputableSoundness` transfers the native suffix
bound to every computational-message prover with shared ambient state.
`Interpreted` and `InterpretedExecution` provide generic message interfaces and preserve both
prover slots, each public draw and the terminal computation under evaluation-preserving message
interpretation. Legacy `Spec` projections and honest prover comparisons are isolated in
`LegacyProjection` and `LegacyProtocol`; native security does not depend on them.

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
  different types. Challenge implementations move between the carriers by `transportDraw`, which
  keeps uniform sampling.
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
