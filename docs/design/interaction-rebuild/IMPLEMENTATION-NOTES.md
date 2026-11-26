# Implementation notes for the interaction core

These notes record where `ArkLib/Interaction/` departs from the design records in this
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
`Transcript.split` and `Transcript.append` (`Interaction/Transcript.lean`, where `TranscriptAt` is also
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

**Superseded by record D2's [universe policy](D2-ownership-and-universes.md#universe-policy)
(2026-11-25); migration in progress.** Under the policy, data lies in `Type`, descriptions of data
in `Type 1`, adversaries in one universe that the model argument determines, and generic
polynomial code in PolyFun's universes. Step 2 removed the security definitions' independent
universes and both `.lift` lemmas. Step 3 removed the independent statement, witness and index
universes of execution, reductions, oracle verifiers, composition and stage chains. Step 4 made
`OracleBundle : Type 1`, with its query indices, responses and data in `Type`, and removed the
adapters that changed a query or response universe. That also retired the full-log limit below.
The universes of the oracle vocabulary disappear in later steps, and this entry is retired with
the last [migration step](D2-ownership-and-universes.md#migration). Until then, the rest of this
entry describes the current code. [`universe-policy.md`](../interaction-layer/universe-policy.md)
records the reasons.

**Retained runner contract.** Run outputs lie in `Type`: the output statement `StmtOut p`, the
output oracle data `(outputs p).Data` returned by a run, prover outputs, extracted
witnesses and the state `σ` of a security experiment. The execution APIs pin their protocols at
`Protocol.{0}` and `OracleProtocol.{0, 0}`, so positions lie in `Type 1`. Moves and returned
values lie in `Type`. The prover's monad is `OracleComp ambient : Type → Type`, with the ambient
index and responses in `Type`. A generic runner keeps its result universe, `m : Type → Type v`.
`simulateQ`, which answers the decision's bundle queries in a run and in `decideWith`, also needs
the value universe to equal the response universe. A run output in another universe would need a
`ULift` adapter or a monad on a larger universe, which record D2 rejects.

`OracleProtocol` takes the tree's actual leaf type as a parameter, defaulting to `PUnit`.
All execution, path-bundle and security APIs use those default trivial leaves, preserving their
previous carriers by definitional equality. An explicit leaf type describes return values in the
authored `FreeM` tree. The parameter is used by the tree representation and is not a phantom:
the universe canary constructs and reads a natural-number leaf. Exposing that parameter also
lets the pinned universe linter distinguish the move universe in the alias's type; the query
universe remains independent, without a linter suppression or source-policy exception.

**Bundle data in `Type`.** A decision reads `pathBundle inputs s p`, the disjoint sum of the
input specification and the path's specification, with their data kept as a pair
(`OracleBundle.sum`). Since step 4, both query types and all bundle data lie in `Type`.
Step 4 did not change the definition of `OracleInterface`. Consolidation PR 5 deleted
`OracleFamily`, `OracleBundle.ofFamily` and `OracleMap.embedding`: an indexed family of oracles is
the bundle `OracleBundle.ofIndexed A O`, and `OracleMap.reindex` renames its indices. Record D6
still describes outputs that form an `OracleFamily`. The oracle messages on a path form the bundle
`oracleMessageBundle s p`, built from `OracleBundle.empty`, `OracleBundle.sum` and
`OracleBundle.of`. It and `splitOracleMessages` take `OracleProtocol.{0, 0}`, as the verifier APIs
do. The R26/R27 client `ArkLibTest/Interaction/Oracle/BundleFamilies.lean` still
checks the named and visible query carriers, the whole-context data, the verifiers and the shared
run, now in `Type`. Its assertions of independent universes are retired under the policy adopted
in #1580.

**Equivalent: Agreement output and witness families (F7 and 3A).** `Security/Agreement.lean`
now preserves path-dependent `T p` and `outputs p` in every agreement and tree
transport law. The output type is `OracleVerifier.Output T outputs`. Since step 2 of the policy
migration, agreement and every agreement and cast law take their data in `Type`.

Round-by-round knowledge agreement and transport quantify over `Win stmt` and `W stmt tr`.
The output relation receives
the input statement, completed transcript, output and witness in that order. The owner definition
in `Security/RoundByRound.lean` is unchanged. Prefix-dependent draws and local errors remain
available; Sumcheck specializes them through `rbrKnowledgeSoundnessOfNodes`. The
[Agreement inventory](../interaction-layer/sumcheck.md#agreement-universes-and-parent-limits)
marks both reviewed contracts equivalent and records the ordinary-import clients.
Neither P1 nor P2 retires an Agreement output or witness contract.

**Retired limit of the full-log runner.** `OracleVerifier.runWithLog` returns the decision's
full query log, which records bundle queries, so it needs the bundle query types in `Type`.
Since step 4 every bundle has them there, so the runner accepts every oracle verifier and no
large-query logging interface from VCVio is needed. Extraction does not use the full-log runner.
`OracleVerifier.runWithAmbientLog` puts the logger on the ambient handler before adding the pure
bundle handler, so its result holds only two ambient logs. `map_runWithLog_eq_runWithAmbientLog`
proves that it is the full-log run with the decision log restricted to its ambient entries, and
`map_fst_runWithAmbientLog` proves that forgetting both logs gives `OracleVerifier.run`. The
oracle extraction game, the classical oracle extraction models and their marginal lemmas run on
it.

**Execution and composition.** Step 3 of the
[policy migration](D2-ownership-and-universes.md#migration) puts the statements, witnesses,
ambient indices and output oracle indices of `Execution.lean`, `Reduction.lean`,
`OracleVerifier.lean`, `Composition.lean`, `StageChain.lean` and `Oracle/LoggedExecution.lean` in
`Type`. `Verifier` and `Verifier.append` take `ambient : OracleSpec.{0, 0} ι`. Step 4 puts
stage-chain query indices, bundles and bundle-backed routing in `Type` and removes the universe
adapters. `OracleVerifier.comapInputs` and `OracleVerifier.mapOutputs` remain general maps.
Generic transcript-split lemmas keep their polynomial universes, and generic monads keep their
result universe `v`.

**Security wrappers.** The security definitions now take their data in `Type`, as step 2 of the
[policy migration](D2-ownership-and-universes.md#migration). Statements, input, intermediate and
output witnesses, problem claims and witnesses, input oracle data and query indices, and the
values of the runner monad lie in `Type` in every file of `Interaction/Security/`. The protocol
and family arguments are pinned at `0` until the vocabulary step removes their universes. Bundles
have had no universe parameters since step 4.
`AdversaryModel` keeps one universe `w` for its adversaries, and an `ExtractionInterface` over a
model takes its extractors in the same universe. The generic round-by-round definitions keep
the position universe `uA` of `P : PFunctor.{uA, 0}`. Generic monads keep their result
universe, which the monad argument determines: `soundnessWith`, `validAcceptanceWith` and the
implication lemmas take `m : Type → Type v`, and `PrefixDraw` takes `m : Type → Type vDraw`.
Step 2 deleted `KnowledgeStateFunction.lift`, `rbrKnowledgeSoundness.lift`, the explicit witness
universe that `rbrKnowledgeSoundness` and its verifier and oracle-verifier forms passed to the
existential, and the legacy adapter `treeRelationProblem`, which duplicated `relProblem` once
claims lie in `Type`. The legacy-to-interaction theorems therefore return their certificate
without lifting it. Step 2 also deleted `KnowledgeStateFunction.withRootWitness`, which moved an
input witness into the universe of the intermediate witnesses. The composition laws in
`KnowledgeComposition/Extraction.lean` and the completion laws in `StateRestoration.lean` each
have one form now, with no `...Aux` duplicate. Extracted witnesses returned by the extraction
games are values of the runner and stay in `Type`. Neither P1 nor P2 retires any of these
contracts; both premises concern scheduling and shape rather than universes.

`ArkLibTest/Interaction/UniverseCanary.lean` checks oracle maps, the oracle append, the routing
law `append_decideWith` and two oracle runs with all bundle data in `Type`. It keeps an oracle
node carrying `OracleInterface.{0, 1} Nat`, whose queries are types, until the vocabulary step.
The R26/R27 constructors in `ArkLibTest/Interaction/Oracle/BundleFamilies.lean` and their
verifier and run examples also work in `Type`.

## Changes that keep to the records

### Verifier outputs are indexed by the shape path

Record D6 fixed the output family for the first milestone. Both verifiers now index their outputs
by the public shape path: `Verifier ambient s StmtIn StmtOut` takes `StmtOut : Path s → Type u`,
and `OracleVerifier ambient s S T inputs outputs` takes `T : Path s → Type` and
`outputs : Path s → OracleBundle`. The decision returns `T p` and the output map
targets `outputs p`; `OracleVerifier.Output T outputs p := T p × (outputs p).Data` is the accepted
claim of a run. In an append the composite's output at a path of `s₁.append s₂` is the suffix's
output at the split path (`splitFamily` for statements, `OracleVerifier.splitOutputs` for
bundles), so composed decisions return the suffix's output without a cast. `Outcome` takes the indexed family, and the security
definitions take output problems over the path context (`PathProblem s T`), with acceptance
predicates typed at the transcript's path (`validAcceptance impl stmt tr (event : T p → Prop)`).
Constant families `fun _ => T` recover every earlier user; the legacy embedding and the sumcheck
core use them, so their statements are unchanged. Record D6 is updated accordingly, and
`ArkLibTest/Interaction/Oracle/DependentRouting.lean` ports the frozen layer's dependent
routing example.

### Finite heterogeneous stage composition

The interaction layer had no replacement for the old-layer ordered execution of a finite family of
closed stages (`ExecutionInterface`, `ClosedStage`, `OrderedExecution.run` in
`ArkLib/Interaction/Oracle/Composition.lean`). `ArkLib/Interaction/StageChain.lean` adds the
right-associated passive composition API: a chain appends its first stage to the composed rest
through the passive append `OracleVerifier.append` (record D5).

- `StageChain ambient S inputs` is the plan of a finite chain of passive oracle verifiers from the
  statement type `S` and the oracle bundle `inputs`. `StageChain.nil` has no stages.
  `StageChain.cons s V draw rest` has a first stage with protocol `s`, verifier `V` and challenge
  draws `draw`. At each path `p` of `s`, the chain `rest p` follows. Its inputs are `V`'s output
  statement type and output bundle at `p`. Statement types and bundles may change at every
  boundary and may depend on the paths. Statements live in the computation universe `u`.
- `StageChain.Compatibility c` is the evidence: at every boundary, an
  `OracleVerifier.OutputCompatibility` certificate between the stage's verifier and the composed
  verifier of the stages after it. `StageChain.compose` computes the evidence type and the composed
  verifier together by recursion on the plan, and `StageChain.verifier c e` is the composed verifier.
  The plan does not store its verifiers' certificates, because the certificate at a boundary
  refers to the composed verifier of the rest. Storing it in the constructor would need an
  inductive-recursive definition. The certificates are general, so an output map may read its
  input statement. `OutputCompatibility.ofStatement` gives a certificate from a function of the
  input statement, the composed path and the view, provided every accepted prefix statement
  equals that function's result. `StageChain.StatementFree c` is the special case in which no
  output map reads its input statement. `StageChain.StatementFree.certify` builds its evidence with
  `OutputCompatibility.ofStatementFree`.
- A chain's oracle families have their queries in `Type`. Step 4 deleted the universe adapters
  (`OracleFamily.liftQueries`, `OracleVerifier.liftInputs`, `OracleVerifier.liftOutputs`,
  `OracleVerifier.lowerOutputs`) and their recovery laws. The general maps
  `OracleVerifier.comapInputs` and `OracleVerifier.mapOutputs` remain. `comapInputs_run` gives
  the same run after the bundle queries are answered from the supplied data. It does not bound
  the source queries that the routing issues, which needs a separate statement.
- `StageChain.protocol`, `StageChain.draw` and `StageChain.run` are the composed protocol, the combined draws
  and the core run `OracleVerifier.run` of the composed verifier with the challenges answered by
  the draws. `StageChain.verifier_cons` and `StageChain.draw_cons` state that a chain with a first stage
  composes by `OracleVerifier.append` and `combineDraw`. `StageChain.run_cons` states that its run is
  the run of the binary append of the first stage and the composed rest.
  `OracleVerifier.run_append` splits that run into both interactions and both decisions.
- The decision laws are `StageChain.decideWith_nil` (no stages accept the input statement, and
  `StageChain.outputData_nil` forwards the input data), `StageChain.decideWith_one` (one stage decides as
  that stage) and `StageChain.decideWith_cons_of_reject` (a rejecting first decision rejects).
- The chain laws derive a property of the composed decision from one hypothesis per stage
  boundary. The predicates may differ in type at every boundary and may depend on the paths up to
  it (`StageChain.Boundaries`). There are three chain laws:
  - deterministic acceptance (`StageChain.decideWith_accepts_of_deterministic` from `StageChain.AcceptsDeterministically`);
  - the support (`StageChain.decideWith_accepts_of_onSupport` from `StageChain.AcceptsOnSupport`);
  - almost-sure acceptance (`StageChain.decideWith_accepts_of_almostSurely` from `StageChain.AcceptsAlmostSurely`).
    Each boundary event is a `StageChain.DiscreteEvent` that carries the discrete measurable
    structure of its statement type. Probabilities come from the `OracleSpec.AnswerMeasure`
    instance on `ambient`. A persistent runtime with private state needs its own compatibility
    statement or invariant relating it to that measure.

  They concern the fold of the decisions after all interactions. Each is proved by induction on
  the chain from the binary law `OracleVerifier.append_decideWith_of_accept`,
  `OracleVerifier.append_decideWith_accepts_of_onSupport` or
  `OracleVerifier.append_decideWith_accepts_of_almostSurely`.

The composition runs the interactions of all stages and then folds the decisions. A rejecting
decision makes the composite reject and skips the later decisions, but no interaction. Only the
path of the earlier stages selects a later stage, and that path records the prover's public
messages. Neither a challenge, nor an oracle message, nor an earlier verdict selects it directly
(premises P1 and P2 of the [stage and execution port table](../interaction-layer/port-stages.md)).
A prover can choose its messages after seeing a challenge, so a challenge can still affect the
choice through the prover. Each challenge comes from a draw program indexed by the challenge node,
over the same ambient interface the prover uses. The types do not make challenges public-coin; a
client that needs public-coin sampling states it as a separate condition.

The old-layer executor decided each stage before the next one started, so a rejection skipped the
later interactions. It also selected each stage's protocol by the statement the previous stage had
accepted. P1 and P2 exclude both. `ArkLibTest/Interaction/Oracle/StageChain.lean` ports
the old-layer two-stage tests with the history `[0, 2, 1, 3]` and the rejection history
`[0, 2, 1]`. It runs three stages with a sampled challenge, with history
`[0, 2, 4, 5, 1, 3, 6]`, or `[0, 2, 4, 5, 1]` when the first decision rejects. It selects a second
stage by the first stage's prover message. It also composes a stage whose output map reads its
input statement, both alone and followed by a second stage. It composes stages whose families
have their queries in `Type` and `Type 1`. Finally, it derives a property of a three-stage
decision from one hypothesis per boundary. A one-stage decision that queries an ambient `Bool`
and rejects on `false` accepts almost surely under the answer measure `alwaysTrue`, although its
support contains the rejection.

The split of a composition at an arbitrary middle stage is ported on completed runs.
`StageChain.then` concatenates two chains, following PolyFun's `Chain.then` and
`PFunctor.FreeM.append_assoc`. `StageChain.decideOn_then` and `StageChain.outputOn_then` split the
composed verifier of a concatenation at the cut, and `OracleVerifier.append_append_decideOn` and
`OracleVerifier.append_append_outputOn` in `Interaction/Oracle/Reassociation.lean` reassociate
`OracleVerifier.append`. The laws are `HEq`s on runs, because the two associations have different
protocols and a certificate's output map agrees with the composite output map only on accepted
intermediate statements. They do not transport the prover of a concatenation to the appended
protocol. A chain's run still unfolds one append at a time through `StageChain.run_cons`.

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

The tests in `ArkLibTest/Interaction/Security.lean` use the carrier `Fin (payload + 1)`
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
earlier moves (the partial transcript, `PartialTranscript` in `Interaction/Transcript.lean`), the querier
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

The test file `ArkLibTest/Interaction/Oracle/LoggedExecution.lean` keeps the aggregate tests.
It adds per-entry runtime observations, membership of the actual join and decision entries, proofs
that oracles were sent, and exclusion of future moves. Its distinguishing test moves one ambient
request across a fixed public message. The ordinary outcomes and aggregate logs stay equal, while
the partial transcripts of the queries differ. P1 excludes intermediate effectful verifier
actions and their former query groups. It does not exclude prover moves or their partial
transcripts. The [port table](../interaction-layer/port-logged-execution.md) records these
qualifications separately.

### Oracle-access tests after the parent merge

DecorationExample row 2 is ported. The old alias is the oracle decoration of an arbitrary tree
at independent message and query universes. Oracle positions carry their interfaces, so
`UniverseOracleDecoration` reads the decoration of an arbitrary `OracleProtocol.{uProtocol, uQuery}`
tree off the tree, as its path family. `universeNode` additionally attaches an arbitrary
`OracleInterface.{0, 1} Nat` to an actual small protocol node, and the path-family assertion keeps
its query type.

The [oracle-access port table](../interaction-layer/port-oracle-access.md) now links two groups
of rows directly to the parent's `LoggedExecutionTests` assertions. The first group holds the
PhasedRun querier, setup and partial-transcript rows. The second group holds the QueryBounds rows
on membership of the join and decision entries and on concrete partial transcripts. It also holds
the QueryBounds rows on node names and on the agreement of the queries by move with the logged
run. P1 excludes intermediate verifier actions and the entries they were assigned to.
`RoutedAccessTests.raw_available` proves that every query in the completed bundle of the composed
doubled-export execution has a matching node at its decision entry.
`RoutedAccessTests.routed_available` applies that permission to the routed program, and
`QueryCostTests.routed_available_and_cost` pairs it with cost five for the same program.
`RoutedAccessTests.loggedSummary_eq` and `RoutedAccessTests.composed_decisionQueries` check the
actual ordered decision queries. The oracle-message splitting checks remain. The parent's large-query
full-log limitation in entry 18 is unchanged.

## 26. Knowledge composition and measured extraction

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
| `KnowledgeStateFunction` | `Win stmt`, `Witness stmt sp history` and `W stmt tr` retain the input statement. Statements and all witnesses lie in `Type`. |
| `extractFrom`, `extractAlong`, `leafWitness` | Pure backward maps take the output witness directly. The root map returns `Win stmt`; no output or seam carrier is encoded. |
| `child`, `extractFromMaps` | Restrict to a first move and factor extraction through its computational fields. |
| `append` and its extraction/state laws | The prefix's output family `Wmid stmt tr₁` is the suffix's input family. The seam states that the suffix root extractor returns a valid prefix witness. |
| `guard`, `condition`, `comap` and their local bounds | Restrict states to admissible inputs, conjoin a statement predicate, or pull back statements and map dependent input/output witnesses. |
| `BadChallengeFrom`, `BadChallengeAlong` | Follow the actual suffix extraction of the supplied output witness. `extraction_failure_implies_badChallengeAlong` identifies a receiver transition without choosing a different witness. |
| `rbrKnowledgeSoundness` and both verifier wrappers | Pass the output family through to the certificate. Legacy wrappers specialize to their original output families. |
| `rbrKnowledgeSoundness_append`, `_of_mid` | Compose local errors and dependent middle relations on every prefix transcript, including false middle claims. `_of_mid` accepts explicit input and output witness maps. |
| Plain/oracle `simulateQ_append_run`, `support_append`, `validAcceptance_append` | Decompose the two decisions with the same intermediate ambient state and, for oracle verifiers, actual routed suffix data. The support laws work in any lawful monad with lawful support. The oracle law takes an `OracleBundle` input. |
| `PrefixDraw.ofView`, `combineViewPrefixDraw`, `rbrKnowledgeSoundness_append_view` | Oracle verifiers draw challenges from the verifier view (`viewSig`), and the suffix draw is chosen from the first stage's view. Errors, states, carriers and backward maps keep the full prefix. |
| `Verifier.rbrKnowledgeSoundness_append`, `_of_pure` | Compose standalone plain verifier hypotheses. The supported prefix result must equal the named middle statement; `_of_pure` derives that law for a pure prefix decision. |

The plain verifier proof conditions suffix states on possible prefix acceptance. The suffix has
its own output relation. No theorem identifies two independently existential acceptance events
with composite acceptance. `TranscriptAt.split_pair` and `Verifier.append_decide_transcript` expose the
transports in the decision fold; heterogeneous equality identifies outputs at equal paths.

The oracle fixture instead uses `rbrKnowledgeSoundness_append`, `_of_mid` and
`rbrKnowledgeSoundness_append_view` with `composed_validAcceptance_iff` as an explicit
relation-level bridge. It does not instantiate a generic standalone oracle verifier composition
theorem. The plain `indexed_composed` client (two empty protocols) and `challenge_composed` (one
uniform challenge that selects the middle claim) do instantiate the standalone plain verifier
theorem. The disposition record keeps these claims separate.

### Full-prefix distributions and local errors

The shared `PrefixDraw` and `PrefixError` interfaces index draws and errors by the same receiver
cursor and full history. The public `rbrKnowledgeSoundness` predicate and the plain verifier form
use these interfaces. The oracle verifier form takes a `PrefixDraw viewSig` and applies it to the
prefix with oracle messages erased (`PrefixDraw.ofView`); its error keeps the full prefix. `combinePrefixDraw` retains the first error before the seam. After the seam,
it selects the second error family by the complete first transcript and evaluates it at the
second prefix history. `appendPrefixSampler_eq_combinePrefixDraw` proves the matching sampler law.

The `_prefix` composition theorems accept these families. The node-indexed predicates end in
`OfNodes`; the established node composition theorems follow from the general laws by ignoring
history. There is one local-bound and composition proof development. P1 removes only challenge
selection that depends on oracle messages and effectful receiver actions. Earlier public challenges
and prover messages may select later distributions and local errors. Fresh uniform draws are a
separate premise of the public-coin specialization. Regressions in `PrefixKnowledge.lean` send
different oracle bits with equal verifier views and check that the view draws, including the
suffix draw of a two-stage composition, do not separate them. The fixed two-bit zero-error
certificate in `ArkLibTest/Interaction/Security/PrefixKnowledge.lean` checks this distinction
without inserting a prover message. The inventory records the corrected schedule correspondences,
including KC-065 as equivalent because its frozen schedule was already constant.

### Measured extraction

`Security/MeasuredExtraction.lean` names one PolyFun `PFunctor.FreeM.BudgetedProgram` for each
root, step and leaf map. `programAlong` composes those programs using PolyFun's
`BudgetedProgram.comp` and `contramap`.
`BudgetAtMost rootBound stepBound leafBound` gives
`leafBound + (completeSpine l tr).length • stepBound + rootBound`.
The frozen `length • bound` result is recovered by explicitly supplying zero root and leaf
bounds to `programAlong_budget_le_nsmul` and `programAlong_costAtMost_nsmul`.
The empty-protocol fixture quantifies all state functions and stage programs with those zero
bounds. It does not assume an arbitrary root or leaf program has budget zero.

The cursor induction counts full moves, including oracle messages. PolyFun's node-dependent
charges do not directly replace it: the stage programs depend on the statement and full earlier
moves, and the root and leaf budgets require separate accounting. Instruction budgets leave pure
work, views, answers, carrier identification and intermediate witness sizes uncharged. The zero
program exists for every state function; the ordered and unbounded-depth tests use named charged
programs to test actual instruction cost as well as budgets. An empty-protocol test charges
both the leaf and the root and checks their order against the general bound. Zero stages give
every state function a measured certificate with zero declared cost, so an operation-count
result names its stage programs and prices. Measured append and a uniform game-extractor
contract are follow-up work.

The measured API retains these small carriers through the binders of `MeasuredStages`. These
restrictions also apply to `programAlong` and `MeasuredKnowledgeStateFunction`, and lifting them
is follow-up work. At the previous VCVio pin `f8d7f8ef`, VCVio's `OracleComp.BudgetedProgram` and
`OracleComp.MeasuredProgram` forced the carriers to `Type`. The pinned PolyFun declarations below
do not:

| Restricted carrier | Pinned declaration at PolyFun `713d8857e49d20927c1447b3ba7397acc5537319` |
| --- | --- |
| Input witnesses `Win stmt : Type` and root-stage result | `PFunctor.FreeM.BudgetedProgram {Input : Type uI} {Result : Type u} (f : Input → Result) (ω : Type w)` in `PolyFun/PFunctor/Free/Cost/Measured.lean:194` takes independent universes. The root program realizes `extractRoot`. |
| Intermediate witnesses and `StageInput : Type` | `BudgetedProgram.comp` at line 221 takes `Mid Result : Type u`. `programAlong` composes the stages, so it puts the intermediate witnesses and the root result in one universe. `BudgetedProgram.contramap` at line 216 takes the new input in any universe. |
| Output witnesses `W stmt tr : Type` | The `BudgetedProgram` input binder takes any universe. `BudgetedProgram.ofFun` at line 210, which `MeasuredStages.zero` uses, puts its input in the universe of its result. |
| Cost type `ω : Type`, instruction names and views | `PFunctor.FreeM.MeasuredProgram (Input : Type uI) (Result : Type u) (ω : Type w)` at line 52, with fields `View : Type u` and `Op : Type u`. `BudgetedProgram` bundles this program. VCVio's bridge `VCVio/OracleComp/QueryTracking/MeasuredProgram.lean:51` at VCVio `f1a4a8ecef2e76b3af3dbe5205c604066dba85e3` states the oracle-cost lemmas for `Input Result ω : Type`. |

The statement universe remains arbitrary. The pure `PartialTranscriptAt`, `KnowledgeStateFunction`,
lifting, extraction, extraction failure, append and restriction laws accept
`P : PFunctor.{uA, u}` and a lens to `rolePoly.{u}`, with leaves `PUnit.{u + 1}`.
The move, statement and witness universes are independent; branches and leaves share the move
universe. KC-318 and KC-322 now send the frozen oracle message `m : ULift.{1} Nat`, retain
`ULift.{2} (Fin (m.down + 1))` witnesses and prove extraction returns six. The measured code
takes `P : PFunctor.{uA, 0}`, so its positions also have their own universe.

Probability bounds use the small-move instance of this general certificate. VCVio's
`ProbComp : Type → Type` at the previous pin `f8d7f8ef` (`VCVio/OracleComp/ProbComp/Basic.lean:31`)
forced `sampleAt` to return a small move. The current pin makes `ProbComp` universe-polymorphic,
and ArkLib has not yet generalized `sampleAt`. `challengeSpec` (`Interaction/Protocol.lean:69–71`)
returns `Move l`, whose universe is
shared by challenges and public/oracle messages. The disposition record's PROB-031 names this
remaining probabilistic limitation. It does not restrict pure backward maps or large output
and seam witnesses in the verifier wrappers.

### Acceptance evidence

The composition fixture sends a public prover selector after the Boolean challenge. That selector
chooses a public unit-message suffix or an oracle-message suffix under P2. Both challenge values
remain available on each selected shape. `Fin (n + 1)` carriers that depend on the oracle message,
extraction composition, leaf relations and the exported oracle from the same execution are checked on
both shapes. The selector change is premise-required under P2, not missing parent support.

The ordinary-import universe canary composes with `Type` itself as the output and seam carrier,
both in `Type 1`, and tests both verifier wrappers and lifting with large output witnesses.
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
They are not a missing parent dependency, as entry 26 also records.

The replacement fixture prepends a prover-authored Boolean `b` to the original one- or two-round
protocol. That public message selects the exact statement carriers `Fin 8` and `Fin 9`. The
challenge remains independent and continues to control acceptance, rejection and knowledge-state
transitions. The fixtures quantify over both selectors and every original challenge, statement,
message and output witness. In particular the diagonal selectors reproduce the numerical frozen
replays, while all four selector/challenge combinations are checked by universal theorems.
The frozen output oracle stays `PUnit → Fin 8`, with the original interface and data. A
separate `varyingVerifier`/`varyingGame` fixture additionally checks genuinely path-dependent
output oracle carriers and interfaces; it does not replace the frozen rows.

### Games and execution

`selectedPlainGame`, `selectedClosedGame` and the two-round `PublicSelection.game` restore the
original adversary and evaluate the full verifier on the public-selector-prefixed transcript.
Their output is dependent on that returned transcript. The public selector makes no restoration
oracle query, so the original salted keys, adaptive repeated query, query counts and error
charges are unchanged. The suffix verifier at each fixed selector is used to instantiate the
generic soundness theorem. Verdict equations and the party-run correspondence identify its
output with the full verifier's output; the game is not a manually predicted verdict. The
generic restoration protocol is a fixed list of oracle-message and challenge pairs, so the tests
cover each fixed selector; the replay also runs the authored selector in the full verifier
protocol.

`plainScriptedRun_eq` and `replayResult_eq` return the value seven on every Boolean challenge, in
both exact statement carriers. `selectedScriptedRun_eq` and `oracleReplayResult_eq` separately
retain rejection on a false challenge. The one-round `selectedGame_eval_run` and two-round
`PublicSelection.game_eval_run` connect restored games to actual `OracleVerifier.run` executions.
The one-round `selected_fresh` checks the complete interaction's uniform challenge marginal,
independently of input, authored selector and oracle message.

### Branch-specific interfaces

The [disposition record](../interaction-layer/state-restoration-disposition.md) gives exact frozen
and target declarations, endpoint correspondences and the P1/P2 classification for each port.
This branch adds the following restoration interfaces on the parent's state functions:

| Interface | Restoration-specific contract |
| --- | --- |
| `verificationGame`, `closedVerificationGame` | Complete the adaptive selection, then return the transcript and its path-indexed passive verdict. |
| `complete_support_matches`, `run_scriptedProver_of_mem_support` | Every supported open completion carries the selected messages and replays through the actual interpreted party runner. |
| Uniform, private-coin and nonuniform knowledge bounds | Read the supplied adversary witness at the completed transcript. The uniform theorems give `(Q + rounds.length) * error`; the per-round theorems give `Q * max + sum` for a fixed adversary program. Both have `_privateCoins` forms that average over coins whose sampler may fail, with the same query bound `Q` for every fixed coin. |
| `MeasuredKnowledgeStateFunction.extractionProgram` | Runs a budgeted program realizing `readOut` before the stage programs. `stateRestoration_oracle_knowledge_soundness_nonuniform_withReadOut` states the failure event on this composite program and charges both; the plain measured theorem charges only the stages, after `readOut`. |
| `programAlong_budget_le_protocol`, `programAlong_budget_le_protocol_zero` | Count message/challenge stages per round, with explicit root/leaf terms and the frozen zero-endpoint specialization. |
| Authored-selector fixtures | A public prover Boolean selects exact `Fin 8`/`Fin 9` statement carriers; challenges still control acceptance and knowledge transitions. |

Unmeasured restoration retains independent input, intermediate and output witness universes.
Probabilistic game outputs remain small; deterministic verdicts accept general move universes.
The record explains these constraints and the change from the frozen layer's arbitrary final
results to optional passive decisions and explicit output-law implications.

### Shared extraction laws and carrier constraints

This branch adds root-failure localization and child restriction laws beside the parent's
extraction definitions in `Security/KnowledgeComposition/Extraction.lean`. The keyed conclusion
`BadChallengeOnCompletion F stmt messages table w key` retains the witness extracted from the
actual suffix and supplied output witness. Only `BadChallengeOnCompletion.mem_badChallenge`
forgets that witness for the probability bound. The [parent inventory](../interaction-layer/knowledge-composition-disposition.md)
describes the shared certificate signatures; the [restoration record](../interaction-layer/state-restoration-disposition.md)
identifies this branch's consumers and source assertions.

The remaining small carriers followed these exact declarations at the previous VCVio pin
`f8d7f8ef52b9afaf4e6d897804b9dce347cdb1db`. At the current pin `f1a4a8ec`, `SampleableType` is
unchanged, `ProbComp` is universe-polymorphic, and the measured programs moved to PolyFun with
independent universes. ArkLib has not yet generalized the code behind the second and third items,
so their restrictions remain:

- `SampleableType (β : Type)` in
  `VCVio/OracleComp/Constructions/SampleableType/Basic.lean:51` forces
  `Round.sampleChallenge` to sample small challenges. `protocol` uses `OraclePoly.{0}`,
  whose messages and challenges share the move universe. Round-specific pure keyed laws
  therefore remain on this small protocol; the shared extraction laws are general.
- `ProbComp : Type → Type` in `VCVio/OracleComp/ProbComp/Basic.lean:31` keeps random
  outputs small in the restoration games and bounds. It does not restrict `readOut`
  or the certificate's input, intermediate or output witness universes.
- `KnowledgeStateFunction.MeasuredStages` (`Interaction/Security/MeasuredExtraction.lean:104`)
  fixes root results, step inputs/results, leaf inputs and the cost carrier `ω` to `Type`. At the
  previous pin, VCVio's `OracleComp.BudgetedProgram {Input Result : Type}` forced this. It now
  applies PolyFun's `PFunctor.FreeM.BudgetedProgram`
  (`PolyFun/PFunctor/Free/Cost/Measured.lean:194`), which takes its input, result and cost
  carrier in independent universes. The restoration budget theorems and the packaged measured game theorem
  retain small input, intermediate and output witnesses.

The measured restoration test (`ArkLibTest/Interaction/Security/StateRestorationBudget.lean`)
runs PolyFun's measured programs through VCVio's bridge. It keeps the finite count profile
`Kind → ℕ` and the named realization evidence
(`BudgetedProgram.realizes`, `run_programAlong`, `run_extractionProgram`).

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
probability bounds require small moves. `Security/RoundByRound.lean` defines the shared full-prefix
interface `PrefixDraw`, its oracle-program form `PrefixChallengePrograms`, `prefixSampleAt`,
and `prefixSampler` with its execution laws. Node-indexed draws embed through
`PrefixDraw.ofNodes`, which ignores history and agrees with `sampleAt`.

`Security/Implications.lean` bounds actual flip events at full prefixes. Its passive sampler
retains history-dependent challenge programs, and an exact equation identifies its execution
with the ordinary Core runner. Encoded event marginals transport prefix-indexed challenge models
into that bound. That bound takes an explicit final continuation and a premise linking positive
probability of the final event to the certificate's acceptance predicate. The plain and oracle
verifier implications give the corresponding bound for node-indexed draws and prove that link
from the final decision. A prefix draw reads the full prefix, oracle messages included, which a
passive oracle verifier reaches only through bundle queries in its final decision.
All forms allow missing probability mass in any lawful distribution monad. The oracle soundness
and acceptance predicates take an `OracleBundle` input, as `OracleVerifier.run` does.

`soundnessUsing` interprets the whole computation. Exact specialization laws retain the
classical initial state distribution and the existential ambient state of `validAcceptance` at the
end of the run.
The generic and classical implications share their run-to-decision and acceptance proof.
The path supremum is bounded by arbitrary finite rank-indexed sums, as well as the existing
all-node sum and uniform-error corollaries.

The [disposition record](../interaction-layer/soundness-implication-disposition.md) gives the
source-to-target inventory, the freshness argument, failure tests, and limits of the correspondence.
Inherited universe constraints remain in [entry 18](#18-run-outputs-are-tied-to-the-monad-universe).

## Sumcheck migration

### 22. Sumcheck domain multiplicity and routing laws


`Sumcheck.Soundness` now proves full-run soundness in the interaction layer for every map
`D : Fin d → R`, with indexed sums that retain repeated points. `Indexed` proves the local
false-to-true bound and constructs the round-by-round state function. It applies #1486's
`OracleVerifier.soundness_of_rbrSoundness_uniform` and counts one challenge per round to obtain
`n * (deg / |R|)` for the actual core run of every prover. `Soundness` derives arbitrary-list
and injective corollaries, plus committed and possibly failing randomized one-round bounds in
probability and measure form. These interaction layer security theorems do not use the legacy
embedding.

`Types`, `Tree` and `IndexedDomain` define the interaction layer statements, fixed protocol and
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
The generic `OracleModel.satisfies_guarantee` interface has no Core counterpart. The Sumcheck
rows that used it, `degreeModel` and `degreeGuarantee`, are retired: their only client,
`message_degree`, reads the bound from the message type.

`Interaction.Prover.simulate_joinSlot` belongs beside `Prover.simulate` in
`Interaction/Reduction.lean`. It now covers every protocol tree, lens, dependent prover
output family and lawful target monad, including trees that are a single leaf. The Sumcheck tests use this law.
`decodeTranscript_succ` is a simplification equation beside `decodeTranscript` in
`Sumcheck/Execution.lean`. The four local transparency attributes added by the Sumcheck
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

**Code.** `Sumcheck/Fold.lean` implements passive interaction-layer checks. `Interval`
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
`Projection` constructs the interaction-layer projected oracle map `projectedMap` and its derived
query handler, which reads the input `d ^ (n - 1 - i)` times at round `i`
(`projectedQuery_isChargeBound`).
`projectedExecute_closed` identifies returned behavior with that handler; `projectedExecute_related`
proves its evaluation claim. `Behavior` handles arbitrary original input behavior at the empty
interval and proves its final remaining-sum relation is evaluation. The polynomial soundness
theorems require polynomial input data and do not cover this arbitrary behavior.
`BehaviorComposition.run_append_behaviorIntervalVerifier` extends the public append equation to
arbitrary original evaluation behavior. `IntervalRoundSoundness` proves the actual one-round
probability and measure bounds at every variable position, including intermediate endpoints.
`Impl/IndexedProjection` computes indexed CompPoly projections, retaining repeated domain points.
`Impl/Projection` specializes it to injective domains, and `ComputableProjection` connects it to
the indexed projection of `IndexedDomain`.
`ComputableInterval` constructs the honest computational strategy and proves its interpretation,
actual execution equality and completeness. `ComputableSoundness` transfers the interaction-layer
suffix bound to every computational-message prover with shared ambient state. `Interpreted` and
`InterpretedExecution` provide generic message interfaces. For a fixed output type `Out`,
evaluation-preserving message interpretation preserves the ambient prover effects, each challenge
draw and the private value at the leaf. Legacy
`Spec` projections and honest prover comparisons are isolated in `LegacyProjection` and
`LegacyProtocol`; interaction-layer security does not depend on them.

The routing fixture uses `Nat`, with semiring-general polynomial export and routing laws.
Explicit deterministic handlers produce query order `[1, 3, 2, 4]`, accepted claim `(10, 10)` and
private output `hidden + 110`. A prefix rejection still runs both interactions under P1, then
skips the suffix decision. It therefore retains the full trace and output rather than the
frozen early-abort trace `[3]` and output `hidden + 50`. Suffix rejection also retains the full
trace. Interval tests cover nonzero starts, zero counts, repeated domains and rejection.

**Premises.** P1 moves all bundle queries to the final decision and makes the verifier passive: a
sampler draws its moves. P2 prevents challenges and oracle messages from selecting shape. The [exact
disposition table](../interaction-layer/sumcheck.md#migration-disposition) names these premises on
changed abort and shape rows. It records the full endpoint ranges and exact targets; a full-run
theorem does not replace an arbitrary interval theorem.

The merged parent supplies generic routing and soundness implications. Constructor, projection
and transport equations replace this branch's added transparency commands. Existing parent
transparency settings remain unchanged. Mathematical polynomial projections remain
noncomputable; the generic interface and deterministic execution use computable carriers.

## 24. Computable Sumcheck runtime

**Migration.** The migration list ports the frozen computable Sumcheck to the interaction core:
`execute_eq_native`, the frozen `ComputableCompleteness` and `ComputableSoundness`, and the seven
rows of `scripts/SumcheckRuntime.lean`. Rows 3, 4 and 6 are premise-required under P1/P2; row 7 now checks the verifier.

**Code.** `Sumcheck.Computable` instantiates the carrier-generic protocol and verifier of
the Sumcheck core (open question OQ17) at CompPoly messages and CompPoly multivariate inputs; see
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
    is `some (16, 4, 4, 16)` and its trace is empty. The prover-only outcome is an additional
    check.
  - Row 8 is new. It runs `Computable.intervalVerifier` for one round after the prefix `[7]` on
    the constant-one input. Target `4` gives `some (2, 7, 3, 1)` and target `3` gives rejection,
    both after the one draw `[c0]`. The executable emits eight checks: rows 2 to 8 and the
    prover-only outcome. Row 1 is a compile-time proof.

**Why.** The interaction core has one protocol per message carrier and a passive verifier, and
names challenges by node occurrences. The restated rows check the same values and effect order
under those rules.

## 25. Routing owners and transparency

**Code.** Forwarding subexpressions in the interaction layer and Sumcheck Core, including their
tests, use `OracleMap.fst`, `OracleMap.snd`, `OracleMap.reindex`, `Interaction.pathLift`
and VCVio's `QueryImpl.id'` restrictions (or `QueryImpl.ofLift` for universe-polymorphic sums).
Coverage includes prover-setup injection, carrier-changing `renameQueries`, routing exports and
path reads, the independent-query-universe verifier, and state-restoration oracle message reads
and selected output maps. A further search also delegates both projections in the routing test's
`closingMap` and the ambient injection in the budget test's `finishSelected`. Proof-local
handlers in `map_fst_runWithProverSetup`, `sentOracleMessageMap_query` and
`OracleVerifier.soundnessUsing_of_localSoundness` also delegate to the existing owners.
Theorem-statement handlers, direct input reads in decisions, legacy transcript queries and
primitive owner implementations retain their explicit query forms. Legacy index
elimination, equality transport, challenge-node transport, setup logging, path elimination,
export arithmetic and surrounding effects are preserved. `OracleMap.par` uses the bundle
projections. `oracleMessageBundle_split` routes an empty prefix through
`OracleMap.emptyLeft`. The ordinary runner and the queries-by-move runners forward ambient queries and
challenge requests through the identity handler, without substituting a sampler. Legacy
`decisionImpl` retains its substantive bundle query translation and delegates only the outer sum
routing to identity restrictions.

**Parent fixes retained.** `Interpreted.headQuery` and `tailLift` query the two sides of the
message bundle's sum directly, as `OracleMap.fst` and `OracleMap.snd` do.
The parent's `Execution.verifier_outputMap` only stated equality to `fst`; this cleanup fixes
`verifierOn.outputMap` through `fst`, including its specialization `verifier`.
`roundRoute` already specializes `roundRouteOn`; the latter now delegates to `headQuery`.
The Sumcheck `Routing` test already uses identity restrictions and projection handlers throughout
its export map. `OracleVerifier.runWithLog` and `runWithAmbientLog` use the same identity
restrictions as the queries-by-move runners. They log directly through `executeWith`.
`Oracle/QueriesByMoveLaws` proves agreement after erasing the move boundaries.

**Transparency.** The Core layers and their tests carry no local transparency overrides.
Imported replication and transcript path definitions retain their definition-site transparency;
proofs use explicit reduction and their equations where needed. The existing definition-site
annotations on `PlainPoly`, `plainSig`, `OraclePoly`, `oracleSig`, `viewSig`,
`OracleMessageIndex`, `OracleMessage`, `oracleMessageBundle`,
`PartialTranscriptAt` and Sumcheck `round` keep `implicit_reducible`.
`perfectCompleteness_uniform` names the existing `challengeSampleable R deg n` instance
explicitly when constructing `challengeQueryImpl`. `OracleMap.fst` is `macro_inline` so the
carrier-generic verifier can project its inputs without computing the mathematical input
family's interpreter. No attribute command changes another declaration's transparency.

**Disposition.** No ledger row changes status. P1 still permits challenge distributions that
depend on earlier public moves and confines bundle queries to the final decision. P2 still
prevents challenges and oracle messages from selecting shape. No statement or premise changes.
