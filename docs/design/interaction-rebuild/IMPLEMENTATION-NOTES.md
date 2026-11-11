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

The knowledge-composition migration adds `Security/KnowledgeComposition.lean` and
`Security/MeasuredResources.lean`. These are its choices.

### Root, step and leaf stages are charged

`MeasuredStages` names a budgeted VCVio program (`OracleComp.BudgetedProgram`) for the root map,
for the step map at every interaction node and for the leaf map, each indexed by the statement and
the full prefix. `BudgetAtMost` bounds the three kinds separately. `programAlong` composes the
programs with VCVio's `BudgetedProgram.comp` and `contramap`, so its budget is the leaf budget,
plus one step budget for each move of the transcript, plus the root budget. Under stage bounds,
`programAlong_budget_le` gives `leafBound + length • stepBound + rootBound`. The frozen interaction-layer
`length • b` bound is `programAlong_budget_le_nsmul`, the case with zero root and leaf bounds.
ArkLib adds no second instruction-cost theory.

### Bounds by cursor length

`programFrom_budget_le` proves the bound by induction along the cursor, with the length of
`completeSpine l tr`. The pinned PolyFun has node-dependent charges (`Path.chargeDec`, with
`Path.chargeDec_le_length_nsmul`) and a full-move path conversion (`PathAlong.toMapLensPath`), so
payload-dependent charges can be expressed there. Neither directly replaces this proof. The proof
indexes stage programs by full prefixes, so using PolyFun's charges would need a decoration built
from the statement and history, an identity between stage budgets and charges, a length bridge, and
separate root and leaf accounting. The short induction stays. Later work that needs nonuniform
path sums should reuse PolyFun's charge calculus.

### Acceptance and the middle claim

`KnowledgeStateFunction.append` takes a seam hypothesis: the suffix root state implies the
prefix valid output on the witness extracted by the suffix root map. The lower-level
`rbrKnowledgeSoundness_append` keeps this predicate interface.

`Verifier.validAcceptance_append` and `OracleVerifier.validAcceptance_append` now decompose a
positive composite acceptance into supported accepted prefix and suffix results. They retain the
same intermediate ambient state. The oracle theorem also retains the actual routed suffix data.
The underlying `Verifier.support_append` and `OracleVerifier.support_append` in `Core/Composition`
work in any lawful monad with lawful support, without probability or inhabited-carrier premises.
They use the owning module's `simulateQ_append_run` equations. `splitFiber_pair` exposes the
transport used when splitting views, and `Verifier.append_decide_pathAlong` identifies the plain
component transcripts. No new transparency attributes are used.

`Verifier.rbrKnowledgeSoundness_append` uses each verifier's standalone knowledge theorem. Its
`accepted` law identifies every supported accepted prefix result with `mid stmt tr₁`. This law
does not assert that the middle claim is true, that it has a witness, or that the prefix accepts.
It matches the frozen composition's named path-dependent closed middle claim. The prefix may use
ambient effects. `Verifier.rbrKnowledgeSoundness_append_of_pure` derives this law when the prefix
decision returns the middle claim directly.

The proof conditions the suffix states on possible prefix acceptance. Suffix admissibility is
required wherever the input promise holds, including paths whose middle relation is false.
`KnowledgeStateFunction.condition` preserves the local error bound because the condition is
constant over the suffix transcript. Thus the suffix premise has its own output relation, not
the composite verifier's valid-output predicate.

No theorem equates two independently existential acceptance predicates with composite acceptance.
A prefix that leaves state 0 and a suffix that accepts only from state 1 illustrate why such an
equivalence would be false.

### Statement-indexed witnesses

All carriers now retain the input statement:

- `Win : Type` becomes `Win : S → Type`, and `relIn : S → Win → Prop` becomes
  `relIn : (stmt : S) → Win stmt → Prop`.
- `W : PathAlong l s → Type` becomes `W : S → PathAlong l s → Type`. Valid-output predicates
  and verifier output relations take witnesses in `W stmt tr`.
- `Witness sp history` becomes `Witness stmt sp history`. `toFun`, `extractStep` and `extractLeaf`
  take the statement first. `extractRoot stmt` returns `Win stmt`.
- Composition uses `Wmid : S → PathAlong l s₁ → Type`; the suffix at `tr₁` takes input witnesses
  in `fun stmt => Wmid stmt tr₁`.
- `extractFrom`, `extractAlong`, `terminalWitness` and the measured stages preserve these indices.
  `StageInput` also takes the statement first. `MeasuredKnowledgeStateFunction` uses the same
  dependent families.
- `comap` pulls back statements and accepts input/output witness maps between the dependent
  families. Its input relation is the image of the original relation under the input witness map.
  `rbrKnowledgeSoundness_append_of_mid` exposes those witness maps as well.

These signature changes propagate through `rbrKnowledgeSoundness`, the plain and oracle verifier
abbreviations, all append witness/state/extraction helpers and their equations, `BoundedAt` and
`LocallyBounded`, the legacy security transfers and their acceptance tests. The legacy transfers
specialize the families to constant legacy witness types. There is no second non-indexed API and
no encoding of a statement-dependent witness family.

`BadChallengeFrom` follows the rest of a transcript below any full prefix. At each receiver move it
compares the states on the witness extracted from the supplied output witness at that suffix.
`BadChallengeAlong` starts this predicate at the root. The theorem
`extraction_failure_implies_badChallengeAlong` proves that an admissible valid output with invalid
extracted input has such a receiver transition, for every permitted protocol tree. It never
replaces that extracted witness by an unrelated existential witness.

The acceptance tests retain their payload-dependent carriers and both challenge values. New
examples use `Win n := Fin (n + 1)` directly, execute measured extraction in that carrier, and
compose standalone verifier knowledge theorems with a statement-dependent suffix carrier.

### Signature changes specific to composition

Entry 18 and the universe ledger describe path-indexed outputs and independent universes.
This migration additionally retains the input statement in every witness carrier:

| Old | New |
| --- | --- |
| `Win : Type uW` | `Win : S → Type uW`, with `S : Type uS` |
| `W : PathAlong l s → Type` | `W : S → PathAlong l s → Type` |
| `Witness sp history : Type uK` | `Witness stmt sp history : Type uK` |
| `relIn : S → Win → Prop` | `relIn : (stmt : S) → Win stmt → Prop` |
| `relOut tr out w` | `relOut stmt tr out w` at the transcript's output type |
| `StageInput sp history` | `StageInput stmt sp history` |
| `comap f F hout` | `comap f F inputMap outputMap hout` between dependent families |
| `mid : S → PathAlong l s₁ → T` | `mid : (stmt : S) → (tr₁ : PathAlong l s₁) → T tr₁` |

The substitutions affect `KnowledgeStateFunction`, its extraction, child, append, guard,
condition, local-bound and pullback APIs; `rbrKnowledgeSoundness` and its two verifier wrappers;
and the generic composition theorems. Both lift operations preserve the statement index and move
only intermediate witnesses from `uK` to `max uK v`. The legacy transfers specialize to constant
witness families and retain their arbitrary certificate universe.

The new plain and oracle simulation/support laws retain their arbitrary lawful target monad.
Their output families now match the base's dependent append. `append_decide_pathAlong` uses
heterogeneous equality between the two equal-path fibers. Plain acceptance decomposition retains
both representatives with their heterogeneous equality; the standalone composition theorems'
`hout` transports that same output between equal-path fibers. For constant families this is the
previous equality-based statement. No carrier is encoded or replaced by a constant.

Measured extraction retains statement-indexed carriers. Its programs use the pinned VCVio
`BudgetedProgram`, whose input and result carriers are in `Type`; this is the same scope as the
frozen measured interface. The unmeasured extraction and composition interfaces have independent
statement, input-witness and intermediate-witness universes.

Relative to the pre-merge statement-indexed branch, every extraction, bad-challenge,
child/append, local-bound and relation-composition signature now admits `S : Type uS`,
`Win : S → Type uW` and intermediate witnesses in `Type uK`, instead of fixing all three to
`Type`. The suffix witness of `_of_mid` additionally has its own universe `uW₂`. The measured
stage APIs generalize the statement universe; their program carriers retain the pinned measured
framework's small universes.

The other changed signatures are:

| API | Before restacking | After restacking |
| --- | --- | --- |
| `Verifier.append_decide_pathAlong` | Equality at constant `T`, `U` | Heterogeneous equality at prefix family `T p₁` and suffix family `U p₁ p₂` |
| Plain/oracle `simulateQ_append_run`, `support_append` | Constant output statements and oracle families | The base's path-indexed output families, independent statement/index/query universes and the same arbitrary lawful target monad |
| Plain/oracle `validAcceptance_iff_support` | `impl event stmt tr`, constant output carrier | `impl stmt tr event`, with `event` at the transcript's output carrier |
| Plain `validAcceptance_append` | One output representative in a constant carrier | Suffix and composite output representatives, with `HEq`, preserving the same event |
| Oracle `validAcceptance_append` | Constant middle/final statements and oracle families; homogeneous `sumData` | Path-indexed middle/final statements and oracle families; paired `pathResources` data |
| Plain verifier `rbrKnowledgeSoundness_append`, `_of_pure` | Constant `T`, `U`, small input witnesses | Path-indexed `T`, `U`, independent input witness universes and an `HEq` premise transporting the final output relation |
| Legacy knowledge transfers | Constant legacy witness families, inferred small certificate | The same legacy relations with explicit arbitrary certificate universe `uK`, using the statement-indexed lift |

### Merge conflicts and their resolution

| Conflicted files | Resolution |
| --- | --- |
| `Core/Composition.lean`, `Core/OracleVerifier.lean` | Union of universe declarations; adapt this branch's owner laws to the base's dependent output families and `Resources`. |
| `Core/Security/RoundByRound.lean` | Keep the statement indices and the base's independent universes, dependent outputs, explicit certificate universe and lifts. |
| `Core/Legacy/Security.lean`, `Core/Legacy/OracleSecurity.lean` | Constant statement-indexed legacy witness families, with the base's arbitrary certificate universe and lift. |
| `ArkLibTest/Interaction/Core/Security.lean`, `ArkLibTest/Interaction/Core/Legacy/Security.lean` | Keep the indexed fixtures and base universe tests; type acceptance events at their paths and specify the concrete fixture certificate universe. |

### Ownership of the recursive maps

`Security/KnowledgeComposition/Extraction.lean` owns transcript cursors, backward extraction,
composition of certificates and the deterministic extraction-failure theorem. The public
`Security/KnowledgeComposition.lean` imports it and owns the relation-level and verifier-level
security composition theorems. The import used by clients remains the same.

`withRootWitness` retains every intermediate carrier, state, step map and leaf map, and names the
actual root witness as an internal input. This lets the cursor recursion use one intermediate
universe, even when the original input witness lies in another. The public composition reapplies
the original root extractor. `extractFromMaps` factors extraction through just its computational
fields, so extraction is definitionally independent of unused root obligations. The public input
carrier remains `Win stmt`; no input or output carrier is encoded into another carrier.

The new owner laws are `splitFiber_pair`, `Verifier.append_decide_pathAlong`, and plain/oracle
`simulateQ_append_run`, `support_append` and `validAcceptance_iff_support`.
`OracleVerifier.simulateQ_decideWith` closes resource queries before interpreting the ambient
queries at independent index and query universes. The generic failure event and theorem are
`BadChallengeFrom`, `BadChallengeAlong`, `state_or_badChallengeFrom` and
`extraction_failure_implies_badChallengeAlong`. The verifier-specific additions are
plain/oracle `validAcceptance_append`, `Verifier.rbrKnowledgeSoundness_append` and its
`_of_pure` corollary. `condition` and `BoundedAt.condition` supply the prefix-acceptance gate.

### Added acceptance cases

`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean` checks the generic failure
theorem on every payload and supplied terminal witness. `indexed_standalone` and
`indexed_composed` use `Fin (n + 1)` at input and output, and compose the suffix verifier's own
standalone theorem. An example with a shared counter checks the actual intermediate state one between two
accepted decisions, and `largeSeamHandler` checks the decision-fold law in an oracle computation with a higher-universe
empty query index. Its output universe is larger than its input universe, without an adapter.

`ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean` adds `indexedState` and executes
its measured program at statement three and witness two, returning two in `Fin 4`. The generic
empty-protocol case in `MeasuredPathBudgets.lean` now quantifies statement-indexed input and output
families. The existing charged-stage, unbounded-depth, signed-weight and empty-carrier tests stay.

The knowledge-composition acceptance module collects the axioms of the new failure and verifier
composition theorems alongside the existing composition equations.

The universe canary combines statements in `Type 2`, statement-indexed input witnesses in
`Type 2` and intermediate witnesses in `Type 1`, composes through a small finite seam carrier,
and lifts the certificate and its error bound to `Type 3`.

### Review dispositions

| Finding | Disposition and evidence |
| --- | --- |
| 2, interface | Statement-indexed input, intermediate and terminal witnesses throughout the single knowledge API. The child state-restoration port remains outside this branch. |
| 3, generic theorem | `BadChallengeAlong` and `extraction_failure_implies_badChallengeAlong` preserve the suffix-extracted witness on arbitrary trees. The keyed specialization belongs to the child branch. |
| 9 | Generic plain/oracle support and acceptance decompositions preserve the seam state; the plain verifier knowledge theorem uses standalone component hypotheses and has a pure-middle corollary. |
| 12 | Removed this branch's local transparency attribute. Constructor and transport equations are exposed in `Core/Composition`. |

### Validation

Both prescribed checks passed on 2026-11-11:

- `~/claude-work/restack-1110/check.sh feat/interaction-migrate-core build` exited zero.
- `DOC_BASE=feat/interaction-migrate-core ~/claude-work/restack-1110/check.sh
  feat/interaction-migrate-core guards` exited zero.

The build includes the compile-time acceptance examples, runtime evaluations and targeted axiom
checks. The guards cover added escape hatches, frozen paths, documentation, headers, imports,
line style and transparency overrides. No whole-library validation command was run.

### `combineDraw` combines errors

The composite error is `combineDraw (m := fun _ => ℝ≥0∞) l s₁ s₂ ε₁ ε₂`: the combinator that
combines the prefix and suffix draws, at a constant result family. Prefix challenge nodes keep the
prefix error, and suffix challenge nodes keep the error of the suffix at their prefix path. No
separate error traversal is added.

### Restoration dependency still required

The frozen restoration fixture's `Out` chooses `Fin 8` or `Fin 9` from the actual Boolean
challenge (`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean`, `Out`). The base's
`OracleVerifier` indexes outputs by `Path s`, while `OraclePoly.B (.challenge C) = PUnit` and
`oracleSig.toFunB` erases that challenge. For the same sent message, both Boolean challenges
therefore have definitionally equal shape paths. Every `T : Path s → Type` assigns them the
same output carrier. The view can change output values, but cannot change this fixed target type.
Public message branches are retained and do support dependent output types.

Restoring the exact challenge-dependent replay and game rows requires a verifier output family
indexed by a public transcript/view retaining challenges, together with its security interfaces.
This is a missing parent dependency. The child restoration branch has not been merged or
adapted here, and none of those rows is marked restored. No constant family, extra public message,
or encoding of `Fin 8`/`Fin 9` is substituted for the frozen statement.
