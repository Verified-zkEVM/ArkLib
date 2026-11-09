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

Entries 14 onwards record the departures of the legacy embedding. They are in
[`legacy-embedding.md`](../interaction-layer/legacy-embedding.md#departures), and
[`departures.md`](../interaction-layer/departures.md) indexes every entry, including 1–13.

## Changes that keep to the records

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

## Migration commit D6

`Security/Implications.lean` proves that round-by-round soundness implies soundness, for plain
and oracle verifiers. `Verifier.soundness_of_rbrSoundness` takes `V.rbrSoundness impl input output
draw ε`, with an error `ε : ChallengeNode plainSig s → ℝ≥0∞` on challenge nodes, to
`V.soundness` with the challenge implementation `draw`, for every initial state distribution
`init`. The error is the supremum, over shape paths, of the sum of `ε` over the challenge nodes
the path meets (`challengeNodesOn`). `OracleVerifier.soundness_of_rbrSoundness` does the same
from `OracleVerifier.rbrSoundness` to `OracleVerifier.soundness`, the model soundness of
`OracleVerifier.classicalModel` with the verdict and output oracle data of the observation. Its
acceptance is the actual oracle run: the decision answers resource queries from the input data and
the run's payloads, and reads its output through the verifier's output oracle map, as in
`OracleVerifier.validAcceptance`. Neither theorem has an acceptance-link hypothesis. The `_tsum`
corollaries bound the error by `∑' c, ε c`. The `_uniform` corollaries give `k • e` when every node
error is at most `e` and every path meets at most `k` challenge nodes. One induction over the
protocol tree, for any signature lens, serves both verifier forms. The proofs go through neither
the legacy layer nor the frozen interaction layer.

### 19. Round-by-round soundness implies soundness in the classical model

The frozen interaction layer proves `executeStrategies_soundness` and
`executeStrategies_soundness_uniform` in `ArkLib/Interaction/Oracle/Security/Soundness.lean`, with
the helpers `OrdinaryState.exists_verifier_escape` and `LocalSoundness.random_prefix`. The
interaction-core forms cover the same plain and oracle trees and differ in four ways.

- **Execution model.** The frozen theorems hold for any lawful monad `m` with a handler, a
  `MonadAttach` instance and a `FreshVerifier` hypothesis, and allow failure through `OptionT`.
  The interaction-core theorems are stated for `Verifier.soundness` and
  `OracleVerifier.soundness`, which use the classical model: ambient queries run in
  `StateT σ ProbComp` from a state drawn by `init`, and each challenge is a fresh draw from
  `draw`. Freshness therefore holds by construction and is not a hypothesis.
- **Node-indexed error.** The frozen error is indexed by a rank function, checked against a
  `ChallengeSchedule` with a count, and summed as `∑ j ∈ Finset.range count, error j`. The
  interaction-core error is indexed by challenge nodes, as in `rbrSoundness`, and the bound is
  the supremum over paths of the node errors along the path. The uniform corollaries replace the
  schedule by the hypothesis that every path meets at most `k` challenge nodes, and
  `(count : ℝ≥0∞) * error` by `k • e`.
- **Escape statement.** `OrdinaryState.exists_verifier_escape` concludes
  `VerifierEscapeOnPath` from an `OrdinaryState` certificate. `StateFunction.escapeAlong`
  concludes `EscapeAlong` from a `StateFunction`, an admissible false statement and an accepted
  transcript. `EscapeAlong` says that some receiver node on the transcript turns the state from
  false to true.
- **Averaged-prefix selection.** `LocalSoundness.random_prefix` takes an `OptionT ProbComp`
  author, a map from its output to a verifier prefix, and the hypothesis that every selected
  prefix has the same rank. `flip_random_prefix_le` takes an `OptionT ProbComp` author and a map
  from its output to a `ReceiverPrefix`, which packages a receiver node's cursor, its ownership
  proof and the full moves before it. The common-rank hypothesis becomes the hypothesis that every
  selected node has error at most `e`. The selected node may vary with the author's output, and
  author failure contributes no mass. `flip_random_history_le` is the fixed-node case with a
  `ProbComp` author, which the soundness induction uses.

The tests in `ArkLibTest/Interaction/Core/Security/Implications.lean` restate the general
statements for plain and oracle verifiers, apply `flip_random_prefix_le` to an author that chooses
between two different challenge nodes, give soundness `1 / 2` for the one-challenge coin protocol
from every initial counter distribution, and give soundness `2 • (1 / 4)` for a protocol with two
uniform `Fin 4` challenges through the uniform corollary.
