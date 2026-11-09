# Implementation notes for the interaction core

These notes record where `ArkLib/Interaction/Core/` departs from the design records in this
directory. The records themselves are unchanged. Each entry states what the record said, what the
code does and why. Entries 1–8 were identified by the review of the first implementation; entries
9–12 were introduced while addressing that review, and entry 13 by core additions that the oracle
migration needs. The section after them records later core changes that keep to the records; they
are not departures. The section after that records the choices of migration commit D3, which adds
knowledge composition and measured extraction to the core. The last entry, 18, was introduced by
the state-restoration port.

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
Entry 18, at the end of this page, records the departures of the state-restoration port. The
number 17 belonged to a removed legacy-embedding entry and is not reused.

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

## Migration commit D3: knowledge composition and measured extraction

Migration commit D3 (not record D3) adds `Security/KnowledgeComposition.lean` and
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

### The seam is a predicate

`KnowledgeStateFunction.append` takes the seam as a hypothesis: the suffix root state implies the
prefix valid output on the witness that the suffix root map extracts. `rbrKnowledgeSoundness_append`
takes it between the suffix input relation and the prefix valid output, under the input promise.
The suffix premise uses the composite valid output restricted along `PathAlong.append`. These
theorems do not derive the security of `V₁.append V₂` from the standalone security statements of
the two verifiers. The test fixture proves an acceptance iff for its own verifiers instead.

A reusable acceptance bridge for appended verifiers is not in this commit; it is a recorded
follow-up. It would start from `Verifier.append_decide` and `OracleVerifier.append_decideWith`,
keep the ambient state through the decision bind, and use output compatibility on supported
accepted prefix results. Its first theorem should be one-way: composite positive acceptance
decomposes into a supported intermediate result and state, and positive suffix acceptance from that
state. It must not be an iff between two separately existential `validAcceptance` predicates,
because their ambient states can be incompatible. For example, a prefix that accepts only from
state 0 and leaves state 0, followed by a suffix that accepts only from state 1, satisfies both
standalone predicates, but the composition rejects. A deterministic-mid corollary needs the
accepted-prefix-result law as a hypothesis. The fixed-protocol state-restoration proofs do not
need the bridge; they use one state function, its local bound, its terminal obligation and its
extractor.

### Dependent witnesses

Output witnesses are transcript families (see "Output witnesses are indexed by the transcript"
above), and composition keeps them typed. The intermediate witness type is
`Wmid : PathAlong l s₁ → Type`. The suffix state function at `tr₁` takes input witnesses in
`Wmid tr₁`, and its output family is `fun tr₂ => W (PathAlong.append l s₁ s₂ tr₁ tr₂)`.

- `extractFrom` takes its output witness at `PrefixMoves.completeWith l sp history tr`, the
  completed transcript through the cursor's prefix followed by the rest of the transcript. It is
  defined by recursion on the rest, so the leaf and step equations of `extractFrom` hold by
  definition.
- `extractAlong` and `terminalWitness` take `W tr`. They transport it by `cast` along
  `PrefixMoves.completeWith_root` and `complete_completeMoves`; the transport reduces by definition
  when the transcript is given by its moves.
- `extractFrom_child` and `extractFrom_append_down` state the extraction below a first move for a
  witness given with a transport to each side.
- `MeasuredStages.leaf` takes `W (PrefixMoves.complete l sp history)`. `programAlong` precomposes
  the same transport, so its input is `W tr`.

There is one theory. A constant output witness type is the constant family `fun _ => W`. The
tests run the composed extraction on the carriers `Fin (payload + 1)` and
`Fin (payload + 1) × Unit` with identity leaf maps. They check that the composite terminal witness
is the output witness itself, and they run the composed measured program on
`witness : Fin (message.val + 1)`.

### `combineDraw` combines errors

The composite error is `combineDraw (m := fun _ => ℝ≥0∞) l s₁ s₂ ε₁ ε₂`: the combinator that
combines the prefix and suffix draws, at a constant result family. Prefix challenge nodes keep the
prefix error, and suffix challenge nodes keep the error of the suffix at their prefix path. No
separate error traversal is added.

## 18. State restoration fixes the output type and the decision ambient

The legacy layer's state-restoration games let the output statement type depend on the transcript
branch, so a claim on a rejecting branch was impossible by typing. In the interaction layer the
verifier has one statement type `T` (records D4 and D6), so `terminalObservation` and
`closedTerminalObservation` in `Core/Security/StateRestoration.lean` return `Option T` and
`Option (T × ∀ j, B j)`: a rejecting branch is the value `none`, and its tests check that value
instead of relying on the type. The ported games also fix the decision's ambient oracle to
`[]ₒ`; a state-restoration game whose decision shares an oracle with the adversary is a later
milestone (record D9 §6).

Knowledge soundness is stated with record D7's knowledge state function instead of the legacy
layer's per-input round extractors. `stateRestoration_knowledge_soundness`,
`stateRestoration_oracle_knowledge_soundness`, their `_privateCoins` forms and the `_nonuniform`
forms in `StateRestorationBudget.lean` take one `KnowledgeStateFunction` whose admissibility
predicate replaces the legacy set of admissible inputs, require it to be `LocallyBounded` at the
uniform draw, and extract with `extractAlong` on the selected transcript. The output law is an
implication from an accepted observation and the output relation to the state function's valid
output, and the output relation may read the transcript; the legacy law is an equivalence between
the terminal state and the output relation on the branch path. The theorems assume decidable
equality of the key type, which the legacy forms derive from decidable equality of inputs and
salts.

The proof bounds the restored execution with VCVio's bad-query bounds for the random oracle.
`exists_badChallenge_of_extraction_failure` shows that a valid output whose extraction fails
passes a bad challenge at one completion key of the selected transcript. It is stated for the
round protocol in `StateRestoration.lean`; its general form for every protocol belongs in
`KnowledgeComposition.lean`. The game replays the selected transcript through
`restoredExecution`, so the legacy scripted prover and its replay theorem have no counterpart.

Measured extraction uses `MeasuredStages` and `programAlong` from `MeasuredResources.lean`, whose
stages include a root and a leaf map. `ProtocolBudgetAtMost` in `StateRestorationBudget.lean`
bounds the root and leaf budgets and the message and challenge step budgets of one statement, and
`programAlong_budget_le_protocol` bounds the composed budget along every transcript by
`leafBound + rounds.length • (messageBound + challengeBound) + rootBound`. The legacy bound has no
root or leaf terms, and its paired form is the instance of `programAlong_costAtMost_protocol` at
`BudgetAtMost.protocolBudgetAtMost`. The composed program already ends with the leaf map, so
`run_programAlong` replaces the legacy terminal-witness bridge.
