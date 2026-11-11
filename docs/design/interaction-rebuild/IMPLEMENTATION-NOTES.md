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

**Round-by-round knowledge** (`Security/RoundByRound.lean`). Input witnesses have family
`Win : S → Type`; output witnesses have family `W : S → PathAlong l s → Type`.
`validOutput` takes `(stmt : S) → (tr : PathAlong l s) → W stmt tr → Prop`, and
`extractLeaf stmt sp history` takes `W stmt (PrefixMoves.complete l sp history)`.
Intermediate carriers also take `stmt` first. The verifier forms take both witness families
implicitly; their output relations take the input statement, transcript, output claim and witness.
For an oracle verifier, the input statement includes its input oracle data, and the output claim
pairs the output statement with its output oracle data.

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

### Changed-signature inventory

The following substitutions describe the old and new signatures of every affected production
API. All other premises and conclusions remain unchanged unless stated here.

1. Input families: `Win : Type` and `relIn : S → Win → Prop` become
   `Win : S → Type` and `relIn : (stmt : S) → Win stmt → Prop`.
2. Output families: `W : PathAlong l s → Type` and `W tr` become
   `W : S → PathAlong l s → Type` and `W stmt tr`. Similarly, `Wmid tr₁` becomes
   `Wmid stmt tr₁`.
3. Intermediate carriers: `Witness sp history` becomes `Witness stmt sp history`.
   The old `toFun sp history stmt`, `extractStep sp history stmt` and
   `extractLeaf sp history stmt` become `toFun stmt sp history`, `extractStep stmt sp history`
   and `extractLeaf stmt sp history`. `extractRoot stmt` now returns `Win stmt`.
4. Verifier relations: `relOut tr out w` becomes `relOut stmt tr out w`, including the oracle
   form whose `stmt` includes input data and whose `out` includes output data.
5. Pullback: the old `comap f F hout` kept fixed input/output witness types. The new
   `comap f F inputMap outputMap hout` maps the dependent witness families explicitly, and
   returns the image input relation. `BoundedAt.comap` has the matching parameters.
6. Deterministic statement composition: `rbrKnowledgeSoundness_append_of_mid` now takes
   `Wmid₂ tr₁ t`, `W₂ tr₁ t tr₂`, `midWitness` and `outWitness`; the previous fixed-carrier
   theorem is the specialization to constant statement families and identity witness maps.
7. Stage inputs: `StageInput sp history` becomes `StageInput stmt sp history`.

In `Security/RoundByRound.lean`, substitutions 1–4 affect `KnowledgeStateFunction` and its
fields, `rbrKnowledgeSoundness`, `Verifier.rbrKnowledgeSoundness` and
`OracleVerifier.rbrKnowledgeSoundness`.

In `Security/KnowledgeComposition.lean`, substitutions 1–3 affect these declarations:

- `extractFrom`, `extractFrom_pure`, `extractFrom_liftBind`, `extractAlong`, `terminalWitness`;
- `badChallenge`, `BoundedAt`, `LocallyBounded`,
  `rbrKnowledgeSoundness_iff_exists_locallyBounded`, `child`;
- `appendWitness`, `appendToFun`, `appendExtractRoot`, `appendExtractStep`, `appendExtractLeaf`;
- `appendToFun_root`, `appendToFun_send`, `appendToFun_leaf`, `append`, `root_append`;
- `extractFrom_child`, `extractFrom_child_family`, `extractFrom_append_pure`,
  `extractFrom_append_down`, `extractFrom_append_down_family`, `extractAlong_append`,
  `toFun_terminalWitness_append`;
- `BoundedAt.child`, `BoundedAt.append`, `guard`, `BoundedAt.guard`, `LocallyBounded.append`;
- `rbrKnowledgeSoundness_append`, `rbrKnowledgeSoundness_append_of_mid`.

`comap` and `BoundedAt.comap` additionally use substitution 5, and
`rbrKnowledgeSoundness_append_of_mid` uses substitution 6.

In `Security/MeasuredResources.lean`, substitutions 1–3 and 7 affect `StageInput`, `stageMap`,
`extractFrom_eq_stageMap`, `MeasuredStages` (including its root/step/leaf fields),
`MeasuredStages.BudgetAtMost`, `zero`, `zero_budgetAtMost`, `programFrom`, `programAlong`,
`run_programAlong`, `programFrom_budget_pure`, `programFrom_budget_liftBind`,
`programAlong_budget`, `programFrom_budget_le`, `programAlong_budget_le`,
`programAlong_budget_le_nsmul`, `programAlong_costAtMost`, `programAlong_costAtMost_nsmul`,
and `MeasuredKnowledgeStateFunction`.

The legacy statements keep constant legacy carriers. Their type specializations change in
`Legacy/Security.lean`: `embedKnowledgeStateFunction`, `languageStateFunction`,
`embedVerifier_rbrKnowledgeSoundness`, `rbrKnowledgeSoundness_of_embedVerifier` and
`rbrKnowledgeSoundness_iff`. In `Legacy/OracleSecurity.lean`, the corresponding changes are
`embedOracleVerifier_rbrKnowledgeSoundness` and `rbrKnowledgeSoundness_of_embedOracleVerifier`.
Their mathematical statements are unchanged.

### New declarations

The following source locations identify the new production definitions and theorems. Unqualified
names below `Security/KnowledgeComposition` belong to `KnowledgeStateFunction`; unqualified
acceptance and support laws in the other files belong to `OracleVerifier`.

`ArkLib/Interaction/Core/Composition.lean`:

- Line 67: `splitFiber_pair`.
- Line 108: `Verifier.append_decide_pathAlong`.
- Line 130: `Verifier.simulateQ_append_run`.
- Line 150: `Verifier.support_append`.
- Line 439: `simulateQ_append_run`.
- Line 460: `support_append`.

`ArkLib/Interaction/Core/OracleVerifier.lean`:

- Line 382: `OracleVerifier.simulateQ_decideWith`.

`ArkLib/Interaction/Core/Security/RoundByRound.lean`:

- Line 178: `Verifier.validAcceptance_iff_support`.
- Line 237: `validAcceptance_iff_support`.

`ArkLib/Interaction/Core/Security/KnowledgeComposition.lean`:

- Line 156: `BadChallengeFrom`.
- Line 170: `BadChallengeAlong`.
- Line 176: `state_or_badChallengeFrom`.
- Line 196: `extraction_failure_implies_badChallengeAlong`.
- Line 931: `condition`.
- Line 948: `BoundedAt.condition`.
- Line 1106: `Verifier.validAcceptance_append`.
- Line 1131: `Verifier.rbrKnowledgeSoundness_append`.
- Line 1205: `Verifier.rbrKnowledgeSoundness_append_of_pure`.
- Line 1254: `OracleVerifier.validAcceptance_append`.

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

### New test declarations

`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean`:

- Line 537: `indexedProtocol`.
- Line 540: `indexedVerifier`.
- Line 544: `indexedDraw`.
- Line 548: `indexedCertificate`.
- Line 561: `indexed_standalone`.
- Line 568: `indexed_composed`.
- Line 585: `seamSpec`.
- Line 588: `seamHandler`.
- Line 594: `seamFirst`.
- Line 600: `seamSecond`.
- Line 628: `largeSpec`.
- Line 631: `largeSeamHandler`.

`ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean`:

- Line 109: `indexedState`.

### Review dispositions

| Finding | Disposition and evidence |
| --- | --- |
| 2, interface | Statement-indexed input, intermediate and terminal witnesses throughout the single knowledge API. The child state-restoration port remains outside this branch. |
| 3, generic theorem | `BadChallengeAlong` and `extraction_failure_implies_badChallengeAlong` preserve the suffix-extracted witness on arbitrary trees. The keyed specialization belongs to the child branch. |
| 9 | Generic plain/oracle support and acceptance decompositions preserve the seam state; the plain verifier knowledge theorem uses standalone component hypotheses and has a pure-middle corollary. |
| 12 | Removed this branch's local transparency attribute. Constructor and transport equations are exposed in `Core/Composition`. |

### Validation

Both prescribed checks passed on 2026-11-10:

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

## 18. State restoration fixes the output type and the decision ambient

The source of this port is the frozen interaction layer's state-restoration games
(`ArkLib/Interaction/Oracle/Security/StateRestoration*.lean`) and their tests. Those games let the
output statement type depend on the transcript branch, so a claim on a rejecting branch was
impossible by typing. In the interaction core the verifier has one statement type `T` (records D4
and D6), so `terminalObservation` and `closedTerminalObservation` in
`Core/Security/StateRestoration.lean` return `Option T` and `Option (T × ∀ j, B j)`: a rejecting
branch is the value `none`, and its tests check that value instead of relying on the type. The
ported games also fix the decision's ambient oracle to `[]ₒ`; a state-restoration game whose
decision shares an oracle with the adversary is a later milestone (record D9 §6).

Knowledge soundness is stated with record D7's knowledge state function instead of the frozen
layer's per-input round extractors. `stateRestoration_knowledge_soundness`,
`stateRestoration_oracle_knowledge_soundness`, their `_privateCoins` forms and the `_nonuniform`
forms in `StateRestorationBudget.lean` take one `KnowledgeStateFunction` whose admissibility
predicate replaces the frozen layer's set of admissible inputs, require it to be `LocallyBounded`
at the uniform draw, and extract with `extractAlong` on the selected transcript. The state
function's output witnesses are a transcript family `Wout`. The adversary outputs a witness of one
type `W` before completion fixes the challenges, as in the frozen game, and the map
`readOut : stmt → (tr : PathAlong _ _) → W → Wout tr` reads it at the completed transcript. It has
the role of the frozen layer's `terminalWitness`, which is an equivalence; a map suffices, and the
identity is the case `Wout = fun _ => W`. The output law is an implication from an accepted
observation and the output relation to the state function's valid output at the read witness, and
the output relation may read the transcript; the frozen law is an equivalence between the terminal
state and the output relation on the branch path. The theorems assume decidable equality of the
key type, which the frozen forms derive from decidable equality of inputs and salts.

The proof bounds the restored execution with VCVio's bad-query bounds for the random oracle.
`exists_badChallenge_of_extraction_failure` shows that a valid output whose extraction fails
passes a bad challenge at one completion key of the selected transcript. The output witness is
typed at the completed transcript. The statement reads the completion keys, their cursors and
prefixes (`keySpine`, `keyHistory`) and the answer table, so it stays in `StateRestoration.lean`. A
general form for every protocol, without keys, would belong in `KnowledgeComposition.lean`; it is
not in this commit.

The game evaluates the verifier's observation on the transcript that `restoredExecution`
completes; it runs no parties. The replay theorem of the frozen layer has a counterpart that runs
them. `scriptedProver` sends the selected messages, `recordedAnswers` answers every challenge query
from a recorded transcript, and `run_scriptedProver` shows that `OracleVerifier.run` with these
parties returns that transcript and its closed observation whenever the transcript carries the
selected messages. `closedVerificationGame_eval_run` instantiates it at the transcript completed
against an answer table, so the run returns the game's transcript and observation;
`verificationGame_eval_run` is the plain form. In the test, `scriptedRun_eq` runs the fixture on
every challenge, `nativeResult_eq` states the sent message, the challenge and the terminal result,
and two evaluations run the parties on `true` and on `false`. The completion check `game_eval`
remains beside them.

Measured extraction uses `MeasuredStages` and `programAlong` from `MeasuredResources.lean`, whose
stages include a root and a leaf map. `ProtocolBudgetAtMost` in `MeasuredResources.lean` bounds the
root and leaf budgets and the message and challenge step budgets of one statement on an oracle
protocol, and `programAlong_budget_le_protocol` in `StateRestorationBudget.lean` bounds the
composed budget along every transcript by
`leafBound + rounds.length • (messageBound + challengeBound) + rootBound`. The frozen bound has no
root or leaf terms, and its paired form is the instance of `programAlong_costAtMost_protocol` at
`BudgetAtMost.protocolBudgetAtMost`. The composed program applies the leaf map first, then the
step maps backwards along the transcript, then the root map. It takes the output witness `Wout tr`
at the transcript, so `run_programAlong` replaces the frozen layer's terminal-witness bridge.

The ported test fixtures use the constant family `fun _ => Nat` with the identity `readOut`,
because the frozen fixtures have a constant witness type. The fixture `knowledgeFin` in
`ArkLibTest/Interaction/Core/Security/StateRestoration.lean` has the output witness family
`Fin (m + 1)` for the sent message `m`, and runs the bad-key lemma and the plain game bound on it.
