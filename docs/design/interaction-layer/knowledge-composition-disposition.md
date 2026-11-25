# Knowledge composition and measured extraction: source-to-port inventory

This record compares the assertions ported by `feat/interaction-migrate-core-3` (#1482) with their
frozen sources. Stable IDs in test comments resolve to the rows below. Source line numbers refer
to unchanged frozen files; target line numbers identify declarations or acceptance commands in Core.

The approved premises are:

- **P1 (passivity):** verifiers draw challenges and make all bundle queries in the final
  decision. An oracle verifier's challenge draw reads only the verifier view of the prefix
  (`viewSig`): earlier public prover messages, earlier challenges and a marker for each oracle
  message. It cannot read an input or the contents of a sent oracle message. Earlier public
  challenges and prover messages may select later challenge distributions. Errors, state
  functions, witness carriers and backward maps keep the full prefix. P1 does not require fresh
  uniform challenges; the public-coin specialization adds that separate premise.
- **P2 (shape):** challenges and oracle messages never select shape. A public prover message may
  select a subtree and its output family.

Each row has exactly one status:

- **equivalent:** the target preserves the observation or law, with the representation changes
  described below. This includes statement indices and independent witness universes.
- **premise-required:** P1 or P2 requires the stated change to the frozen assertion's domain or
  execution boundary. The row names the premise.
- **retired:** the row names a removed mechanism. Retiring an adapter does not retire its
  mathematical observations; those have separate rows.
- **unresolved:** the row names the exact missing parent interface and declaration. No such gap
  prevents this branch's pure move, output or seam universe port.

## Scope and correspondence

The tables include the production laws used by this branch's extraction, certificate composition
and measured port, proof-bearing fixture definitions, anonymous examples, executable assertions,
negative elaboration tests and audits. They do not claim the whole frozen layer is migrated.
`Knowledge.lean`'s arbitrary multi-prefix convenience APIs, `RoundByRound.lean`'s ordinary global
escape/rank framework and the child restoration games are outside this branch's claim.
The exhaustive-search section of `ArkLibTest/OracleReduction/MeasuredExtraction.lean:25–61` still
tests the separate OracleReduction API in its original file. This branch ports that file's
interaction extractor and fixed-count assertions, not that independent legacy API. No Core test
imports a frozen interaction source.

A Core certificate separates root, step and leaf backward maps. An explicit seam law relates the
suffix root extraction to the prefix output relation. The maps and predicates retain the statement,
full prefix, oracle messages included, and the supplied output witness. Pure maps allow independent
statement, input, intermediate, seam and output universes. `PartialTranscriptAt`, the certificate, lifting, extraction,
extraction failure, append and pure restriction laws are polymorphic in the move universe `u`,
with `P : PFunctor.{uA, u}`, a lens to `rolePoly.{u}` and leaves `PUnit.{u + 1}`. Positions have
their own universe `uA`; branches and leaves share the move universe as in the structural parents.
The ordinary-import canary uses `Type` itself as a `Type 1` seam and output carrier, without
encoding either into a small type. It also sends the frozen `ULift.{1} Nat` oracle message and
retains its dependent witness carrier (KC-318 and KC-322).

The generic **plain standalone verifier** theorem is `Verifier.rbrKnowledgeSoundness_append`
(and `_of_pure`). Its hypotheses are the components' own standalone verifier knowledge theorems
and an identified middle claim. The added `indexed_composed` client checks that interface on two
empty protocols. [`challenge_composed`][r257] checks it with a uniform challenge that selects the
middle claim and the suffix witness carrier `Fin (n + 1)`. For oracle verifiers this branch ships
an acceptance decomposition, not a standalone composition theorem:
`OracleVerifier.validAcceptance_append` splits actual acceptance using the routed bundle and the
shared boundary state. It takes the general `OracleBundle` input with an independent data
universe. The **oracle fixture** then composes relation-level certificates with
`rbrKnowledgeSoundness_append` (and `_of_mid`), using its separately proved
`composed_validAcceptance_iff` to identify the appended verifier's output relation.
[`composed_rbrKnowledgeSoundness_view`][r258] does the same with view draws through
`rbrKnowledgeSoundness_append_view`. The oracle fixture is not evidence for a generic standalone
oracle verifier composition theorem.

Structural equivalences use the approved Core protocol domain. P2's domain change is recorded on
the extractor and selector rows; equivalent extraction equations do not restore challenge-selected
shape. P1 removes effectful verifier interaction phases, while preserving final bundle access
and the actual shared ambient state between decisions. A retired leaf adapter is distinct from
its execution equations, which are listed separately.

## Full-prefix challenge schedules

`Security/RoundByRound.lean` supplies the shared `PrefixDraw`, `PrefixChallengePrograms`,
`prefixSampleAt` and `prefixSampler` interfaces. `BoundedAt`, `LocallyBounded`,
`rbrKnowledgeSoundness` and the plain verifier wrapper draw at `sp`, its receiver proof and its
full `history`; the local error uses those same indices. Every compatible history is quantified,
including histories of probability zero.

The oracle wrapper [`OracleVerifier.rbrKnowledgeSoundness`][r253] takes a draw on the verifier
view, `PrefixDraw viewSig ProbComp s`. [`PrefixDraw.ofView`][r249] applies that draw to the
prefix after `PartialTranscriptAt.mapMoves` erases oracle messages with `eraseOracle`, so the
draw cannot read them by construction. The local error, the state function, the witness carriers
and the backward maps keep the full `oracleSig` prefix. Node-indexed draws ignore history, so they
factor through the view: `rbrKnowledgeSoundnessOfNodes_iff` identifies the node-indexed oracle
wrapper with the view wrapper at `PrefixDraw.ofNodesView`. `PartialTranscriptAt.mapMoves` belongs
next to PolyFun's cursor and move-map operations and lives in `RoundByRound.lean` until then.

`combinePrefixDraw` combines both draws and errors. Before the seam it uses the first family's
error at the first prefix. After the seam it selects the second family using the entire first
transcript, then uses the second prefix and its history. Challenge values erased from shape still
select this family. `appendPrefixSampler_eq_combinePrefixDraw` identifies the appended counterpart
with this combined sampler. For oracle verifiers, [`combineViewPrefixDraw`][r250] instead selects
the suffix draw from the shape path and the first stage's view. `ofView_combineViewPrefixDraw`
identifies its full-prefix form with `combinePrefixDraw` applied to the view draws,
[`appendViewPrefixSampler_eq_combineViewPrefixDraw`][r252] proves the sampler law, and
[`rbrKnowledgeSoundness_append_view`][r251] composes knowledge soundness for view draws. The
generic `combinePrefixDraw` remains for other lenses and for errors, which keep the full first
transcript. The node-indexed predicates (`rbrKnowledgeSoundnessOfNodes` and the
certificate's `BoundedAtOfNodes` and `LocallyBoundedOfNodes`) ignore history through `ofNodes`.
The established node composition theorems are corollaries of the `_prefix` laws and the two
`combinePrefixDraw_ofNodes` / `combinePrefixError_ofNodes` equations.

P1 retires challenge selection that depends on oracle messages and effectful receiver interaction
actions. It does not retire dependence on earlier public challenges or prover messages. The
visibility restriction is separate from the fresh uniform draw premise of the public-coin
specialization: a view draw may still depend on earlier public challenges and prover messages.
The fixed two-challenge Boolean regression in
[`PrefixKnowledge.lean`](../../../ArkLibTest/Interaction/Security/PrefixKnowledge.lean)
samples the second bit as the complement of the first, uses unit witnesses and identity backward
maps, and proves zero error with false root/intermediate predicates and equality of the bits at the
leaf. It sends no prover message. A second assertion checks different suffix errors for first
transcripts with the same shape path. The view regressions in the same file send the oracle bit
`true` or `false` before a challenge. The two executions have equal verifier views, and
[`ofView_oracleBit_eq`][r254] shows that a view draw draws the challenge the same way after
either bit. In a two-stage composition, [`combineView_oracleBit_eq`][r255] shows the same for the
suffix draw chosen from the first-stage view. The full-prefix draws `leakyDraw` and
[`leakySuffixDraw`][r256] return the bit, so the restriction comes from the view type.

## Measured bounds and universes

For frozen measured extraction, install its named stage program at each Core step and use
`BudgetedProgram.ofFun` for the newly explicit identity root and leaf maps. Those programs have
budget zero. The generic bound is
`leafBound + (completeSpine l tr).length • stepBound + rootBound`.
With the explicit hypothesis `BudgetAtMost 0 bound 0`, `programAlong_budget_le_nsmul` and
`programAlong_costAtMost_nsmul` recover the frozen `path.length • bound` result: `completeSpine`
counts the same full moves. On an empty protocol the length is zero. The empty-protocol assertion
quantifies every state function and every stage family with zero root/leaf bounds; it does not
assume arbitrary root or leaf programs cost zero. The signed-weight example retains the generic
ordered monoid, without adding a nonnegativity premise. The endpoint test
[`endpoint_budget_le`][r259] charges one addition at the leaf (doubling) and one at the root
(increment) of the empty protocol. It checks the general bound with bounds one, zero and one, the
budget two, the cost bound, and that the leaf runs before the root: input three gives seven, not
eight.

`programAlong` composes the stages supplied for one state function and transcript. Measured
append is follow-up work: it needs a realization and a charge for its witness conversions. A
uniform game-extractor contract is also follow-up work: it needs a depth or size envelope.
`MeasuredStages.zero` gives every state function a measured certificate with zero declared cost.
The node-indexed reduction from ordinary round-by-round soundness of the input relation's
language yields such a certificate. It assumes a default input witness at each statement and
that valid output witnesses imply acceptance, and it uses classical choice for the root map. An
operation-count result therefore names the stage programs and their prices. Stage selection,
uncharged host computations and carrier conversions remain outside that cost.

Instruction budgets leave pure code, views, handlers, carrier identification and witness size
uncharged. Ordered-program and unbounded-depth assertions retain actual instrumented charges,
not just declared budgets. Zero-stage assertions deliberately show that the budget contract
alone gives no total running-time bound.

Pinned VCVio `OracleComp.BudgetedProgram` in
`VCVio/OracleComp/QueryTracking/MeasuredProgram.lean:156` fixes `Input` and `Result` to `Type`.
This forces small `Win stmt` at root results, small intermediate witnesses and `StageInput` at
step inputs/results, and small `W stmt tr` at leaf inputs. `MeasuredStages.programAlong` and
`MeasuredKnowledgeStateFunction` retain those restrictions. The underlying
`OracleComp.MeasuredProgram` at line 66 also fixes `ω`, `View` and `Op` to `Type`. The statement
universe remains independent, and the measured code takes `P : PFunctor.{uA, 0}`, so positions
have their own universe. These restrictions apply only to measured programs, not pure backward
maps. The VCVio pin is `f8d7f8ef52b9afaf4e6d897804b9dce347cdb1db`.

## ArkLib/Interaction/Oracle/Security/Knowledge.lean

| ID | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| K-037 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:37`][r1], `KnowledgeState` | equivalent | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L368`][r2], `KnowledgeStateFunction`. The predicate and carrier are fields indexed by statement and prefix. |
| K-052 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:52`][r3], `RoundExtractor` | premise-required (P2) | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L368`][r4], `KnowledgeStateFunction`. Receiver challenges no longer select subtrees. Pure output and seam witnesses retain arbitrary universes. |
| K-074 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:74`][r5], `terminalState` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L350`][r6], `leafWitness`. The leaf cursor identifies the leaf witness carrier; the leaf map takes the supplied output witness into it. |
| K-082 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:82`][r7], `extractWitness` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L345`][r8], `extractAlong`. Backward extraction returns the input witness through its explicit root map. |
| K-202 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:202`][r9], `IsProverPreserving` | equivalent | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L368`][r10], `KnowledgeStateFunction`. The send field preserves the predicate through every sender backward map. |
| K-216 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:216`][r11], `BadChallengeOnPath` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L390`][r12], `BadChallengeAlong`. Retains actual suffix extraction of the supplied witness. |
| K-233 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:233`][r13], `extraction_failure_implies_bad_challenge` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L436`][r14], `extraction_failure_implies_badChallengeAlong`. Invalid extracted input and valid output imply a receiver transition on that same witness. |
| K-331 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:331`][r15], `badChallenge` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L446`][r16], `badChallenge`. The eventual witness is existential inside the local challenge event. |
| K-347 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:347`][r17], `ChallengeSchedule` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L155`][r18], `PrefixDraw` and `PrefixError` in `RoundByRound.lean`, composed by `combinePrefixDraw`. The oracle wrapper's draw is a `PrefixDraw viewSig`, applied through [`PrefixDraw.ofView`][r249], so it reads earlier public messages and challenges but not oracle messages. Errors keep the full prefix. P1 does not make draws fresh or uniform; that is the separate public-coin premise. Pure schedule metadata is not an effectful receiver action. |
| K-359 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:359`][r19], `IsLocallyBounded` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1318`][r20], `LocallyBounded` samples with `prefixSampleAt l draw sp h history` and bounds by `ε sp h history` at every admissible statement and full prefix, including unsupported histories. |
| K-419 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:419`][r21], `KnowledgeCertificate` | equivalent | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L395`][r22], `rbrKnowledgeSoundness`. Existence of a certificate with sender laws and local bounds; the root law is guarded by the input promise. |
| K-433 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:433`][r23], `TerminalRelation` | retired (bundled leaf witness equivalence) | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1274`][r24], `toFun_leafWitness_append`. Witness maps and relation identifications are explicit. The generic leaf composition law preserves any supplied suffix equivalence; KC-292 and KC-308 test both directions. |

## ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean

| ID | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| KA-033 | [`ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean:33`][r25], `append` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L909`][r26], `append`. An explicit seam permits separate input and output carriers. |
| KA-048 | [`ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean:48`][r27], `terminalState_append` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1274`][r28], `toFun_leafWitness_append`. The composite leaf predicate equals the suffix leaf predicate on the supplied witness. |
| KA-066 | [`ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean:66`][r29], `extractWitness_append` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1211`][r30], `extractAlong_append`. Suffix extraction precedes prefix extraction, without witness selection. |
| KA-088 | [`ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean:88`][r31], `isProverPreserving_append` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L812`][r32], `appendToFun_send`. Every sender step preserves the composed predicate. |
| KA-111 | [`ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean:111`][r33], `appendSchedule` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L129`][r34], `combinePrefixDraw` and `rbrKnowledgeSoundness_append_prefix`; for oracle verifiers [`combineViewPrefixDraw`][r250] and [`rbrKnowledgeSoundness_append_view`][r251]. P1 removes only challenge selection that depends on oracle messages. The oracle suffix draw is selected by the shape path and the first stage's view, which includes earlier public challenges and prover messages. The suffix error family is selected by the complete first transcript. |
| KA-130 | [`ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean:130`][r35], `isLocallyBounded_append` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L169`][r36], `LocallyBounded.append`. The composed local error is the first error on first-protocol prefixes and the full-transcript-selected second error on the remaining prefixes. |

## ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean

| ID | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| KCO-036 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:36`][r37], `TerminalRelation.append` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1274`][r38], `toFun_leafWitness_append`. Preserves any supplied suffix leaf relation equivalence on the supplied witness. |
| KCO-071 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:71`][r39], `withLeaf` | retired (verifier leaf attachment) | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L458`][r40], `Verifier.validAcceptance`. The verifier record already has its final decision; execution observations have separate rows. |
| KCO-081 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:81`][r41], `toCounterpartValue_withLeaf` | premise-required (P1) | [`ArkLib/Interaction/Core/Composition.lean#L160`][r42], `Verifier.append_decide_transcript`. Only a final decision remains; heterogeneous equality identifies the dependent outputs at equal paths. |
| KCO-102 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:102`][r43], `run_withLeaf` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L394`][r44], `Verifier.validAcceptance_append`. Both final decisions retain the actual intermediate ambient state. |
| KCO-121 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:121`][r45], `withOutput` | retired (optional open-claim leaf adapter) | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L550`][r46], `OracleVerifier.validAcceptance`. Optional decisions and deterministic output maps are separate fields. |
| KCO-131 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:131`][r47], `executeStrategies_withOutput` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L696`][r48], `OracleVerifier.validAcceptance_append`. Acceptance uses the actual final output bundle. |
| KCO-163 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:163`][r49], `toCounterpartWith_output` | premise-required (P1) | [`ArkLib/Interaction/Core/Composition.lean#L662`][r50], `OracleVerifier.simulateQ_append_run`. The passive decision fold preserves returned outputs and the routed bundle. |
| KCO-191 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:191`][r51], `closedMiddle` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L64`][r52], `firstVerifier`. The decision and output map return the claim and export together. |
| KCO-202 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:202`][r53], `closedMiddle_oracles` | equivalent | [`ArkLib/Interaction/Core/OracleVerifier.lean#L168`][r54], `OracleMap.simulate_eq`. An output map’s simulation law identifies exported behavior with its pure data map. KC-093 specializes this to every prefix oracle message. |
| KCO-216 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:216`][r55], `run_withLeaf_closedMiddle` | premise-required (P1) | [`ArkLib/Interaction/Core/Composition.lean#L662`][r56], `OracleVerifier.simulateQ_append_run`. Final decisions replace effectful verifier fragments. |
| KCO-249 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:249`][r57], `executeStrategies_appendExported_withLeaf_close` | premise-required (P1) | [`ArkLib/Interaction/Core/Composition.lean#L662`][r58], `OracleVerifier.simulateQ_append_run`. The actual prefix output bundle is routed before the suffix decision. |
| KCO-342 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:342`][r59], `append` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L909`][r60], `append`. Certificate composition with an explicit seam. |
| KCO-377 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:377`][r61], `sequentialSuffix` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L89`][r62], `comap`. Explicit input/output witness maps transport the middle relation. |
| KCO-386 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:386`][r63], `sequential` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L299`][r64], `rbrKnowledgeSoundness_append`. The suffix covers every prefix transcript; no true middle witness is assumed. |
| KCO-394 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:394`][r65], `extractWitness_sequential` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1211`][r66], `extractAlong_append`. The named witness maps are part of the suffix certificate; extraction then composes. |
| KCO-426 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:426`][r67], `terminalKnowledge_sequential_iff` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1274`][r68], `toFun_leafWitness_append`. Composing this equivalence with the supplied suffix relation equivalence recovers the exact final relation, as in KC-292. |
| KCO-460 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:460`][r69], `sequentialTerminalRelation` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L514`][r70], `composite_leaf_iff`. Leaf assertions following KC-308 identify the actual final relation. |
| KCO-489 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:489`][r71], `sequentialClosed` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L320`][r72], `rbrKnowledgeSoundness_append_of_mid`. Uses the deterministic middle statement and explicit witness maps; the oracle acceptance bridge remains a fixture proof. |
| KCO-514 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:514`][r73], `SamplesChallenges` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L154`][r74], `appendPrefixSampler_eq_combinePrefixDraw`, [`appendViewPrefixSampler_eq_combineViewPrefixDraw`][r252] for view draws, and the shared `runPrefixChallenges_eq_run`. P1 removes receiver actions that depend on the bundle and effectful receiver actions. Oracle-verifier draws read the verifier view, which retains earlier public challenge values and prover messages. |
| KCO-548 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:548`][r75], `native_badChallenge_bound` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1310`][r76], `BoundedAt`. P1 replaces effectful receiver actions with passive prefix draws. The local probability uses `prefixSampleAt` with the same full history as its error; the witness existential remains inside the event. |
| KCO-567 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:567`][r77], `samplesChallenges_mapOutput` | retired (effectful verifier-output freshness adapter) | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L240`][r78], `appendSampler_eq_combineDraw`. Final outputs do not alter the sampler. |
| KCO-625 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:625`][r79], `samplesChallenges_routeFragment` | retired (fragment freshness routing) | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L240`][r80], `appendSampler_eq_combineDraw`. P1 confines bundle routing to final decisions. |
| KCO-683 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:683`][r81], `samplesChallenges_routeStrategy` | retired (strategy freshness routing) | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L240`][r82], `appendSampler_eq_combineDraw`. The sampler is separate from the final decision's bundle. |
| KCO-703 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:703`][r83], `samplesChallenges_routeClaimStrategy` | retired (open-claim freshness routing) | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L240`][r84], `appendSampler_eq_combineDraw`. No verifier interaction strategy remains to reroute. |
| KCO-726 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:726`][r85], `samplesChallenges_withLeaf` | retired (leaf freshness adapter) | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L240`][r86], `appendSampler_eq_combineDraw`. The leaf is a final decision, not a sampler action. |
| KCO-745 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:745`][r87], `samplesChallenges_append_withLeaf` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L154`][r88], `appendPrefixSampler_eq_combinePrefixDraw`. P1 removes effectful receiver actions. Both samplers retain full-prefix dependence, and the suffix sampler is selected by the full first transcript before the final decisions. |
| KCO-847 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:847`][r89], `samplesChallenges_appendExported_withLeaf` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L154`][r90], `appendPrefixSampler_eq_combinePrefixDraw`. P1 confines queries to the exported bundle to final decisions; it does not erase public history from challenge selection. The suffix draw and error use the actual first transcript on either permitted shape. |

## ArkLib/Interaction/Oracle/Security/RoundByRound.lean

| ID | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| RBR-168 | [`ArkLib/Interaction/Oracle/Security/RoundByRound.lean:168`][r91], `FreshVerifier` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L277`][r92], `runPrefixChallenges_eq_run`, `appendPrefixSampler_eq_combinePrefixDraw` and [`PrefixDraw.ofView`][r249]. P1 removes effectful receiver actions, and the oracle wrapper's draw reads only the verifier view. The passive sampler may still depend on earlier public challenges and prover messages. Fresh uniform draws are a separate premise of the public-coin specialization. |
| RBR-212 | [`ArkLib/Interaction/Oracle/Security/RoundByRound.lean:212`][r93], `FreshVerifier.mapPrefixes` | retired (effectful verifier prefix-map adapter) | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L240`][r94], `appendSampler_eq_combineDraw`. Sampler composition supplies the needed challenge correspondence; the ordinary global rank/escape framework is outside this port. |

## ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean

| ID | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| KR-076 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean:76`][r95], `StageInput` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L81`][r96], `StageInput`. A full move and later witness, now indexed by statement and prefix. |
| KR-083 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean:83`][r97], `stageMap` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L87`][r98], `stageMap`. The pure backward step map. |
| KR-091 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean:91`][r99], `extractWitness_public` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L94`][r100], `extractFrom_eq_stageMap`. Applies at a public-message node. |
| KR-101 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean:101`][r101], `extractWitness_oracle` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L94`][r102], `extractFrom_eq_stageMap`. Applies at an oracle-message node with its actual oracle message. |
| KR-111 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean:111`][r103], `MeasuredStages` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L104`][r104], `MeasuredStages`. Explicit root and leaf identity programs recover the frozen steps. |
| KR-123 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean:123`][r105], `MeasuredStages.BudgetAtMost` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L125`][r106], `BudgetAtMost`. The frozen bound is BudgetAtMost 0 bound 0 with zero-budget root/leaf identities. |
| KR-136 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean:136`][r107], `MeasuredKnowledgeCertificate` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L261`][r108], `MeasuredKnowledgeStateFunction`. Standard natural count profiles over a finite kind type, without caller-supplied arithmetic or order. |

## ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean

| ID | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| KRC-037 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean:37`][r109], `MeasuredStages.programAlong` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L171`][r110], `programAlong`. Composes the same named programs, with explicit root and leaf identities. |
| KRC-051 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean:51`][r111], `MeasuredStages.run_programAlong` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L177`][r112], `run_programAlong`. Realizes full backward extraction on every supplied output witness. |
| KRC-058 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean:58`][r113], `MeasuredStages.programAlong_budget_done` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L183`][r114], `programFrom_budget_pure`. The frozen leaf is an identity of budget zero; programAlong_budget adds the explicit zero root budget. |
| KRC-064 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean:64`][r115], `MeasuredStages.programAlong_budget_public` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L189`][r116], `programFrom_budget_liftBind`. Suffix budget plus the public backward step budget. |
| KRC-072 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean:72`][r117], `MeasuredStages.programAlong_budget_oracle` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L189`][r118], `programFrom_budget_liftBind`. Suffix budget plus the oracle backward step budget. |
| KRC-081 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean:81`][r119], `MeasuredStages.programAlong_budget_le` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L225`][r120], `programAlong_budget_le_nsmul`. Explicit zero root/leaf bounds recover length times the step bound. |
| KRC-097 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean:97`][r121], `MeasuredStages.programAlong_costAtMost` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L239`][r122], `programAlong_costAtMost_nsmul`. The same bound holds for actual instruction paths. |

## ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean

| ID | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| KC-052 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:52`][r123], `middleProblem` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L275`][r124], `MidWitness`. The carrier reads the actual oracle message; relMid tests the actual challenge. |
| KC-061 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:61`][r125], `firstExtractor` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L297`][r126], `firstState`. Witnesses after the oracle depend on its message. |
| KC-065 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:65`][r127], `firstSchedule` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L187`][r128], `firstDraw` embeds through `PrefixDraw.ofNodes`, paired with `PrefixError.ofNodes`. The frozen `firstSchedule` already uses `pure true` and error one independently of its oracle message; P1 requires no change to that schedule. |
| KC-068 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:68`][r129], `firstCertificate` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L565`][r130], `first_rbrKnowledgeSoundness`. The prefix local bound remains one. |
| KC-086 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:86`][r131], `middleEndpoint` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L255`][r132], `firstVerifier_validAcceptance_iff`. True-claim acceptance is exactly the true challenge. |
| KC-097 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:97`][r133], `suffixProtocol` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L47`][r134], `secondProtocol`. A public prover selector chooses public Unit versus oracle Nat. Both challenges remain on each shape. |
| KC-108 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:108`][r135], `suffixExtractor` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L353`][r136], `secondState`. The backward step removes the unit component on both selected shapes. |
| KC-114 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:114`][r137], `suffixSchedule` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L194`][r138], `secondDraw`. Neither suffix shape draws a challenge. |
| KC-120 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:120`][r139], `suffixCertificate` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L576`][r140], `second_rbrKnowledgeSoundness`. Every suffix is certified even at false middle claims. |
| KC-131 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:131`][r141], `secondCertificate` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L576`][r142], `second_rbrKnowledgeSoundness`. The family quantifies every complete prefix transcript. |
| KC-135 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:135`][r143], `compositeCertificate` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L605`][r144], `composed_rbrKnowledgeSoundness`. Relation-level composition plus the explicit oracle acceptance bridge, not a standalone oracle theorem. |
| KC-279 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:279`][r145], `finalProblem` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L277`][r146], `OutWitness`. The finite witness, which depends on the oracle message, is paired with Unit; validOutput tests the actual closed claim. |
| KC-286 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:286`][r147], `finalClosed` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L113`][r148], `composed_export_eq`. The appended output map exports the actual prefix oracle message at every message value, challenge and public selector, after either suffix message. |
| KC-292 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:292`][r149], `finalEndpoint` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L514`][r150], `composite_leaf_iff`. Together with leaf assertions following KC-308, identifies the final relation in both directions on both shapes. |
| KC-303 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:303`][r151], `compositeEndpoint` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L494`][r152], `composite_leafWitness`. The assertions following KC-308 preserve the whole witness and final relation. |
| KC-312 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:312`][r153], `emptyExtractor` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L888`][r154], `emptyState`. No fabricated message or witness is needed. |
| KC-093 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:93`][r155], `example: exported payload` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L100`][r156], `example (n`. Every oracle message and challenge, independently of selector. |
| KC-095 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:95`][r157], `#eval firstExtractor.extractWitness` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L447`][r158], `firstState.extractAlong stmt₀ (firstPath 7 true true) (⟨6, by decide⟩ : Fin 8)`. The guarded evaluation below the example also returns six. |
| KC-207 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:207`][r159], `example: observed run` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L164`][r160], `theorem observed_eq (choice b`. observed_eq quantifies both selector and challenge, including false challenge. |
| KC-215 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:215`][r161], `#eval observed` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L171`][r162], `observed true true`. Retains the true/public result; an added guarded matrix checks all four runs. |
| KC-219 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:219`][r163], `first_fresh` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L223`][r164], `example (choice`. The prefix sampler draws true at each selector. |
| KC-234 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:234`][r165], `second_fresh` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L230`][r166], `example (p`. The suffix samples no challenge; the actual public Unit or oracle message five is retained. |
| KC-249 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:249`][r167], `composite_fresh` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L240`][r168], `theorem appendSampler_eq_combineDraw`. appendSampler_eq_combineDraw identifies the composite sampler. |
| KC-268 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:268`][r169], `example: truePath extraction` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L469`][r170], `example`. The universal law above it also quantifies both selector values. |
| KC-271 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:271`][r171], `example: falsePath extraction` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L473`][r172], `example`. The universal law also covers false challenge on the public suffix. |
| KC-274 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:274`][r173], `#eval truePath extraction` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L479`][r174], `compositeState.extractAlong stmt₀ truePath (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit)`. Guarded executable result six. |
| KC-276 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:276`][r175], `#eval falsePath extraction` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L484`][r176], `compositeState.extractAlong stmt₀ falsePath (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit)`. Guarded executable result six. |
| KC-308 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:308`][r177], `example: terminal witness value` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L489`][r178], `example`. Following assertions identify the entire witness by HEq and per-shape equality, and prove exact leaf relation equivalence. |
| KC-316 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:316`][r179], `largeState` | equivalent | [`ArkLibTest/Interaction/Core/UniverseCanary.lean#L492`][r180], `largeTypeCertificate`. Large input, intermediate, seam and output carriers are supported directly. The general API has independent witness universes. |
| KC-318 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:318`][r181], `largeExtractor: higher-universe oracle payload` | equivalent | [`ArkLibTest/Interaction/Core/UniverseCanary.lean#L569`][r182], `largePayloadCertificate`. The general pure certificate receives ULift.{1} Nat in Type 1. For the sent message m, its output and post-message carriers are ULift.{2} (Fin (m.down + 1)), retaining the full dependence on the message; the backward map returns the finite witness value as ULift.{2} Nat. |
| KC-322 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:322`][r183], `example: large oracle-message extraction` | equivalent | [`ArkLibTest/Interaction/Core/UniverseCanary.lean#L592`][r184], `largePayload_extractAlong`. The ordinary-import client sends the Type 1 oracle message seven, supplies witness six in ULift.{2} (Fin 8), and proves that pure extraction returns six. |

## ArkLibTest/OracleReduction/MeasuredExtraction.lean

| ID | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| ME-086 | [`ArkLibTest/OracleReduction/MeasuredExtraction.lean:86`][r185], `example: addStages run` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L74`][r186], `example (message`. The actual message and supplied witness select the same dependent carrier. A separate stage equation precedes this program equation. |
| ME-091 | [`ArkLibTest/OracleReduction/MeasuredExtraction.lean:91`][r187], `example: budget one` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L81`][r188], `example (m`. Root and leaf programs have explicit budget zero. |
| ME-094 | [`ArkLibTest/OracleReduction/MeasuredExtraction.lean:94`][r189], `example: empty witness budget` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L98`][r190], `example (tr`. Empty witnesses need no fabricated input. |
| ME-103 | [`ArkLibTest/OracleReduction/MeasuredExtraction.lean:103`][r191], `example: finite Kind` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L104`][r192], `example (Kind`. Uses standard natural count profiles. |
| ME-112 | [`ArkLibTest/OracleReduction/MeasuredExtraction.lean:112`][r193], `example: fixed count stages` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L142`][r194], `example (F`. Fills the fixed arithmetic certificate. |
| ME-138 | [`ArkLibTest/OracleReduction/MeasuredExtraction.lean:138`][r195], `negative example: max-additive profile` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L168`][r196], `example (F`. fail_if_success still rejects that arithmetic. |
| ME-153 | [`ArkLibTest/OracleReduction/MeasuredExtraction.lean:153`][r197], `negative example: reversed order` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L184`][r198], `example (F`. fail_if_success still rejects that order. |
| ME-166 | [`ArkLibTest/OracleReduction/MeasuredExtraction.lean:166`][r199], `negative example: infinite Kind` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L196`][r200], `example`. fail_if_success still rejects infinitely many kinds. |
| ME-186 | [`ArkLibTest/OracleReduction/MeasuredExtraction.lean:186`][r201], `zeroStages_budgetAtMost` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L214`][r202], `example (F`. Root, step and leaf bounds are explicitly zero. |
| ME-194 | [`ArkLibTest/OracleReduction/MeasuredExtraction.lean:194`][r203], `example: every certificate has zero stages` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L221`][r204], `example (F`. Preserves extraction and the zero instruction budget without claiming bounded pure work. |
| ME-178 | [`ArkLibTest/OracleReduction/MeasuredExtraction.lean:178`][r205], `zeroStages` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L139`][r206], `zero`. Root and leaf maps also use zero-instruction programs. |

## ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean

| ID | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| MP-031 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:31`][r207], `recorded_comp` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L34`][r208], `theorem recorded_comp {A B C`. Actual charges add in the same suffix-before-root order. |
| MP-063 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:63`][r209], `chainStages_budgetAtMost` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L139`][r210], `theorem chainStages_budgetAtMost (n`. Step bound one, with explicit zero root/leaf bounds. |
| MP-071 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:71`][r211], `chain_budget` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L159`][r212], `theorem chain_budget (n`. Every authored chain message contributes one. |
| MP-076 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:76`][r213], `deep_budget` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L175`][r214], `theorem deep_budget (n`. The selector step and root/leaf maps have zero budgets. |
| MP-081 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:81`][r215], `no_global_budget_of_stage_bound` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L180`][r216], `theorem no_global_budget_of_stage_bound`. Unbounded public depth defeats a global budget. |
| MP-090 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:90`][r217], `chain_recorded_cost` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L198`][r218], `theorem chain_recorded_cost (n w`. Actual cost equals depth for every output witness. |
| MP-107 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:107`][r219], `deep_recorded_cost` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L219`][r220], `theorem deep_recorded_cost (n w`. Actual cost equals the selected depth. |
| MP-119 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:119`][r221], `no_global_cost_bound_of_stage_bound` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L228`][r222], `theorem no_global_cost_bound_of_stage_bound`. Local budget one does not imply a global actual-cost bound. |
| MP-137 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:137`][r223], `example: path-length cost` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L241`][r224], `example (tr`. The nsmul theorem recovers the full-move length bound. |
| MP-142 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:142`][r225], `example: empty protocol cost` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L248`][r226], `example {S`. Quantifies every state function and stage family with zero root/leaf bounds. |
| MP-149 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:149`][r227], `example: empty path length` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L261`][r228], `example (tr`. No authored moves means zero length. |
| MP-152 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:152`][r229], `example: signed weight` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L266`][r230], `example`. A negative step bound cannot be relaxed to a larger depth cap; root/leaf bounds remain zero. |
| MP-183 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:183`][r231], `example: ordered result and charge` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L359`][r232], `example (w`. Both additions and the intervening uncharged map execute for every input. |
| MP-186 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:186`][r233], `example: swapped stages rejected` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L363`][r234], `example`. Retains the unequal arithmetic alternative. |
| MP-189 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:189`][r235], `example: omitted middle map rejected` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L367`][r236], `example`. Retains the unequal arithmetic alternative. |
| MP-198 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:198`][r237], `#guard_msgs checkOrderedObservation` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L378`][r238], `#guard_msgs in`. Retains the exact runtime success message. |
| MP-202 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:202`][r239], `#guard_msgs deep cost` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L383`][r240], `#guard_msgs in`. Retains result four and recorded charge four. |
| MP-199 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:199`][r241], `#eval checkOrderedObservation` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L379`][r242], `#eval checkOrderedObservation`. Executable command protected by the separately listed message guard. |
| MP-203 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:203`][r243], `#eval deep cost` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L384`][r244], `#eval deep cost`. Executable command protected by the separately listed message guard. |
| MP-191 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:191`][r245], `checkOrderedObservation` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L370`][r246], `checkOrderedObservation`. Tests the same three inputs against result and charge together. |

## Added canaries, audits and remaining work

The canary's `largeTypeCertificate` and its composition example use a seam carrier in
`Type 1` and an output carrier in `Type 1` directly. `largeOutputCertificate` checks both verifier
wrappers at that output universe. Lifting raises only the intermediate universe. These are
additional ordinary-import elaboration contracts, not measured programs.

The frozen files in these tables contain no `#print axioms` commands. The replacement composition
and path-budget acceptance files add `run_cmd` collectors using `Lean.collectAxioms`, rejecting
dependencies beyond `propext`, `Classical.choice` and `Quot.sound`. The collectors cover the
extraction-failure theorem, append extraction/leaf laws, relation-level composition, plain
standalone verifier composition, acceptance bridges, fixture equations and both no-global-bound
theorems. They also cover the view laws (`PrefixDraw.ofView_ofNodesView`,
`ofView_combineViewPrefixDraw`, `appendViewPrefixSampler_eq_combineViewPrefixDraw`,
`rbrKnowledgeSoundness_append_view`, `rbrKnowledgeSoundnessOfNodes_iff`), the view regressions,
the challenge composition client and the endpoint bound. The added statement-indexed measured
execution returns witness two in `Fin 4`; it is additional coverage, not a replacement for ME-086.

The restoration disposition is premise-required under P2. Child branch #1483 selects `Fin 8`
versus `Fin 9` by a public prover message, retains the plain replay's payload return on both
challenges and keeps oracle rejection separate. No missing challenge-indexed parent output
interface is asserted. KC-318 and KC-322 are equivalent through the general pure move interface.
Restoration games and the excluded multi-prefix/ordinary global APIs are outside the port claim
above.

The extractor design page (`docs/design/03a-extractor-efficiency.md`) and the status pages are
not part of this branch. Follow-up work updates them to name the Core and frozen APIs, keeps the
older straight-line contract and the FRI certificate separate from this backward-stage port, and
records that no security game yet links to this extractor. The planned VCVio-to-PolyFun
measured-program repin should include `MeasuredExtraction.lean`, its tests and #1483's measured
restoration consumer.

The required checks are the targeted reverse-dependency build and guards relative to
`feat/interaction-migrate-core`. They check Core consumers, source restrictions, frozen paths,
imports and documentation. They do not claim a whole-library build or validation.

## Remaining probabilistic move restriction

This restriction affects sampling and probability bounds, not the frozen pure extraction assertions.

| ID | Forcing parent declarations | Status | Exact target and limitation |
| --- | --- | --- | --- |
| PROB-031 | [`ProbComp : Type → Type`, pinned VCVio `Basic.lean:31`](https://github.com/Verified-zkEVM/VCVio/blob/f8d7f8ef52b9afaf4e6d897804b9dce347cdb1db/VCVio/OracleComp/ProbComp/Basic.lean#L31); [`ArkLib/Interaction/Core/Protocol.lean#L70`][r247], `challengeSpec` (`Interaction/Protocol.lean:69–71`) | accepted upstream limit (large-move probability: `ProbComp` and shared challenge/message universe; [VCVio#1236](https://github.com/Verified-zkEVM/VCVio/pull/1236) makes `ProbComp` universe-polymorphic) | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L141`][r248], `sampleAt`. `sampleAt`, `BoundedAt`, `LocallyBounded` and round-by-round probability bounds use the small-move instance of the general certificate. `challengeSpec` returns `Move l` in the same universe as oracle/public messages; `ProbComp` cannot sample these moves at `u > 0`. Measured specializations also require small stage inputs through `BudgetedProgram`, as recorded above. |

[r1]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/Knowledge.lean#L37
[r2]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/RoundByRound.lean#L368
[r3]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/Knowledge.lean#L52
[r4]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/RoundByRound.lean#L368
[r5]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/Knowledge.lean#L74
[r6]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L350
[r7]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/Knowledge.lean#L82
[r8]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L345
[r9]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/Knowledge.lean#L202
[r10]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/RoundByRound.lean#L368
[r11]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/Knowledge.lean#L216
[r12]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L390
[r13]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/Knowledge.lean#L233
[r14]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L436
[r15]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/Knowledge.lean#L331
[r16]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L446
[r17]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/Knowledge.lean#L347
[r18]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/RoundByRound.lean#L155
[r19]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/Knowledge.lean#L359
[r20]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1318
[r21]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/Knowledge.lean#L419
[r22]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/RoundByRound.lean#L395
[r23]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/Knowledge.lean#L433
[r24]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1274
[r25]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean#L33
[r26]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L909
[r27]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean#L48
[r28]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1274
[r29]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean#L66
[r30]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1211
[r31]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean#L88
[r32]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L812
[r33]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean#L111
[r34]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L129
[r35]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean#L130
[r36]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L169
[r37]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L36
[r38]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1274
[r39]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L71
[r40]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/RoundByRound.lean#L458
[r41]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L81
[r42]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Composition.lean#L160
[r43]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L102
[r44]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L394
[r45]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L121
[r46]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/RoundByRound.lean#L550
[r47]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L131
[r48]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L696
[r49]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L163
[r50]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Composition.lean#L662
[r51]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L191
[r52]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L64
[r53]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L202
[r54]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/OracleVerifier.lean#L168
[r55]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L216
[r56]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Composition.lean#L662
[r57]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L249
[r58]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Composition.lean#L662
[r59]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L342
[r60]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L909
[r61]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L377
[r62]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L89
[r63]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L386
[r64]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L299
[r65]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L394
[r66]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1211
[r67]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L426
[r68]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1274
[r69]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L460
[r70]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L514
[r71]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L489
[r72]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L320
[r73]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L514
[r74]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L154
[r75]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L548
[r76]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1310
[r77]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L567
[r78]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L240
[r79]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L625
[r80]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L240
[r81]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L683
[r82]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L240
[r83]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L703
[r84]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L240
[r85]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L726
[r86]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L240
[r87]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L745
[r88]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L154
[r89]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L847
[r90]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L154
[r91]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/RoundByRound.lean#L168
[r92]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/RoundByRound.lean#L277
[r93]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/RoundByRound.lean#L212
[r94]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L240
[r95]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean#L76
[r96]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L81
[r97]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean#L83
[r98]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L87
[r99]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean#L91
[r100]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L94
[r101]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean#L101
[r102]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L94
[r103]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean#L111
[r104]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L104
[r105]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean#L123
[r106]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L125
[r107]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean#L136
[r108]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L261
[r109]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean#L37
[r110]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L171
[r111]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean#L51
[r112]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L177
[r113]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean#L58
[r114]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L183
[r115]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean#L64
[r116]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L189
[r117]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean#L72
[r118]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L189
[r119]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean#L81
[r120]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L225
[r121]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean#L97
[r122]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L239
[r123]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L52
[r124]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L275
[r125]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L61
[r126]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L297
[r127]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L65
[r128]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L187
[r129]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L68
[r130]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L565
[r131]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L86
[r132]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L255
[r133]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L97
[r134]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L47
[r135]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L108
[r136]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L353
[r137]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L114
[r138]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L194
[r139]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L120
[r140]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L576
[r141]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L131
[r142]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L576
[r143]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L135
[r144]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L605
[r145]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L279
[r146]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L277
[r147]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L286
[r148]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L113
[r149]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L292
[r150]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L514
[r151]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L303
[r152]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L494
[r153]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L312
[r154]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L888
[r155]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L93
[r156]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L100
[r157]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L95
[r158]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L447
[r159]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L207
[r160]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L164
[r161]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L215
[r162]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L171
[r163]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L219
[r164]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L223
[r165]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L234
[r166]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L230
[r167]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L249
[r168]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L240
[r169]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L268
[r170]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L469
[r171]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L271
[r172]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L473
[r173]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L274
[r174]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L479
[r175]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L276
[r176]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L484
[r177]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L308
[r178]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L489
[r179]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L316
[r180]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/UniverseCanary.lean#L492
[r181]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L318
[r182]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/UniverseCanary.lean#L569
[r183]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L322
[r184]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/UniverseCanary.lean#L592
[r185]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/OracleReduction/MeasuredExtraction.lean#L86
[r186]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L74
[r187]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/OracleReduction/MeasuredExtraction.lean#L91
[r188]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L81
[r189]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/OracleReduction/MeasuredExtraction.lean#L94
[r190]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L98
[r191]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/OracleReduction/MeasuredExtraction.lean#L103
[r192]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L104
[r193]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/OracleReduction/MeasuredExtraction.lean#L112
[r194]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L142
[r195]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/OracleReduction/MeasuredExtraction.lean#L138
[r196]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L168
[r197]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/OracleReduction/MeasuredExtraction.lean#L153
[r198]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L184
[r199]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/OracleReduction/MeasuredExtraction.lean#L166
[r200]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L196
[r201]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/OracleReduction/MeasuredExtraction.lean#L186
[r202]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L214
[r203]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/OracleReduction/MeasuredExtraction.lean#L194
[r204]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L221
[r205]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/OracleReduction/MeasuredExtraction.lean#L178
[r206]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L139
[r207]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L31
[r208]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L34
[r209]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L63
[r210]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L139
[r211]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L71
[r212]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L159
[r213]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L76
[r214]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L175
[r215]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L81
[r216]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L180
[r217]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L90
[r218]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L198
[r219]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L107
[r220]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L219
[r221]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L119
[r222]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L228
[r223]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L137
[r224]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L241
[r225]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L142
[r226]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L248
[r227]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L149
[r228]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L261
[r229]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L152
[r230]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L266
[r231]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L183
[r232]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L359
[r233]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L186
[r234]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L363
[r235]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L189
[r236]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L367
[r237]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L198
[r238]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L378
[r239]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L202
[r240]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L383
[r241]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L199
[r242]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L379
[r243]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L203
[r244]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L384
[r245]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L191
[r246]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L370
[r247]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Protocol.lean#L70
[r248]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/RoundByRound.lean#L141
[r249]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/RoundByRound.lean#L210
[r250]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L234
[r251]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L371
[r252]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L279
[r253]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLib/Interaction/Core/Security/RoundByRound.lean#L616
[r254]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/PrefixKnowledge.lean#L115
[r255]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/PrefixKnowledge.lean#L140
[r256]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/PrefixKnowledge.lean#L148
[r257]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L806
[r258]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L619
[r259]: https://github.com/Verified-zkEVM/ArkLib/blob/8472a86fb744c8fcd22f024eba65cf494ce0a32e/ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L302
