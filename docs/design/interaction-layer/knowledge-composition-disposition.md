# Knowledge composition and measured extraction: source-to-port inventory

This record compares the assertions ported by `feat/interaction-migrate-core-3` (#1482) with their
frozen sources. Stable IDs in test comments resolve to the rows below. Source line numbers refer
to unchanged frozen files; target line numbers identify declarations or acceptance commands in Core.

The approved premises are:

- **P1 (passivity):** verifiers send only public-coin challenges and make all resource queries in
  the final decision. A challenge cannot be computed from an input or previously sent oracle.
  Earlier public challenges and prover messages may select later challenge distributions and errors.
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
  prevents this branch's pure move, terminal or seam universe port.

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
full prefix payloads and supplied terminal witness. Pure maps allow independent statement, input,
intermediate, seam and terminal universes. `PrefixMoves`, the certificate, lifting, extraction,
extraction failure, append and pure restriction laws are polymorphic in the move universe `u`,
with `P : PFunctor.{uA, u}`, a lens to `rolePoly.{u}` and leaves `PUnit.{u + 1}`. Positions have
their own universe `uA`; branches and leaves share the move universe as in the structural parents.
The ordinary-import canary uses `Type` itself as a `Type 1` seam and terminal carrier, without
encoding either into a small type. It also sends the frozen `ULift.{1} Nat` oracle payload and
retains its dependent witness carrier (KC-318 and KC-322).

The generic **plain standalone verifier** theorem is `Verifier.rbrKnowledgeSoundness_append`
(and `_of_pure`). Its hypotheses are the components' own standalone verifier knowledge theorems.
The added `indexed_composed` client checks that interface. The **oracle fixture** instead composes
relation-level certificates with `rbrKnowledgeSoundness_append` (and `_of_mid`), using its separately
proved `composed_validAcceptance_iff` to identify the appended verifier's output relation. The
oracle fixture is not evidence for a generic standalone oracle verifier composition theorem.

Structural equivalences use the approved Core protocol domain. P2's domain change is recorded on
the extractor and selector rows; equivalent extraction equations do not restore challenge-selected
shape. P1 removes effectful verifier interaction phases, while preserving final resource access
and the actual shared ambient state between decisions. A retired leaf adapter is distinct from
its execution equations, which are listed separately.

## Full-prefix challenge schedules

`Security/RoundByRound.lean` supplies the shared `PrefixDraw`, `PrefixChallengePrograms`,
`prefixSampleAt` and `prefixSampler` interfaces. `BoundedAt`, `LocallyBounded`,
`rbrKnowledgeSoundness` and both verifier wrappers draw at `sp`, its receiver proof and its full
`history`; the local error uses those same indices. Every compatible history is quantified,
including histories of probability zero.

`combinePrefixDraw` combines both draws and errors. Before the seam it uses the first family's
error at the first prefix. After the seam it selects the second family using the entire first
transcript, then uses the second prefix and its history. Challenge values erased from shape still
select this family. `appendPrefixSampler_eq_combinePrefixDraw` identifies the appended counterpart
with this combined sampler. The node-indexed predicates (`rbrKnowledgeSoundnessOfNodes` and the
certificate's `BoundedAtOfNodes` and `LocallyBoundedOfNodes`) ignore history through `ofNodes`.
The established node composition theorems are corollaries of the `_prefix` laws and the two
`combinePrefixDraw_ofNodes` / `combinePrefixError_ofNodes` equations.

P1 retires oracle-payload-dependent challenge selection and effectful receiver interaction
actions. It does not retire dependence on earlier public challenges or prover messages.
The fixed two-challenge Boolean regression in
[`PrefixKnowledge.lean`](../../../ArkLibTest/Interaction/Core/Security/PrefixKnowledge.lean)
samples the second bit as the complement of the first, uses unit witnesses and identity backward
maps, and proves zero error with false root/intermediate predicates and terminal equality of the
bits. It sends no prover message. A second assertion checks different suffix errors for first
transcripts with the same shape path.

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
ordered monoid, without adding a nonnegativity premise.

Instruction budgets leave pure code, views, handlers, carrier identification and witness size
uncharged. Ordered-program and unbounded-depth assertions retain actual instrumented charges,
not just declared budgets. Zero-stage assertions deliberately show that the resource contract
alone gives no total running-time bound.

Pinned VCVio `OracleComp.BudgetedProgram` in
`VCVio/OracleComp/QueryTracking/MeasuredProgram.lean:156` fixes `Input` and `Result` to `Type`.
This forces small `Win stmt` at root results, small intermediate witnesses and `StageInput` at
step inputs/results, and small `W stmt tr` at leaf inputs. `MeasuredStages.programAlong` and
`MeasuredKnowledgeStateFunction` retain those restrictions. The underlying
`OracleComp.MeasuredProgram` at line 66 also fixes `ω`, `View` and `Op` to `Type`. The statement
universe remains independent. These restrictions apply only to measured programs, not pure
backward maps. The VCVio pin is `fc54dd3d7691d6f5db7dc829e321a727f095bc2d`.

## ArkLib/Interaction/Oracle/Security/Knowledge.lean

| ID | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| K-037 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:37`][r1], `KnowledgeState` | equivalent | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L253`][r2], `KnowledgeStateFunction`. The predicate and carrier are fields indexed by statement and prefix. |
| K-052 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:52`][r3], `RoundExtractor` | premise-required (P2) | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L253`][r4], `KnowledgeStateFunction`. Receiver challenges no longer select subtrees. Pure terminal and seam witnesses retain arbitrary universes. |
| K-074 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:74`][r5], `terminalState` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L267`][r6], `terminalWitness`. The complete cursor identifies the terminal carrier; the leaf map takes the supplied output witness into it. |
| K-082 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:82`][r7], `extractWitness` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L262`][r8], `extractAlong`. Backward extraction returns the input witness through its explicit root map. |
| K-202 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:202`][r9], `IsProverPreserving` | equivalent | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L253`][r10], `KnowledgeStateFunction`. The send field preserves the predicate through every sender backward map. |
| K-216 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:216`][r11], `BadChallengeOnPath` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L287`][r12], `BadChallengeAlong`. Retains actual suffix extraction of the supplied witness. |
| K-233 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:233`][r13], `extraction_failure_implies_bad_challenge` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L313`][r14], `extraction_failure_implies_badChallengeAlong`. Invalid extracted input and valid output imply a receiver transition on that same witness. |
| K-331 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:331`][r15], `badChallenge` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L332`][r16], `badChallenge`. The eventual witness is existential inside the local challenge event. |
| K-347 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:347`][r17], `ChallengeSchedule` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L98`][r18], `PrefixDraw` and `PrefixError` in `RoundByRound.lean`, composed by `combinePrefixDraw`. P1 removes oracle-payload-dependent challenge selection; distributions and errors retain all earlier public messages and challenges. Pure schedule metadata is not an effectful receiver action. |
| K-359 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:359`][r19], `IsLocallyBounded` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1156`][r20], `LocallyBounded` samples with `prefixSampleAt l draw sp h history` and bounds by `ε sp h history` at every admissible statement and full prefix, including unsupported histories. |
| K-419 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:419`][r21], `KnowledgeCertificate` | equivalent | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L280`][r22], `rbrKnowledgeSoundness`. Existence of a certificate with sender laws and local bounds; the root law is guarded by the input promise. |
| K-433 | [`ArkLib/Interaction/Oracle/Security/Knowledge.lean:433`][r23], `TerminalRelation` | retired (bundled terminal witness equivalence) | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1111`][r24], `toFun_terminalWitness_append`. Witness maps and relation identifications are explicit. The generic terminal composition law preserves any supplied suffix equivalence; KC-292 and KC-308 test both directions. |

## ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean

| ID | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| KA-033 | [`ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean:33`][r25], `append` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L803`][r26], `append`. An explicit seam permits separate input and output carriers. |
| KA-048 | [`ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean:48`][r27], `terminalState_append` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1111`][r28], `toFun_terminalWitness_append`. The composite terminal predicate equals the suffix terminal predicate on the supplied witness. |
| KA-066 | [`ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean:66`][r29], `extractWitness_append` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1046`][r30], `extractAlong_append`. Suffix extraction precedes prefix extraction, without witness selection. |
| KA-088 | [`ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean:88`][r31], `isProverPreserving_append` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L704`][r32], `appendToFun_send`. Every sender step preserves the composed predicate. |
| KA-111 | [`ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean:111`][r33], `appendSchedule` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L112`][r34], `combinePrefixDraw` and `rbrKnowledgeSoundness_append_prefix`. P1 removes oracle-payload-dependent challenge selection only. The suffix draw/error family is selected by the complete first transcript, including earlier public challenges. |
| KA-130 | [`ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean:130`][r35], `isLocallyBounded_append` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L152`][r36], `LocallyBounded.append`. The composed local error is the first error on first-protocol prefixes and the full-transcript-selected second error on the remaining prefixes. |

## ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean

| ID | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| KCO-036 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:36`][r37], `TerminalRelation.append` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1111`][r38], `toFun_terminalWitness_append`. Preserves any supplied suffix terminal relation equivalence on the supplied witness. |
| KCO-071 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:71`][r39], `withLeaf` | retired (verifier leaf attachment) | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L342`][r40], `Verifier.validAcceptance`. The verifier record already has its final decision; execution observations have separate rows. |
| KCO-081 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:81`][r41], `toCounterpartValue_withLeaf` | premise-required (P1) | [`ArkLib/Interaction/Core/Composition.lean#L146`][r42], `Verifier.append_decide_pathAlong`. Only a final decision remains; heterogeneous equality identifies the dependent output fibers. |
| KCO-102 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:102`][r43], `run_withLeaf` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L345`][r44], `Verifier.validAcceptance_append`. Both final decisions retain the actual intermediate ambient state. |
| KCO-121 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:121`][r45], `withOutput` | retired (optional open-claim leaf adapter) | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L434`][r46], `OracleVerifier.validAcceptance`. Optional decisions and deterministic output maps are separate fields. |
| KCO-131 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:131`][r47], `executeStrategies_withOutput` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L651`][r48], `OracleVerifier.validAcceptance_append`. Acceptance uses actual final output resources. |
| KCO-163 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:163`][r49], `toCounterpartWith_output` | premise-required (P1) | [`ArkLib/Interaction/Core/Composition.lean#L644`][r50], `OracleVerifier.simulateQ_append_run`. The passive decision fold preserves returned outputs and routed resources. |
| KCO-191 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:191`][r51], `closedMiddle` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L64`][r52], `firstVerifier`. The decision and output map return the claim and export together. |
| KCO-202 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:202`][r53], `closedMiddle_oracles` | equivalent | [`ArkLib/Interaction/Core/OracleVerifier.lean#L168`][r54], `OracleMap.simulate_eq`. An output map’s simulation law identifies exported behavior with its pure data map. KC-093 specializes this to every prefix payload. |
| KCO-216 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:216`][r55], `run_withLeaf_closedMiddle` | premise-required (P1) | [`ArkLib/Interaction/Core/Composition.lean#L644`][r56], `OracleVerifier.simulateQ_append_run`. Final decisions replace effectful verifier fragments. |
| KCO-249 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:249`][r57], `executeStrategies_appendExported_withLeaf_close` | premise-required (P1) | [`ArkLib/Interaction/Core/Composition.lean#L644`][r58], `OracleVerifier.simulateQ_append_run`. Actual prefix output resources are routed before the suffix decision. |
| KCO-342 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:342`][r59], `append` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L803`][r60], `append`. Certificate composition with an explicit seam. |
| KCO-377 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:377`][r61], `sequentialSuffix` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L72`][r62], `comap`. Explicit input/output witness maps transport the middle relation. |
| KCO-386 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:386`][r63], `sequential` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L284`][r64], `rbrKnowledgeSoundness_append`. The suffix covers every prefix transcript; no true middle witness is assumed. |
| KCO-394 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:394`][r65], `extractWitness_sequential` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1046`][r66], `extractAlong_append`. The named witness maps are part of the suffix certificate; extraction then composes. |
| KCO-426 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:426`][r67], `terminalKnowledge_sequential_iff` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1111`][r68], `toFun_terminalWitness_append`. Composing this equivalence with the supplied suffix relation equivalence recovers the exact final relation, as in KC-292. |
| KCO-460 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:460`][r69], `sequentialTerminalRelation` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L511`][r70], `composite_terminal_iff`. Terminal assertions following KC-308 identify the actual final relation. |
| KCO-489 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:489`][r71], `sequentialClosed` | equivalent | [`ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L305`][r72], `rbrKnowledgeSoundness_append_of_mid`. Uses the deterministic middle statement and explicit witness maps; the oracle acceptance bridge remains a fixture proof. |
| KCO-514 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:514`][r73], `SamplesChallenges` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L137`][r74], `appendPrefixSampler_eq_combinePrefixDraw` and the shared `runPrefixChallenges_eq_run`. P1 removes resource-dependent and effectful receiver actions. Full-prefix programs retain earlier public challenge values and prover messages. |
| KCO-548 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:548`][r75], `native_badChallenge_bound` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1148`][r76], `BoundedAt`. P1 replaces effectful receiver actions with passive prefix draws. The local probability uses `prefixSampleAt` with the same full history as its error; the witness existential remains inside the event. |
| KCO-567 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:567`][r77], `samplesChallenges_mapOutput` | retired (effectful verifier-output freshness adapter) | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L239`][r78], `appendSampler_eq_combineDraw`. Final outputs do not alter the sampler. |
| KCO-625 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:625`][r79], `samplesChallenges_routeFragment` | retired (fragment freshness routing) | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L239`][r80], `appendSampler_eq_combineDraw`. P1 confines resource routing to final decisions. |
| KCO-683 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:683`][r81], `samplesChallenges_routeStrategy` | retired (strategy freshness routing) | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L239`][r82], `appendSampler_eq_combineDraw`. The sampler is separate from final-decision resources. |
| KCO-703 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:703`][r83], `samplesChallenges_routeClaimStrategy` | retired (open-claim freshness routing) | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L239`][r84], `appendSampler_eq_combineDraw`. No verifier interaction strategy remains to reroute. |
| KCO-726 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:726`][r85], `samplesChallenges_withLeaf` | retired (leaf freshness adapter) | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L239`][r86], `appendSampler_eq_combineDraw`. The leaf is a final decision, not a sampler action. |
| KCO-745 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:745`][r87], `samplesChallenges_append_withLeaf` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L137`][r88], `appendPrefixSampler_eq_combinePrefixDraw`. P1 removes effectful receiver actions. Both samplers retain full-prefix dependence, and the suffix sampler is selected by the full first transcript before the final decisions. |
| KCO-847 | [`ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:847`][r89], `samplesChallenges_appendExported_withLeaf` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L137`][r90], `appendPrefixSampler_eq_combinePrefixDraw`. P1 confines exported-resource queries to final decisions; it does not erase public history from challenge selection. The suffix draw and error use the actual first transcript on either permitted shape. |

## ArkLib/Interaction/Oracle/Security/RoundByRound.lean

| ID | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| RBR-168 | [`ArkLib/Interaction/Oracle/Security/RoundByRound.lean:168`][r91], `FreshVerifier` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L164`][r92], `runPrefixChallenges_eq_run` and `appendPrefixSampler_eq_combinePrefixDraw`. P1 removes effectful receiver actions and oracle-payload-dependent challenge selection. The passive sampler may still depend on earlier public challenges and prover messages. |
| RBR-212 | [`ArkLib/Interaction/Oracle/Security/RoundByRound.lean:212`][r93], `FreshVerifier.mapPrefixes` | retired (effectful verifier prefix-map adapter) | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L239`][r94], `appendSampler_eq_combineDraw`. Sampler composition supplies the needed challenge correspondence; the ordinary global rank/escape framework is outside this port. |

## ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean

| ID | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| KR-076 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean:76`][r95], `StageInput` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredResources.lean#L71`][r96], `StageInput`. A full move and later witness, now indexed by statement and prefix. |
| KR-083 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean:83`][r97], `stageMap` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredResources.lean#L77`][r98], `stageMap`. The pure backward step map. |
| KR-091 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean:91`][r99], `extractWitness_public` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredResources.lean#L84`][r100], `extractFrom_eq_stageMap`. Applies at a public-message node. |
| KR-101 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean:101`][r101], `extractWitness_oracle` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredResources.lean#L84`][r102], `extractFrom_eq_stageMap`. Applies at an oracle-message node with its actual payload. |
| KR-111 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean:111`][r103], `MeasuredStages` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredResources.lean#L94`][r104], `MeasuredStages`. Explicit root and leaf identity programs recover the frozen steps. |
| KR-123 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean:123`][r105], `MeasuredStages.BudgetAtMost` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredResources.lean#L115`][r106], `BudgetAtMost`. The frozen bound is BudgetAtMost 0 bound 0 with zero-budget root/leaf identities. |
| KR-136 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean:136`][r107], `MeasuredKnowledgeCertificate` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredResources.lean#L242`][r108], `MeasuredKnowledgeStateFunction`. Standard natural count profiles over a finite kind type, without caller-supplied arithmetic or order. |

## ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean

| ID | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| KRC-037 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean:37`][r109], `MeasuredStages.programAlong` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredResources.lean#L161`][r110], `programAlong`. Composes the same named programs, with explicit root and leaf identities. |
| KRC-051 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean:51`][r111], `MeasuredStages.run_programAlong` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredResources.lean#L167`][r112], `run_programAlong`. Realizes full backward extraction on every supplied terminal witness. |
| KRC-058 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean:58`][r113], `MeasuredStages.programAlong_budget_done` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredResources.lean#L173`][r114], `programFrom_budget_pure`. The frozen leaf is an identity of budget zero; programAlong_budget adds the explicit zero root budget. |
| KRC-064 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean:64`][r115], `MeasuredStages.programAlong_budget_public` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredResources.lean#L179`][r116], `programFrom_budget_liftBind`. Suffix budget plus the public backward step budget. |
| KRC-072 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean:72`][r117], `MeasuredStages.programAlong_budget_oracle` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredResources.lean#L179`][r118], `programFrom_budget_liftBind`. Suffix budget plus the oracle backward step budget. |
| KRC-081 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean:81`][r119], `MeasuredStages.programAlong_budget_le` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredResources.lean#L215`][r120], `programAlong_budget_le_nsmul`. Explicit zero root/leaf bounds recover length times the step bound. |
| KRC-097 | [`ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean:97`][r121], `MeasuredStages.programAlong_costAtMost` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredResources.lean#L229`][r122], `programAlong_costAtMost_nsmul`. The same bound holds for actual instruction paths. |

## ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean

| ID | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| KC-052 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:52`][r123], `middleProblem` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L274`][r124], `MidWitness`. The carrier reads the actual payload; relMid tests the actual challenge. |
| KC-061 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:61`][r125], `firstExtractor` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L295`][r126], `firstState`. Witnesses after the oracle depend on its payload. |
| KC-065 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:65`][r127], `firstSchedule` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L186`][r128], `firstDraw` embeds through `PrefixDraw.ofNodes`, paired with `PrefixError.ofNodes`. The frozen `firstSchedule` already uses `pure true` and error one independently of its payload; P1 requires no change to that schedule. |
| KC-068 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:68`][r129], `firstCertificate` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L561`][r130], `first_rbrKnowledgeSoundness`. The prefix local bound remains one. |
| KC-086 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:86`][r131], `middleEndpoint` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L254`][r132], `firstVerifier_validAcceptance_iff`. True-claim acceptance is exactly the true challenge. |
| KC-097 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:97`][r133], `suffixProtocol` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L47`][r134], `secondProtocol`. A public prover selector chooses public Unit versus oracle Nat. Both challenges remain on each shape. |
| KC-108 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:108`][r135], `suffixExtractor` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L351`][r136], `secondState`. The backward step removes the unit component on both selected shapes. |
| KC-114 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:114`][r137], `suffixSchedule` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L193`][r138], `secondDraw`. Neither suffix shape draws a challenge. |
| KC-120 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:120`][r139], `suffixCertificate` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L572`][r140], `second_rbrKnowledgeSoundness`. Every suffix is certified even at false middle claims. |
| KC-131 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:131`][r141], `secondCertificate` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L572`][r142], `second_rbrKnowledgeSoundness`. The family quantifies every complete prefix transcript. |
| KC-135 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:135`][r143], `compositeCertificate` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L601`][r144], `composed_rbrKnowledgeSoundness`. Relation-level composition plus the explicit oracle acceptance bridge, not a standalone oracle theorem. |
| KC-279 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:279`][r145], `finalProblem` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L277`][r146], `OutWitness`. The payload-dependent finite witness is paired with Unit; validOutput tests the actual closed claim. |
| KC-286 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:286`][r147], `finalClosed` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L112`][r148], `composed_export_eq`. The appended output map exports the actual prefix payload at every payload, challenge and public selector, after either suffix message. |
| KC-292 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:292`][r149], `finalEndpoint` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L511`][r150], `composite_terminal_iff`. Together with terminal assertions following KC-308, identifies the final relation in both directions on both shapes. |
| KC-303 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:303`][r151], `compositeEndpoint` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L491`][r152], `composite_terminalWitness`. The assertions following KC-308 preserve the whole witness and final relation. |
| KC-312 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:312`][r153], `emptyExtractor` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L793`][r154], `emptyState`. No fabricated message or witness is needed. |
| KC-093 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:93`][r155], `example: exported payload` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L99`][r156], `example (n`. Every payload and challenge, independently of selector. |
| KC-095 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:95`][r157], `#eval firstExtractor.extractWitness` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L444`][r158], `firstState.extractAlong stmt₀ (firstPath 7 true true) (⟨6, by decide⟩ : Fin 8)`. The guarded evaluation below the example also returns six. |
| KC-207 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:207`][r159], `example: observed run` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L163`][r160], `theorem observed_eq (choice b`. observed_eq quantifies both selector and challenge, including false challenge. |
| KC-215 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:215`][r161], `#eval observed` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L170`][r162], `observed true true`. Retains the true/public result; an added guarded matrix checks all four runs. |
| KC-219 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:219`][r163], `first_fresh` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L222`][r164], `example (choice`. The prefix sampler draws true at each selector. |
| KC-234 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:234`][r165], `second_fresh` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L229`][r166], `example (p`. The suffix samples no challenge; the actual public Unit or oracle payload five is retained. |
| KC-249 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:249`][r167], `composite_fresh` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L239`][r168], `theorem appendSampler_eq_combineDraw`. appendSampler_eq_combineDraw identifies the composite sampler. |
| KC-268 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:268`][r169], `example: truePath extraction` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L466`][r170], `example`. The universal law above it also quantifies both selector values. |
| KC-271 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:271`][r171], `example: falsePath extraction` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L470`][r172], `example`. The universal law also covers false challenge on the public suffix. |
| KC-274 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:274`][r173], `#eval truePath extraction` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L476`][r174], `compositeState.extractAlong stmt₀ truePath (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit)`. Guarded executable result six. |
| KC-276 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:276`][r175], `#eval falsePath extraction` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L481`][r176], `compositeState.extractAlong stmt₀ falsePath (⟨⟨6, by decide⟩, ()⟩ : Fin 8 × Unit)`. Guarded executable result six. |
| KC-308 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:308`][r177], `example: terminal witness value` | equivalent | [`ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L486`][r178], `example`. Following assertions identify the entire witness by HEq and per-shape equality, and prove exact terminal relation equivalence. |
| KC-316 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:316`][r179], `largeState` | equivalent | [`ArkLibTest/Interaction/Core/UniverseCanary.lean#L454`][r180], `largeTerminalCertificate`. Large input, intermediate, seam and terminal carriers are supported directly. The general API has independent witness universes. |
| KC-318 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:318`][r181], `largeExtractor: higher-universe oracle payload` | equivalent | [`ArkLibTest/Interaction/Core/UniverseCanary.lean#L531`][r182], `largePayloadCertificate`. The general pure certificate receives ULift.{1} Nat in Type 1. Its terminal and post-message carriers are ULift.{2} (Fin (payload.down + 1)), retaining the full payload dependence; the backward map returns the finite witness value as ULift.{2} Nat. |
| KC-322 | [`ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean:322`][r183], `example: large oracle-message extraction` | equivalent | [`ArkLibTest/Interaction/Core/UniverseCanary.lean#L554`][r184], `largePayload_extractAlong`. The ordinary-import client sends the Type 1 payload seven, supplies witness six in ULift.{2} (Fin 8), and proves that pure extraction returns six. |

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
| ME-178 | [`ArkLibTest/OracleReduction/MeasuredExtraction.lean:178`][r205], `zeroStages` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredResources.lean#L129`][r206], `zero`. Root and leaf maps also use zero-instruction programs. |

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
| MP-183 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:183`][r231], `example: ordered result and charge` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L316`][r232], `example (w`. Both additions and the intervening uncharged map execute for every input. |
| MP-186 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:186`][r233], `example: swapped stages rejected` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L320`][r234], `example`. Retains the unequal arithmetic alternative. |
| MP-189 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:189`][r235], `example: omitted middle map rejected` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L324`][r236], `example`. Retains the unequal arithmetic alternative. |
| MP-198 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:198`][r237], `#guard_msgs checkOrderedObservation` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L335`][r238], `#guard_msgs in`. Retains the exact runtime success message. |
| MP-202 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:202`][r239], `#guard_msgs deep cost` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L340`][r240], `#guard_msgs in`. Retains result four and recorded charge four. |
| MP-199 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:199`][r241], `#eval checkOrderedObservation` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L336`][r242], `#eval checkOrderedObservation`. Executable command protected by the separately listed message guard. |
| MP-203 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:203`][r243], `#eval deep cost` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L341`][r244], `#eval deep cost`. Executable command protected by the separately listed message guard. |
| MP-191 | [`ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean:191`][r245], `checkOrderedObservation` | equivalent | [`ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L327`][r246], `checkOrderedObservation`. Tests the same three inputs against result and charge together. |

## Added canaries, audits and remaining work

The canary's `largeTerminalCertificate` and its composition example use a seam carrier in
`Type 1` and a terminal carrier in `Type 1` directly. `largeOutputCertificate` checks both verifier
wrappers at that terminal universe. Lifting raises only the intermediate universe. These are
additional ordinary-import elaboration contracts, not measured programs.

The frozen files in these tables contain no `#print axioms` commands. The replacement composition
and path-budget acceptance files add `run_cmd` collectors using `Lean.collectAxioms`, rejecting
dependencies beyond `propext`, `Classical.choice` and `Quot.sound`. The collectors cover the
extraction-failure theorem, append extraction/terminal laws, relation-level composition, plain
standalone verifier composition, acceptance bridges, fixture equations and both no-global-bound
theorems. The added statement-indexed measured execution returns witness two in `Fin 4`; it is
additional coverage, not a replacement for ME-086.

The restoration disposition is premise-required under P2. Child branch #1483 selects `Fin 8`
versus `Fin 9` by a public prover message, retains the plain replay's payload return on both
challenges and keeps oracle rejection separate. No missing challenge-indexed parent output
interface is asserted. KC-318 and KC-322 are equivalent through the general pure move interface.
Restoration games and the excluded multi-prefix/ordinary global APIs are outside the port claim
above.

The required checks are the targeted reverse-dependency build and guards relative to
`feat/interaction-migrate-core`. They check Core consumers, source restrictions, frozen paths,
imports and documentation. They do not claim a whole-library build or validation.

## Remaining probabilistic move restriction

This restriction affects sampling and probability bounds, not the frozen pure extraction assertions.

| ID | Forcing parent declarations | Status | Exact target and limitation |
| --- | --- | --- | --- |
| PROB-031 | [`ProbComp : Type → Type`, pinned VCVio `Basic.lean:31`](https://github.com/Verified-zkEVM/VCVio/blob/fc54dd3d7691d6f5db7dc829e321a727f095bc2d/VCVio/OracleComp/ProbComp/Basic.lean#L31); [`ArkLib/Interaction/Core/Protocol.lean#L65`][r247], `challengeSpec` (`Core/Protocol.lean:65–67`) | unresolved (large-move probability: `ProbComp` and shared challenge/message universe) | [`ArkLib/Interaction/Core/Security/RoundByRound.lean#L90`][r248], `sampleAt`. `sampleAt`, `BoundedAt`, `LocallyBounded` and round-by-round probability bounds use the small-move instance of the general certificate. `challengeSpec` returns `Move l` in the same universe as oracle/public messages; `ProbComp` cannot sample these moves at `u > 0`. Measured specializations also require small stage inputs through `BudgetedProgram`, as recorded above. |

[r1]: ../../../ArkLib/Interaction/Oracle/Security/Knowledge.lean#L37
[r2]: ../../../ArkLib/Interaction/Core/Security/RoundByRound.lean#L253
[r3]: ../../../ArkLib/Interaction/Oracle/Security/Knowledge.lean#L52
[r4]: ../../../ArkLib/Interaction/Core/Security/RoundByRound.lean#L253
[r5]: ../../../ArkLib/Interaction/Oracle/Security/Knowledge.lean#L74
[r6]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L267
[r7]: ../../../ArkLib/Interaction/Oracle/Security/Knowledge.lean#L82
[r8]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L262
[r9]: ../../../ArkLib/Interaction/Oracle/Security/Knowledge.lean#L202
[r10]: ../../../ArkLib/Interaction/Core/Security/RoundByRound.lean#L253
[r11]: ../../../ArkLib/Interaction/Oracle/Security/Knowledge.lean#L216
[r12]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L305
[r13]: ../../../ArkLib/Interaction/Oracle/Security/Knowledge.lean#L233
[r14]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L313
[r15]: ../../../ArkLib/Interaction/Oracle/Security/Knowledge.lean#L331
[r16]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L361
[r17]: ../../../ArkLib/Interaction/Oracle/Security/Knowledge.lean#L347
[r18]: ../../../ArkLib/Interaction/Core/Security/RoundByRound.lean#L98
[r19]: ../../../ArkLib/Interaction/Oracle/Security/Knowledge.lean#L359
[r20]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1241
[r21]: ../../../ArkLib/Interaction/Oracle/Security/Knowledge.lean#L419
[r22]: ../../../ArkLib/Interaction/Core/Security/RoundByRound.lean#L280
[r23]: ../../../ArkLib/Interaction/Oracle/Security/Knowledge.lean#L433
[r24]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1196
[r25]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean#L33
[r26]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L832
[r27]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean#L48
[r28]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1196
[r29]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean#L66
[r30]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1131
[r31]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean#L88
[r32]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L733
[r33]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean#L111
[r34]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L112
[r35]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean#L130
[r36]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L152
[r37]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L36
[r38]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1196
[r39]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L71
[r40]: ../../../ArkLib/Interaction/Core/Security/RoundByRound.lean#L342
[r41]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L81
[r42]: ../../../ArkLib/Interaction/Core/Composition.lean#L146
[r43]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L102
[r44]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L345
[r45]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L121
[r46]: ../../../ArkLib/Interaction/Core/Security/RoundByRound.lean#L434
[r47]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L131
[r48]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L651
[r49]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L163
[r50]: ../../../ArkLib/Interaction/Core/Composition.lean#L644
[r51]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L191
[r52]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L64
[r53]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L202
[r54]: ../../../ArkLib/Interaction/Core/OracleVerifier.lean#L168
[r55]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L216
[r56]: ../../../ArkLib/Interaction/Core/Composition.lean#L644
[r57]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L249
[r58]: ../../../ArkLib/Interaction/Core/Composition.lean#L644
[r59]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L342
[r60]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L832
[r61]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L377
[r62]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L72
[r63]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L386
[r64]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L284
[r65]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L394
[r66]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1131
[r67]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L426
[r68]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1196
[r69]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L460
[r70]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L511
[r71]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L489
[r72]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition.lean#L305
[r73]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L514
[r74]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L137
[r75]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L548
[r76]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L1233
[r77]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L567
[r78]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L239
[r79]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L625
[r80]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L239
[r81]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L683
[r82]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L239
[r83]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L703
[r84]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L239
[r85]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L726
[r86]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L239
[r87]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L745
[r88]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L137
[r89]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L847
[r90]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L137
[r91]: ../../../ArkLib/Interaction/Oracle/Security/RoundByRound.lean#L168
[r92]: ../../../ArkLib/Interaction/Core/Security/RoundByRound.lean#L164
[r93]: ../../../ArkLib/Interaction/Oracle/Security/RoundByRound.lean#L212
[r94]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L239
[r95]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean#L76
[r96]: ../../../ArkLib/Interaction/Core/Security/MeasuredResources.lean#L76
[r97]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean#L83
[r98]: ../../../ArkLib/Interaction/Core/Security/MeasuredResources.lean#L82
[r99]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean#L91
[r100]: ../../../ArkLib/Interaction/Core/Security/MeasuredResources.lean#L89
[r101]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean#L101
[r102]: ../../../ArkLib/Interaction/Core/Security/MeasuredResources.lean#L89
[r103]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean#L111
[r104]: ../../../ArkLib/Interaction/Core/Security/MeasuredResources.lean#L99
[r105]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean#L123
[r106]: ../../../ArkLib/Interaction/Core/Security/MeasuredResources.lean#L120
[r107]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean#L136
[r108]: ../../../ArkLib/Interaction/Core/Security/MeasuredResources.lean#L247
[r109]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean#L37
[r110]: ../../../ArkLib/Interaction/Core/Security/MeasuredResources.lean#L166
[r111]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean#L51
[r112]: ../../../ArkLib/Interaction/Core/Security/MeasuredResources.lean#L172
[r113]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean#L58
[r114]: ../../../ArkLib/Interaction/Core/Security/MeasuredResources.lean#L178
[r115]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean#L64
[r116]: ../../../ArkLib/Interaction/Core/Security/MeasuredResources.lean#L184
[r117]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean#L72
[r118]: ../../../ArkLib/Interaction/Core/Security/MeasuredResources.lean#L184
[r119]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean#L81
[r120]: ../../../ArkLib/Interaction/Core/Security/MeasuredResources.lean#L220
[r121]: ../../../ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean#L97
[r122]: ../../../ArkLib/Interaction/Core/Security/MeasuredResources.lean#L234
[r123]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L52
[r124]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L274
[r125]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L61
[r126]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L295
[r127]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L65
[r128]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L186
[r129]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L68
[r130]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L561
[r131]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L86
[r132]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L254
[r133]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L97
[r134]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L47
[r135]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L108
[r136]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L351
[r137]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L114
[r138]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L193
[r139]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L120
[r140]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L572
[r141]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L131
[r142]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L572
[r143]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L135
[r144]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L601
[r145]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L279
[r146]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L277
[r147]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L286
[r148]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L112
[r149]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L292
[r150]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L511
[r151]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L303
[r152]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L491
[r153]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L312
[r154]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L793
[r155]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L93
[r156]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L99
[r157]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L95
[r158]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L444
[r159]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L207
[r160]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L163
[r161]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L215
[r162]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L170
[r163]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L219
[r164]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L222
[r165]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L234
[r166]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L229
[r167]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L249
[r168]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L239
[r169]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L268
[r170]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L466
[r171]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L271
[r172]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L470
[r173]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L274
[r174]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L476
[r175]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L276
[r176]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L481
[r177]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L308
[r178]: ../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean#L486
[r179]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L316
[r180]: ../../../ArkLibTest/Interaction/Core/UniverseCanary.lean#L558
[r181]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L318
[r182]: ../../../ArkLibTest/Interaction/Core/UniverseCanary.lean#L635
[r183]: ../../../ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean#L322
[r184]: ../../../ArkLibTest/Interaction/Core/UniverseCanary.lean#L658
[r185]: ../../../ArkLibTest/OracleReduction/MeasuredExtraction.lean#L86
[r186]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L74
[r187]: ../../../ArkLibTest/OracleReduction/MeasuredExtraction.lean#L91
[r188]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L81
[r189]: ../../../ArkLibTest/OracleReduction/MeasuredExtraction.lean#L94
[r190]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L98
[r191]: ../../../ArkLibTest/OracleReduction/MeasuredExtraction.lean#L103
[r192]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L104
[r193]: ../../../ArkLibTest/OracleReduction/MeasuredExtraction.lean#L112
[r194]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L142
[r195]: ../../../ArkLibTest/OracleReduction/MeasuredExtraction.lean#L138
[r196]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L168
[r197]: ../../../ArkLibTest/OracleReduction/MeasuredExtraction.lean#L153
[r198]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L184
[r199]: ../../../ArkLibTest/OracleReduction/MeasuredExtraction.lean#L166
[r200]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L196
[r201]: ../../../ArkLibTest/OracleReduction/MeasuredExtraction.lean#L186
[r202]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L214
[r203]: ../../../ArkLibTest/OracleReduction/MeasuredExtraction.lean#L194
[r204]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean#L221
[r205]: ../../../ArkLibTest/OracleReduction/MeasuredExtraction.lean#L178
[r206]: ../../../ArkLib/Interaction/Core/Security/MeasuredResources.lean#L134
[r207]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L31
[r208]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L34
[r209]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L63
[r210]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L139
[r211]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L71
[r212]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L159
[r213]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L76
[r214]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L175
[r215]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L81
[r216]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L180
[r217]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L90
[r218]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L198
[r219]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L107
[r220]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L219
[r221]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L119
[r222]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L228
[r223]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L137
[r224]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L241
[r225]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L142
[r226]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L248
[r227]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L149
[r228]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L261
[r229]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L152
[r230]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L266
[r231]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L183
[r232]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L316
[r233]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L186
[r234]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L320
[r235]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L189
[r236]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L324
[r237]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L198
[r238]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L335
[r239]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L202
[r240]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L340
[r241]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L199
[r242]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L336
[r243]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L203
[r244]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L341
[r245]: ../../../ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean#L191
[r246]: ../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean#L327
[r247]: ../../../ArkLib/Interaction/Core/Protocol.lean#L66
[r248]: ../../../ArkLib/Interaction/Core/Security/RoundByRound.lean#L90
