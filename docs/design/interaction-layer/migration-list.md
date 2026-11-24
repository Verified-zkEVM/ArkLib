# Migration list: the old interaction layer

This list gives every module and every test file of the old interaction layer one row. Each row
names the file's status, where its content went in the interaction core and which record
justifies that. A reviewer can use it to check that the deletion loses nothing that no record
accounts for. It completes PR D's migration list, which
[record D6](../interaction-rebuild/D6-oracle-access.md) requires: "PR D restates each test of
mid-run access growth for passive verifiers ... or records it as retired with its mechanism".
The [rebuild plan](../interaction-rebuild/README.md) assigns the deletion itself to PR D.

## Scope

The old layer is these files:

- the 42 modules under `ArkLib/Interaction/` outside `Core/`: `Oracle/**`, `Reduction.lean` and
  `CompositionSoundness.lean`;
- the 19 modules under `ArkLib/ProofSystem/Sumcheck/Interaction/`;
- the 32 test files under `ArkLibTest/Interaction/` outside `Core/`;
- the 12 test files under `ArkLibTest/ProofSystem/Sumcheck/Interaction/`;
- two test files outside those directories that import the old layer:
  `ArkLibTest/ProofSystem/Sumcheck/LegacyVerifier.lean` and
  `ArkLibTest/OracleReduction/MeasuredExtraction.lean`.

The legacy `ArkLib/OracleReduction` layer and `ArkLib/Interaction/Core/Legacy` are not part of the
old interaction layer. Both stay, and this list does not cover them.

Four open PRs carry ledgers and core tests that this list cites: #1476 (`port-oracle-bundles.md`),
#1477 (`port-stages.md`), #1478 (`port-oracle-access.md`) and #1567 (a revision of
`port-logged-execution.md`). None of them is on this branch. This list therefore names their ledgers
and code as backticked paths with the PR number. Every ledger path is under
`docs/design/interaction-layer/`, and every core test path is under `ArkLibTest/Interaction/Core/`
unless it says otherwise. PR #1485, which ported composition soundness, is merged and has no
ledger. Its rows are labelled in its core tests.

In the Sumcheck rows, `C/` means `ArkLib/ProofSystem/Sumcheck/Core/` and `T/` means
`ArkLibTest/ProofSystem/Sumcheck/Core/`, as in [sumcheck.md](sumcheck.md).

## Status values

The ledgers use two vocabularies for the same four statuses. The older dispositions say
equivalent, premise-required, retired and unresolved. The port tables say ported, excluded by P1
or P2, removed and open. This list uses one vocabulary:

- **ported:** the core target checks the same mathematical observation. The row names the target.
  Ledger statuses "equivalent" and "ported" map here.
- **retired:** the core removes the mechanism. Every mathematical observation that the mechanism
  carried is covered elsewhere, and the row says where. Ledger statuses "retired" and "removed"
  map here.
- **premise-required:** the assertion changes because of an approved premise, recorded in
  [knowledge-composition-disposition.md](knowledge-composition-disposition.md) and the port tables.
  Ledger statuses "premise-required" and "excluded by P1 (or P2)" map here.
  - **P1 (passivity):** the verifier's only moves before the final decision are challenge draws,
    and every bundle query happens in the final decision. P1 does not require fresh uniform
    challenges.
  - **P2 (shape):** neither a challenge nor an oracle message selects the subtree.
- **moved-upstream:** the content is generic theory that now lives in PolyFun (pin
  `713d8857e49d20927c1447b3ba7397acc5537319`) or VCVio (pin
  `f8d7f8ef52b9afaf4e6d897804b9dce347cdb1db`).
- **unresolved:** a parent interface is missing. The row names it, and
  [Unresolved rows and options](#unresolved-rows-and-options) lists the choices.

A file usually holds rows of several statuses. Its row in this list takes the most restrictive
one, in the order unresolved, premise-required, retired, moved-upstream, ported. The status cell
gives the row counts from the covering record when that record has per-row statuses.

Several generic modules have no declaration-by-declaration record. The port tables of #1476,
#1477, #1478 and #1567 list test assertions, not module declarations. For those modules the
status below comes from the test rows that exercise the module, and the row says so.

## Modules

| Old module | Status | Core target | Covering record |
| --- | --- | --- | --- |
| `ArkLib/Interaction/CompositionSoundness.lean` | ported | [`Core/Security/CompositionSoundness.lean`](../../../ArkLib/Interaction/Core/Security/CompositionSoundness.lean) | PR #1485 (merged, no ledger); the row comments in [the core test](../../../ArkLibTest/Interaction/Core/Security/CompositionSoundness.lean) |
| `ArkLib/Interaction/Reduction.lean` | retired (from its test: 6 ported, 2 retired) | [`Core/Reduction.lean`](../../../ArkLib/Interaction/Core/Reduction.lean) and [`Core/Composition.lean`](../../../ArkLib/Interaction/Core/Composition.lean) | `port-stages.md` (#1477), section Reduction/DependentExample.lean |
| `ArkLib/Interaction/Oracle/Access.lean` | retired | None: per-node access has no replacement. Passive replacements are `pathBundle` in [`Core/OracleVerifier.lean`](../../../ArkLib/Interaction/Core/OracleVerifier.lean) and `IsSent`, `SentOracleMessageIndex` in [`Core/Oracle/SentOracles.lean`](../../../ArkLib/Interaction/Core/Oracle/SentOracles.lean) | [D6](../interaction-rebuild/D6-oracle-access.md), Consequences; `port-oracle-access.md` (#1478), section AccessExample (15 ported, 3 retired) |
| `ArkLib/Interaction/Oracle/Claim.lean` | retired (from its test: 6 ported, 1 retired) | Open and closed claims are removed: a verdict is a statement with concrete data. `Problem` and its admissibility already live in `ArkLib/Relation/Basic.lean` | `port-stages.md` (#1477), section ClaimExample.lean; [D7](../interaction-rebuild/D7-security-definitions.md) for admissibility |
| `ArkLib/Interaction/Oracle/Composition.lean` | unresolved: `run_append` (L258). Also 2 ported, 8 premise-required (P1, two of them also P2), 4 retired | `OracleVerifier.append` and `run_append` in [`Core/Composition.lean`](../../../ArkLib/Interaction/Core/Composition.lean); `ArkLib/Interaction/Core/StageChain.lean` (#1477) | `port-stages.md` (#1477), section Oracle/Composition.lean |
| `ArkLib/Interaction/Oracle/CompositionSoundness.lean` | ported | [`Core/Security/CompositionSoundness.lean`](../../../ArkLib/Interaction/Core/Security/CompositionSoundness.lean) | PR #1485; "Oracle example row" comments in [the core test](../../../ArkLibTest/Interaction/Core/Security/CompositionSoundness.lean) |
| `ArkLib/Interaction/Oracle/CoreRun.lean` | premise-required (P1), from its test: 7 ported, 1 P1, 2 retired | `OracleVerifier.run` and the output map in [`Core/OracleVerifier.lean`](../../../ArkLib/Interaction/Core/OracleVerifier.lean) | `port-stages.md` (#1477), section CoreRunExample.lean |
| `ArkLib/Interaction/Oracle/Execution.lean` | premise-required (P1, P2), from its test: 12 ported, 10 P1, 3 P1 and P2, 4 retired | [`Core/Execution.lean`](../../../ArkLib/Interaction/Core/Execution.lean) and [`Core/OracleVerifier.lean`](../../../ArkLib/Interaction/Core/OracleVerifier.lean); the per-node `localSyntax` is retired | `port-stages.md` (#1477), section ExecutionExample.lean; [D6](../interaction-rebuild/D6-oracle-access.md), Why |
| `ArkLib/Interaction/Oracle/LoggedExecution.lean` | premise-required (P1) | [`Core/Oracle/LoggedExecution.lean`](../../../ArkLib/Interaction/Core/Oracle/LoggedExecution.lean), [`Core/Oracle/QueriesByMove.lean`](../../../ArkLib/Interaction/Core/Oracle/QueriesByMove.lean), [`Core/Oracle/QueriesByMoveLaws.lean`](../../../ArkLib/Interaction/Core/Oracle/QueriesByMoveLaws.lean) | [port-logged-execution.md](port-logged-execution.md) (revised by #1567); [departures.md](departures.md), entry 19 |
| `ArkLib/Interaction/Oracle/LoggedRun.lean` | ported (from LoggedExecutionExample rows) | `runWithLog` in [`Core/Security/Knowledge.lean`](../../../ArkLib/Interaction/Core/Security/Knowledge.lean) and its erasure laws in [`Core/Oracle/LoggedExecution.lean`](../../../ArkLib/Interaction/Core/Oracle/LoggedExecution.lean) | [port-logged-execution.md](port-logged-execution.md) |
| `ArkLib/Interaction/Oracle/PhasedExecution.lean` | retired | None: world-query segments per node are gone. Per-move logs come from [`Core/Oracle/QueriesByMove.lean`](../../../ArkLib/Interaction/Core/Oracle/QueriesByMove.lean) | [D6](../interaction-rebuild/D6-oracle-access.md), Alternatives ("phased execution"); PhasedRun rows of [port-logged-execution.md](port-logged-execution.md) |
| `ArkLib/Interaction/Oracle/PhasedRun.lean` | premise-required (P1) | [`Core/Oracle/QueriesByMove.lean`](../../../ArkLib/Interaction/Core/Oracle/QueriesByMove.lean), [`Core/Oracle/LoggedExecution.lean`](../../../ArkLib/Interaction/Core/Oracle/LoggedExecution.lean) | [port-logged-execution.md](port-logged-execution.md), section PhasedRun.lean; `port-oracle-access.md` (#1478), section PhasedRun |
| `ArkLib/Interaction/Oracle/Prefix.lean` | ported (all 8 Prefix test rows) | `PartialTranscript` and `IsSent.mono` in [`Core/Oracle/SentOracles.lean`](../../../ArkLib/Interaction/Core/Oracle/SentOracles.lean) | `port-oracle-access.md` (#1478), section Prefix |
| `ArkLib/Interaction/Oracle/Protocol.lean` | ported | `OracleProtocol` in [`Core/Protocol.lean`](../../../ArkLib/Interaction/Core/Protocol.lean). Ownership comes from the signature instead of a role decoration | `port-oracle-access.md` (#1478), sections DecorationExample and MixedExample |
| `ArkLib/Interaction/Oracle/Resource.lean` | unresolved: `OracleModel.satisfies_guarantee` has no core counterpart. From its test: 21 ported, 7 retired | `OracleBundle` in [`Core/OracleVerifier.lean`](../../../ArkLib/Interaction/Core/OracleVerifier.lean); `ArkLib/Interaction/Core/Oracle/BundleOps.lean` (#1476). Named contexts and property-symbol languages are retired | `port-oracle-bundles.md` (#1476), sections ResourceExample and Representation changes; [sumcheck.md](sumcheck.md), Remaining work |
| `ArkLib/Interaction/Oracle/RunSources.lean` | ported (all 12 RunSourcesExample rows) | `pathBundle` in [`Core/OracleVerifier.lean`](../../../ArkLib/Interaction/Core/OracleVerifier.lean); `ArkLib/Interaction/Core/Oracle/BundleOps.lean` (#1476) | `port-oracle-bundles.md` (#1476), section RunSourcesExample |
| `ArkLib/Interaction/Oracle/Runtime.lean` | ported | A persistent runtime is any lawful interpreter of the logged run: `simulateQ_toLog_runWithQueriesByMove` in [`Core/Oracle/QueriesByMoveLaws.lean`](../../../ArkLib/Interaction/Core/Oracle/QueriesByMoveLaws.lean) | [port-logged-execution.md](port-logged-execution.md), sections RuntimeExample.lean and Persistent-runtime tests |
| `ArkLib/Interaction/Oracle/RuntimeSoundness.lean` | premise-required (P1): the informed prover's reveal now precedes the dummy request | [`Core/Security/CompositionSoundness.lean`](../../../ArkLib/Interaction/Core/Security/CompositionSoundness.lean) | PR #1485; the port comments in [the core runtime soundness test](../../../ArkLibTest/Interaction/Core/Security/RuntimeSoundness.lean) |
| `ArkLib/Interaction/Oracle/Security/Knowledge.lean` | premise-required: 9 ported, 2 premise-required, 1 retired | [`Core/Security/RoundByRound.lean`](../../../ArkLib/Interaction/Core/Security/RoundByRound.lean), [`Core/Security/KnowledgeComposition/Extraction.lean`](../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean) | [knowledge-composition-disposition.md](knowledge-composition-disposition.md), rows K-* |
| `ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean` | premise-required: 5 ported, 1 premise-required | [`Core/Security/KnowledgeComposition.lean`](../../../ArkLib/Interaction/Core/Security/KnowledgeComposition.lean) | [knowledge-composition-disposition.md](knowledge-composition-disposition.md), rows KA-* |
| `ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean` | premise-required: 10 ported, 10 premise-required, 7 retired | [`Core/Security/KnowledgeComposition.lean`](../../../ArkLib/Interaction/Core/Security/KnowledgeComposition.lean), [`Core/Security/KnowledgeComposition/Extraction.lean`](../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean) | [knowledge-composition-disposition.md](knowledge-composition-disposition.md), rows KCO-* |
| `ArkLib/Interaction/Oracle/Security/KnowledgeResources.lean` | ported (7 rows) | [`Core/Security/MeasuredExtraction.lean`](../../../ArkLib/Interaction/Core/Security/MeasuredExtraction.lean) | [knowledge-composition-disposition.md](knowledge-composition-disposition.md), rows KR-* |
| `ArkLib/Interaction/Oracle/Security/KnowledgeResources/Composition.lean` | ported (7 rows) | [`Core/Security/MeasuredExtraction.lean`](../../../ArkLib/Interaction/Core/Security/MeasuredExtraction.lean) | [knowledge-composition-disposition.md](knowledge-composition-disposition.md), rows KRC-* |
| `ArkLib/Interaction/Oracle/Security/RoundByRound.lean` | premise-required: R1–R4 give 1 ported, 3 premise-required; RBR-168 is premise-required (P1) and RBR-212 is retired | [`Core/Security/Implications.lean`](../../../ArkLib/Interaction/Core/Security/Implications.lean), [`Core/Security/RoundByRound.lean`](../../../ArkLib/Interaction/Core/Security/RoundByRound.lean) | [soundness-implication-disposition.md](soundness-implication-disposition.md), rows R1–R4; [knowledge-composition-disposition.md](knowledge-composition-disposition.md), rows RBR-168 and RBR-212 |
| `ArkLib/Interaction/Oracle/Security/Soundness.lean` | premise-required: S1–S4 give 1 ported, 3 premise-required | [`Core/Security/Implications.lean`](../../../ArkLib/Interaction/Core/Security/Implications.lean) | [soundness-implication-disposition.md](soundness-implication-disposition.md), rows S1–S4 |
| `ArkLib/Interaction/Oracle/Security/StateRestoration.lean` | premise-required: 30 ported, 1 premise-required, 5 retired | [`Core/Security/StateRestoration.lean`](../../../ArkLib/Interaction/Core/Security/StateRestoration.lean) | [state-restoration-disposition.md](state-restoration-disposition.md) |
| `ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean` | premise-required: 9 ported, 2 premise-required, 2 retired | [`Core/Security/StateRestorationBudget.lean`](../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean) | [state-restoration-disposition.md](state-restoration-disposition.md) |
| `ArkLib/Interaction/Oracle/Security/StateRestorationCoins.lean` | premise-required: 2 premise-required | [`Core/Security/StateRestoration.lean`](../../../ArkLib/Interaction/Core/Security/StateRestoration.lean) | [state-restoration-disposition.md](state-restoration-disposition.md) |
| `ArkLib/Interaction/Oracle/Security/StateRestorationGame.lean` | premise-required: 4 premise-required, 1 retired | [`Core/Security/StateRestoration.lean`](../../../ArkLib/Interaction/Core/Security/StateRestoration.lean) | [state-restoration-disposition.md](state-restoration-disposition.md) |
| `ArkLib/Interaction/Oracle/Security/StateRestorationOracle.lean` | premise-required: 4 premise-required, 1 retired | [`Core/Security/StateRestoration.lean`](../../../ArkLib/Interaction/Core/Security/StateRestoration.lean) | [state-restoration-disposition.md](state-restoration-disposition.md) |
| `ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean` | premise-required: 4 ported, 9 premise-required, 6 retired | [`Core/Security/StateRestoration.lean`](../../../ArkLib/Interaction/Core/Security/StateRestoration.lean) | [state-restoration-disposition.md](state-restoration-disposition.md) |
| `ArkLib/Interaction/Oracle/Security/StateRestorationResources.lean` | premise-required: 5 ported, 1 premise-required | [`Core/Security/StateRestorationBudget.lean`](../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean), [`Core/Security/MeasuredExtraction.lean`](../../../ArkLib/Interaction/Core/Security/MeasuredExtraction.lean) | [state-restoration-disposition.md](state-restoration-disposition.md) |
| `ArkLib/Interaction/Oracle/Sequential.lean` | premise-required (P1, P2): its fragments run each verifier to a decision before the next stage | `OracleVerifier.append` in [`Core/Composition.lean`](../../../ArkLib/Interaction/Core/Composition.lean); `ArkLib/Interaction/Core/StageChain.lean` (#1477) | No module ledger. ExecutionExample rows of `port-stages.md` (#1477); [D5](../interaction-rebuild/D5-composition.md); Sumcheck clients in [sumcheck.md](sumcheck.md), production section Sequential |
| `ArkLib/Interaction/Oracle/Source.lean` | ported (all 18 SourceExample rows) | `OracleMap` in [`Core/OracleVerifier.lean`](../../../ArkLib/Interaction/Core/OracleVerifier.lean); `ArkLib/Interaction/Core/Oracle/BundleOps.lean` (#1476) | `port-oracle-bundles.md` (#1476), section SourceExample |
| `ArkLib/Interaction/Oracle/SourceRouting.lean` | premise-required (P1) | [`Core/Oracle/Routing.lean`](../../../ArkLib/Interaction/Core/Oracle/Routing.lean) | [port-logged-execution.md](port-logged-execution.md), section SourceRoutingExample.lean; `port-oracle-bundles.md` (#1476), section SourceRoutingExample; [D6](../interaction-rebuild/D6-oracle-access.md) on `appendExported` |
| `ArkLib/Interaction/Oracle/Terminal.lean` | retired | None: a core verdict is an `Option`, and a handler failure keeps its label through `decideCatching` in [`Core/Oracle/LoggedExecution.lean`](../../../ArkLib/Interaction/Core/Oracle/LoggedExecution.lean) | `port-oracle-bundles.md` (#1476), section Representation changes; the Terminal/Examples row in [Tests](#tests) |
| `ArkLib/Interaction/Oracle/TerminalMeasure.lean` | retired | None: the core keeps missing runtime mass separate from rejection instead of decoding it as a named fault | No module ledger and no old test imports it. [soundness-implication-disposition.md](soundness-implication-disposition.md), row T2; [D7](../interaction-rebuild/D7-security-definitions.md) |
| `ArkLib/Interaction/Oracle/TerminalRun.lean` | premise-required (P1) | `decideCatching` in [`Core/Oracle/LoggedExecution.lean`](../../../ArkLib/Interaction/Core/Oracle/LoggedExecution.lean) | [port-logged-execution.md](port-logged-execution.md), section TerminalRun/Examples.lean (revised by #1567); `port-oracle-bundles.md` (#1476), section TerminalRun/Examples |
| `ArkLib/Interaction/Oracle/TypeTree.lean` | ported (all 9 MixedExample rows) | `oracleSig` and `OraclePos` in [`Core/Signature.lean`](../../../ArkLib/Interaction/Core/Signature.lean); `OracleProtocol` in [`Core/Protocol.lean`](../../../ArkLib/Interaction/Core/Protocol.lean) | `port-oracle-access.md` (#1478), section MixedExample |
| `ArkLib/Interaction/Oracle/TypeTree/Decoration.lean` | premise-required (P2), from its test: 8 ported, 1 P2, 4 retired | Role decorations are retired: ownership is read from the signature, and oracle interfaces sit in positions | `port-oracle-access.md` (#1478), section DecorationExample; [port-bundle-universes.md](port-bundle-universes.md) for the decoration canaries |
| `ArkLib/Interaction/Oracle/Virtual.lean` | ported (all 3 Virtual rows) | `OracleMap` in [`Core/OracleVerifier.lean`](../../../ArkLib/Interaction/Core/OracleVerifier.lean) | `port-oracle-bundles.md` (#1476), section Virtual; [D6](../interaction-rebuild/D6-oracle-access.md), Alternatives |
| `ArkLib/Interaction/Oracle/WorldSegments.lean` | retired | None: world segments exist only for mid-run verifier queries. Per-move logs come from [`Core/Oracle/QueriesByMove.lean`](../../../ArkLib/Interaction/Core/Oracle/QueriesByMove.lean) | No module ledger and no old test imports it directly. [D6](../interaction-rebuild/D6-oracle-access.md), Alternatives ("world segments") |
| `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryCompleteness.lean` | ported: 5 ported | `C/IntervalCompleteness` | [sumcheck.md](sumcheck.md), production inventory |
| `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean` | premise-required: 7 ported, 6 premise-required | `C/Behavior`, `C/FoldComposition`, `C/Interval`, `C/IntervalCompleteness` | [sumcheck.md](sumcheck.md), production inventory |
| `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean` | unresolved: `degreeModel` (L40) and `degreeGuarantee` (L53). Also 20 ported, 4 premise-required, 1 retired | `C/Domain`, `C/Indexed` | [sumcheck.md](sumcheck.md), production inventory and Remaining work |
| `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean` | premise-required: 10 premise-required, 4 retired | `C/BehaviorComposition`, `C/Indexed` | [sumcheck.md](sumcheck.md), production inventory |
| `ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean` | premise-required: 2 ported, 5 premise-required | `C/Domain`, `C/InterpretedExecution`, `C/Types` | [sumcheck.md](sumcheck.md), production inventory |
| `ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean` | premise-required: 5 premise-required | `C/ComputableInterval` | [sumcheck.md](sumcheck.md), production inventory |
| `ArkLib/ProofSystem/Sumcheck/Interaction/ComputableSoundness.lean` | premise-required: 1 premise-required | `C/ComputableSoundness` | [sumcheck.md](sumcheck.md), production inventory |
| `ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean` | retired: 7 ported, 1 retired | `C/Domain`, `C/Indexed`, `C/LegacyEquivalence` | [sumcheck.md](sumcheck.md), production inventory |
| `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean` | premise-required: 9 ported, 13 premise-required | `C/Behavior`, `C/Fold`, `C/Interpreted`, `C/Interval`, `C/IntervalCompleteness`, `C/IntervalRoundSoundness` | [sumcheck.md](sumcheck.md), production inventory |
| `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateSoundness.lean` | premise-required: 4 ported, 1 premise-required, 1 retired | `C/Behavior`, `C/Domain`, `C/DomainEquivalence`, `C/IntervalRoundSoundness` | [sumcheck.md](sumcheck.md), production inventory |
| `ArkLib/ProofSystem/Sumcheck/Interaction/Projection.lean` | ported: 6 ported | `C/Projection` | [sumcheck.md](sumcheck.md), production inventory |
| `ArkLib/ProofSystem/Sumcheck/Interaction/ProjectionTransport.lean` | ported: 1 ported | `C/Projection` | [sumcheck.md](sumcheck.md), production inventory |
| `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean` | premise-required: 13 ported, 20 premise-required | `C/Behavior`, `C/Domain`, `C/Interpreted`, `C/InterpretedExecution`, `C/InterpretedPath`, `C/MessageTree`, `C/Protocol`, `C/Types` | [sumcheck.md](sumcheck.md), production inventory |
| `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolCompleteness.lean` | premise-required: 3 premise-required | `C/IntervalCompleteness` | [sumcheck.md](sumcheck.md), production inventory |
| `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean` | premise-required: 1 ported, 5 premise-required | `C/Indexed`, `C/IntervalSoundness` | [sumcheck.md](sumcheck.md), production inventory |
| `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean` | premise-required: 3 premise-required, 38 retired | `C/Indexed`, `C/IntervalSoundness` | [sumcheck.md](sumcheck.md), production inventory |
| `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean` | premise-required: 2 ported, 7 premise-required | `C/FoldComposition`, `C/IntervalCompleteness` | [sumcheck.md](sumcheck.md), production inventory |
| `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean` | premise-required: 13 ported, 4 premise-required | `C/Domain`, `C/Indexed`, `C/SingleRound`, `C/Types` | [sumcheck.md](sumcheck.md), production inventory |
| `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean` | retired: 10 ported, 2 retired | `C/Domain`, `C/Indexed`, `C/Soundness` | [sumcheck.md](sumcheck.md), production inventory |

## Tests

| Old test file | Status | Core test or target | Covering record |
| --- | --- | --- | --- |
| `ArkLibTest/Interaction/CompositionExecution.lean` | moved-upstream | PolyFun `PolyFunTest/Interaction/TwoParty/Lens/CompositionExecution.lean` at pin `713d8857`. Both examples, with outputs `((8,7), trace)` and `((12,11), trace)`, appear there unchanged (around lines 165–230) | [D1](../interaction-rebuild/D1-signatures-and-shape.md), Consequences |
| `ArkLibTest/Interaction/CompositionSoundness.lean` | ported (14 theorems) | Rows 1–14 of [`Core/Security/CompositionSoundness.lean`](../../../ArkLibTest/Interaction/Core/Security/CompositionSoundness.lean) | PR #1485; row comments in the core test |
| `ArkLibTest/Interaction/Oracle/ClaimExample.lean` | retired: 6 ported, 1 retired | `Oracle/AnswerOnlyRelations.lean` (#1477) | `port-stages.md` (#1477) |
| `ArkLibTest/Interaction/Oracle/CompositionExample.lean` | premise-required (P1): 8 ported, 4 P1, 2 retired | `Oracle/HeterogeneousAppend.lean`, `Oracle/StageChain.lean` (#1477) | `port-stages.md` (#1477) |
| `ArkLibTest/Interaction/Oracle/CompositionSoundnessExample.lean` | ported (15 theorems) | "Oracle example row" 1–15 of [`Core/Security/CompositionSoundness.lean`](../../../ArkLibTest/Interaction/Core/Security/CompositionSoundness.lean) | PR #1485; row comments in the core test |
| `ArkLibTest/Interaction/Oracle/CoreRunExample.lean` | premise-required (P1): 7 ported, 1 P1, 2 retired | `Oracle/OutputClosing.lean` (#1477); [`Core/Oracle/LoggedExecution.lean`](../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean) | `port-stages.md` (#1477) |
| `ArkLibTest/Interaction/Oracle/ExecutionExample.lean` | premise-required (P1, P2): 12 ported, 10 P1, 3 P1 and P2, 4 retired | `Oracle/PassiveExecution.lean` (#1477); [`Core/Oracle/LoggedExecution.lean`](../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean) | `port-stages.md` (#1477) |
| `ArkLibTest/Interaction/Oracle/LoggedExecutionExample.lean` | premise-required (P1): 7 ported, 2 P1 | [`Core/Oracle/LoggedExecution.lean`](../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean) | [port-logged-execution.md](port-logged-execution.md) |
| `ArkLibTest/Interaction/Oracle/NativeRuntime.lean` | ported: 10 ported | [`Core/Oracle/LoggedExecution.lean`](../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean) | [port-logged-execution.md](port-logged-execution.md), section Persistent-runtime tests |
| `ArkLibTest/Interaction/Oracle/PhasedRun.lean` | premise-required (P1). Logged table: 11 ported, 2 P1 on this branch; 10 ported, 2 P1, 1 retired after #1567. Access table: 4 ported, 2 P1, 1 retired | [`Core/Oracle/LoggedExecution.lean`](../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean); `Oracle/HiddenSendRun.lean` (#1478) | [port-logged-execution.md](port-logged-execution.md); `port-oracle-access.md` (#1478) |
| `ArkLibTest/Interaction/Oracle/Prefix.lean` | ported: 8 ported | `Oracle/PartialTranscripts.lean` (#1478) | `port-oracle-access.md` (#1478) |
| `ArkLibTest/Interaction/Oracle/QueryBounds.lean` | ported: 18 ported (logged table), 17 ported (access table) | [`Core/Oracle/LoggedExecution.lean`](../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean); `Oracle/QueryCost.lean`, `Oracle/RoutedAccess.lean` (#1478) | [port-logged-execution.md](port-logged-execution.md); `port-oracle-access.md` (#1478) |
| `ArkLibTest/Interaction/Oracle/ResourceExample.lean` | retired: 21 ported, 7 retired (named-context and property-symbol mechanisms) | `Oracle/BundleFamilies.lean` (#1476); R26 and R27 in [`Core/UniverseCanary.lean`](../../../ArkLibTest/Interaction/Core/UniverseCanary.lean) | `port-oracle-bundles.md` (#1476); [port-bundle-universes.md](port-bundle-universes.md) |
| `ArkLibTest/Interaction/Oracle/RunSourcesExample.lean` | ported: 12 ported | `Oracle/RunBundles.lean` (#1476) | `port-oracle-bundles.md` (#1476) |
| `ArkLibTest/Interaction/Oracle/RuntimeExample.lean` | ported: 2 ported | [`Core/Oracle/LoggedExecution.lean`](../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean) | [port-logged-execution.md](port-logged-execution.md) |
| `ArkLibTest/Interaction/Oracle/RuntimeQueryBounds.lean` | premise-required (P1). Logged table: 15 ported, 3 P1 on this branch, 4 P1 after #1567. Access table: 14 ported, 4 P1 | [`Core/Oracle/LoggedExecution.lean`](../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean); `Oracle/HiddenBitAccess.lean`, `Oracle/QueryCost.lean` (#1478); rows 12, 16 and 17 also in [`Core/Security/RuntimeSoundness.lean`](../../../ArkLibTest/Interaction/Core/Security/RuntimeSoundness.lean) | [port-logged-execution.md](port-logged-execution.md); `port-oracle-access.md` (#1478); PR #1485 |
| `ArkLibTest/Interaction/Oracle/RuntimeSoundness.lean` | premise-required (P1): 22 rows (20 lemmas, 2 examples); the informed prover's reveal now precedes the dummy request | [`Core/Security/RuntimeSoundness.lean`](../../../ArkLibTest/Interaction/Core/Security/RuntimeSoundness.lean) | PR #1485; row comments in the core test |
| `ArkLibTest/Interaction/Oracle/Security/KnowledgeComposition.lean` | premise-required: 30 ported, 1 premise-required | [`Core/Security/KnowledgeComposition.lean`](../../../ArkLibTest/Interaction/Core/Security/KnowledgeComposition.lean) | [knowledge-composition-disposition.md](knowledge-composition-disposition.md), rows KC-* |
| `ArkLibTest/Interaction/Oracle/Security/MeasuredPathBudgets.lean` | ported: 20 ported | [`Core/Security/MeasuredPathBudgets.lean`](../../../ArkLibTest/Interaction/Core/Security/MeasuredPathBudgets.lean) | [knowledge-composition-disposition.md](knowledge-composition-disposition.md), rows MP-* |
| `ArkLibTest/Interaction/Oracle/Security/Soundness.lean` | premise-required: T1–T6 give 3 ported, 3 premise-required | [`Core/Security/Implications.lean`](../../../ArkLibTest/Interaction/Core/Security/Implications.lean) | [soundness-implication-disposition.md](soundness-implication-disposition.md), rows T1–T6 |
| `ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean` | premise-required: 6 ported, 15 premise-required | [`Core/Security/StateRestoration.lean`](../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean) | [state-restoration-disposition.md](state-restoration-disposition.md), rows SRT-* |
| `ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean` | premise-required: 30 ported, 8 premise-required | [`Core/Security/StateRestorationBudget.lean`](../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean) | [state-restoration-disposition.md](state-restoration-disposition.md), rows SRBT-* |
| `ArkLibTest/Interaction/Oracle/SourceExample.lean` | ported: 18 ported | `Oracle/OracleMaps.lean` (#1476) | `port-oracle-bundles.md` (#1476) |
| `ArkLibTest/Interaction/Oracle/SourceRoutingDependentExample.lean` | premise-required (P1): the prover now sends the Boolean, because a passive verifier sends no messages. The `#check` of `executeStrategies_appendExported_close` is retired with its mechanism | [`Core/Oracle/DependentRouting.lean`](../../../ArkLibTest/Interaction/Core/Oracle/DependentRouting.lean), with the same observations `(true, 13, some (0, 0))` and `(false, 29, some (7, 7))` | [D6](../interaction-rebuild/D6-oracle-access.md), Open points; [IMPLEMENTATION-NOTES.md](../interaction-rebuild/IMPLEMENTATION-NOTES.md), "Verifier outputs are indexed by the shape path" |
| `ArkLibTest/Interaction/Oracle/SourceRoutingExample.lean` | premise-required (P1). Logged table: 5 ported, 2 P1. Bundles table: 3 ported | [`Core/Oracle/Routing.lean`](../../../ArkLibTest/Interaction/Core/Oracle/Routing.lean); `Oracle/ExportCost.lean` (#1476) | [port-logged-execution.md](port-logged-execution.md); `port-oracle-bundles.md` (#1476) |
| `ArkLibTest/Interaction/Oracle/Terminal/Examples.lean` | retired: the `Terminal`, `.fault` and `decodeRuntime` mechanism is gone. Three of its four cases are covered; the fourth has no core test (see below) | `decision_outcomes` and `close_optional_ok` in [`Core/Oracle/LoggedExecution.lean`](../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean) | None. This list is its only record |
| `ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean` | premise-required (P1). Logged table: 9 ported, 1 P1 on this branch; 7 ported, 1 P1, 2 retired after #1567. Bundles table: 7 ported, 2 retired | [`Core/Oracle/LoggedExecution.lean`](../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean) | [port-logged-execution.md](port-logged-execution.md) (revised by #1567); `port-oracle-bundles.md` (#1476) |
| `ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean` | retired: 15 ported, 3 retired | `Oracle/ProtocolTree/AccessTyping.lean` (#1478) | `port-oracle-access.md` (#1478) |
| `ArkLibTest/Interaction/Oracle/TypeTree/DecorationExample.lean` | premise-required (P2): 8 ported, 1 P2, 4 retired | `Oracle/ProtocolTree/PositionsAndOwners.lean` (#1478); decoration canaries in [`Core/UniverseCanary.lean`](../../../ArkLibTest/Interaction/Core/UniverseCanary.lean) | `port-oracle-access.md` (#1478); [port-bundle-universes.md](port-bundle-universes.md) |
| `ArkLibTest/Interaction/Oracle/TypeTree/MixedExample.lean` | ported: 9 ported | `Oracle/ProtocolTree/MixedTranscripts.lean` (#1478) | `port-oracle-access.md` (#1478) |
| `ArkLibTest/Interaction/Oracle/Virtual.lean` | ported: 3 ported | `Oracle/DerivedOracles.lean` (#1476) | `port-oracle-bundles.md` (#1476) |
| `ArkLibTest/Interaction/Reduction/DependentExample.lean` | retired: 6 ported, 2 retired | `Reduction/DependentAppend.lean` (#1477) | `port-stages.md` (#1477) |
| `ArkLibTest/ProofSystem/Sumcheck/Interaction/ArbitraryCompleteness.lean` | ported: 4 ported | `C/IntervalCompleteness` | [sumcheck.md](sumcheck.md), Migration disposition |
| `ArkLibTest/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean` | premise-required: 3 ported, 3 premise-required | `T/Effects`, `T/Rounds`; `C/Behavior`, `C/IntervalCompleteness` | [sumcheck.md](sumcheck.md), Migration disposition |
| `ArkLibTest/ProofSystem/Sumcheck/Interaction/Closing.lean` | ported: 9 ported | `T/Domain`, `T/SingleRound`; `C/Indexed` | [sumcheck.md](sumcheck.md), Migration disposition |
| `ArkLibTest/ProofSystem/Sumcheck/Interaction/Legacy.lean` | ported: 2 ported | `T/Soundness`; `C/LegacyEquivalence` | [sumcheck.md](sumcheck.md), Migration disposition |
| `ArkLibTest/ProofSystem/Sumcheck/Interaction/Projection.lean` | ported: 8 ported | `T/Rounds`; `C/Projection` | [sumcheck.md](sumcheck.md), Migration disposition |
| `ArkLibTest/ProofSystem/Sumcheck/Interaction/ProjectionTransport.lean` | ported: 3 ported | `T/Rounds`; `C/Projection` | [sumcheck.md](sumcheck.md), Migration disposition |
| `ArkLibTest/ProofSystem/Sumcheck/Interaction/Protocol.lean` | premise-required: 2 ported, 8 premise-required | `T/Completeness`, `T/Effects`, `T/Interval`; `C/Completeness`, `C/FoldComposition`, `C/Indexed`, `C/Soundness` | [sumcheck.md](sumcheck.md), Migration disposition |
| `ArkLibTest/ProofSystem/Sumcheck/Interaction/RoundByRound.lean` | premise-required: 1 premise-required | `C/Indexed`, `C/Soundness` | [sumcheck.md](sumcheck.md), Migration disposition |
| `ArkLibTest/ProofSystem/Sumcheck/Interaction/Sequential.lean` | premise-required: 3 ported, 3 premise-required | `T/Rounds`; `C/IntervalCompleteness` | [sumcheck.md](sumcheck.md), Migration disposition |
| `ArkLibTest/ProofSystem/Sumcheck/Interaction/SingleRound.lean` | ported: 6 ported | `T/Domain`, `T/SingleRound`; `C/Indexed` | [sumcheck.md](sumcheck.md), Migration disposition |
| `ArkLibTest/ProofSystem/Sumcheck/Interaction/Soundness.lean` | ported: 28 ported | `T/SingleRound`, `T/Soundness`; `C/Indexed`, `C/Soundness` | [sumcheck.md](sumcheck.md), Migration disposition |
| `ArkLibTest/ProofSystem/Sumcheck/Interaction/SourceRouting.lean` | premise-required: 5 ported, 1 premise-required, 1 retired | `T/Effects`, `T/Routing`; `C/Tree` | [sumcheck.md](sumcheck.md), Migration disposition |
| `ArkLibTest/ProofSystem/Sumcheck/LegacyVerifier.lean` | ported (rows #3–#11 have bridge versions). The file stays: rows #1, #2, #12 and #13 test the legacy verifier itself | `T/LegacyVerifier` | [sumcheck.md](sumcheck.md), "B and the kept legacy regressions" |
| `ArkLibTest/OracleReduction/MeasuredExtraction.lean` | ported (rows ME-086 to ME-194, 11 rows). The file stays: its Search section tests the legacy layer | [`Core/Security/MeasuredExtraction.lean`](../../../ArkLibTest/Interaction/Core/Security/MeasuredExtraction.lean) | [knowledge-composition-disposition.md](knowledge-composition-disposition.md), rows ME-* |

`Terminal/Examples.lean` checks four cases of `Terminal.decodeRuntime 9`: an accepted claim, a
rejection, a model fault 3, and missing runtime mass decoded as the caller's fault 9. In
`ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean`, `decision_outcomes` distinguishes
handler failures (labels 17 and 23), rejection and acceptance, and `close_optional_ok` maps only
accepted claims. No core test covers the fourth case, because the core does not decode missing
runtime mass as a fault: it keeps missing mass distinct from rejection, as row T2 of
[soundness-implication-disposition.md](soundness-implication-disposition.md) shows with
`EmptyResponse.run_mass`. This list records the fourth case as retired with `TerminalMeasure`.

## Unresolved rows and options

Five items stay open. The first three are restrictions of the core port that the ledgers record
without tying them to one old declaration. The last two are old declarations with no core target.

**1. The full-log runner cannot return large query indices.**
[departures.md](departures.md) lists this as an unresolved entry 18, and `port-oracle-access.md`
(#1478) lists it as its only open item. `OracleVerifier.runWithLog` returns bundle-query entries
through a small computation monad. Its complete log therefore cannot record large query indices.
`runWithAmbientLog` and `runWithAmbientQueriesByMove` keep independent universes because they
return only ambient decision queries. What is missing is a parent logging interface whose result
universe is large enough. Options:

- implement that logging interface in VCVio or PolyFun and generalize `runWithLog`;
- accept the restriction as an upstream limit and document it at `runWithLog`, pointing to the
  ambient-log runners for large indices;
- retire the full-log runner in favor of the ambient-log runners.

Decision: open.

**2. PROB-031: probability bounds use small moves only.**
Row PROB-031 of [knowledge-composition-disposition.md](knowledge-composition-disposition.md)
records it. Pinned VCVio defines `ProbComp : Type → Type` (`VCVio/OracleComp/ProbComp/Basic.lean`,
line 31), and `challengeSpec` (`Core/Protocol.lean`, lines 69–71) returns a move in the universe
that challenges share with public and oracle messages. As a result, `sampleAt`, `BoundedAt`,
`LocallyBounded` and the round-by-round probability bounds use the small-move instance. What is
missing is a universe-polymorphic `ProbComp`, or a challenge universe separate from the message
universe. Options:

- implement a universe-polymorphic `ProbComp` in VCVio, or separate the challenge universe in the
  core signature;
- accept the restriction as an upstream limit and document it in the security modules;
- retire large-move probability bounds as out of scope.

Decision: open.

**3. VCVio cost universes.**
`port-oracle-bundles.md` (#1476), section Open cost universes, records it.
`OracleMap.withAmbient_worstCaseCost` in `ArkLib/Interaction/Core/Oracle/Cost.lean` (#1476) keeps
the ambient index, both bundle-query indices, the responses and the cost carrier `ω` in `Type`.
The restriction comes from VCVio `VCVio/OracleComp/QueryTracking/CostModel.lean` (variables at
line 63, `CostModel` at line 86, `WorstCaseCostBound` at line 217) and `CostModel/Simulation.lean`
(variables at line 32). What is missing is a VCVio cost API with explicit query-index,
response and cost universes. Options:

- implement the generalization in VCVio (PR R-clean is the natural place) and rebase the ArkLib
  wrapper on it;
- accept the restriction as an upstream limit and document it at the wrapper;
- retire universe-polymorphic cost bounds as out of scope.

Decision: open.

**4. `run_append`: splitting an ordered execution at an arbitrary stage.**
Old `Oracle/Composition.lean` L258 has no core target. `port-stages.md` (#1477) records the
missing parent interface: a reassociation law for `OracleVerifier.append`, which relates
`(V₁.append V₂ c₁₂).append V₃ c` to the append of `V₁` with the append of `V₂` and `V₃`. The law
needs the transport of paths and views along protocol associativity, agreement of
`prefixRoute` and `suffixRoute` on both sides, reassociation of the compatibility certificates
and their output maps, chain concatenation, and the prover continuation kept at the cut. The
protocol part exists at the PolyFun pin as `PFunctor.FreeM.append_assoc`
(`PolyFun/PFunctor/Free/Path.lean`, line 727), `Path.split_append` (line 766),
`Path.append_split` (line 777) and `Chain.then` with `Chain.toTypeTree_then`
(`PolyFun/Interaction/Basic/Chain/Append.lean`, line 94). `StageChain.run_cons` gives only the
split after the first stage. Options:

- implement the reassociation law for `OracleVerifier.append` and the chain split;
- accept the first-stage split as the supported interface and document the restriction;
- retire the arbitrary-stage split.

Decision: open.

**5. `degreeModel` and `degreeGuarantee`.**
Old `Sumcheck/Interaction/Closing.lean` lines 40 and 53 use the generic
`OracleModel.satisfies_guarantee` interface of old `Oracle/Resource.lean`, which has no core
counterpart. [sumcheck.md](sumcheck.md) and [departures.md](departures.md) (entry 22) record it as
a separate gap. `port-oracle-bundles.md` (#1476) retires the property-symbol languages of
`Resource.lean` and uses carrier refinements for actual bounds instead: its rows R23 and R24 keep
the true and false degree facts about the same polynomial. What is missing is a core interface
that promises a property of every admissible realization of an oracle bundle. Options:

- implement a core counterpart of `OracleModel.satisfies_guarantee` over `OracleBundle`;
- accept carrier refinements as the replacement and document it in sumcheck.md;
- retire both declarations, citing the degree bound carried by the message type
  `R⦃≤ deg⦄[X]` (whether every client of the two declarations is covered by that bound is not
  verified).

Decision: open.

## The deletion step

### Files that need more than deletion

Two test files outside the old directories import the old layer and must stay.

- `ArkLibTest/ProofSystem/Sumcheck/LegacyVerifier.lean` imports
  `ArkLib.ProofSystem.Sumcheck.Interaction.Legacy` (line 7) for `legacyTranscript` (opened at
  line 29, used at lines 56, 63, 72, 80, 87, 103 and 111). Its rows #1, #2, #12 and #13 stay as
  legacy tests. The deletion PR must replace the helper. `roundFullTranscript` in
  `ArkLib/ProofSystem/Sumcheck/Core/Execution.lean` (line 64) has the same target type,
  `FullTranscript (Spec.SingleRound.pSpec R deg)`. Whether its reductions satisfy the test's
  `rfl` and `simp` steps is not verified; a local two-line definition is the fallback. The core
  `legacyTranscript` (`Core/Execution.lean`, line 70) has a different signature.
- `ArkLibTest/OracleReduction/MeasuredExtraction.lean` imports
  `ArkLib.Interaction.Oracle.Security.KnowledgeResources.Composition` (line 7). Lines 24–61
  (section `Search`) test the legacy layer and stay. Lines 63–203 (`MeasuredExtractionTest`, the
  done-tree example, `FixedCountArithmeticTest` and `ZeroStageAccountingTest`) are ported as rows
  ME-086 to ME-194 and go. The import on line 7 and the second paragraph of the module docstring
  (lines 17–19) go with them. Whether the `Search` section still needs the `AddProgram` import is
  not verified.

### Umbrella imports

`ArkLib.lean` imports the old layer at line 776 (`ArkLib.Interaction.CompositionSoundness`), lines
813–853 (`ArkLib.Interaction.Oracle.Access` through `ArkLib.Interaction.Reduction`) and lines
1176–1194 (the 19 `ArkLib.ProofSystem.Sumcheck.Interaction.*` modules). The test library has no
umbrella: `lakefile.toml` builds `ArkLibTest` from the glob `ArkLibTest.+`.

### The polynomial-family alias

`ArkLib/ProofSystem/Sumcheck/Spec/PolynomialInterface.lean`, lines 36–45, defines
`Sumcheck.Interaction.MultivariateRound.polynomialFamily` as an alias of
`Spec.polynomialFamily` (the `abbrev` is at line 43). Its docstring says it is kept for the frozen
layer and `scripts/SumcheckRuntime.lean`. That docstring is stale: the script no longer uses the
alias. Outside the old layer nothing uses it. Inside, old Sumcheck tests such as
`ArkLibTest/ProofSystem/Sumcheck/Interaction/RoundByRound.lean` use it, and the deletion removes
them. The alias namespace then goes too. Two docs also name the alias:
[sumcheck.md](sumcheck.md) line 597 and
[`docs/wiki/interaction-naming.md`](../../wiki/interaction-naming.md) line 198.

The docstring of `ArkLib/ProofSystem/Sumcheck/Impl/Basic.lean`, lines 20–21, names
`Sumcheck.Interaction.Computable` and `ComputableCompleteness` and needs new targets.

### Blueprint

- `blueprint/lean_decls` has 18 old-layer entries: lines 138–153 (16
  `Interaction.Oracle.Security.*` declarations) and lines 363–364
  (`Sumcheck.Interaction.Native.execute_perfectCompleteness` and `execute_soundness`).
- `blueprint/src/oracle_reductions/defs.tex` cites old declarations in `\lean{...}` at lines
  931–935, 951–955, 979–982 and 1005–1006.
- `blueprint/src/proof_systems/sumcheck.tex` cites the two Sumcheck declarations at lines 275–276.

Each citation needs a core target from the ledgers above, or removal of its `\leanok`.

### CI workflow

`.github/workflows/interaction.yml` needs two edits.

- Its triggers (lines 6–9) and its build step (lines 85–87) list the globs
  `ArkLib/ProofSystem/Sumcheck/Interaction/` and `ArkLibTest/ProofSystem/Sumcheck/Interaction/`.
  After the deletion those globs match nothing. The build step's guard "No Interaction modules
  were discovered" does not fire, because the `ArkLib/Interaction/*.lean` pathspec still matches
  `Core/`. The workflow does not list the Sumcheck core directories. The deletion PR should
  therefore replace the two globs with `ArkLib/ProofSystem/Sumcheck/Core/` and
  `ArkLibTest/ProofSystem/Sumcheck/Core/`. Whether another workflow already builds those
  directories is not verified.
- Its warning-budget step (lines 105 and 107) checks `--path-prefix` for the two Sumcheck
  interaction directories. These need the same replacement. How the budget script handles a
  prefix that matches no file is not verified.

### Prose that describes the old layer as current

- [`00-current-status.md`](../00-current-status.md): lines 4, 36, 112–113, 119, 133, 142–163,
  227, 296 and 375–376.
- `ROADMAP.md`: lines 11–12, 20–34, 66–71 (`Sumcheck.Interaction.Native.*`) and 150–161.
- `README.md`: lines 65 and 94.
- `BACKGROUND.md`: lines 26, 528 and 1410–1473.
- [`docs/wiki/repo-map.md`](../../wiki/repo-map.md): lines 11, 32, 38–39, 63–89, 109–110, 826
  and 841.
- [`docs/wiki/quickstart.md`](../../wiki/quickstart.md): lines 130–131.
- [`docs/wiki/interaction-naming.md`](../../wiki/interaction-naming.md): lines 4–5 and 366–367.
- `docs/design/01-foundations.md`, `02-oracle-reduction-core.md`,
  `03-adversarial-oracle-execution.md` and `03a-extractor-efficiency.md`.

The D-records stay: they describe the old layer as it was when they were written.
`docs/kb/_generated/` is regenerated on main and needs no hand edit.

### Link rot

`scripts/check-docs-integrity.py` checks inline Markdown links in `AGENTS.md`,
`scripts/README.md` and `docs/**/*.md`, excluding `docs/kb/_generated/`. It ignores anchors,
reference-style links and the root `README.md`, `ROADMAP.md` and `BACKGROUND.md`.

The check will catch 18 inline links into deleted files:

- `docs/design/02-oracle-reduction-core.md`: 8 links, at lines 34, 147, 183, 196, 213, 230, 294
  and 328;
- `docs/design/03-adversarial-oracle-execution.md`: 5 links, at lines 44–47 and 98;
- `docs/design/03a-extractor-efficiency.md`: 1 link, at line 300;
- `docs/wiki/interaction-naming.md`: 4 links, at lines 4, 5, 366 and 367.

The check will not catch these:

- inline links in root files: 4 in `ROADMAP.md` (lines 22, 34, 67 and 161) and 11 in
  `BACKGROUND.md` (lines 1417–1473);
- reference-style links into deleted files in the ledgers on this branch: 112 in
  [knowledge-composition-disposition.md](knowledge-composition-disposition.md), 145 in
  [state-restoration-disposition.md](state-restoration-disposition.md) and 14 in
  [soundness-implication-disposition.md](soundness-implication-disposition.md);
- `#L` links into surviving files, whose line numbers drift: 147 in the knowledge-composition
  ledger, 43 in [port-logged-execution.md](port-logged-execution.md), 42 in the soundness ledger
  and 153 in the state-restoration ledger;
- the ledgers of the open PRs, once merged: `port-oracle-access.md` (#1478) has 89 links into
  deleted files and 122 `#L` links into core files; `port-oracle-bundles.md` (#1476) has 74 and
  59; `port-stages.md` (#1477) has 0 and 140; `port-logged-execution.md` as revised by #1567 has
  0 and 44.

The generated `docs/kb/_generated/dedup-report.md` has 163 links into deleted files; it is
excluded from the check and regenerated on main.

The ledger links should become GitHub permalinks at one fixed commit: the last main commit
before the deletion. The ledgers then keep their evidence after the files are gone.

### Merge order

1. Merge the four PRs based on main: #1476, #1477, #1478 and #1567. Their ledgers and core tests
   are the evidence for many rows above.
2. Merge the stack: #1486, #1482, #1483, #1484, #1488, #1487 and #1493.
3. Decide on #1341 (LogUp, `feat/logup-native`). It builds on the old layer. On its branch,
   `ArkLib.lean` imports 60 old-layer modules, 14 LogUp, `Impl` or script files import 10
   distinct old-layer modules directly, and the PR modifies 10 old-layer production files, adds
   2 (`Sumcheck/Interaction/Resources.lean` and `SamplingResources.lean`) and adds 7 old-layer
   tests. It must be ported to the core, or closed, before step 4. sumcheck.md notes that the
   LogUp port needs a law about raw decision queries, their order and their charges.
4. Delete the frozen Sumcheck layer: the 19 modules, the 12 tests, the alias, the Sumcheck
   blueprint citations and the Sumcheck workflow globs. Retarget `LegacyVerifier.lean`.
5. Delete the generic layer: the 42 modules, the 32 tests, the remaining blueprint citations and
   the old part of `MeasuredExtraction.lean`. Fix the prose and the links listed above.
6. Clean PolyFun and VCVio: PolyFun P-clean and VCVio R-clean.
