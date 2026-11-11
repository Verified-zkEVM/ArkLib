# Soundness implications: source-to-port inventory

This record compares the frozen soundness declarations and acceptance tests with the Core port
on `feat/interaction-migrate-core-6`, relative to `feat/interaction-migrate-core-5`.
Row identifiers S1–S4, R1–R4 and T1–T6 are the references used by the ordinary-import tests.
Source links identify the frozen declaration or assertion, including its file and line.

The approved premises are:

- **P1 (passivity):** verifiers send only public-coin challenges and make all resource queries
  in the final decision.
- **P2 (shape):** challenges and oracle messages never select the next subtree.

Each row has exactly one status:

- **equivalent:** the target retains the mathematical assertion.
- **premise-required (P1/P2):** the named approved premise changes the represented verifier or tree.
- **retired (mechanism):** the named mechanism has been removed; the row identifies its replacement.
- **unresolved (interface):** the named parent interface is missing. This record has no such rows.

The table links point to declarations, not just modules. The failure assertion begins at frozen
line 38; the actual-run assertion begins at line 45, after the line-44 local option. These are the
assertions referred to as lines 37 and 44 in the review brief.

## Soundness.lean

Frozen source: `ArkLib/Interaction/Oracle/Security/Soundness.lean`.

| Row | Exact frozen source and declaration | Exact target and declaration | Status |
| --- | --- | --- | --- |
| S1 | [Soundness.lean:43][source-state], `executeStrategies_state_bound` | [Implications.lean, `prEvent_runPrefixChallenges_le`][prefix-bound], with [the finite rank-sum bound][rank-sum] | premise-required (P1/P2): terminal decisions replace effectful verifier continuations; challenge and payload values do not select shape. The actual interpreted action, history-dependent challenges and arbitrary rank errors remain. |
| S2 | [Soundness.lean:157][source-sound], `executeStrategies_soundness` | [Implications.lean, `prEvent_runPrefixChallenges_soundness`][prefix-sound]; [plain][plain-local] and [oracle][oracle-local] fixed-sampler interfaces; [plain][plain-with] and [oracle][oracle-with] raw-freshness specializations | premise-required (P1/P2): same passive, shape-preserving representation as S1. [Rank-sum transport][rank-sum] retains the finite nonuniform error sum. |
| S3 | [Soundness.lean:188][source-uniform], `executeStrategies_soundness_uniform` | [Implications.lean, `prEvent_runPrefixChallenges_soundness`][prefix-sound] with [finite rank-sum transport][rank-sum]; [plain][plain-uniform] and [oracle][oracle-uniform] fixed-sampler corollaries | premise-required (P1/P2): same representation as S1. `k • e = (k : ℝ≥0∞) * e`, including zero challenges. |
| S4 | [Soundness.lean:218][source-prefix], `LocalSoundness.random_prefix` | [Implications.lean, `flip_random_model_le`][random-model]; [raw-node specialization][random-prefix] | equivalent: an `OptionT ProbComp` author selects a full prefix before the fresh challenge; its failure contributes no mass. Choosing `e = error round` and equal ranks recovers the frozen conclusion. |

## RoundByRound.lean

Frozen source: `ArkLib/Interaction/Oracle/Security/RoundByRound.lean`.

| Row | Exact frozen source and declaration | Exact target and declaration | Status |
| --- | --- | --- | --- |
| R1 | [RoundByRound.lean:102][source-escape], `OrdinaryState.exists_verifier_escape` | [Implications.lean: `StateFunction.escapeAlong`][escape] | premise-required (P1/P2): the sender/root/leaf certificate uses Core full prefixes and a passive final decision. The conclusion still asserts an actual false-to-true challenge on every accepting path. |
| R2 | [RoundByRound.lean:111][source-schedule], `ChallengeSchedule` | [Implications.lean: `iSup_sum_challengeNodesOn_le_rank_sum`][rank-sum] | premise-required (P2): challenge ranks factor through structural nodes; strict rank increases make them injective along a path. Arbitrary `error : ℕ → ℝ≥0∞` remains. |
| R3 | [RoundByRound.lean:140][source-model], `ChallengeModel`, in particular `sample` at line 142 | [Implications.lean: `ReceiverPrefix.flip_le_of_encoded_marginals`][encoded] | equivalent: instantiate `Result`, `sample`, `encode` and `modelEvent` separately at each full prefix. The target does not require the model distribution to factor through the node. |
| R4 | [RoundByRound.lean:168][source-fresh], `FreshVerifier` | [Implications.lean: `prEvent_runPrefixChallenges_le`][prefix-bound] and [`ReceiverPrefix.flip_le_of_encoded_marginals`][encoded]; [Execution.lean: `FreshChallenges`][fresh] is the raw-move specialization | premise-required (P1/P2): the argument below removes private verifier continuations and shape selection. Encoded prefix models use the general actual-event interface, not an assumed equality with one global draw. |

## Frozen soundness test

Frozen source: `ArkLibTest/Interaction/Oracle/Security/Soundness.lean`. Every assertion is listed.
The target fixture has an empty-response service, a Core sender prover that queries it before
sending, and a verifier that accepts every completed transcript. The frozen uniform-service
summand is unused by either failure assertion; the fixture isolates the empty-response service.
The frozen empty input-access handler disappears with its threaded verifier-access mechanism;
Core routes resources only in a terminal decision under P1.

| Row | Exact frozen assertion | Exact target and declaration | Status |
| --- | --- | --- | --- |
| T1 | [Soundness.lean:38][source-test-action], anonymous `simulateQ handler prover = failure` assertion | [Implications.lean: `EmptyResponse.interpreted_action`][test-action] | equivalent: interpreting the prover action yields `OptionT` failure before any move. |
| T2 | [Soundness.lean:45][source-test-run], anonymous actual executor `Pr[True] = 0` assertion | [Implications.lean: `EmptyResponse.run_mass`][test-run] | equivalent: the actual Core verifier run has no successful observation, even though its terminal decision accepts. This also excludes converting failure into returned rejection. |
| T3 | [Soundness.lean:54][source-test-sound], `#check executeStrategies_soundness` | [Implications.lean: general plain soundness example][test-sound] and [oracle example][test-oracle] | premise-required (P1/P2): the ordinary-import consumers check both passive verifier forms, as in S2. |
| T4 | [Soundness.lean:55][source-test-uniform], `#check executeStrategies_soundness_uniform` | [Implications.lean: general plain uniform example][test-uniform] and [oracle uniform example][test-oracle-uniform] | premise-required (P1/P2): the ordinary-import consumers check both forms, as in S3. |
| T5 | [Soundness.lean:57][source-test-escape], `#check OrdinaryState.exists_verifier_escape` | [Implications.lean: general escape example][test-escape] | premise-required (P1/P2): the ordinary-import consumer checks R1. |
| T6 | [Soundness.lean:58][source-test-prefix], `#check LocalSoundness.random_prefix` | [Implications.lean: prefix-dependent model example][test-model] and [raw-node example][test-prefix] | equivalent: the author remains optional and can select the node and full prefix. |

The [half-mass test][half-mass] remains additional coverage. The [optional soundness theorem][optional]
instantiates the generic implication in `OptionT ProbComp`; neither replaces T1 or T2.

## Prefix-indexed freshness and supported continuations

The frozen premise compares **encoded** marginals at a concrete execution prefix. Its extension
law identifies the model successor with the concrete prefix extended by the actual move. For a
fixed prefix, choose the model event “the old state is false and the extended state is true”.
The extension law identifies its pullback under `encode` with the actual flip event.
[ReceiverPrefix.flip_le_of_encoded_marginals][encoded] proves precisely this transport for any
monad with distribution semantics. Apply it separately at each full prefix. `Result`, `sample`,
`encode` and the model event can change between prefixes reaching the same shape node. P2 does
not imply that `ChallengeModel.sample` is prefix-independent, and this port makes no such claim.

P1 moves every resource query to the final decision and makes verifier receive actions pure
observations. At each receiver node, the public-coin action has one sampler and a pure
continuation for each sampled move. P2 fixes the structural successor independently of a
challenge or payload. It does **not** fix the next sampler: two histories at the same shape node
can choose different public-coin programs. For example, after a Boolean challenge `x`, a second
challenge can be deterministically `!x` without changing shape. The [adaptive execution test][adaptive]
checks this case.

The general interface therefore uses `PrefixChallengePrograms`, indexed by the structural spine
**and the full history**, and retains every erased challenge and oracle payload in `PrefixMoves`.
At a sender, the passive continuation observes the sent value. At a receiver, the draw at that
history selects the move and hence its pure continuation. Recursing this construction yields
`prefixSampler`; [runPrefixChallenges_eq_run][prefix-run] proves exact equality with the ordinary
Core focal-first runner against that counterpart. Resource effects can still fail in focal slots
or the final decision. No draw restarts the prover or an ambient handler.

Supported-continuation freshness says nothing about a prefix after an unsupported challenge.
When extending a frozen certificate to all Core prefixes, set its state to true outside the
supported-prefix set. That set is closed under arbitrary sender moves and supported challenge
moves. The new state cannot flip there, preserves the sender and leaf obligations, and agrees
with the old state on actual runs. A challenge from a supported prefix to an unsupported one has
probability zero. This completion does not add an off-support freshness premise.

[prEvent_runPrefixChallenges_le][prefix-bound] consumes the transported actual flip bound at
each matching history. [prEvent_runPrefixChallenges_soundness][prefix-sound] derives the acceptance
bound from the full-prefix state certificate and a possibly failing final decision. The frozen
state bound is its underlying no-escape argument: initial falsity and sender preservation force
any true terminal state to have a false-to-true challenge, by [escapeAlong_of_accepts][escape-general].
Apply the encoded transport separately at each supported prefix and recursively at its supported
continuations; the completion above handles the remaining prefixes. This derives structural-node
**error bounds**, while keeping prefix-dependent samplers and model distributions. It does not
derive raw node-indexed sampler equality from P1/P2.

`FreshChallenges` is stronger than frozen encoded freshness because it fixes raw marginals at
all histories reaching a node. It remains a convenient specialization. The [raw-marginal
bridge][action-marginals], `prEvent_run_state_le` and the plain/oracle `soundnessUsing` implications
support that case. `FreshChallengesAt` additionally quantifies every ambient state. This is a
sufficient condition for arbitrary stateful handlers, not an equivalence with frozen freshness.
The classical wrappers introduce no such caller premise: [freshChallengesAt_addLift][fresh-state]
proves it for a separate challenge draw. The general prefix-dependent runner needs neither raw
node equality nor a bound for an unrelated history/state pair.

## Finite ranks, probability semantics and classical specializations

The frozen schedule preserves rank at sender/oracle moves and increases it by one at each
challenge. Under P2, define a node's rank by counting its challenge ancestors, plus the initial
rank. Each path then has distinct challenge ranks in `Finset.Ico first count`.
[iSup_sum_challengeNodesOn_le_rank_sum][rank-sum] bounds the path supremum by exactly that finite
sum for arbitrary rank-indexed errors, including skipped ranks and zero challenges. Taking
`first = 0` gives `Finset.range count`; the [ordinary-import rank example][test-rank] checks this
form. This argument does not use the sum over all nodes: different public branches may contain
different nodes with the same rank, which that sum would charge separately.

The prefix-dependent execution bound and both verifier implications quantify `m : Type → Type v` with `Monad`,
`LawfulMonad`, `EvalDistSemantics` and `LawfulEvalDistSemantics`. No attachment or losslessness
instance is needed. Optional prover actions and terminal computations can lose mass. A returned
`none` remains a rejecting observation; ambient failure yields no observation. The [general random-prefix lemma][random-model] retains its separate `OptionT ProbComp` author
quantifier and permits dependent model result types. The [ordinary-import example][test-model]
retains the frozen rank-indexed error and equal-rank premise.

Both `soundnessWith` predicates are specializations of `soundnessUsing` by `simulateQ handler`.
The [plain soundness bridge][plain-bridge] and [oracle soundness bridge][oracle-bridge] specialize
the same interface by the **whole** `experiment init impl draw`. The experiment samples `init`
once and threads the resulting state across all queries. The [plain acceptance bridge][plain-acc]
and [oracle acceptance bridge][oracle-acc] retain `∃ state`, then evaluate the decision from that
state. Resource answers and the oracle output map remain those of the fixed transcript.
[Ordinary-import checks][test-bridges] expose all four laws. The classical implication wrappers
use them and the generic implication, without a separate run-to-decision or acceptance proof.

Statement, input-index, input-query and output-query universes remain independent; acceptance
and soundness retain path-indexed outputs. The execution and resource-interpretation universe
constraints are inherited from [IMPLEMENTATION-NOTES entry 18][universes], rather than introduced
by this implication. This record adds no second inventory of those constraints.

[source-state]: ../../../ArkLib/Interaction/Oracle/Security/Soundness.lean#L43
[source-sound]: ../../../ArkLib/Interaction/Oracle/Security/Soundness.lean#L157
[source-uniform]: ../../../ArkLib/Interaction/Oracle/Security/Soundness.lean#L188
[source-prefix]: ../../../ArkLib/Interaction/Oracle/Security/Soundness.lean#L218
[source-escape]: ../../../ArkLib/Interaction/Oracle/Security/RoundByRound.lean#L102
[source-schedule]: ../../../ArkLib/Interaction/Oracle/Security/RoundByRound.lean#L111
[source-model]: ../../../ArkLib/Interaction/Oracle/Security/RoundByRound.lean#L140
[source-fresh]: ../../../ArkLib/Interaction/Oracle/Security/RoundByRound.lean#L168
[source-test-action]: ../../../ArkLibTest/Interaction/Oracle/Security/Soundness.lean#L38
[source-test-run]: ../../../ArkLibTest/Interaction/Oracle/Security/Soundness.lean#L45
[source-test-sound]: ../../../ArkLibTest/Interaction/Oracle/Security/Soundness.lean#L54
[source-test-uniform]: ../../../ArkLibTest/Interaction/Oracle/Security/Soundness.lean#L55
[source-test-escape]: ../../../ArkLibTest/Interaction/Oracle/Security/Soundness.lean#L57
[source-test-prefix]: ../../../ArkLibTest/Interaction/Oracle/Security/Soundness.lean#L58
[universes]: ../interaction-rebuild/IMPLEMENTATION-NOTES.md#18-run-outputs-are-tied-to-the-monad-universe
[state-local]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L307
[prefix-bound]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L599
[prefix-sound]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L674
[prefix-run]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L574
[escape-general]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L69
[rank-sum]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L711
[plain-local]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L746
[oracle-local]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L953
[plain-with]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L832
[oracle-with]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L1049
[plain-uniform]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L888
[oracle-uniform]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L1120
[random-prefix]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L193
[random-model]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L177
[encoded]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L158
[escape]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L100
[action-marginals]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L279
[action-at]: ../../../ArkLib/Interaction/Core/Security/Implications.lean#L269
[plain-bridge]: ../../../ArkLib/Interaction/Core/Security/Soundness.lean#L161
[oracle-bridge]: ../../../ArkLib/Interaction/Core/Security/Soundness.lean#L201
[plain-acc]: ../../../ArkLib/Interaction/Core/Security/RoundByRound.lean#L208
[oracle-acc]: ../../../ArkLib/Interaction/Core/Security/RoundByRound.lean#L272
[fresh]: ../../../ArkLib/Interaction/Core/Execution.lean#L55
[fresh-state]: ../../../ArkLib/Interaction/Core/Execution.lean#L75
[half-mass]: ../../../ArkLibTest/Interaction/Core/Security/Implications.lean#L494
[optional]: ../../../ArkLibTest/Interaction/Core/Security/Implications.lean#L465
[adaptive]: ../../../ArkLibTest/Interaction/Core/Security/Implications.lean#L384
[test-action]: ../../../ArkLibTest/Interaction/Core/Security/Implications.lean#L527
[test-run]: ../../../ArkLibTest/Interaction/Core/Security/Implications.lean#L540
[test-bridges]: ../../../ArkLibTest/Interaction/Core/Security/Implications.lean#L23
[test-rank]: ../../../ArkLibTest/Interaction/Core/Security/Implications.lean#L351
[test-sound]: ../../../ArkLibTest/Interaction/Core/Security/Implications.lean#L39
[test-oracle]: ../../../ArkLibTest/Interaction/Core/Security/Implications.lean#L65
[test-uniform]: ../../../ArkLibTest/Interaction/Core/Security/Implications.lean#L53
[test-oracle-uniform]: ../../../ArkLibTest/Interaction/Core/Security/Implications.lean#L82
[test-escape]: ../../../ArkLibTest/Interaction/Core/Security/Implications.lean#L115
[test-prefix]: ../../../ArkLibTest/Interaction/Core/Security/Implications.lean#L124
[test-model]: ../../../ArkLibTest/Interaction/Core/Security/Implications.lean#L392
