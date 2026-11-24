# State restoration: source-to-port disposition record

This record compares `feat/interaction-migrate-core-4` (#1483), on parent
`feat/interaction-migrate-core-3` (#1482), with the unchanged frozen state-restoration sources.
It is the production and fixture disposition inventory for this branch.
[Entry 20](../interaction-rebuild/IMPLEMENTATION-NOTES.md#20-state-restoration-under-p2-authored-output-selection)
explains the authored-selector fixtures. The [parent inventory](knowledge-composition-disposition.md)
covers the shared extraction and measured-stage interfaces.

The approved premises are:

- **P1 (passivity):** passive verifiers send only public-coin challenges and make all bundle
  queries in the final decision.
- **P2 (shape):** challenges and oracle messages never select shape. A public prover message may
  select a subtree and its output family.

Each row has exactly one status:

- **equivalent:** the target preserves the law or outcome under the stated representation
  correspondence. Extra endpoint terms specialize as described below.
- **premise-required:** P1 or P2 requires the stated change to the domain or execution boundary.
  The row names the premise; the common Core domain still satisfies both premises.
- **retired:** the row names the removed mechanism. The target column identifies its successor
  interface, not an assertion that the removed API still exists.
- **unresolved:** the row must name the missing parent interface. There are no unresolved rows in
  this branch's stated scope; support-based completion now has a proved Core counterpart.

## Scope and endpoint correspondence

Each frozen production file has its own table, including helper declarations and instances.
Each frozen test file has one table with an individual row for every theorem, anonymous example,
and executable assertion. Test rows retain entry 20's row numbers where those annotations are
accurate. Data-only fixture definitions are context, not additional assertions.
Frozen two-round line 308 evaluates rejection, not extraction. The Core extraction evaluation is
additional evidence for the universal extraction assertion at frozen line 242.

The restored-execution bound maps the frozen input state predicate to `relIn`, membership in `Z`
to `admissible`, and the frozen terminal-state predicate to `validOutput`. The certificate contains the
sender preservation laws. `readOut` applies the supplied output-witness transport at the actual
completed transcript; `extractLeaf`, the backward step maps and `extractRoot` replace the bundled
extractor. Statement-indexed input witnesses and independent intermediate and output witness
universes are retained. The event remains admissible input, valid supplied output, and failure of
the named backward extraction, bounded by `(Q + rounds.length) * error`. The per-round theorems
bound the same event by `Q * max + sum` for a fixed adversary program. Their `_privateCoins`
forms average that bound over private coins whose sampler may fail, when every fixed-coin
adversary has the same query bound `Q`.

For `StateRestorationGame.lean:102`, the frozen terminal returns arbitrary `Out z p` and its
`outputLaw` is an iff with the terminal-state predicate. Core's final decision returns
`Option (T p)`; successful outputs satisfy `verdict = some t` and `relOut ... t w`.
For an always-returning frozen terminal, use `some` of its result. The frozen `terminalWitness`
equivalence supplies `readOut`. Its input iff identifies `relIn`; its output iff implies Core's
one-way `outputLaw`. Thus the implication is a weaker certificate obligation, not an assumed
success condition. Rejection-sensitive oracle games already use the existential accepted-claim
event. Core separates the optional statement from its deterministic output map and returns the
same closed result on acceptance. P1 restricts the authoring interface; P2 excludes
challenge-selected output families. These are premise-required ports, not a claim to support every
frozen source-only terminal authoring program.

## Support and interpreted replay

[`completedPath_matchesMessages`][r291] covers completion against a complete answer table. Alone, it
does not establish structural support: an arbitrary open program can receive inconsistent answers
to repeated queries. The new `complete_support_matches` proves the open-program claim directly,
by peeling both completion binds and applying pinned VCVio's `support_simulateQ_subset` to the
suffix. It does not infer structural support from table evaluation. The existing table theorem
remains available for table-completed transcripts.

[`run_scriptedProver_of_mem_support`][r292] composes the support theorem with `run_scriptedProver`.
For every supported completion, the actual `OracleVerifier.run`, interpreted with `recordedAnswers`
from that transcript, returns that transcript and its closed verdict. This is the explicit
support-to-execution implication for frozen `complete_support_matches` and `execute_pathReplay`.
P1 replaces the frozen open executor equation by interpreted passive replay; the target does not
assert equality of arbitrary open ambient-effect programs. `closedVerificationGame_eval_run` and
`verificationGame_eval_run` separately connect the games to party runs on table-completed paths.

## Measured budgets and carrier scope

Core's protocol bound is
`leafBound + rounds.length • (messageBound + challengeBound) + rootBound`.
The root program converts the root state witness to the input witness; the leaf program converts
the supplied output witness to the leaf state witness. Install the frozen named step programs
and use `BudgetedProgram.ofFun` for these extra pure endpoint maps. Both endpoint budgets are zero.
[`programAlong_budget_le_protocol_zero`][r293] proves the exact specialization
`rounds.length • (messageBound + challengeBound)`. The corresponding `CostAtMost` bound
specializes by `zero_add` and `add_zero`. The two-round fixture proves cost two on all transcripts
and witnesses. No zero-cost hypothesis is inferred for arbitrary endpoint programs.

The measured budget begins after `readOut`. The game tests failure of
`M.extractAlong stmt tr (readOut stmt tr w)`. The cost conjunct of
[`MeasuredKnowledgeStateFunction.stateRestoration_oracle_knowledge_soundness_nonuniform`][r172]
bounds `M.stages.programAlong stmt tr` on the witness that `readOut` has already converted, and
its realization equality lets the failure event use that program. `readOut` itself is an
arbitrary function of the input, the completed transcript and the adversary's witness. The budget
therefore assumes that the conversion has run and that the statement, the transcript and the stage
programs are supplied. The root, message, challenge and leaf bounds are per statement; the theorem
gives a uniform size-based budget only if the caller bounds them separately.
[`stateRestoration_oracle_knowledge_soundness_nonuniform_withReadOut`][c1] supplies the full
extractor contract: [`extractionProgram`][c2] composes a budgeted program realizing `readOut`
with `programAlong`, the failure event runs that composite program, and the cost conjunct charges
both programs. The fixture's `converted_game_bound` and `convertedObservation_path` add a charged
`w + 1` conversion; witness six on `path 0 1` extracts nineteen with three recorded additions.
The identity-conversion fixture still records two stage additions.

These are declared instruction bounds. Pure work, carrier conversions, program construction,
handlers, witness size and adversary/replay/restoration work remain uncharged, as in the frozen
contract, unless a conversion program is charged as above. Pinned VCVio
`BudgetedProgram {Input Result : Type}` forces small measured input/result
carriers; `ProbComp : Type → Type` forces small random outputs, and
`SampleableType (β : Type)` forces small sampled challenges. Unmeasured witness maps retain their
independent universes, and deterministic verdicts and shared extraction laws accept general
move universes. Entry 20 records the forcing declarations and dependency pin.

## Correspondence with the papers

Chiesa and Yogev's book (`ChiesaYogev2024`, Chapters 23 and 31) and WARP (`BCFW25`, Appendix B)
state the results that this port formalizes. Chiesa and Yogev's Definitions 23.2.1 and 23.2.3 give
the salted state-restoration game and the straight-line knowledge experiment, and their Theorem
31.3.1 gives the uniform error bound. WARP's Definitions B.1 and B.2 give the salted game, its
Theorem B.4 gives the uniform bound, and its Construction B.5 gives the backward witness
sequence. The cited statements are the same in the May 2025 and June 2026 revisions of WARP.
[Chiesa and Yogev](https://snargsbook.org/) · [WARP revision history](https://eprint.iacr.org/2025/753)

The Lean statements differ from the papers in the following ways.

- **One cached table.** The Lean game answers every challenge from one cached random oracle
  with a dependent key-to-challenge signature ([`oracleSpec`][c3]), in place of the papers'
  per-round random functions. A key of a later round can be queried before a key of an earlier
  round.
- **Resampling one key.** The probability proof fixes all other table entries and resamples only
  the current key ([`badKey_resample_bound`][c4]). Updating that key leaves its prefix history
  fixed ([`keyHistory_update`][c5]), so the local error bound applies at the actual prefix.
- **The conversion is an extra budget boundary.** Construction B.5 starts the backward sequence
  directly from the adversary's output witness. The Lean statements first apply `readOut` at the
  completed transcript. The measured theorem charges only the stage programs after that
  conversion; the `_withReadOut` form also charges a program realizing it.
- **Nonuniform sum.** The per-round bound `Q * max + sum` ([`restoredExecution_round_cost`][c6])
  charges each completion query the error of its own round. It is a stronger accounting of the
  completion queries than the uniform `(Q + rounds.length) * error`.
- **Declared instructions, not extraction time.** WARP's stated extraction time covers its whole
  extractor. The Lean budget counts the declared instructions of the stage programs, and of the
  conversion program when one is charged.

## ArkLib/Interaction/Oracle/Security/StateRestoration.lean

| ID | Exact frozen declaration | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| SR-036 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:36`][r1], `Round` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L58`][r2], `Round`. Same message, interface and uniform challenge data; Core drops unnecessary finite-message and decidable-message fields. |
| SR-050 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:50`][r3], `protocol` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L71`][r4], `protocol`. Same fixed alternation of oracle message and public challenge under P2. |
| SR-056 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:56`][r5], `length_executionPath_protocol` | retired (ExecutionPath.length metric) | [`ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L371`][r6], `programFrom_budget_le_rounds`. Core counts the two stages per round directly in the rounds induction. The tree-specific path-length API is removed; the target is not claimed as a path-length equality. |
| SR-066 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:66`][r7], `Key` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L78`][r8], `Key`. Same salted sum-of-prefixes representation, with no earlier challenges in a key. |
| SR-076 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:76`][r9], `Key.here` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L88`][r10], `here`. Same first-round key. |
| SR-081 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:81`][r11], `Key.later` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L93`][r12], `later`. Same suffix-key injection. |
| SR-085 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:85`][r13], `Key.instDecidableEq` | retired (automatic key equality instance) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L78`][r14], `Key`. Core asks clients for DecidableEq of the full key at the probability theorems instead of storing message equality in Round. |
| SR-094 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:94`][r15], `Key.input` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L98`][r16], `input`. Same selected input recovered from a key. |
| SR-100 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:100`][r17], `Key.Challenge` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L104`][r18], `Challenge`. Same answer alphabet at the key depth. |
| SR-106 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:106`][r19], `Key.remaining` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L110`][r20], `Key.remaining`. Same three recursive cases: it returns the rounds after the addressed challenge. `keySpine` uses it in its result type. |
| SR-111 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:111`][r21], `instance : Finite key.Challenge` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L116`][r22], `instSampleableType`. The same Finite fact follows from the key sampler by pinned VCVio SampleableType.finite; the duplicated specialized instance is unnecessary. |
| SR-119 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:119`][r23], `instance : Nonempty key.Challenge` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L116`][r24], `instSampleableType`. The same Nonempty fact follows from the key sampler by pinned VCVio SampleableType.nonempty. |
| SR-127 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:127`][r25], `instance : SampleableType key.Challenge` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L116`][r26], `instSampleableType`. The key inherits exactly its round sampler. |
| SR-138 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:138`][r27], `Table` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L128`][r28], `Table`. Same complete answer assignment. |
| SR-144 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:144`][r29], `keyExtractor` | retired (reconstructed RoundExtractor subtree) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L284`][r30], `keyHistory`. keySpine and keyHistory select the typed cursor and actual full prefix used by the state function, without rebuilding an extractor. |
| SR-158 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:158`][r31], `keyExtractor_update` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L293`][r32], `keyHistory_update`. Updating the key itself leaves its strict-ancestor history unchanged. Subtree equality becomes equality of the prefix used by the state function. |
| SR-192 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:192`][r33], `uniformSchedule` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L336`][r34], `uniformDraw`. External uniform draws replace the authored verifier challenge-program schedule; uniformEps separately supplies the constant error. |
| SR-199 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:199`][r35], `keyExtractor_local_bound` | retired (local bound on a reconstructed extractor) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L921`][r36], `badKey_resample_bound`. LocallyBounded applies directly at keySpine/keyHistory; sampleAt_keySpine identifies the draw. The target proves the admissible-key consequence, not an extractor-subtree API. |
| SR-223 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:223`][r37], `Messages` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L132`][r38], `Messages`. Same messages and salts; salts are not sent. |
| SR-228 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:228`][r39], `oracleSpec` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L137`][r40], `oracleSpec`. Same dependent key-to-challenge signature. |
| SR-232 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:232`][r41], `prependQuery` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L144`][r42], `prependQuery`. Same suffix-key routing. |
| SR-239 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:239`][r43], `complete` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L150`][r44], `complete`. Same open completion program with one query per round. |
| SR-249 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:249`][r45], `complete_queryBound` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L160`][r46], `complete_queryBound`. Same rounds.length query bound. |
| SR-273 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:273`][r47], `completedPath` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L182`][r48], `completedPath`. Same transcript against a complete answer table. |
| SR-281 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:281`][r49], `completionKeys` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L190`][r50], `completionKeys`. Same ordered list of completion accesses. |
| SR-289 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:289`][r51], `complete_eval` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L197`][r52], `complete_eval`. Same exact table-evaluation equation. |
| SR-305 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:305`][r53], `complete_log_keys` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L212`][r54], `complete_log_keys`. Same query log after forgetting responses. |
| SR-324 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:324`][r55], `completionKeys_input` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L230`][r56], `completionKeys_input`. Every completion key retains the selected input. |
| SR-337 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:337`][r57], `badChallengeOnPath_completion` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L897`][r58], `BadChallengeOnCompletion.mem_badChallenge`. Compose badChallengeAlong_completion with the witness-preserving keyed localization. This final membership bridge forgets the suffix witness and retains membership in completionKeys. |
| SR-362 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:362`][r59], `Key.instFinite` | retired (finite enumeration of restoration keys) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L78`][r60], `Key`. The cached-oracle proof needs no finite input, salt or message domain. Core removes the unused finite-key instance. |
| SR-371 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:371`][r61], `restoredExecution` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L243`][r62], `restoredExecution`. Same adaptive selection followed by completion in the same oracle. |
| SR-380 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:380`][r63], `restoredExecution_queryBound` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L252`][r64], `restoredExecution_queryBound`. Same Q + rounds.length bound. |
| SR-392 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:392`][r65], `badKey` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L913`][r66], `badKey`. Same admissible-input event and existential local bad transition, at the actual prefix. |
| SR-400 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:400`][r67], `badKey_resample_bound` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L921`][r68], `badKey_resample_bound`. Set uniformEps to the constant error to obtain the same resampling bound for every background table. |
| SR-426 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:426`][r69], `restored_bad_trace` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L951`][r70], `restored_bad_trace`. Valid output with failed extraction implies an actual bad query in the same table log, for arbitrary adaptive adversaries. |
| SR-474 | [`ArkLib/Interaction/Oracle/Security/StateRestoration.lean:474`][r71], `restored_extraction_bound` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L996`][r72], `restoredExecution_knowledge_soundness`. Same (Q + rounds.length) * error bound, with readOut and explicit endpoint maps. The endpoint correspondence above identifies the complete event. |

## ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean

| ID | Exact frozen declaration | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| Replay-037 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:37`][r73], `ChallengePrograms` | premise-required (P1) | [`ArkLib/Interaction/Core/Reduction.lean#L159`][r74], `sampler`. Draws from the supplied draw program replace recursive challenge-program authoring data. |
| Replay-043 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:43`][r75], `ambientQueries` | retired (ambient challenge-query lifting adapter) | [`ArkLib/Interaction/Core/OracleVerifier.lean#L580`][r76], `OracleVerifier.run`. The runner injects challenge queries directly; the effectful verifier-fragment signature is removed. |
| Replay-048 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:48`][r77], `sourceQueries` | retired (source-only terminal lifting adapter) | [`ArkLib/Interaction/Core/OracleVerifier.lean#L517`][r78], `OracleVerifier.decideWith`. Answering bundle queries is part of the final decision fold. |
| Replay-054 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:54`][r79], `challengeFragment` | retired (effectful challenge fragment) | [`ArkLib/Interaction/Core/Reduction.lean#L159`][r80], `sampler`. A passive verifier uses the external sampler rather than an authored receive/send fragment. |
| Replay-067 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:67`][r81], `challengeVerifier` | premise-required (P1) | [`ArkLib/Interaction/Core/OracleVerifier.lean#L580`][r82], `OracleVerifier.run`. The final decision and output map replace the fragment completed by a source-only terminal. |
| Replay-081 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:81`][r83], `messageProver` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L477`][r84], `scriptedProver`. Same deterministic selected sends without oracle queries; the obsolete Unit continuation output becomes PUnit. |
| Replay-090 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:90`][r85], `scriptedProver` | retired (duplicated path in prover output) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L477`][r86], `scriptedProver`. The runner already returns the transcript; the scripted prover returns PUnit. run_scriptedProver identifies the returned transcript. |
| Replay-099 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:99`][r87], `pathPrograms` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L495`][r88], `recordedAnswers`. A challenge handler reads the transcript instead of authoring pure challenge programs. |
| Replay-106 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:106`][r89], `MatchesMessages` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L501`][r90], `MatchesMessages`. Same recursive equality of sent and selected messages, with equality oriented in the opposite direction. |
| Replay-113 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:113`][r91], `simulateQ_support_subset` | equivalent | [`VCVio/OracleComp/SimSemantics/StateT/Basic.lean#L324`][r92], `support_simulateQ_subset`. Pinned VCVio already proves the stronger generic-monad support-subset law; the Core support proof uses it directly. |
| Replay-131 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:131`][r93], `complete_support_matches` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L517`][r94], `complete_support_matches`. Proves support of the open completion implies MatchesMessages. run_scriptedProver_of_mem_support then replays every supported member without a table hypothesis. |
| Replay-147 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:147`][r95], `uniformPrograms` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L336`][r96], `uniformDraw`. Same round samplers, indexed by challenge nodes rather than recursive authoring data. |
| Replay-151 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:151`][r97], `simulate_ambientQueries` | retired (ambientQueries cancellation proof) | [`ArkLib/Interaction/Core/OracleVerifier.lean#L580`][r98], `OracleVerifier.run`. The effectful ambient lifting adapter is removed with challengeFragment. |
| Replay-162 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:162`][r99], `simulate_sourceQueries` | retired (sourceQueries cancellation proof) | [`ArkLib/Interaction/Core/OracleVerifier.lean#L517`][r100], `OracleVerifier.decideWith`. The final decision interpreter replaces the source lifting adapter. |
| Replay-178 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:178`][r101], `execute_sourceTerminal` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L665`][r102], `run_scriptedProver`. Interpreted execution returns the verdict using the same input and transcript bundle. |
| Replay-224 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:224`][r103], `pathReplay_run` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L636`][r104], `evalWithAnswerFn_run_scriptedProver`. Actual party replay under any draws whose interpreted answers equal the recorded challenges. |
| Replay-300 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:300`][r105], `execute_pathReplay` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L665`][r106], `run_scriptedProver`. Interpreted replay under recordedAnswers replaces the open executeStrategies = pure equation. Transcript and closed verdict remain exact; arbitrary ambient-effect executors are outside P1. The support-to-replay corollary above supplies the completion implication. |
| Replay-331 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:331`][r107], `uniformFragment_fresh` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L350`][r108], `sampleAt_keySpine`. The external sampler supplies the actual uniform draw at every key prefix; no authored fragment needs a freshness predicate. |
| Replay-354 | [`ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean:354`][r109], `uniformVerifier_fresh` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L350`][r110], `sampleAt_keySpine`. The generic external draw is uniform at every key prefix; no verifier-authored fragment needs a freshness predicate. selected_fresh separately checks the full fixture interaction for every input, selector and oracle message. |

## ArkLib/Interaction/Oracle/Security/StateRestorationGame.lean

| ID | Exact frozen declaration | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| Game-036 | [`ArkLib/Interaction/Oracle/Security/StateRestorationGame.lean:36`][r111], `terminalObservation` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L368`][r112], `verdict`. The passive decision uses the input and transcript bundle. Its result is Option of the path-indexed statement, rather than an arbitrary result `Out z p`. |
| Game-048 | [`ArkLib/Interaction/Oracle/Security/StateRestorationGame.lean:48`][r113], `verificationGame` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L396`][r114], `verificationGame`. Records the completed transcript and passive decision; verificationGame_eval_run and run_scriptedProver_of_mem_support supply actual interpreted party correspondence. |
| Game-068 | [`ArkLib/Interaction/Oracle/Security/StateRestorationGame.lean:68`][r115], `verificationGame_eq` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L419`][r116], `verificationGame_eq`. The verdict equation is definitional for the passive game; a separate run theorem proves its execution interpretation. |
| Game-092 | [`ArkLib/Interaction/Oracle/Security/StateRestorationGame.lean:92`][r117], `extractInputWitness` | retired (bundled terminal-witness equivalence adapter) | [`ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L345`][r118], `extractAlong`. readOut explicitly transports the adversary witness; extractLeaf and extractRoot provide endpoint maps, without requiring bijections. |
| Game-102 | [`ArkLib/Interaction/Oracle/Security/StateRestorationGame.lean:102`][r119], `stateRestoration_knowledge_soundness` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L1039`][r120], `stateRestoration_knowledge_soundness`. Same adaptive Q-query bound. The optional final decision and one-way outputLaw replace the arbitrary result and iff law as detailed above. P2 excludes challenge-selected output families. |

## ArkLib/Interaction/Oracle/Security/StateRestorationOracle.lean

| ID | Exact frozen declaration | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| Oracle-032 | [`ArkLib/Interaction/Oracle/Security/StateRestorationOracle.lean:32`][r121], `OracleOutput` | retired (open-claim terminal result wrapper) | [`ArkLib/Interaction/Core/OracleVerifier.lean#L508`][r122], `OracleVerifier.Output`. Core separates optional statement decisions from deterministic output maps. Output is the closed statement/oracle-data pair. |
| Oracle-045 | [`ArkLib/Interaction/Oracle/Security/StateRestorationOracle.lean:45`][r123], `closedVerificationGame` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L407`][r124], `closedVerificationGame`. Same rejection-sensitive closed-claim game on the completed transcript, using decide and outputMap. |
| Oracle-066 | [`ArkLib/Interaction/Oracle/Security/StateRestorationOracle.lean:66`][r125], `closedTerminalObservation` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L375`][r126], `closedVerdict`. Closes output data from the same input and transcript, without giving verifier authoring concrete realizations. |
| Oracle-083 | [`ArkLib/Interaction/Oracle/Security/StateRestorationOracle.lean:83`][r127], `closedVerificationGame_eq` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L430`][r128], `closedVerificationGame_eq`. Same equation for the verdict on the restored execution; closedVerificationGame_eval_run identifies the interpreted party run. |
| Oracle-106 | [`ArkLib/Interaction/Oracle/Security/StateRestorationOracle.lean:106`][r129], `stateRestoration_oracle_knowledge_soundness` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L1070`][r130], `stateRestoration_oracle_knowledge_soundness`. Same bound and accepted closed-behavior relation; readOut and the acceptance implication instantiate the frozen equivalence/iff laws. P2 restricts output-family shape. |

## ArkLib/Interaction/Oracle/Security/StateRestorationCoins.lean

| ID | Exact frozen declaration | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| Coins-035 | [`ArkLib/Interaction/Oracle/Security/StateRestorationCoins.lean:35`][r131], `stateRestoration_knowledge_soundness_privateCoins` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L1101`][r132], `stateRestoration_knowledge_soundness_privateCoins`. Same pre-sampled coins, possible coin failure, fixed-coin query bounds and (Q + rounds.length) * error, with the passive optional final decision and outputLaw. |
| Coins-076 | [`ArkLib/Interaction/Oracle/Security/StateRestorationCoins.lean:76`][r133], `stateRestoration_oracle_knowledge_soundness_privateCoins` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L1134`][r134], `stateRestoration_oracle_knowledge_soundness_privateCoins`. Same averaging of the accepted closed-output event; failed coins contribute probability zero. |

## ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean

| ID | Exact frozen declaration | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| Budget-030 | [`ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean:30`][r135], `RoundErrors` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L57`][r136], `RoundErrors`. Same error vector in protocol order. |
| Budget-033 | [`ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean:33`][r137], `roundErrorSchedule` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L68`][r138], `roundEps`. Per-round errors index challenge nodes; uniformDraw separately supplies the uniform challenges. |
| Budget-040 | [`ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean:40`][r139], `keyError` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L73`][r140], `keyError`. Same charge by key depth. |
| Budget-047 | [`ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean:47`][r141], `keyError_le_max` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L88`][r142], `keyError_le_max`. Same maximum bound, including zero and infinite errors. |
| Budget-062 | [`ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean:62`][r143], `keyExtractor_round_bound` | retired (per-round bound on a reconstructed extractor) | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L921`][r144], `badKey_resample_bound`. Use LocallyBounded with roundEps errors at the key prefix and keyError_eq_roundEps. The nonuniform restored-execution proof applies precisely this consequence. |
| Budget-086 | [`ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean:86`][r145], `badKey_round_resample_bound` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestoration.lean#L921`][r146], `badKey_resample_bound`. Instantiate node errors with roundEps errors and rewrite keyError_eq_roundEps to obtain the exact keyError bound. |
| Budget-111 | [`ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean:111`][r147], `costDist_prependQuery` | retired (cost-distribution equality under suffix-key routing) | [`ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L127`][r148], `roundCost_prependQuery`. Pinned VCVio's `WorstCaseCostBound.simulateQ` transfers the worst-case charge bound directly, because the handler issues one query at the routed key's charge. The stronger distribution equality had no other consumer. |
| Budget-127 | [`ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean:127`][r149], `queryBound_round_cost` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L103`][r150], `queryBound_round_cost`. Same worst-case Q * max error charge. |
| Budget-149 | [`ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean:149`][r151], `roundCost_prependQuery` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L127`][r152], `roundCost_prependQuery`. Same worst-case charge preserved by suffix routing, proved with pinned VCVio's `WorstCaseCostBound.simulateQ`. |
| Budget-162 | [`ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean:162`][r153], `complete_round_cost` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L139`][r154], `complete_round_cost`. Same sum of one round error for each completion access. |
| Budget-184 | [`ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean:184`][r155], `restoredExecution_round_cost` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L161`][r156], `restoredExecution_round_cost`. Same Q * max + sum bound for adaptive selection plus completion. |
| Budget-202 | [`ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean:202`][r157], `restored_extraction_round_bound` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L188`][r158], `restoredExecution_knowledge_soundness_nonuniform`. Same probability bound Q * max + sum, with explicit endpoint maps and readOut. |
| Budget-232 | [`ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean:232`][r159], `stateRestoration_oracle_knowledge_soundness_nonuniform` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L255`][r160], `stateRestoration_oracle_knowledge_soundness_nonuniform`. Same closed-output event and Q * max + sum; passive decision/output-map presentation replaces the source-only terminal. |

## ArkLib/Interaction/Oracle/Security/StateRestorationResources.lean

| ID | Exact frozen declaration | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| Resources-040 | [`ArkLib/Interaction/Oracle/Security/StateRestorationResources.lean:40`][r161], `RoundExtractor.MeasuredStages.ProtocolBudgetAtMost` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L290`][r162], `ProtocolBudgetAtMost`. Adds explicit root/leaf bounds to the message/challenge bounds; zero-cost endpoint programs embed the frozen stages. |
| Resources-052 | [`ArkLib/Interaction/Oracle/Security/StateRestorationResources.lean:52`][r163], `RoundExtractor.MeasuredStages.BudgetAtMost.protocolBudgetAtMost` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L303`][r164], `BudgetAtMost.protocolBudgetAtMost`. A common step bound supplies equal message/challenge bounds and retains the endpoint bounds. |
| Resources-065 | [`ArkLib/Interaction/Oracle/Security/StateRestorationResources.lean:65`][r165], `RoundExtractor.MeasuredStages.programAlong_budget_le_protocol` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L396`][r166], `programAlong_budget_le_protocol`. Bounds leafBound + rounds.length • (messageBound + challengeBound) + rootBound. programAlong_budget_le_protocol_zero proves the zero-endpoint specialization recovering the frozen bound. |
| Resources-093 | [`ArkLib/Interaction/Oracle/Security/StateRestorationResources.lean:93`][r167], `RoundExtractor.MeasuredStages.programAlong_costAtMost_protocol_paired` | equivalent | [`ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L423`][r168], `programAlong_costAtMost_protocol`. Same every-execution-path CostAtMost consequence with explicit endpoints; zero specialization recovers the frozen bound. |
| Resources-107 | [`ArkLib/Interaction/Oracle/Security/StateRestorationResources.lean:107`][r169], `MeasuredKnowledgeCertificate.run_programAlong_terminalWitness` | equivalent | [`ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L177`][r170], `run_programAlong`. Instantiate its witness with readOut stmt tr w. The program returns extractAlong on that witness, including endpoint conversions. |
| Resources-125 | [`ArkLib/Interaction/Oracle/Security/StateRestorationResources.lean:125`][r171], `MeasuredKnowledgeCertificate.stateRestoration_oracle_knowledge_soundness_nonuniform` | premise-required (P1) | [`ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L506`][r172], `MeasuredKnowledgeStateFunction.stateRestoration_oracle_knowledge_soundness_nonuniform`. Retains Q * max + sum, all admissible inputs/transcripts/witnesses and actual program results. Root/leaf budgets are explicit and may be zero; instruction accounting has the same limitations. The budget begins after `readOut`: the cost conjunct charges the stage programs on the converted witness, not the conversion, and every bound is per statement. `stateRestoration_oracle_knowledge_soundness_nonuniform_withReadOut` charges a program realizing `readOut` as well. |

## ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean

| ID (entry 20 row) | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| SRT-087 (1) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:87`][r173], `inputLaw` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L300`][r174], `inputLaw`. Every input and witness has exactly the original root relation. |
| SRT-089 (2) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:89`][r175], `outputLaw` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L962`][r176], `selectedPlainOutputLaw_iff`. An authored selector replaces the challenge-selected carrier; retains the leaf-state iff for every selector, input, transcript and witness. |
| SRT-096 (3) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:96`][r177], `preserving` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L313`][r178], `preserving`. Retains the sender preservation laws at every input and message; the state-function structure contains the remaining trivial sender obligations. |
| SRT-105 (4) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:105`][r179], `badChallenge_iff` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L323`][r180], `badChallenge_iff`. Retains the full equivalence on both Boolean challenges. |
| SRT-113 (5) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:113`][r181], `bounded` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L339`][r182], `bounded`. Retains the exact local error 1/2 at every prefix. |
| SRT-146 (6) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:146`][r183], `example` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L366`][r184], `example (extraction)`. Witness six and message seven extract thirteen on every challenge; the selector does not affect extraction. |
| SRT-150 (7) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:150`][r185], `example` | premise-required (P1) | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L996`][r186], `selected_fresh`. The complete selected interaction has the uniform challenge marginal for every input, authored selector and oracle message; external draws replace the authored verifier freshness predicate. |
| SRT-156 (8) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:156`][r187], `actual_game_bound` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L938`][r188], `selected_actual_game_bound`. Retains the always-returning plain verifier, challenge-based relation and error 1/2 in both exact authored carriers. |
| SRT-175 (9) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:175`][r189], `nativeResult_eq` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L783`][r190], `replayResult_eq`. Returns the value seven on both challenges, in the authored Fin 8/Fin 9 carriers. plainScriptedRun_eq proves actual party replay. |
| SRT-182 (10) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:182`][r191], `#eval evalWithAnswerFn` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L807`][r192], `#eval replayResult true true`. Retains (7, true, 7); the universal replay theorem covers both selectors independently. |
| SRT-183 (11) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:183`][r193], `#eval evalWithAnswerFn` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L811`][r194], `#eval replayResult false false`. Retains (7, false, 7), separately from rejecting oracle replay. |
| SRT-184 (12) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:184`][r195], `#eval extractInputWitness inputState extractor terminalWitness 0` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L371`][r196], `#eval knowledge.extractAlong`. Retains the evaluated extraction thirteen. |
| SRT-215 (13) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:215`][r197], `oracleObservation_true` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L826`][r198], `selectedVerdict`. For every input and message, true returns the exact selected statement and original Fin 8 output oracle. |
| SRT-219 (14) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:219`][r199], `oracleObservation_false` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L826`][r200], `selectedVerdict`. For every input and message, false rejects; only the statement-carrier selector changes. |
| SRT-223 (15) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:223`][r201], `oracleOutputLaw` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L851`][r202], `selectedOracleOutputLaw`. Retains the complete leaf-state iff at every input, transcript and supplied witness. The output oracle remains Fin 8. |
| SRT-245 (16) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:245`][r203], `actual_oracle_game_bound` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L1004`][r204], `selected_actual_oracle_game_bound`. Retains the zero-query closed-game bound 1/2 in both authored carriers, derived from the general selectedGame_bound. |
| SRT-258 (17) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:258`][r205], `example` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L1060`][r206], `example (no related rejecting claim)`. False excludes every claim satisfying any relation, which implies the frozen assertion for each witness. |
| SRT-264 (18) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:264`][r207], `#eval closedTerminalObservation` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L815`][r208], `#eval oracleReplayResult false true`. Actual selected oracle replay retains some (7, 7) on true; oracleReplayResult_eq proves the quantified law. |
| SRT-266 (19) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:266`][r209], `#eval closedTerminalObservation` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L819`][r210], `#eval oracleReplayResult true false`. Actual selected oracle replay retains none on false. |
| SRT-274 (20) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:274`][r211], `actual_coin_oracle_game_bound` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L1012`][r212], `selected_actual_coin_game_bound`. Retains both original coin-selected adversaries, their fixed-coin bounds and error 1/2. |
| SRT-291 (21) | [`ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean:291`][r213], `example` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L1026`][r214], `example (failed coins)`. Retains probability zero when the private coin computation fails. |

## ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean

| ID (entry 20 row) | Exact frozen assertion | Status | Exact target and correspondence |
| --- | --- | --- | --- |
| SRBT-091 (1) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:91`][r215], `preserving` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L294`][r216], `preserving`. Retains all sender preservation laws at every input and prefix. |
| SRBT-104 (2) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:104`][r217], `bounded` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L326`][r218], `bounded`. Retains distinct challenge alphabets and local errors 1/8 and 1/16. |
| SRBT-176 (3) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:176`][r219], `inputLaw` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L378`][r220], `inputLaw`. Retains the root relation for every input and witness. |
| SRBT-182 (4) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:182`][r221], `observation` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L841`][r222], `PublicSelection.observation`. For every input, two messages and two challenges, retains the acceptance disjunction and second message; an authored Boolean selects Fin 8/Fin 9. |
| SRBT-198 (5) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:198`][r223], `outputLaw` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L869`][r224], `PublicSelection.outputLaw`. Retains the complete leaf-state iff and every witness under each authored selector; output oracles remain Fin 8. |
| SRBT-235 (6) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:235`][r225], `queryBound` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L150`][r226], `queryBound`. The adversary still queries the later salted key twice before completion; bound two is unchanged. |
| SRBT-242 (7) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:242`][r227], `example` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L413`][r228], `example (extraction)`. Retains extracted value eighteen on every pair of challenges. The extra Core #eval at line 418 checks one instance. |
| SRBT-246 (8) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:246`][r229], `max_errors` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L159`][r230], `max_errors`. Retains maximum error 1/8. |
| SRBT-253 (9) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:253`][r231], `sum_errors` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L168`][r232], `sum_errors`. Retains sum 3/16. |
| SRBT-261 (10) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:261`][r233], `actual_nonuniform_game_bound` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L900`][r234], `PublicSelection.actual_nonuniform_game_bound`. Retains the same adaptive adversary and error 7/16 in both authored carriers. restoredExecution_charge at line 179 retains the original complete-path round charge. |
| SRBT-284 (11) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:284`][r235], `example` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L203`][r236], `example (strict improvement)`. Retains the strict comparison against the coarser uniform bound. |
| SRBT-292 (12) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:292`][r237], `example` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L1032`][r238], `example (reachable bad execution)`. For each authored selector the accepting claim is related to witness six, extraction returns eighteen and the input relation fails. |
| SRBT-305 (13a) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:305`][r239], `#eval closedTerminalObservation` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L1046`][r240], `#eval closedVerdict (selectedTranscript false 5 0 7 1)`. Retains some (7, 7) at challenges (0, 1). |
| SRBT-308 (13b) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:308`][r241], `#eval closedTerminalObservation` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L1051`][r242], `#eval closedVerdict (selectedTranscript true 5 1 7 1)`. Retains none at challenges (1, 1). This source line was mislabeled as extraction evaluation in entry 20's row 14. |
| SRBT-315 (stage 1) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:315`][r243], `firstMessageStage` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L487`][r244], `stages`. The first message stage uses the same charged addCountProgram on the actual message. Explicit root and leaf programs are uncharged. |
| SRBT-320 (stage 2) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:320`][r245], `firstChallengeStage` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L487`][r246], `stages`. The first challenge stage remains the uncharged identity. |
| SRBT-325 (stage 3) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:325`][r247], `secondMessageStage` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L487`][r248], `stages`. The second message stage uses the same charged addition on its actual message. |
| SRBT-332 (stage 4) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:332`][r249], `secondChallengeStage` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L487`][r250], `stages`. The second challenge stage is identity after the frozen Nat × Unit leaf witness is identified with Nat; Core uses Nat as the identified leaf carrier, with an uncharged identity leaf program. |
| SRBT-338 (15) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:338`][r251], `example` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L512`][r252], `example (challenge stage maps)`. Retains identity and first projection under the Nat × Unit leaf identification, for every prefix, challenge and witness. |
| SRBT-346 (stages) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:346`][r253], `stages` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L487`][r254], `stages`. Composes the four named stage programs in the same order, with explicit zero-cost endpoint programs. |
| SRBT-353 (16) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:353`][r255], `example` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L525`][r256], `example (stage budgets)`. Retains stage budgets one, zero, one, zero along every prefix; stages_budgetAtMost_one also bounds both endpoints by zero. |
| SRBT-360 (17) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:360`][r257], `stages_budgetAtMost_one` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L535`][r258], `stages_budgetAtMost_one`. Retains the common step bound one and explicitly proves root/leaf bounds zero. |
| SRBT-365 (18) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:365`][r259], `stages_protocolBudgetAtMost` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L555`][r260], `stages_protocolBudgetAtMost`. Retains one charged message and zero-cost challenge per round, plus zero-cost endpoints. |
| SRBT-369 (19) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:369`][r261], `example` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L574`][r262], `example (coarser protocol bound)`. Retains the coarser equal-message/challenge CostAtMost bound on every transcript. |
| SRBT-381 (20) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:381`][r263], `extractionProgram_budget` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L581`][r264], `extractionProgram_budget`. Retains budget two on every input and transcript. |
| SRBT-385 (21) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:385`][r265], `extractionProgram_costAtMost` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L586`][r266], `extractionProgram_costAtMost`. Retains CostAtMost two on every input and transcript. |
| SRBT-390 (22) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:390`][r267], `example` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L591`][r268], `example (program result)`. The composed run returns the named backward extraction on every transcript and supplied witness. |
| SRBT-396 (23) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:396`][r269], `extractionProgram_run_inputWitness` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L597`][r270], `extractionProgram_run`. Under the uncharged leaf identification, returns w + m₂ + m₁, exactly the game's extracted input witness, for all messages/challenges/witnesses. |
| SRBT-410 (24) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:410`][r271], `extractionObservation_cost` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L610`][r272], `extractionObservation_cost`. Every typed transcript and supplied witness records the two actual additions. |
| SRBT-417 (25) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:417`][r273], `extractionObservation_result` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L617`][r274], `extractionObservation_result`. Erasing the recorded instruction charge returns the extracted witness. |
| SRBT-424 (26) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:424`][r275], `extractionProgram_writer` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L632`][r276], `extractionProgram_writer`. Retains the exact suffix-before-first-message writer equation on every transcript and view. Zero-cost endpoint conversions are separate. |
| SRBT-452 (27) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:452`][r277], `#eval checkExtractionObservation` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L659`][r278], `#eval checkExtractionObservation`. Executes the composed program and checks witness eighteen with two charged additions. |
| SRBT-455 (28) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:455`][r279], `example` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L663`][r280], `example (first stage composition)`. Retains backward extraction as suffix extraction followed by the first message stage, for every path and witness. |
| SRBT-461 (certificate) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:461`][r281], `measuredCertificate` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L669`][r282], `measured`. Packages the same state function, local bounds and measured stages; the parent state-function record includes sender preservation. |
| SRBT-470 (29) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:470`][r283], `example` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L675`][r284], `example (underlying state function)`. The measured object's underlying state function is the named knowledge state function. |
| SRBT-473 (30) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:473`][r285], `example` | equivalent | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L678`][r286], `example (measured witness bridge)`. The library run_programAlong bridge returns the game's input witness, for every input/transcript/witness. |
| SRBT-482 (31) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:482`][r287], `example` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L1002`][r288], `PublicSelection.measured_game_bound`. The packaged theorem retains the selected closed-game bound, all input/path/witness quantifiers and cost two. |
| SRBT-502 (32) | [`ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean:502`][r289], `example` | premise-required (P2) | [`ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L1022`][r290], `PublicSelection.program_run_game_bound`. The failure event uses the actual program result and retains error 7/16 and cost two. |

## Verification

The targeted reverse-dependency build compiles both production modules and both Core fixtures,
including their guarded executable assertions and transitive axiom collectors. The collectors
also audit the new support, supported-replay and zero-endpoint budget theorems. The branch guard
checks documentation, frozen paths, forbidden proof escapes, module headers, imports and style.
No whole-library or site build is part of this branch's acceptance checks.

[r1]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L36
[r2]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L58
[r3]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L50
[r4]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L71
[r5]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L56
[r6]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L371
[r7]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L66
[r8]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L78
[r9]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L76
[r10]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L88
[r11]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L81
[r12]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L93
[r13]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L85
[r14]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L78
[r15]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L94
[r16]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L98
[r17]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L100
[r18]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L104
[r19]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L106
[r20]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L110
[r21]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L111
[r22]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L116
[r23]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L119
[r24]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L116
[r25]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L127
[r26]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L116
[r27]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L138
[r28]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L128
[r29]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L144
[r30]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L284
[r31]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L158
[r32]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L293
[r33]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L192
[r34]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L336
[r35]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L199
[r36]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L921
[r37]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L223
[r38]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L132
[r39]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L228
[r40]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L137
[r41]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L232
[r42]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L144
[r43]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L239
[r44]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L150
[r45]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L249
[r46]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L160
[r47]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L273
[r48]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L182
[r49]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L281
[r50]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L190
[r51]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L289
[r52]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L197
[r53]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L305
[r54]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L212
[r55]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L324
[r56]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L230
[r57]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L337
[r58]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L897
[r59]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L362
[r60]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L78
[r61]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L371
[r62]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L243
[r63]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L380
[r64]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L252
[r65]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L392
[r66]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L913
[r67]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L400
[r68]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L921
[r69]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L426
[r70]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L951
[r71]: ../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L474
[r72]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L996
[r73]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L37
[r74]: ../../../ArkLib/Interaction/Core/Reduction.lean#L159
[r75]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L43
[r76]: ../../../ArkLib/Interaction/Core/OracleVerifier.lean#L580
[r77]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L48
[r78]: ../../../ArkLib/Interaction/Core/OracleVerifier.lean#L517
[r79]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L54
[r80]: ../../../ArkLib/Interaction/Core/Reduction.lean#L159
[r81]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L67
[r82]: ../../../ArkLib/Interaction/Core/OracleVerifier.lean#L580
[r83]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L81
[r84]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L477
[r85]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L90
[r86]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L477
[r87]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L99
[r88]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L495
[r89]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L106
[r90]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L501
[r91]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L113
[r92]: https://github.com/Verified-zkEVM/VCVio/blob/f8d7f8ef52b9afaf4e6d897804b9dce347cdb1db/VCVio/OracleComp/SimSemantics/StateT/Basic.lean#L324
[r93]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L131
[r94]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L517
[r95]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L147
[r96]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L336
[r97]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L151
[r98]: ../../../ArkLib/Interaction/Core/OracleVerifier.lean#L580
[r99]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L162
[r100]: ../../../ArkLib/Interaction/Core/OracleVerifier.lean#L517
[r101]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L178
[r102]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L665
[r103]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L224
[r104]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L636
[r105]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L300
[r106]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L665
[r107]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L331
[r108]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L350
[r109]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationReplay.lean#L354
[r110]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L350
[r111]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationGame.lean#L36
[r112]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L368
[r113]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationGame.lean#L48
[r114]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L396
[r115]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationGame.lean#L68
[r116]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L419
[r117]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationGame.lean#L92
[r118]: ../../../ArkLib/Interaction/Core/Security/KnowledgeComposition/Extraction.lean#L345
[r119]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationGame.lean#L102
[r120]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L1039
[r121]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationOracle.lean#L32
[r122]: ../../../ArkLib/Interaction/Core/OracleVerifier.lean#L508
[r123]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationOracle.lean#L45
[r124]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L407
[r125]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationOracle.lean#L66
[r126]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L375
[r127]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationOracle.lean#L83
[r128]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L430
[r129]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationOracle.lean#L106
[r130]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L1070
[r131]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationCoins.lean#L35
[r132]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L1101
[r133]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationCoins.lean#L76
[r134]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L1134
[r135]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean#L30
[r136]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L57
[r137]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean#L33
[r138]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L68
[r139]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean#L40
[r140]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L73
[r141]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean#L47
[r142]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L88
[r143]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean#L62
[r144]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L921
[r145]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean#L86
[r146]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L921
[r147]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean#L111
[r148]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L127
[r149]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean#L127
[r150]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L103
[r151]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean#L149
[r152]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L127
[r153]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean#L162
[r154]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L139
[r155]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean#L184
[r156]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L161
[r157]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean#L202
[r158]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L188
[r159]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationBudget.lean#L232
[r160]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L255
[r161]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationResources.lean#L40
[r162]: ../../../ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L290
[r163]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationResources.lean#L52
[r164]: ../../../ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L303
[r165]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationResources.lean#L65
[r166]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L396
[r167]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationResources.lean#L93
[r168]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L423
[r169]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationResources.lean#L107
[r170]: ../../../ArkLib/Interaction/Core/Security/MeasuredExtraction.lean#L177
[r171]: ../../../ArkLib/Interaction/Oracle/Security/StateRestorationResources.lean#L125
[r172]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L506

[r173]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L87
[r174]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L300
[r175]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L89
[r176]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L962
[r177]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L96
[r178]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L313
[r179]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L105
[r180]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L323
[r181]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L113
[r182]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L339
[r183]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L146
[r184]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L366
[r185]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L150
[r186]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L996
[r187]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L156
[r188]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L938
[r189]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L175
[r190]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L783
[r191]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L182
[r192]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L807
[r193]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L183
[r194]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L811
[r195]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L184
[r196]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L371
[r197]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L215
[r198]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L826
[r199]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L219
[r200]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L826
[r201]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L223
[r202]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L851
[r203]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L245
[r204]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L1004
[r205]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L258
[r206]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L1060
[r207]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L264
[r208]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L815
[r209]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L266
[r210]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L819
[r211]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L274
[r212]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L1012
[r213]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestoration.lean#L291
[r214]: ../../../ArkLibTest/Interaction/Core/Security/StateRestoration.lean#L1026
[r215]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L91
[r216]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L294
[r217]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L104
[r218]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L326
[r219]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L176
[r220]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L378
[r221]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L182
[r222]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L841
[r223]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L198
[r224]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L869
[r225]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L235
[r226]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L150
[r227]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L242
[r228]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L413
[r229]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L246
[r230]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L159
[r231]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L253
[r232]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L168
[r233]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L261
[r234]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L900
[r235]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L284
[r236]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L203
[r237]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L292
[r238]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L1032
[r239]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L305
[r240]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L1046
[r241]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L308
[r242]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L1051
[r243]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L315
[r244]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L487
[r245]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L320
[r246]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L487
[r247]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L325
[r248]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L487
[r249]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L332
[r250]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L487
[r251]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L338
[r252]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L512
[r253]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L346
[r254]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L487
[r255]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L353
[r256]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L525
[r257]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L360
[r258]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L535
[r259]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L365
[r260]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L555
[r261]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L369
[r262]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L574
[r263]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L381
[r264]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L581
[r265]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L385
[r266]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L586
[r267]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L390
[r268]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L591
[r269]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L396
[r270]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L597
[r271]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L410
[r272]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L610
[r273]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L417
[r274]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L617
[r275]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L424
[r276]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L632
[r277]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L452
[r278]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L659
[r279]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L455
[r280]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L663
[r281]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L461
[r282]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L669
[r283]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L470
[r284]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L675
[r285]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L473
[r286]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L678
[r287]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L482
[r288]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L1002
[r289]: ../../../ArkLibTest/Interaction/Oracle/Security/StateRestorationBudget.lean#L502
[r290]: ../../../ArkLibTest/Interaction/Core/Security/StateRestorationBudget.lean#L1022

[r291]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L508

[r292]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L694

[r293]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L410

[c1]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L549
[c2]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L452
[c3]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L137
[c4]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L921
[c5]: ../../../ArkLib/Interaction/Core/Security/StateRestoration.lean#L293
[c6]: ../../../ArkLib/Interaction/Core/Security/StateRestorationBudget.lean#L161
