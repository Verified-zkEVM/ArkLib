# Stage composition and oracle execution: port table

This table compares six old-layer sources with their interaction-layer ports:

- the acceptance clients `ClaimExample.lean`, `CompositionExample.lean`, `CoreRunExample.lean`
  and `ExecutionExample.lean` in `ArkLibTest/Interaction/Oracle/`;
- the client `ArkLibTest/Interaction/Reduction/DependentExample.lean`;
- the ordered-execution laws in `ArkLib/Interaction/Oracle/Composition.lean`.

Line numbers such as L29 are lines of the old-layer source. Each one identifies a single
declaration, example, negative elaboration test or axiom check. The
[logged-execution table][logged] covers the other old-layer test files that use
`ExecutionExample.lean` and `CoreRunExample.lean` as fixtures. This table covers the assertions of
those two files themselves.

The two approved premises are:

- **P1 (passive verifier):** bundle queries happen only in the final decision, and a program
  indexed by the challenge node supplies each challenge. In a chain, that program is a stage's
  `draw : (c : ChallengeNode oracleSig s) → OracleComp ambient _`. It cannot read an input or a
  previously sent oracle. This is the structural restriction that the core enforces.
  Public-coin sampling is a separate condition that a client states when it needs it. For example,
  [WARP §3.2](https://eprint.iacr.org/2025/753) specifies a uniformly random verifier message in
  each round. The types do not impose it: a draw runs in `OracleComp ambient`, the interface the
  prover also uses. Under a stateful interpretation of `ambient`, a draw can return a bit that the
  prover wrote earlier, so the condition concerns both the draws and the interpretation of
  `ambient`.
- **P2 (fixed shape):** neither a challenge nor an oracle message directly selects the protocol's
  subtree. Only the prover's public messages select the continuation. A prover can choose those
  messages after seeing a challenge, so a challenge can still affect the continuation through the
  prover.

Each row has one of four statuses:

- **ported:** the new tests check the same mathematical observation, at least as generally as the
  old-layer assertion.
- **excluded by P1** (or **P2**): the row states exactly which assertion P1 (or P2) excludes, and
  what the new tests still check.
- **removed:** the row names a mechanism that no longer exists. Every mathematical observation
  that the mechanism carried has its own row.
- **open:** the row names an interface that the parent branch is missing.

`StageChain` is the right-associated passive composition API: a chain appends its first stage to
the composed rest. The old-layer executor could skip later interactions after a rejection. A
chain runs every interaction and then folds the decisions. `StageChain.run_cons` unfolds one
append, and `OracleVerifier.run_append` splits that append into its interactions and decisions.

One row is open: the split of an ordered execution at an arbitrary stage (`Composition.lean`
L258). It needs a reassociation law for `OracleVerifier.append`, with the ingredients listed in
that row.

## Universes

The ports keep the old-layer universe placement, with one restriction in the dependent-reduction
canary.

- `StageChain` ([stages]) puts every statement type, oracle index type and oracle data type of a
  chain in the computation universe `u`, as `ExecutionInterface.{u}` does. It takes
  `ambient : OracleSpec.{u, u} ι` with `ι : Type u`, as the old-layer stage does. The old-layer
  stage passes its input resource as `I.oracles.spec.toPFunctor : PFunctor.{u, u}`, so its query
  domain lies in `u`.
- Inside a chain, the oracle families have their query types in one universe `w`, because a
  recursive occurrence of an inductive type keeps the type's universe parameters. This is a
  choice of representation, not a consequence of P1 or P2. It does not restrict the families at a
  chain's boundaries.
  - `OracleFamily.liftQueries` ([liftQueries]) gives a family with query universe `wI` its queries
    in `max wI w'`, as `ULift` of the original queries, with the same data and answers.
  - `OracleVerifier.liftInputs` ([liftInputs]) and `OracleVerifier.liftOutputs` ([liftOutputs])
    adapt a stage verifier with families in other query universes. `OracleVerifier.lowerOutputs`
    ([lowerOutputs]) recovers the original family of a chain's output.
  - The recovery laws keep the decision and the output data on the same data ([liftInputsDecide],
    [liftInputsData], [liftOutputsData], [lowerOutputsData]). The adapters are instances of
    `OracleVerifier.comapInputs` and `OracleVerifier.mapOutputs` ([comapInputs], [mapOutputs],
    [comapInputsDecide]). Reading the inputs through an oracle map gives the same run after the
    decision's bundle queries are answered from the supplied data ([comapInputsRun]). This
    equality does not bound the queries that the map issues for each routed query. Two maps with
    the same answers can charge differently. In the answer-only fixture, `repeated` issues two
    source queries for each routed query and `identity` issues one, and both give the same
    answers ([claimRow3]). A client that needs a charge bound proves it separately, for
    example with `OracleMap.withAmbient_worstCaseCost` from #1476 in the universes it supports.
    The stage API does not depend on the resource contracts of #1528.
  - The binary `OracleVerifier.append` keeps independent query universes for its input, middle
    and output families. So do the binary decision laws ([appendReject] to [appendMeasure]).
  - The canary [wideStages] reads inputs with queries in `Type` and exports a family with queries
    in `Type 1`. [wideDecide] states that the chain decides as the original stage on the original
    data. [wideNarrow] continues to a stage that exports a family with queries in `Type`, which
    leaves the chain through `lowerOutputs` ([wideNarrowRows]).
- The old-layer private state lies in `u`. In the port it is part of the prover's output, whose
  family lies in `u` ([stagesRun]).
- The dependent-reduction canary ([depCanary]) keeps the shared, statement, witness and
  interaction universes independent, as the old-layer canary does. There is one restriction. A
  nonempty ambient specification lies in the interaction universe, because the prover runs in
  `OracleComp ambient : Type u → Type u` (implementation note 18). The old-layer canary has no
  ambient oracles, and the empty specification recovers it.

## ClaimExample.lean

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| L25 `observed` and L31 `answerProblem`, the relation over closed claims | ported | [claimClosedProblem] states the same claim-dependent witness relation over `Nat × tagged.Behavior`, a statement with arbitrary deterministic answers. [claimBridge] shows that on concrete data it is the relation [claimAnswerProblem]. |
| L27, the unobservable tag vanishes from the closed claim | ported | [claimRow1]: the closed claims of statement 7 with the behaviors of `(7, true)` and `(7, false)` are equal. `ConcreteClaim.toClosed` is exactly this pair of the statement and `behaviorOfRealizations`. |
| L37, the closed claim 7 is in the language | ported | [claimRow2Closed] at the old-layer closed-claim relation; [claimRow2] at the concrete-data relation. |
| L46, `SemEquiv (.id tagged) repeated` | ported | [claimRow3]: under every deterministic handler of `tagged.spec`, the query-twice program and the identity embedding give the same answers. [claimLaws] adds that both oracle maps agree with the materialized data. |
| L53, closing a substituted open claim | ported | [claimRow4] quantifies over every source index type in `Type`, every source specification, every virtual program `view : QueryImpl tagged.spec (OracleComp spec)` and every deterministic source handler. For all of these, closing the claim `(7, repeated)` after substituting `view` equals closing it with the evaluated view. [claimRow4Map] and [claimRow4Data] state the same substitution for `OracleMap.comp`, with its data map. |
| L60, the relation cannot distinguish derivations with the same answers | ported | [claimRow5] quantifies over every source specification and two claims made of a statement and virtual programs. If the statements are equal and the answers are equal under every deterministic handler, the claims have the same membership in the old-layer closed-claim language under every handler. [claimRow5Map] states the oracle-map form through the maps' laws and [claimCongr]. |
| L25 `ClosedClaim`, L27 `ConcreteClaim.toClosed`, L42 `VirtualOracle.ofQuery`, L55 `OpenClaim.subst` and `closeWith`, L65 `closeWith_congr` as API | removed | Removed mechanism: claims that carry behaviors or open query programs. Record D6 keeps concrete data with an oracle map (`f`, `impl` and the law tying them). It rejects the alternative "behavior only, without `f`". The rows above port each assertion these names carried, with `QueryImpl` programs and handlers. |

## CoreRunExample.lean

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| L91, history `[0, 1, 2]` | ported | [coreRow1]: the history is `[0, 1, 2]` for every hidden value, each event once. |
| L51, verifier event 1 at the oracle receive | excluded by P1 | P1 excludes verifier effects at protocol nodes. The passive decision performs event 1 as its first effect ([coreVerifier]). The history of L91 does not change, because no prover effect follows the receive. |
| L93, private output `hidden` | ported | [coreRow2], for every hidden value. |
| L95, accepted statement 11 | ported | [coreRow3]: the statement is the queried first coordinate 11. |
| L97, output oracle answers 18 | ported | [coreRow4]: the output data is `7 + 11`, computed by the oracle map [closeMap] from this run's input and oracle messages. [coreSummary] states the full accepted result for every message and hidden value. |
| L102, a different run answers 26 | ported | [coreRow5]: the run with message 19 closes with its own data, 26. |
| L106, rejection yields no claim | ported | [coreRow6], for every message and hidden value. |
| L109, setup runs once before the strategies | ported | [coreRow7]: setup event 3 runs once, before the send and decision events, and the outcome equals the run without setup. The old-layer row states this for the accepting verdict; the new test states it for both verdicts. The old-layer setup is a reduction-level effect. Here it is the prover's first effect. [coreRunCmd] evaluates the same runs. |
| L38 `outputOracle` and L44 `terminal`, an output program in an open terminal claim | removed | Removed mechanism: `OpenClaim` terminal outputs, closed by `CoreRun.closedOutput` with the run's input handler. The output is concrete data from [closeMap]. L97 and L102 keep its answers. |
| L67 `reduction`, L73 `reductionWithSetup`, L86 `executeStrategiesCore` | removed | Removed mechanism: the strategy executor and the reduction executor `executeCore` with a separate setup step. [oracleRun] runs the prover against the sampler, then the decision. |

## CompositionExample.lean

The old-layer ordered execution decides each stage before the next stage's interaction starts, and
a rejection skips the later stages. P1 excludes that schedule. A passive decision runs after the
whole interaction, and its bundle queries happen in the final decision. The port is the chain
`twoStages` in the core test `StageChain.lean`. Both interactions run first, and then the decisions
fold. The accepted history is therefore `[0, 2, 1, 3]`. The second stage's interaction runs before
the first decision, including when that decision rejects. `StageChain.run_cons` identifies the chain's run with the binary
composition of the same two stages in `HeterogeneousAppend.lean` ([compRow3to5], [compSummary],
[compRow13]), which states the same rows. Additional coverage:

- a third stage with a sampled challenge, whose interaction also runs before the first decision,
  including when that decision rejects ([threeAccept], [threeReject]);
- a second stage selected by the first stage's prover message ([shapeTrue], [shapeFalse]).

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| L24, local `implicit_reducible` attribute | removed | Removed mechanism: a local transparency override on `OracleInterface.toOracleSpec` and `OracleInterface.Response`. The ports drop these two local attributes and need no transparency command. The new fixtures keep two `@[reducible]` annotations, both on definitions of class type: `wideInterface : OracleInterface Bool` and the answer measure `alwaysTrue`. Without the one on `wideInterface`, the build warns that a definition of class type is semireducible. The earlier revision also marked 15 protocols and oracle families `@[instance_reducible]`. The fixtures elaborate without them, so this revision removes them. |
| L134, `firstStage_run` | ported | [compRow1] holds for every verdict, input, branch choice and hidden value. It checks events 0 then 1, the input's parity as statement, the input plus 11 as data, and `hidden + 1` in the prover output. The old-layer input behavior `answers : naturals.spec.Domain → Nat` and the new data `answers : Unit → Nat` determine each other. The family has one index with one `Unit` query, answered by the data. |
| L144, `secondStage_run` | ported | [compRow2True] and [compRow2False] hold for both message types and every input statement, exported value and hidden value. They check events 2 then 3 and the same statement, data and private output. The old-layer setup event 2 is the prover's first effect. |
| L169 `stages_zero` and L173 `stages_one` | removed | Removed mechanism: the `Fin`-indexed stage family built with `Fin.cons`, whose indices must be resolved. A chain lists its stages in order as constructors. [threeVerifierCons] states that a chain's verifier is the append of its first stage and the rest, without unfolding either. |
| L176, `run_two` | excluded by P1 | P1 excludes running the first stage to its decision before the second stage's interaction. It also excludes skipping the second stage after a rejection. [twoRunCons] keeps the resolution of the chain into its two actual stages. The chain's run is the run of the binary append of the first stage and the second. [runAppend] splits that run into the first interaction, the second interaction, the first decision and, after acceptance only, the second decision. [threeRunCons] states the same for three stages. |
| L202, `observed_true` | excluded by P1 | P1 excludes the order of L217. [summaryTwoWithTrue] keeps the normal form, the statement, the oracle and the private outputs for every branch choice, input and hidden value, with history `[0, 2, 1, 3]`. |
| L217, history `[0, 1, 2, 3]` | excluded by P1 | P1 excludes the first decision's event 1 before the second stage's events. [stagesRow7] keeps each of the four events once, in the passive order `[0, 2, 1, 3]`. |
| L220, statement 118 on the `Bool` branch | ported | [stagesRow8]. |
| L225, statement 72 on the `Nat` branch | ported | [stagesRow9]. |
| L230, final oracle `true` | ported | [stagesRow10]: the data of the exported `Bool` oracle, which is its answer. |
| L235, final oracle `false` | ported | [stagesRow11]. |
| L241, private outputs `(41, 42)` | ported | [stagesRow12]. |
| L246, rejection gives `(none, [0, 1])` | excluded by P1 | P1 excludes the abort on rejection, which skips the second stage's seam event 2 and its interaction. [stagesRow13] keeps the `none` verdict and the skipped second decision, whose event 3 does not run, for every branch choice, input and hidden value. The second stage's interaction runs, so the history is `[0, 2, 1]`. [stagesRow13Fixed] states `(none, (41, 42), [0, 2, 1])` at the old-layer input. |
| L249, the lower adapter keeps oracle output and private output | ported | [compRow14]: output data 18 and private output `hidden`, for every hidden value. The table for `Composition.lean` lists `executeClosed` as removed. |

## ExecutionExample.lean

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| L107, verdict 37 | excluded by P1 | P1 excludes the challenge `7 + 11` computed from the input and the first oracle. [execRow1] samples the challenge and checks it against the queried input plus the first answer. It keeps the verdict `19 + 18 = 37` at the draw 18, for every hidden value. Other draws reject. |
| L110, history `[0, 1, 5, 2, 4, 3]` | excluded by P1 | P1 excludes verifier events 0, 5 and 2 at the public receive, the oracle receive and the challenge. [execRow2] keeps the six events, each once, in the passive order `[1, 4, 0, 5, 2, 3]`. [full] reproduces the old-layer list with private output `(777, hidden)` and verdict 37 in a passive client. It does not reproduce the old-layer assignment of each event to a participant. |
| L113, private output `(777, hidden)` | ported | [execRow3]. |
| L116, public result `⟨true, (), 18, (), ()⟩` | excluded by P1 | P1 makes the challenge 18 in the view sampled rather than computed. [execRow4] keeps the view, with both oracle messages erased, at the draw 18. |
| L123, `publicResult_eq` | excluded by P1 | P1, as for L116. [execRow5] keeps the view and the verdict 37 at the draw 18. |
| L129, hidden data does not change the public result | excluded by P1 | P1, as for L116. [execRow6] keeps the invariance for every pair of hidden values, at the draw 18. |
| L141, negative test: an oracle-node verifier cannot receive the oracle message | ported | [execRow7]: a decision that reads the hidden coordinate of a sent oracle does not elaborate, because the view gives oracle moves the type `PUnit`. |
| L149, positive counterpart: a query reaches the observable coordinate | ported | [execRow8]. |
| L159, negative test: the verifier action at the receive node before the second send cannot query the second oracle | excluded by P1 | P1 removes verifier actions at protocol nodes, so the core has no action at that receive node to test. The next row checks the same restriction at decision time. |
| L159, the same restriction at decision time: a decision cannot query an oracle sent after its own path | ported | [execRow9Neg]: the prefix decision's bundle does not name the second sent oracle, so the query does not elaborate. [execRow9Pos]: the composed decision can name it. |
| L165, `executeStrategies_eq_run` erasure equation | removed | Removed mechanism: conversion of oracle strategies to plain counterparts on the type tree (`Verifier.toCounterpart`, `TypeTree.ExecutionPath.ofTypeTreePath`). [execRow10] states the oracle verifier's run of the same strategies by definition. It is the paired run against the sampler followed by the decision. |
| L44 and L47, access after each oracle send | removed | Removed mechanism: per-node access (`Access.extend`). A decision's bundle depends only on its path ([pathBundle]). Record D6 removes per-node access once verifiers are passive. |
| L180 to L182, axioms of `accessAt_comp`, `AccessDecoration.restrict_build`, `Verifier.decorate_access` | removed | Removed mechanism: per-node access decorations. |
| L183 and L184, axioms of `toCounterpart_oracle_eq_of_answer_eq`, `executeStrategies_eq_run` | removed | Removed mechanism: the counterpart conversion of L165. |
| L185, axioms of `Reduction.execute` | ported | [execAxioms] checks that `OracleVerifier.run` and `Reduction.run` use only `propext`, `Classical.choice` and `Quot.sound`, and fails the build otherwise. |
| L279, `#check executeStrategies_append` at this fixture | ported | [execRow19] rewrites the composed run with `OracleVerifier.run_append` ([runAppend]) at this fixture. |
| L285, axioms of `executeStrategies_append` | ported | [execAxioms] covers `OracleVerifier.run_append`, `run_splitSampler` and `run_appendSampler`. |
| L292, verdict `some 30` | excluded by P1 and P2 | The old-layer prefix computes an `Option Nat` challenge from its oracle (P1), and `some` selects the branch with a second oracle send (P2). [execRow19] keeps the verdict `19 + 11 = 30` at the draw 18: the second message's answer plus the prefix value 11. [execRow19All] states the verdict for every draw on the same protocol. |
| L295, history `[10, 11, 12, 14, 15, 16, 17]` | excluded by P1 | P1 excludes prefix verifier events 11 and 12 before the prover's response. [execRow19] keeps the seven events, each once, as `[10, 14, 15, 11, 12, 16, 17]`. |
| L298, private output `hidden + 14` | ported | [execRow19] and [execRow19All]: the private output keeps the ambient answer 14 read after the challenge. |
| L300, abort gives `none` | excluded by P1 and P2 | P2 excludes the `none` challenge that selects a branch without a second send. P1 excludes the abort, which ends the execution before the remaining interaction. [execRow22] keeps the `none` verdict, for every draw and hidden value, through a rejecting prefix decision that runs after the whole interaction. |
| L303, abort history `[10, 11, 12, 14, 17]` | excluded by P1 and P2 | P1 excludes abort on rejection. The old-layer run stops at the abort and runs the abort branch's final action 17 instead of the remaining interaction. Under P1 every interaction runs before any decision, so the prefix verifier events 11 and 12 follow the prover's events. P2 excludes the abort branch without a second send. The port keeps the five old-layer events, each once, and the `none` verdict, with two changes. It adds event 15, the suffix send, which runs on the fixed protocol. It records event 17 in the rejecting prefix decision, as that decision's last query ([execFirstVerifier]), instead of as an abort action. [execRow22] gives `[10, 14, 15, 11, 12, 17]` for every draw and hidden value. The skipped suffix decision records neither 16 nor its own 17. |
| L305, abort private output `hidden + 14` | ported | [execRow22]. |
| L352, completed prefix then next send: `[40, 41]` | ported | [execRow25]. |
| L354, appended: `[41, 40]` | ported | [execRow26]. The appended completed decision is an end decision, so event 40 follows the next prover's event 41, as in the old-layer run. |
| L357, the two histories differ | ported | [execRow27]. |
| L407, history `[48, 49, 50, 51, 52]` | excluded by P1 | P1 excludes the suffix verifier's first move computed from an ambient answer at the seam, with events 49 and 50 before the response 51. [execRow28] keeps a sampled first suffix move after the prefix prover's event 48 and before the response 51. The history is `[48, 59, 51, 49, 50, 52]`, and the draw is logged as its value 59. |
| L409, private output `hidden + 59 + 51` | excluded by P1 | P1 makes the challenge 59 sampled rather than computed. [execRow29] keeps `hidden + 59 + 51` at the draw 59. |
| L411, verdict 59 | excluded by P1 | P1, as for L409. [execRow30] reads the challenge from the view, checks it against the answer 50 plus the prefix value 9, and returns 59. |

## Reduction/DependentExample.lean

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| L69, universe canary | ported | [depCanary]: the shared, statement, witness and interaction universes are independent. The output statement and prover output lie in the interaction universe, as in the old-layer canary. [depCanaryUse] instantiates it at `Type 3`, `Type 2`, `Type 1` and `Type 0`. The ambient restriction is recorded under Universes. |
| L24 and L32, role decorations | removed | Removed mechanism: role decorations. The prover and verifier signatures assign each move to a participant. |
| L99, `Reduction.then` over a shared index with `packAppend` outputs | removed | Removed mechanism: composition over a shared index that records the prefix path. [depComposed] composes with `Prover.append` and `Verifier.append`. Outputs are typed over the appended transcript, so `PFunctor.FreeM.Path.packAppend` is not needed. |
| L107, the false prefix selects the `Bool` branch | ported | [depRow2]. |
| L111, the true prefix selects the `Fin 3` branch | ported | [depRow3]. |
| L115, both participants' results on the `Bool` branch | ported | [depRow4] and [depObserveFalse]: the path, the prover's statement 0 with unit witness, and the verifier's statement 0. |
| L124, both participants' results on the `Fin 3` branch | ported | [depRow5] and [depObserveTrue]: both statements are 2. |
| L152, distinct intermediate outputs reach the suffix | ported | [depRow6]: the suffix prover sees the prover's `true` and witness 7, and the suffix verifier sees the verifier's `false`. The old-layer row fixes the sent bit `false`; the new test states it for both bits. |

## Oracle/Composition.lean

| Old-layer assertion | Status | Where it is ported, or what remains |
| --- | --- | --- |
| L34 `ClosedOutput`, L44 `CoreRun.closedOutput`, L54 `executeClosed` | removed | Removed mechanism: closing an open terminal claim with the run's input handler and sent messages. [oracleRun] applies the verifier's output map to the run's input data and oracle messages. CompositionExample L249 keeps the adapter's outcome ([compRow14]). |
| L70, `ExecutionInterface` | removed | Removed mechanism: boundary records that pair a public claim with a private prover state. A chain's boundary is the statement type and the oracle family of a stage's verifier output, which may depend on the path ([stages]). The private state is the prover's output ([stagesRow12]). |
| L83, `ExecutionInterface.Claim` as a closed claim | removed | Removed mechanism: behavior-only claims at a stage boundary, which record D6 replaces by concrete data. A chain's accepted claim is a statement with concrete data, the verdict of [stagesRun]. |
| L86, `ExecutionInterface.State` | removed | Removed mechanism: the boundary record of L70. Its public part is the claim of L83; its private part is the prover's output. |
| L92, `ClosedStage` | excluded by P1 and P2 | P1 excludes a stage that runs its own verifier strategies to a decision before the next stage starts, with node effects and verifier-computed challenges. P2 excludes a protocol selected by the statement that the previous stage accepted, which a challenge or an oracle answer may determine. [stages] keeps a stage as a passive oracle verifier with its protocol and its challenge draws. Its output map may read the stage's input statement. [compatibility] holds a general `OutputCompatibility` certificate at every boundary, and [stagesVerifier] builds the composed verifier from it ([compose]). [echoVerifier] exports its input statement as a scalar oracle, which no statement-free map describes ([echoNotFree]). [echoEvidence] and [echoOutput] compose it. [echoCheckEvidence] and [echoCheckRows] compose it with a second stage through `OutputCompatibility.ofStatement`. Statement-free output maps are the special case [statementFree], with certificates from [statementFreeCertify]. The path, which records prover messages only, selects the next stage ([shapeTrue], [shapeFalse]). The prover sees its private state through its own output instead of a witness prepared by the executor. |
| L119, `ClosedStage.run` | excluded by P1 | P1 excludes a stage run that ends in a decision before the next stage and hands over the next private state after acceptance only. [decideWithOne] keeps the single stage: a chain of one stage decides as that stage. [compRow1] keeps the outcome of the first stage's run. [rejectCons] keeps that a rejection hands over no claim. |
| L128, `run_eq_executeCore` | ported | [stagesRun]: a chain's run is by definition the core run `OracleVerifier.run` of the composed verifier under the stages' combined draws ([drawCons]). Its verdict is the accepted claim. The prover's output in the same run replaces the computed private state. |
| L145, `OrderedExecution.run` | excluded by P1 and P2 | P1 excludes the fold of whole stage runs, in which each stage decides before the next interaction and a rejection skips the later interactions and draws. P2 excludes later protocols selected by accepted statements. [stagesRun] keeps an n-ary execution of heterogeneous stages. Every interaction runs, and then the decisions fold through the binary append ([verifierCons]). Paths select the later stages. |
| L157, `run_zero` | ported | [decideWithNil] and [outputDataNil]: the empty chain accepts the input statement with the input data. |
| L162, `run_succ` | excluded by P1 | P1 excludes running the first stage to its decision before the rest. [runCons] keeps the split after the first stage: a chain's run is the run of the binary append of its first stage and the rest. [runAppend] splits that run into both interactions, the first decision and, after acceptance only, the rest's decision ([appendDecide]). |
| L171, `run_succ_of_reject` | excluded by P1 | P1 excludes skipping the later interactions after a rejection. [rejectCons] keeps the rejection: a rejecting first decision makes the chain reject and skips the later decisions. [appendReject] states it for the binary append. The later interactions have run ([stagesRow13], [threeReject]). |
| L182, `run_preserves` | excluded by P1 | P1 excludes the invariant over whole stage runs, which include each stage's interaction. [chainAccept] keeps the chain statement over the decisions. Its hypotheses are one deterministic acceptance per stage, with the predicate at that stage's boundary ([deterministicSteps]). From them, the composed decision accepts a statement with the final predicate. The predicates may differ in type at every boundary and may depend on the paths up to it ([boundaries]). The law concerns the fold of the decisions after all interactions. It is proved by induction on the chain from the binary law [appendAccept]. [sumAccepts] applies it to three stages ([sumStages], [sumSteps]). |
| L203, `run_preserves_support` | excluded by P1 | P1, as for L182. [chainSupport] keeps the chain statement over the support of the decisions, from one hypothesis per stage ([supportSteps]), by induction from [appendSupport]. [sumSupport] applies it to the three stages. |
| L230, `run_preserves_measure` | excluded by P1 | P1, as for L182. [chainMeasure] keeps the almost-sure chain statement over the decisions, from one hypothesis per stage ([measureSteps]), by induction from [appendMeasure]. It uses the old-layer assumptions: an answer measure on the ambient oracles and measurable, discrete statement spaces. Each boundary event carries the discrete measurable structure of its statement type ([discreteEvent]). Probabilities come from the chosen `OracleSpec.AnswerMeasure` instance on the ambient oracles. [coinAlmostSurely] applies the law to a one-stage decision that queries an ambient `Bool` and rejects on `false`, under the answer measure `alwaysTrue`, which puts all mass on `true`. The same decision can reject on its structural support ([coinRejectSupport]), so the support law does not apply ([coinNotOnSupport]). A persistent runtime with private state needs its own compatibility statement or invariant relating it to the chosen measure. |
| L258, `run_append` | open | Missing parent interface: a reassociation law for `OracleVerifier.append`. It relates `(V₁.append V₂ c₁₂).append V₃ c` to the append of `V₁` with the appends of `V₂` and `V₃`. The interface also includes the transport of paths and views along protocol associativity and the agreement of `prefixRoute` and `suffixRoute` on both sides. It also includes the reassociation of the compatibility certificates and their output maps. The split of a chain at an arbitrary stage needs this law and the concatenation of chains. It also needs the prover continuation retained at the cut. The protocol part exists at the PolyFun pin `713d8857`: `PFunctor.FreeM.append_assoc` (`PolyFun/PFunctor/Free/Path.lean` L727), with the inverse laws `Path.split_append` (L766) and `Path.append_split` (L777). The concatenation pattern is `Chain.then` with `Chain.toTypeTree_then` (`PolyFun/Interaction/Basic/Chain/Append.lean` L94). [runCons] gives only the split after the first stage. |

[logged]: port-logged-execution.md
[full]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L589
[closeMap]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L84
[claimRow1]: ../../../ArkLibTest/Interaction/Core/Oracle/AnswerOnlyRelations.lean#L30
[claimAnswerProblem]: ../../../ArkLibTest/Interaction/Core/Oracle/AnswerOnlyRelations.lean#L42
[claimRow2]: ../../../ArkLibTest/Interaction/Core/Oracle/AnswerOnlyRelations.lean#L50
[claimClosedProblem]: ../../../ArkLibTest/Interaction/Core/Oracle/AnswerOnlyRelations.lean#L61
[claimBridge]: ../../../ArkLibTest/Interaction/Core/Oracle/AnswerOnlyRelations.lean#L68
[claimRow2Closed]: ../../../ArkLibTest/Interaction/Core/Oracle/AnswerOnlyRelations.lean#L74
[claimCongr]: ../../../ArkLibTest/Interaction/Core/Oracle/AnswerOnlyRelations.lean#L78
[claimRow3]: ../../../ArkLibTest/Interaction/Core/Oracle/AnswerOnlyRelations.lean#L100
[claimLaws]: ../../../ArkLibTest/Interaction/Core/Oracle/AnswerOnlyRelations.lean#L107
[claimRow4Map]: ../../../ArkLibTest/Interaction/Core/Oracle/AnswerOnlyRelations.lean#L116
[claimRow4Data]: ../../../ArkLibTest/Interaction/Core/Oracle/AnswerOnlyRelations.lean#L124
[claimRow5Map]: ../../../ArkLibTest/Interaction/Core/Oracle/AnswerOnlyRelations.lean#L131
[claimRow4]: ../../../ArkLibTest/Interaction/Core/Oracle/AnswerOnlyRelations.lean#L141
[claimRow5]: ../../../ArkLibTest/Interaction/Core/Oracle/AnswerOnlyRelations.lean#L154
[coreVerifier]: ../../../ArkLibTest/Interaction/Core/Oracle/OutputClosing.lean#L28
[coreRow1]: ../../../ArkLibTest/Interaction/Core/Oracle/OutputClosing.lean#L67
[coreRow2]: ../../../ArkLibTest/Interaction/Core/Oracle/OutputClosing.lean#L70
[coreRow3]: ../../../ArkLibTest/Interaction/Core/Oracle/OutputClosing.lean#L73
[coreRow4]: ../../../ArkLibTest/Interaction/Core/Oracle/OutputClosing.lean#L77
[coreRow5]: ../../../ArkLibTest/Interaction/Core/Oracle/OutputClosing.lean#L80
[coreSummary]: ../../../ArkLibTest/Interaction/Core/Oracle/OutputClosing.lean#L83
[coreRow6]: ../../../ArkLibTest/Interaction/Core/Oracle/OutputClosing.lean#L87
[coreRow7]: ../../../ArkLibTest/Interaction/Core/Oracle/OutputClosing.lean#L92
[coreRunCmd]: ../../../ArkLibTest/Interaction/Core/Oracle/OutputClosing.lean#L97
[execRow1]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L103
[execRow2]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L108
[execRow3]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L111
[execRow4]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L115
[execRow5]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L119
[execRow6]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L123
[execRow7]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L128
[execRow8]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L138
[execRow10]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L150
[execFirstVerifier]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L204
[execRow19]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L286
[execRow19All]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L295
[execRow22]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L309
[execRow9Pos]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L319
[execRow9Neg]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L324
[execRow25]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L403
[execRow26]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L407
[execRow27]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L410
[execRow28]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L492
[execRow29]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L498
[execRow30]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L505
[execAxioms]: ../../../ArkLibTest/Interaction/Core/Oracle/PassiveExecution.lean#L513
[depCanary]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentAppend.lean#L36
[depCanaryUse]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentAppend.lean#L51
[depComposed]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentAppend.lean#L93
[depRow2]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentAppend.lean#L113
[depRow3]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentAppend.lean#L116
[depRow4]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentAppend.lean#L121
[depRow5]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentAppend.lean#L124
[depObserveFalse]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentAppend.lean#L127
[depObserveTrue]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentAppend.lean#L130
[depRow6]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentAppend.lean#L166
[compRow1]: ../../../ArkLibTest/Interaction/Core/Oracle/HeterogeneousAppend.lean#L168
[compRow2True]: ../../../ArkLibTest/Interaction/Core/Oracle/HeterogeneousAppend.lean#L179
[compRow2False]: ../../../ArkLibTest/Interaction/Core/Oracle/HeterogeneousAppend.lean#L186
[compRow3to5]: ../../../ArkLibTest/Interaction/Core/Oracle/HeterogeneousAppend.lean#L198
[compSummary]: ../../../ArkLibTest/Interaction/Core/Oracle/HeterogeneousAppend.lean#L208
[compRow13]: ../../../ArkLibTest/Interaction/Core/Oracle/HeterogeneousAppend.lean#L260
[compRow14]: ../../../ArkLibTest/Interaction/Core/Oracle/HeterogeneousAppend.lean#L269
[threeVerifierCons]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L142
[threeRunCons]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L177
[threeAccept]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L185
[threeReject]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L194
[twoRunCons]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L260
[summaryTwoWithTrue]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L268
[stagesRow7]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L293
[stagesRow8]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L297
[stagesRow9]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L303
[stagesRow10]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L308
[stagesRow11]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L313
[stagesRow12]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L319
[stagesRow13]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L324
[stagesRow13Fixed]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L339
[shapeTrue]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L434
[shapeFalse]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L438
[echoVerifier]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L455
[echoEvidence]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L477
[echoOutput]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L487
[echoNotFree]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L496
[echoCheckEvidence]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L526
[echoCheckRows]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L542
[wideStages]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L601
[wideDecide]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L609
[wideNarrow]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L619
[wideNarrowRows]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L651
[sumStages]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L679
[sumSteps]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L700
[sumAccepts]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L714
[sumSupport]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L737
[coinAlmostSurely]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L820
[coinNotOnSupport]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L832
[coinRejectSupport]: ../../../ArkLibTest/Interaction/Core/Oracle/StageChain.lean#L839
[liftQueries]: ../../../ArkLib/Interaction/Core/StageChain.lean#L77
[comapInputs]: ../../../ArkLib/Interaction/Core/StageChain.lean#L120
[mapOutputs]: ../../../ArkLib/Interaction/Core/StageChain.lean#L128
[comapInputsDecide]: ../../../ArkLib/Interaction/Core/StageChain.lean#L137
[comapInputsRun]: ../../../ArkLib/Interaction/Core/StageChain.lean#L212
[liftInputs]: ../../../ArkLib/Interaction/Core/StageChain.lean#L166
[liftOutputs]: ../../../ArkLib/Interaction/Core/StageChain.lean#L171
[lowerOutputs]: ../../../ArkLib/Interaction/Core/StageChain.lean#L176
[liftInputsDecide]: ../../../ArkLib/Interaction/Core/StageChain.lean#L182
[liftInputsData]: ../../../ArkLib/Interaction/Core/StageChain.lean#L189
[liftOutputsData]: ../../../ArkLib/Interaction/Core/StageChain.lean#L195
[lowerOutputsData]: ../../../ArkLib/Interaction/Core/StageChain.lean#L201
[appendReject]: ../../../ArkLib/Interaction/Core/StageChain.lean#L281
[appendAccept]: ../../../ArkLib/Interaction/Core/StageChain.lean#L289
[appendSupport]: ../../../ArkLib/Interaction/Core/StageChain.lean#L302
[appendMeasure]: ../../../ArkLib/Interaction/Core/StageChain.lean#L323
[stages]: ../../../ArkLib/Interaction/Core/StageChain.lean#L361
[compose]: ../../../ArkLib/Interaction/Core/StageChain.lean#L433
[compatibility]: ../../../ArkLib/Interaction/Core/StageChain.lean#L445
[stagesVerifier]: ../../../ArkLib/Interaction/Core/StageChain.lean#L451
[stagesRun]: ../../../ArkLib/Interaction/Core/StageChain.lean#L474
[statementFree]: ../../../ArkLib/Interaction/Core/StageChain.lean#L487
[statementFreeCertify]: ../../../ArkLib/Interaction/Core/StageChain.lean#L509
[verifierCons]: ../../../ArkLib/Interaction/Core/StageChain.lean#L550
[drawCons]: ../../../ArkLib/Interaction/Core/StageChain.lean#L556
[runCons]: ../../../ArkLib/Interaction/Core/StageChain.lean#L565
[rejectCons]: ../../../ArkLib/Interaction/Core/StageChain.lean#L575
[decideWithNil]: ../../../ArkLib/Interaction/Core/StageChain.lean#L585
[outputDataNil]: ../../../ArkLib/Interaction/Core/StageChain.lean#L596
[decideWithOne]: ../../../ArkLib/Interaction/Core/StageChain.lean#L606
[boundaries]: ../../../ArkLib/Interaction/Core/StageChain.lean#L635
[deterministicSteps]: ../../../ArkLib/Interaction/Core/StageChain.lean#L656
[supportSteps]: ../../../ArkLib/Interaction/Core/StageChain.lean#L668
[measureSteps]: ../../../ArkLib/Interaction/Core/StageChain.lean#L738
[discreteEvent]: ../../../ArkLib/Interaction/Core/StageChain.lean#L727
[chainAccept]: ../../../ArkLib/Interaction/Core/StageChain.lean#L680
[chainSupport]: ../../../ArkLib/Interaction/Core/StageChain.lean#L703
[chainMeasure]: ../../../ArkLib/Interaction/Core/StageChain.lean#L760
[appendDecide]: ../../../ArkLib/Interaction/Core/Composition.lean#L471
[pathBundle]: ../../../ArkLib/Interaction/Core/OracleVerifier.lean#L490
[oracleRun]: ../../../ArkLib/Interaction/Core/OracleVerifier.lean#L558
[runAppend]: ../../../ArkLib/Interaction/Core/Oracle/Routing.lean#L123
