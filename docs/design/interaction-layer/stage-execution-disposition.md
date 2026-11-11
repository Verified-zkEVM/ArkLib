# Stage fold and oracle execution: source-to-port inventory

This inventory compares six frozen sources with their interaction-layer ports:

- the acceptance clients `ClaimExample.lean`, `CompositionExample.lean`, `CoreRunExample.lean`
  and `ExecutionExample.lean` in `ArkLibTest/Interaction/Oracle/`;
- the client `ArkLibTest/Interaction/Reduction/DependentExample.lean`;
- the ordered-execution laws in `ArkLib/Interaction/Oracle/Composition.lean`.

Source line numbers identify individual declarations, examples, negative elaboration tests and
axiom checks. The [logged-execution inventory][logged] covers the other frozen clients that use
`ExecutionExample.lean` and `CoreRunExample.lean` as fixtures; this inventory covers the
assertions of those two files themselves.

The two approved premises are:

- **P1 (passivity):** verifiers send public-coin challenges only, and resource queries occur in
  the final decision. A challenge cannot be computed from an input or previously sent oracle.
- **P2 (shape):** neither a challenge nor an oracle payload selects the protocol's subtree.

Each row has exactly one of four statuses. An **equivalent** row's target states the same
mathematical observation, at least as generally as the source. A **premise-required** row names
the premise, states which part of the assertion that premise retires, and states what the target
keeps. A **retired** row belongs to a removed mechanism, which it names; every mathematical
observation the mechanism carried has its own row. An **unresolved** row needs a parent interface
that does not exist yet, and names it. No row in this inventory is unresolved.

## Universes

The ports keep the frozen universe placement, with one generalization and one restriction.

- `StageInterface.{u, uQ}` ([stageInterface]) puts the statement, the index, the data and the
  private state in `u`, as `ExecutionInterface.{u}` does. Answer types stay in `u`. Query types
  have their own universe `uQ`, and a `ClosedStage` may change it between its input interface and
  its output interface. The frozen stage passes its input resource as
  `I.oracles.spec.toPFunctor : PFunctor.{u, u}`, so its query domain lies in `u`.
- `ClosedStage` ([closedStage]) takes `ambient : OracleSpec.{u, u} ι` with `ι : Type u`, as the
  frozen stage does.
- The fold `foldStages` ([foldStages]) takes an arbitrary family of state types in `u`.
- The dependent-reduction canary ([depCanary]) keeps the shared, statement, witness and
  interaction universes independent, as the frozen canary does. The restriction: a nonempty
  ambient specification lies in the interaction universe, because the prover runs in
  `OracleComp ambient : Type u → Type u` (implementation note 18). The frozen canary has no
  ambient oracles, and the empty specification recovers it.

## ClaimExample.lean

| Source assertion | Status | Exact target or remaining obligation |
| --- | --- | --- |
| L25 `observed` and L31 `answerProblem`, the relation over closed claims | equivalent | [claimClosedProblem] states the same claim-dependent witness relation over `Nat × tagged.Behavior`, a statement with arbitrary deterministic answers. [claimBridge] shows that on concrete data it is the relation [claimAnswerProblem]. |
| L27, the unobservable tag vanishes from the closed claim | equivalent | [claimRow1]: the closed claims of statement 7 with the behaviors of `(7, true)` and `(7, false)` are equal. `ConcreteClaim.toClosed` is exactly this pair of the statement and `behaviorOfRealizations`. |
| L37, the closed claim 7 is in the language | equivalent | [claimRow2Closed] at the frozen closed-claim relation; [claimRow2] at the concrete-data relation. |
| L46, `SemEquiv (.id tagged) repeated` | equivalent | [claimRow3]: under every deterministic handler of `tagged.spec`, the query-twice program and the identity embedding give the same answers. [claimLaws] adds that both oracle maps agree with the materialized data. |
| L53, closing a substituted open claim | equivalent | [claimRow4]: for every source index type in `Type`, every source specification, every virtual program `view : QueryImpl tagged.spec (OracleComp spec)` and every deterministic source handler, closing the claim `(7, repeated)` after substituting `view` equals closing it with the evaluated view. [claimRow4Map] and [claimRow4Data] state the same substitution for `OracleMap.comp`, with its data map. |
| L60, the relation cannot distinguish derivations with the same answers | equivalent | [claimRow5]: for every source specification, two claims made of a statement and virtual programs, with equal statements and equal answers under every deterministic handler, have the same membership in the frozen closed-claim language under every handler. [claimRow5Map] states the oracle-map form through the maps' laws and [claimCongr]. |
| L25 `ClosedClaim`, L27 `ConcreteClaim.toClosed`, L42 `VirtualOracle.ofQuery`, L55 `OpenClaim.subst` and `closeWith`, L65 `closeWith_congr` as API | retired | Removed mechanism: claims that carry behaviors or open query programs. Record D6 keeps concrete data with an oracle map (`f`, `impl` and the law tying them), and rejects the alternative "behavior only, without `f`". The rows above port each assertion these names carried, with `QueryImpl` programs and handlers. |

## CoreRunExample.lean

| Source assertion | Status | Exact target or remaining obligation |
| --- | --- | --- |
| L91, history `[0, 1, 2]` | equivalent | [coreRow1]: the history is `[0, 1, 2]` for every hidden value, each event once. |
| L51, verifier event 1 at the oracle receive | premise-required | P1 retires verifier effects at protocol nodes. The passive decision performs event 1 as its first effect ([coreVerifier]); the history of L91 does not change, because no prover effect follows the receive. |
| L93, private output `hidden` | equivalent | [coreRow2], for every hidden value. |
| L95, accepted statement 11 | equivalent | [coreRow3]: the statement is the queried first coordinate 11. |
| L97, output oracle answers 18 | equivalent | [coreRow4]: the output data is `7 + 11`, computed by the oracle map [closeMap] from this run's input and payloads. [coreSummary] states the full accepted result for every message and hidden value. |
| L102, a different run answers 26 | equivalent | [coreRow5]: the run with message 19 closes with its own data, 26. |
| L106, rejection yields no claim | equivalent | [coreRow6], for every message and hidden value. |
| L109, setup runs once before the strategies | equivalent | [coreRow7]: setup event 3 runs once, before the send and decision events, and the observation equals the run without setup. The frozen row states this for the accepting verdict; the target states it for both. The frozen setup is a reduction-level effect; here it is the prover's first slot. [coreRunCmd] evaluates the same runs. |
| L38 `outputOracle` and L44 `terminal`, an output program in an open terminal claim | retired | Removed mechanism: `OpenClaim` terminal outputs, closed by `CoreRun.closedOutput` with the run's input handler. The output is concrete data from [closeMap]; L97 and L102 keep its answers. |
| L67 `reduction`, L73 `reductionWithSetup`, L86 `executeStrategiesCore` | retired | Removed mechanism: the strategy executor and the reduction executor `executeCore` with a separate setup step. [oracleRun] runs the prover against the sampler, then the decision. |

## CompositionExample.lean

The frozen ordered execution is ported as the stage fold in `StagesExample.lean`. The binary
composition of the same two stages in `CompositionExample.lean` ([compRow1], [compRow2True],
[compRow2False], [compRow3to5], [compSummary], [compRow13]) is additional coverage. It is a
different execution: both passive decisions run after the whole interaction, so its history is
`[0, 2, 1, 3]`.

| Source assertion | Status | Exact target or remaining obligation |
| --- | --- | --- |
| L24, local `implicit_reducible` attribute | retired | Removed mechanism: a local transparency override on `OracleInterface.toOracleSpec` and `OracleInterface.Response`. The ports need no transparency command. |
| L134, `firstStage_run` | equivalent | [firstStageRun]: for every verdict, input and hidden value, events 0 then 1, the input's parity as statement, the input plus 11 as data, and `hidden + 1` as private state. The frozen input behavior `answers : naturals.spec.Domain → Nat` and the target data `answers : Unit → Nat` determine each other: the family has one index with one `Unit` query, answered by the data. |
| L144, `secondStage_run` | equivalent | [secondStageRun]: for both message types and every input and hidden value, events 2 then 3 and the same statement, data and private state. The frozen setup event 2 is the prover's first slot. |
| L169, `stages_zero` | equivalent | [twoStagesZero]. |
| L173, `stages_one` | equivalent | [twoStagesOne]. |
| L176, `run_two` | equivalent | [runTwo]: the fold runs the first stage, returns `none` on rejection, and otherwise runs the second stage on the accepted state. [runThree] extends it to three stages. |
| L202, `observed_true` | equivalent | [observedTwoTrue]: the same normal form for every input and hidden value, with history `[0, 1, 2, 3]`. |
| L217, history `[0, 1, 2, 3]` | equivalent | [stagesRow7]. |
| L220, statement 118 on the `Bool` branch | equivalent | [stagesRow8]. |
| L225, statement 72 on the `Nat` branch | equivalent | [stagesRow9]. |
| L230, final oracle `true` | equivalent | [stagesRow10]: the data of the exported `Bool` oracle, which is its answer. |
| L235, final oracle `false` | equivalent | [stagesRow11]. |
| L241, private outputs `(41, 42)` | equivalent | [stagesRow12]. |
| L246, rejection gives `(none, [0, 1])` | equivalent | [stagesRow13]. |
| L249, the lower adapter keeps oracle output and private output | equivalent | [compRow14]: output data 18 and private output `hidden`, for every hidden value. `executeClosed` is retired in the table for `Composition.lean`. |

## ExecutionExample.lean

| Source assertion | Status | Exact target or remaining obligation |
| --- | --- | --- |
| L107, verdict 37 | premise-required | P1 retires the challenge `7 + 11` computed from the input and the first oracle. [execRow1] samples the challenge, checks it against the queried input plus the first answer, and keeps the verdict `19 + 18 = 37` at the draw 18, for every hidden value. Other draws reject. |
| L110, history `[0, 1, 5, 2, 4, 3]` | premise-required | P1 retires verifier events 0, 5 and 2 at the public receive, the oracle receive and the challenge. [execRow2] keeps the six events, each once, in the passive order `[1, 4, 0, 5, 2, 3]`. [full] reproduces the frozen list with private output `(777, hidden)` and verdict 37 in a passive client, but not the frozen ownership of each event. |
| L113, private output `(777, hidden)` | equivalent | [execRow3]. |
| L116, public result `⟨true, (), 18, (), ()⟩` | premise-required | P1: the challenge 18 in the view is sampled rather than computed. [execRow4] keeps the view, with both payloads erased, at the draw 18. |
| L123, `publicResult_eq` | premise-required | P1, as for L116. [execRow5] keeps the view and the verdict 37 at the draw 18. |
| L129, hidden data does not change the public result | premise-required | P1, as for L116. [execRow6] keeps the invariance for every pair of hidden values, at the draw 18. |
| L141, negative test: an oracle-node verifier cannot receive the payload | equivalent | [execRow7]: a decision that reads the hidden coordinate of a sent oracle does not elaborate, because the view gives oracle moves the type `PUnit`. |
| L149, positive counterpart: a query reaches the observable coordinate | equivalent | [execRow8]. |
| L159, negative test: a verifier before the second send cannot query the second oracle | equivalent | [execRow9Neg]: the prefix decision's resources do not name the second sent oracle, so the query does not elaborate. [execRow9Pos]: the composed decision can name it. |
| L165, `executeStrategies_eq_run` erasure equation | retired | Removed mechanism: conversion of oracle strategies to plain counterparts on the type tree (`Verifier.toCounterpart`, `TypeTree.ExecutionPath.ofTypeTreePath`). [execRow10] states, by definition, the oracle verifier's run of the same strategies as the paired run against the sampler followed by the decision. |
| L44 and L47, access after each oracle send | retired | Removed mechanism: per-node access (`Access.extend`). A decision's resources depend only on its shape path ([pathResources]). Record D6 retires per-node access once verifiers are passive. |
| L180 to L182, axioms of `accessAt_comp`, `AccessDecoration.restrict_build`, `Verifier.decorate_access` | retired | Removed mechanism: per-node access decorations. |
| L183 and L184, axioms of `toCounterpart_oracle_eq_of_answer_eq`, `executeStrategies_eq_run` | retired | Removed mechanism: the counterpart conversion of L165. |
| L185, axioms of `Reduction.execute` | equivalent | [execAxioms] checks that `OracleVerifier.run` and `Reduction.run` use only `propext`, `Classical.choice` and `Quot.sound`, and fails the build otherwise. |
| L279, `#check executeStrategies_append` at this fixture | equivalent | [execRow19] rewrites the composed run with `OracleVerifier.run_append` ([runAppend]) at this fixture. |
| L285, axioms of `executeStrategies_append` | equivalent | [execAxioms] covers `OracleVerifier.run_append`, `run_splitSampler` and `run_appendSampler`. |
| L292, verdict `some 30` | premise-required | P1 and P2. The frozen prefix computes an `Option Nat` challenge from its oracle (P1), and `some` selects the branch with a second oracle send (P2). [execRow19] keeps the verdict `19 + 11 = 30` at the draw 18: the second message's answer plus the prefix value 11. [execRow19All] states the verdict for every draw on the same shape. |
| L295, history `[10, 11, 12, 14, 15, 16, 17]` | premise-required | P1 retires prefix verifier events 11 and 12 before the prover's response. [execRow19] keeps the seven events, each once, as `[10, 14, 15, 11, 12, 16, 17]`. |
| L298, private output `hidden + 14` | equivalent | [execRow19] and [execRow19All]: the private output keeps the ambient answer 14 read after the challenge. |
| L300, abort gives `none` | premise-required | P2 retires the `none` challenge that selects a branch without a second send. [execRow22] keeps the `none` verdict through a rejecting prefix decision, for every draw and hidden value. |
| L303, abort history `[10, 11, 12, 14, 17]` | premise-required | P1 and P2: the frozen abort branch has no second send, and its events 11 and 12 precede the response. [execRow22] runs each event at most once, as `[10, 14, 15, 11, 12]`: the suffix send's event 15 runs on the fixed shape, and the suffix decision's events 16 and 17 are skipped. |
| L305, abort private output `hidden + 14` | equivalent | [execRow22]. |
| L352, completed prefix then next send: `[40, 41]` | equivalent | [execRow25]. |
| L354, appended: `[41, 40]` | equivalent | [execRow26]. The appended completed decision is an end decision, so event 40 follows the next prover's event 41, as in the frozen run. |
| L357, the two histories differ | equivalent | [execRow27]. |
| L407, history `[48, 49, 50, 51, 52]` | premise-required | P1 retires the suffix verifier's first move computed from an ambient answer at the seam, with events 49 and 50 before the response 51. [execRow28] keeps a sampled first suffix move after the prefix prover's event 48 and before the response 51: `[48, 59, 51, 49, 50, 52]`, with the draw logged as its value 59. |
| L409, private output `hidden + 59 + 51` | premise-required | P1: the challenge 59 is sampled rather than computed. [execRow29] keeps `hidden + 59 + 51` at the draw 59. |
| L411, verdict 59 | premise-required | P1, as for L409. [execRow30] reads the challenge from the view, checks it against the answer 50 plus the prefix value 9, and returns 59. |

## Reduction/DependentExample.lean

| Source assertion | Status | Exact target or remaining obligation |
| --- | --- | --- |
| L69, universe canary | equivalent | [depCanary]: the shared, statement, witness and interaction universes are independent; the output statement and prover output lie in the interaction universe, as in the frozen canary. [depCanaryUse] instantiates it at `Type 3`, `Type 2`, `Type 1` and `Type 0`. The ambient restriction is recorded under Universes. |
| L24 and L32, role decorations | retired | Removed mechanism: role decorations. Ownership comes from the prover and verifier signatures. |
| L99, `Reduction.then` over a shared index with `packAppend` outputs | retired | Removed mechanism: composition over a shared index that records the prefix path. [depComposed] composes with `Prover.append` and `Verifier.append`; outputs are typed over the appended transcript, so `PFunctor.FreeM.Path.packAppend` is not needed. |
| L107, the false prefix selects the `Bool` branch | equivalent | [depRow2]. |
| L111, the true prefix selects the `Fin 3` branch | equivalent | [depRow3]. |
| L115, both participants' results on the `Bool` branch | equivalent | [depRow4] and [depObserveFalse]: the path, the prover's statement 0 with unit witness, and the verifier's statement 0. |
| L124, both participants' results on the `Fin 3` branch | equivalent | [depRow5] and [depObserveTrue]: both statements are 2. |
| L152, distinct intermediate outputs reach the suffix | equivalent | [depRow6]: the suffix prover sees the prover's `true` and witness 7, and the suffix verifier sees the verifier's `false`. The frozen row fixes the sent bit `false`; the target states it for both bits. |

## Oracle/Composition.lean

| Source assertion | Status | Exact target or remaining obligation |
| --- | --- | --- |
| L34 `ClosedOutput`, L44 `CoreRun.closedOutput`, L54 `executeClosed` | retired | Removed mechanism: closing an open terminal claim with the run's input handler and sent messages. [oracleRun] applies the verifier's output map to the run's input data and payloads. CompositionExample L249 keeps the adapter's observation ([compRow14]). |
| L70, `ExecutionInterface` | equivalent | [stageInterface], with the universes recorded under Universes. |
| L83, `ExecutionInterface.Claim` as a closed claim | retired | Removed mechanism: behavior-only claims at a stage boundary, which record D6 replaces by concrete data. [stageClaim] is a statement with concrete data, the accepted output of an oracle verifier. The fold laws below hold for an arbitrary family of state types ([foldStages]), including states whose claims are behaviors. |
| L86, `ExecutionInterface.State` | equivalent | [stageState]. |
| L92, `ClosedStage` | premise-required | P1 and P2. The frozen stage runs verifier strategies with node effects and verifier-computed challenges on a protocol that challenges may branch, and its prover sees a witness prepared from the private state. [closedStage] keeps the protocol selected by the public statement and the private-state transport `nextPrivate`. Challenges come from `draw`, the verifier is a passive oracle verifier, and the prover sees the claim and the private state. |
| L119, `ClosedStage.run` | equivalent | [stageRun]: one core run on the input claim's data, which hands over the accepted output claim with the next private state; a rejection hands over nothing. |
| L128, `run_eq_executeCore` | equivalent | [stageRunEq]: the handoff is the verdict of the same core run, paired with the private state computed from that run's transcript and prover output. |
| L145, `OrderedExecution.run` | equivalent | [runStages], the fold [foldStages] of the stage runs. |
| L157, `run_zero` | equivalent | [foldZero]; [lawZero] instantiates it for every family of closed stages. |
| L162, `run_succ` | equivalent | [foldSucc]; [lawSucc]. |
| L171, `run_succ_of_reject` | equivalent | [foldReject]; [lawReject]. |
| L182, `run_preserves` | equivalent | [foldPreserves]; [lawPreserves]. |
| L203, `run_preserves_support` | equivalent | [foldSupport]; [lawSupport]. |
| L230, `run_preserves_measure` | equivalent | [foldMeasure]; [lawMeasure], under the frozen assumptions: an answer measure on the ambient oracles and measurable, discrete state spaces. |
| L258, `run_append` | equivalent | [foldSplit]; [lawSplit] states it with the frozen cast along `m + n = n + m`. |

[logged]: logged-execution-disposition.md
[full]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L557
[closeMap]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L84
[claimRow1]: ../../../ArkLibTest/Interaction/Core/Oracle/ClaimExample.lean#L30
[claimAnswerProblem]: ../../../ArkLibTest/Interaction/Core/Oracle/ClaimExample.lean#L42
[claimRow2]: ../../../ArkLibTest/Interaction/Core/Oracle/ClaimExample.lean#L50
[claimClosedProblem]: ../../../ArkLibTest/Interaction/Core/Oracle/ClaimExample.lean#L61
[claimBridge]: ../../../ArkLibTest/Interaction/Core/Oracle/ClaimExample.lean#L68
[claimRow2Closed]: ../../../ArkLibTest/Interaction/Core/Oracle/ClaimExample.lean#L74
[claimCongr]: ../../../ArkLibTest/Interaction/Core/Oracle/ClaimExample.lean#L78
[claimRow3]: ../../../ArkLibTest/Interaction/Core/Oracle/ClaimExample.lean#L100
[claimLaws]: ../../../ArkLibTest/Interaction/Core/Oracle/ClaimExample.lean#L107
[claimRow4Map]: ../../../ArkLibTest/Interaction/Core/Oracle/ClaimExample.lean#L116
[claimRow4Data]: ../../../ArkLibTest/Interaction/Core/Oracle/ClaimExample.lean#L124
[claimRow5Map]: ../../../ArkLibTest/Interaction/Core/Oracle/ClaimExample.lean#L131
[claimRow4]: ../../../ArkLibTest/Interaction/Core/Oracle/ClaimExample.lean#L141
[claimRow5]: ../../../ArkLibTest/Interaction/Core/Oracle/ClaimExample.lean#L154
[coreVerifier]: ../../../ArkLibTest/Interaction/Core/Oracle/CoreRunExample.lean#L28
[coreRow1]: ../../../ArkLibTest/Interaction/Core/Oracle/CoreRunExample.lean#L67
[coreRow2]: ../../../ArkLibTest/Interaction/Core/Oracle/CoreRunExample.lean#L70
[coreRow3]: ../../../ArkLibTest/Interaction/Core/Oracle/CoreRunExample.lean#L73
[coreRow4]: ../../../ArkLibTest/Interaction/Core/Oracle/CoreRunExample.lean#L77
[coreRow5]: ../../../ArkLibTest/Interaction/Core/Oracle/CoreRunExample.lean#L80
[coreSummary]: ../../../ArkLibTest/Interaction/Core/Oracle/CoreRunExample.lean#L83
[coreRow6]: ../../../ArkLibTest/Interaction/Core/Oracle/CoreRunExample.lean#L87
[coreRow7]: ../../../ArkLibTest/Interaction/Core/Oracle/CoreRunExample.lean#L92
[coreRunCmd]: ../../../ArkLibTest/Interaction/Core/Oracle/CoreRunExample.lean#L97
[compRow1]: ../../../ArkLibTest/Interaction/Core/Oracle/CompositionExample.lean#L168
[compRow2True]: ../../../ArkLibTest/Interaction/Core/Oracle/CompositionExample.lean#L180
[compRow2False]: ../../../ArkLibTest/Interaction/Core/Oracle/CompositionExample.lean#L187
[compRow3to5]: ../../../ArkLibTest/Interaction/Core/Oracle/CompositionExample.lean#L201
[compSummary]: ../../../ArkLibTest/Interaction/Core/Oracle/CompositionExample.lean#L211
[compRow13]: ../../../ArkLibTest/Interaction/Core/Oracle/CompositionExample.lean#L263
[compRow14]: ../../../ArkLibTest/Interaction/Core/Oracle/CompositionExample.lean#L272
[lawZero]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L47
[lawSucc]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L54
[lawReject]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L64
[lawSplit]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L72
[lawPreserves]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L88
[lawSupport]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L99
[lawMeasure]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L111
[firstStageRun]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L244
[secondStageRun]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L255
[twoStagesZero]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L311
[twoStagesOne]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L315
[runTwo]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L323
[observedTwoTrue]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L341
[stagesRow7]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L355
[stagesRow8]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L359
[stagesRow9]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L365
[stagesRow10]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L370
[stagesRow11]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L375
[stagesRow12]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L381
[stagesRow13]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L387
[runThree]: ../../../ArkLibTest/Interaction/Core/Oracle/StagesExample.lean#L399
[execRow1]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L102
[execRow2]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L107
[execRow3]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L110
[execRow4]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L114
[execRow5]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L118
[execRow6]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L122
[execRow7]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L127
[execRow8]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L137
[execRow10]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L149
[execRow19]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L282
[execRow19All]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L291
[execRow22]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L301
[execRow9Pos]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L310
[execRow9Neg]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L315
[execRow25]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L394
[execRow26]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L398
[execRow27]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L401
[execRow28]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L483
[execRow29]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L489
[execRow30]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L496
[execAxioms]: ../../../ArkLibTest/Interaction/Core/Oracle/ExecutionExample.lean#L504
[depCanary]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentExample.lean#L35
[depCanaryUse]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentExample.lean#L50
[depComposed]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentExample.lean#L92
[depRow2]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentExample.lean#L112
[depRow3]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentExample.lean#L115
[depRow4]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentExample.lean#L120
[depRow5]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentExample.lean#L123
[depObserveFalse]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentExample.lean#L126
[depObserveTrue]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentExample.lean#L129
[depRow6]: ../../../ArkLibTest/Interaction/Core/Reduction/DependentExample.lean#L165
[foldStages]: ../../../ArkLib/Interaction/Core/Stages.lean#L44
[foldZero]: ../../../ArkLib/Interaction/Core/Stages.lean#L53
[foldSucc]: ../../../ArkLib/Interaction/Core/Stages.lean#L59
[foldReject]: ../../../ArkLib/Interaction/Core/Stages.lean#L66
[foldSplit]: ../../../ArkLib/Interaction/Core/Stages.lean#L125
[foldPreserves]: ../../../ArkLib/Interaction/Core/Stages.lean#L156
[foldSupport]: ../../../ArkLib/Interaction/Core/Stages.lean#L176
[foldMeasure]: ../../../ArkLib/Interaction/Core/Stages.lean#L199
[stageInterface]: ../../../ArkLib/Interaction/Core/Stages.lean#L226
[stageClaim]: ../../../ArkLib/Interaction/Core/Stages.lean#L240
[stageState]: ../../../ArkLib/Interaction/Core/Stages.lean#L243
[closedStage]: ../../../ArkLib/Interaction/Core/Stages.lean#L248
[stageRun]: ../../../ArkLib/Interaction/Core/Stages.lean#L278
[stageRunEq]: ../../../ArkLib/Interaction/Core/Stages.lean#L286
[runStages]: ../../../ArkLib/Interaction/Core/Stages.lean#L295
[pathResources]: ../../../ArkLib/Interaction/Core/OracleVerifier.lean#L462
[oracleRun]: ../../../ArkLib/Interaction/Core/OracleVerifier.lean#L503
[runAppend]: ../../../ArkLib/Interaction/Core/Oracle/Routing.lean#L119
