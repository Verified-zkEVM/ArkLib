# Sumcheck in the interaction layer

The modules under `ArkLib/ProofSystem/Sumcheck/Core/` define Sumcheck in the interaction layer.
They prove that it is the embedded legacy Sumcheck at the common observation of record
[D8](../interaction-rebuild/D8-legacy-equivalence-observation.md), and they transfer the legacy
security results to it. The legacy specification `Sumcheck.Spec` stays the mathematical source:
the interaction-layer verifier runs the legacy decision fold, and its relations are the legacy
`Spec.relationRound`.

## Modules

| Module | Contents |
|---|---|
| `SingleRound` | One round: an oracle node for the round polynomial, then one challenge in `R`. |
| `Composition` | Standalone checked rounds, projected output oracles, and program equality of a first round appended to the remaining rounds. |
| `Protocol` | `protocol R deg n`, the `n`-fold replication of the round; the honest prover as a fold with `pure` slots. |
| `Execution` | The verifier: the legacy decision fold on the view's challenges, with message queries routed to oracle nodes. Closed forms of runs; the round check `roundCheck` and its accept and reject equations. |
| `Completeness` | Perfect completeness of the interaction-layer honest prover, proved directly, for every challenge implementation. |
| `LegacyEquivalence` | The equivalence with the embedded legacy verifier, and the transport of every security notion along it. |
| `LegacyCompleteness` | Perfect completeness of the embedded legacy honest prover, transferred. |
| `Soundness` | Soundness, transferred, with error `∑ challenges, deg / |R|`, and its form `n * (deg / |R|)`. |
| `Knowledge` | Straight-line knowledge soundness, transferred, with the same error. |
| `RoundByRound` | Round-by-round soundness and knowledge soundness, transferred, with error `deg / |R|` at every challenge. |

## The protocol and the verifier

The shape of `protocol R deg n` does not depend on challenges: every run has `n` rounds, and the
interaction never rejects. The verifier is passive. After the run it decides on the view with
`legacyProgram`, the legacy fold `Spec.oracleVerifierProgram` of the per-round checks. A failed
round check skips only the remaining checks; the prover's messages, the challenge draws and the
prover's effects of every round have already run. The output oracle is the input polynomial.

`run_verifier_foldRounds` gives the run of any prover whose slots are `pure` in closed form: draw
every challenge in round order, then return the transcript, the output and the legacy verdict of
the decoded transcript.

## Equivalence with the legacy Sumcheck

The equivalence runs through three correspondences:

- **Tree and transcripts.** `protocol_eq` identifies `protocol R deg n` with the oracle tree of
  `Spec.pSpec R deg n`, and `oracleDecode_eq_decodeTranscript` identifies the two transcript
  decodings.
- **Decision.** `decide_eq_legacy`: on every completed run, the decision of the Sumcheck verifier
  and that of the embedded legacy verifier `legacyVerifier` are the same `OracleComp` program,
  before any query is answered, so they make the same queries in the same order.
  `outputMap_eq_legacy` says both keep the input polynomial as output oracle, and
  `verifier_agrees` packages the two as `OracleVerifier.Agrees`. `runWithLog_eq_legacy` follows:
  the logged executions are equal, including the decision log of ambient, input and message
  queries. `decide_ambient_trace` is narrower: once the input and message oracles are answered
  from the run's data, both decisions are `pure` of the legacy verdict, so neither makes an
  ambient query. The decisions do query the round messages.
- **Challenges.** `challengeQueryImpl_eq_legacy`: the uniform challenge oracle of the Sumcheck tree
  is the reindexed uniform legacy challenge oracle.

The main results are:

- `run_eq_legacy`: for every prover, the reindexed and finalized Sumcheck run is the reindexed and
  finalized run of the embedded legacy verifier, as a program. It includes every ambient query of
  the prover and the decision, and keeps the decoded transcript, the prover's output and the
  accepted statement apart.
- `run_legacyProver`: against the embedded legacy honest prover, that program is the legacy run
  `OracleReduction.run`. The legacy honest prover's challenge slots are `pure`
  (`legacyProver_pureChallengeSlots`), which is the hypothesis of the program-equality exchange
  between challenge sampling and the prover's challenge step.

`OracleVerifier.Agrees` in `ArkLib/Interaction/Core/Security/Agreement.lean` collects what
decision agreement gives: equal runs and logged runs, and equal completeness, soundness, knowledge
soundness and round-by-round forms. The `*_cast` lemmas there and in
`Core/Legacy/OracleKnowledge.lean` carry each notion along `protocol_eq`. The chain and routing
lemmas for appended legacy oracle specifications are in `Core/Legacy/OracleAppend.lean`, and the
purity of challenge slots under appending is in `Core/Legacy/PureSlots.lean`.

## Security

Each transfer starts from the stated legacy theorem and goes through the legacy embedding's
transfer theorem, the cast lemmas and `Agrees`, and keeps the legacy error. The quantifiers
differ:

- Soundness and round-by-round soundness quantify over every prover, with any prover output type.
- Straight-line knowledge soundness quantifies over every prover with the legacy-compatible
  output type: a pair of the output statement with its oracle data and the `Unit` output witness.
- Round-by-round knowledge soundness quantifies over every prover, with the `Unit` witnesses of
  the legacy relations.
- Completeness concerns one prover, the embedded legacy honest prover `legacyProver`.

No transfer assumes that the ambient oracle's answer types are inhabited. A proof that needs a
default ambient answer takes one from the support of the ambient implementation
(`supportedAnswer` in `Core/Legacy/OracleReduction.lean`).

| Theorem | Statement | Legacy source |
|---|---|---|
| `verifier_soundness` | Soundness for the languages of `relationRound 0` and `relationRound (Fin.last n)`, error `∑ challenges, deg / |R|`. | `Spec.oracleVerifier_rbrKnowledgeSoundness`, through round-by-round soundness and the guarded implication to soundness |
| `verifier_soundness_rounds` | The same, with error `n * (deg / |R|)`. | `card_challengeIdx`: one challenge per round |
| `verifier_knowledgeSoundness` | Straight-line knowledge soundness for the relations, same error. | `Spec.oracleVerifier_knowledgeSoundness` |
| `verifier_rbrSoundness` | Round-by-round soundness, error `deg / |R|` at every challenge. | `Spec.oracleVerifier_rbrKnowledgeSoundness` |
| `verifier_rbrKnowledgeSoundness` | Round-by-round knowledge soundness, same error. | `Spec.oracleVerifier_rbrKnowledgeSoundness` |
| `legacyProver_perfectCompleteness` | The embedded legacy honest prover is perfectly complete; its output statement and witness lie in the final relation. | `Spec.oracleReduction_perfectCompleteness` |

The round-by-round transfers need a terminal certificate for every state function (departure
15). The legacy verifier's guarded form `Spec.oracleVerifierGuardedForm` supplies it through
`StateTerminalCertificate.of_guarded` and `KnowledgeTerminalCertificate.of_guarded`.

`perfectCompleteness` in `Completeness` is proved directly for the interaction-layer honest
prover, for every challenge implementation, and judges the accepted statement. The transferred
`legacyProver_perfectCompleteness` is a different statement: it concerns the legacy honest
prover, assumes uniform challenges, and judges the output witness as well.

The knowledge transfers use a constant output-witness family: the extracted output witness is
`Unit`, read from the prover's output by `fun _ o => o.2`.

## Tests

The acceptance tests are in `ArkLibTest/ProofSystem/Sumcheck/Core/`.

| File | Checks |
|---|---|
| `Protocol`, `Execution`, `Completeness` | Shape, closed-form runs, zero rounds, a bad first round followed by an honest round, completeness. |
| `LegacyEquivalence` | Legacy prover runs, rejection agreement of the two decisions, zero rounds. |
| `SingleRound` | One-round runs: accepting, rejecting, a dishonest message that passes, distributions of one-round runs; the sum of `X` over `{0, 1}`. |
| `Soundness` | Soundness against any one-round prover; a soundness bound over `ZMod 17`; exact probabilities over `ZMod 5`; the adaptive message's endpoint and hit facts; the exclusion of `X ^ 2` from the degree-one carrier. |
| `RoundByRound` | Clients of the round-by-round, knowledge and completeness transfers. |
| `Rounds` | Two- and three-round runs: challenge draws in round order, the accepted claim, a wrong target that still runs every round and rejects. Two honest rounds on the bilinear input `1 + 2 X₀ + 3 X₁ + 4 X₀ X₁` with the challenges `3` and then `5`: exactly two challenge queries, in round order, and the accepted claim `⟨14, ![3, 5]⟩` with the input polynomial as output oracle. The honest messages on that input, `5 + 8 X` and `1 + 2 c + 3 X + 4 c X`, their sums, and the first-round relation transport. |
| `Composition` | `projection_bilinear`, `projection_answer`, `run_projected_bilinear`, `projected_relation`, `run_projected_relation`, and `run_append_bilinear`: the projected oracle, its standalone run and relation, and the append equivalence at two rounds. |
| `Routing` | `accepted`, `prefix_rejected`, `suffix_rejected`, `accepted_relation`: two rounds through the exported polynomial `p(r, ·) + q(r)`. The private component is any `Nat`; every recorded run returns `hidden + 110` and trace `[1, 3, 2, 4]`. |
| `LegacyVerifier` | `sent_target`, `inconsistent_sum_rejected`, `honest_zero_accepted`, `linear_sent_target`, `run_false_relation`: the regression cases on both the core verifier and the embedded legacy verifier. |
| `Effects` | A prover with ambient effects before each message and after the last challenge: the run executes them in protocol order, and a recording handler observes the order. An accepted claim that is not in the final relation. A claim whose first check fails still runs both rounds and rejects, and the decision log holds only the first round's check queries (`decide_log_badFirst` for every completed run whose first message fails its check, at every round count; `runWithLog_wrong` for the logged execution of that prover). The round message's oracle interface. |

## Remaining integration work

The full verifier covers rounds `0` to `n`. `Composition.projectedVerifier` verifies an arbitrary
single round `i`, while the appended full-protocol equality starts at `0`, as OQ11 permits.
There is no general interval runner. Departure [20](../interaction-rebuild/IMPLEMENTATION-NOTES.md#20-sumcheck-ports)
records the ports and restatements.

### Waits on D1/D5/D6

The modules these rows need are added by part D, commits 1, 5 and 6, and are not on this
branch's base. Sumcheck does not duplicate them.

| Rows | Owner and dependency | Disposition on this branch |
|---|---|---|
| Generic routing clients outside Sumcheck | D1, `Core/Oracle/Routing.lean` | Waits on D1. The Sumcheck-specific one-round specialization is in `Core/Composition.lean`; SourceRouting #4–#7 do not wait. |
| `Interaction/CompositionSoundness` #1–#14; `Interaction/Oracle/CompositionSoundnessExample` #1–#15 | D5, `Core/Security/CompositionSoundness.lean` | Waits on D1/D5. Preserve the arbitrary midpoint, weighted almost-everywhere suffix premise and final-query variants; do not duplicate them in Sumcheck. |
| `Interaction/Oracle/RuntimeSoundness` #1–#22; `RuntimeQueryBounds` #12, #16, #17 | D5 and the VCVio runtime support (OQ2) | Waits on D1/D5. Runtime soundness is an application of composition soundness to `OracleRuntime.run`, not a second production module. |
| `Interaction/Oracle/Security/Soundness` #3–#6 | D6, `Core/Security/Implications.lean` | Waits on D6: local-to-global soundness, uniform error, escape and averaged-prefix lemmas. The Sumcheck transfers already use the legacy guarded implication. |

The migration list has **no LegacyVerifier rows tagged CompositionSoundness or
RuntimeSoundness**: its 13 LegacyVerifier rows are all `keep`. The composition/runtime rows above
belong to the generic interaction tests. The additional LegacyVerifier bridge obligations from
§4.4 are accounted for below; they need no D1/D5/D6 module.

OQ17's generic message-carrier change and the executable instance belong to part D, commit 8.
Until then no computable instance shares the decision.

## Migration disposition

The migration list assigns to this work the assertions of the frozen Sumcheck tests in
`ArkLibTest/ProofSystem/Sumcheck/Interaction/`, the four implication assertions of
`ArkLibTest/Interaction/Oracle/Security/Soundness.lean`, and, by open question OQ4, 23 fixture
facts of the frozen Sumcheck tests. Rows are named `File #k` after the frozen test file and the
row number in the migration list. "Covered" means covered by the approved restatement: concrete
data, all `n` rounds, a passive verifier. Tests are in `ArkLibTest/ProofSystem/Sumcheck/Core/`.

### Assertion rows

| Rows | Disposition |
|---|---|
| ArbitraryCompleteness #1–#4 | Covered by `Completeness`: perfect completeness for every challenge implementation, support and closed-form runs. |
| ArbitraryRounds #1 | Covered: the zero-round run draws nothing. |
| ArbitraryRounds #2, #3, #5 | Covered by `Rounds.run_three`: three rounds, draws in round order. |
| ArbitraryRounds #4 | Covered. `Rounds.run_three_wrong` runs all three rounds on a wrong target and rejects. `Effects.decide_log_badFirst` applies to its honest first message: the decision log holds only the first round's check queries. |
| Closing #1 | Covered by the degree subtype `R⦃≤ deg⦄[X]` of the round message. |
| Closing #2, #3, #5–#8 | Covered by `SingleRound.run_oneRound`, the verdict equations, the output-relation examples and their axiom guards. |
| Closing #4, #9 | Covered by direct perfect completeness and its uniform specialization. |
| Legacy #1, #2 | Covered by `legacy_prover_run` and `embedded_prover_generates` in `LegacyEquivalence`, including wrong targets. |
| Projection #3 | Covered by `Sumcheck.Core.projectionMap`, `projectionMap_f`, `simulateQ_projectionMap` in `SingleRound`; tested by `CompositionTest.projection_bilinear` and `projection_answer`. The implementation and law reuse `Spec.SingleRound.simulateProjectedRoundPolynomial` and `simulateProjectedRoundPolynomial_eq`. |
| Projection #7 | Covered by `projectedVerifier`, `run_projectedVerifier_roundProver`, and `CompositionTest.run_projected_bilinear`: challenge `3`, accepted target `12`, projected output `5 + 8 X`. The output map is the projection composed with the input-slot map. |
| Projection #8, ProjectionTransport #2 | Covered by `projectedVerifier_relation`, `CompositionTest.projected_relation`, and `run_projected_relation`, which checks the relation on the standalone run's own returned verdict. `RoundsTest.firstRound_relation` retains the original input in the next-round relation. |
| Protocol #1, #2 | Covered by `Effects.two_rounds` and the recording handler. |
| Protocol #3, #4 | Covered. `Effects.bad_first_rounds` runs both rounds and rejects. `Effects.decide_log_badFirst` and `Effects.runWithLog_wrong` show that the decision log holds only the first round's check queries. |
| Protocol #6, #8 | Covered by the sampled adaptive prover's bound and the soundness axiom guards. |
| Protocol #7 | Covered by `run_append_foldVerifier` for every whole prover and `run_append_verifier` for `Prover.append p f`, with an effectful suffix constructor and dependent output. These are open-program equalities, preserving every query and verdict. `CompositionTest.run_append_bilinear` instantiates two rounds. |
| Protocol #9, #10 | Covered by the completeness axiom guards. |
| RoundByRound #1 | Covered by the round-by-round clients and `false_claim_bound`. |
| Sequential #2, #4 | Covered by `Rounds.run_two_bilinear` and the recording example: challenges `3` then `5`, two challenge queries in round order, target `14`, the bilinear input as output oracle. |
| Sequential #5, #6 | Covered: rejection after both draws, and honest completeness. |
| SingleRound #2–#6 | Covered by the committed-run equations, the acceptance, rejection and dishonest-output examples, and their axiom guards. |
| Soundness #1–#6, #10, #12 | Covered by the accepted and rejected observations, the bound, the exact repair and rejection probabilities, the challenge-first attack and empty-domain rejection. |
| Soundness #15, #16, #21, #23–#28 | Covered by the axiom guards, the committed and randomized prover bounds and the run equations. |
| SourceRouting #1, #2 | Covered by the affine evaluation and oracle-interface tests in `Effects`, over `ZMod 17`. |
| SourceRouting #3 | Covered by the protocol shape. The challenge and abort branches of `Option` are retired. |
| SourceRouting #4 | Covered by `RoutingTest.exportPoly`, `eval_exportPoly`, `exportMap`, `exportOut`, `firstVerifier`, `secondVerifier`, `compatible`, `routed`, `run_routed`, and `accepted`: exported oracle `p(r, ·) + q(r)`, trace `[1, 3, 2, 4]`, private output `hidden + 110` for every `hidden : Nat`, accepted claim `(10, 10)`. |
| SourceRouting #5 | Covered by `RoutingTest.routedVerdict_prefix` and `prefix_rejected`. Both interactions run and retain the same trace and private output. `decideWith_append_checkVerifier` skips the suffix decision when the prefix rejects. |
| SourceRouting #6 | Covered by `RoutingTest.routedVerdict_suffix` and `suffix_rejected`, after both challenges and both prover events. |
| SourceRouting #7 | Covered by `RoutingTest.routedVerdict_accepted` and `accepted_relation` for every pair of challenges and every returned claim. `run_routed` identifies that verdict with the composite run's verdict. |
| `Interaction/Oracle/Security/Soundness.lean` #3–#6 | Waits on D6 (OQ3), as listed under [Remaining integration work](#waits-on-d1d5d6). |

### Fixture rows (OQ4)

| Row | Disposition |
|---|---|
| ArbitraryRounds #6 | Covered by `Spec.relationRound_last_iff` next to `relationRound`. `RoundsTest.relationLast_iff_eval` uses it and keeps its axiom guard. |
| Projection #1 | Covered: `Rounds.domain_points`. |
| Projection #2 | Covered: `Rounds.suffix_points`. |
| Projection #4 | Covered: `Rounds.bilinear_relation`. |
| Projection #5 | Covered: `Rounds.projected_eval`, the honest first message is `5 + 8 X`. |
| Projection #6 | Covered: `Rounds.projected_sum`. |
| ProjectionTransport #1 | Covered: `Rounds.bilinear_relation`. |
| ProjectionTransport #3 | Covered: the first-round example in `Rounds`, the claim `⟨12, ![3]⟩` with the bilinear input in the round-`1` relation. |
| Protocol #5 | Covered: `Effects.target_seven_not_final`. |
| Sequential #1 | Covered: `Rounds.second_eval`. |
| Sequential #3 | Covered: `Rounds.second_sum`. |
| SingleRound #1 | Covered: `SingleRound.msgX_sum`. |
| Soundness #7 | Covered: `Soundness.excludes_quadratic`. |
| Soundness #8 | Covered: `Soundness.adaptive_endpoints`. |
| Soundness #9 | Covered: `Soundness.adaptive_hits`. |
| Soundness #11 | Covered: `Soundness.fresh_bound_lt_one`. |
| Soundness #13, #14 | Covered: axiom guards of the zero and linear input fixtures `poly0`, `polyX` and `polyXK`. |
| Soundness #17 | Covered: axiom guard of `excludes_quadratic`. |
| Soundness #18 | Covered: axiom guard of the adaptive message `adaptive`. |
| Soundness #19, #20 | Covered: axiom guards of `adaptive_endpoints` and `adaptive_hits`. |
| Soundness #22 | Covered: axiom guard of `fresh_bound_lt_one`. |

### B and the kept legacy regressions

| Rows | Disposition |
|---|---|
| Virtual V1 (B's one row, migration §3.3 / §4.4) | Already covered on this base: `OracleMap.ofLegacySimulation` and `Legacy.simulateQ_ofLegacySimulation_impl`, instantiated at `ToyProblem.SimplifiedIOR.outputSimulation` in `ArkLibTest/Interaction/Core/Legacy/OracleReduction.lean`. No duplicate lemma or fixture is added. |
| LegacyVerifier #1, #2 | Keep the legacy tests `input_relation_false`, `message_sum_passes`. |
| LegacyVerifier #3, #4 (bridge versions, §4.4) | `LegacyVerifierTest.answered_pair` and `sent_target` check both core and embedded decisions; the next target is the message's evaluation one. |
| LegacyVerifier #5 (bridge version) | `LegacyVerifierTest.run_false_relation` checks the false output relation on each run's returned verdict, retaining input zero. |
| LegacyVerifier #6, #7 (bridge versions) | `LegacyVerifierTest.inconsistent_sum_rejected`, `honest_zero_accepted`, on both verifiers at every challenge. |
| LegacyVerifier #8, #9 (bridge versions) | `LegacyVerifierTest.linearMessage` and `linear_sent_target`: both decisions return `r + 1` for message `X + 1` at every `r : ZMod 5`. |
| LegacyVerifier #10, #11 (bridge versions) | The axiom guard in `Core/LegacyVerifier.lean` checks `linear_sent_target` and `run_false_relation`, together with all four other bridge facts. |
| LegacyVerifier #12, #13 | Keep the legacy RBR knowledge guards. Core transfers remain guarded in `Core/RoundByRound.lean`. |

The original kept `ArkLibTest/ProofSystem/Sumcheck/LegacyVerifier.lean` is outside D7's editable
paths. Its frozen import still needs retargeting when D9 removes the frozen providers. None of
the new Core tests imports it.

### Supporting declarations added by D7

All names in this table are in `Sumcheck.Core` unless qualified otherwise. They support the rows
above rather than adding independent security claims.

| Module | Declarations and purpose |
|---|---|
| `Spec/PolynomialInterface` | `Spec.polynomialFamily`; the plain alias `Interaction.MultivariateRound.polynomialFamily` remains only until D9. Existing Core and `Impl/Projection` clients use the neutral name. |
| `SingleRound` | `messageFamily`, `projectionMap`, `projectionMap_f`, `simulateQ_projectionMap`: the univariate output interface and lawful projection. |
| `Composition`, decisions | `simulateQ_addLift_eq`, `simulateQ_decide_eq_decideWith`, `run_eq_decideWith`, `inputSlot`: resource interpretation and the existing `OracleMap.embedding` for the input slot. The simulation proof uses VCVio's `simulateQ_simulateQ_eq_of_apply`. |
| `Composition`, round | `checkRoute`, `roundChallenges`, `checkVerifier`, `roundChallenges_eq`, `decideWith_checkVerifier`, `checkVerdict`, `run_checkVerifier`: reuse the legacy per-round check, with no ambient queries in that check. |
| `Composition`, append | `splitFiber_val`, `split_toView_round`, `appendHead`, `appendTail`, `prefixRoute_round`, `suffixRoute_round`, `decideWith_append_checkVerifier`, `run_append_checkVerifier`: specialize the Core append routing to one Sumcheck round. The generic routing of part D, commit 1 is not duplicated. |
| `Composition`, fold | `foldLift`, `foldVerifier`, `verifier_eq_foldVerifier`, `simulateQ_foldLift`, `decideWith_foldVerifier`, `foldHead`, `foldCompatibility`, `decideWith_append_foldVerifier`, `run_append_foldVerifier`, `run_append_verifier`: reuse `Spec.oracleVerifierProgram` and C's `simulateQ_oracleVerifierProgram_succ`, allowing a suffix that starts from a round-1 statement. |
| `Composition`, projection | `simulate_roundProver`, `projectedVerifier`, `run_projectedVerifier_roundProver`, `projectedVerifier_relation`: run the standalone projected round and reuse `projected_sum_of_relationRound` and `relationRound_projected_output` for its mathematical relation. |

## Departures

These entries continue the numbering of [`departures.md`](departures.md).

### 17. The transferred completeness is in its own module

**Plan.** The implementation plan for the Sumcheck modules lists `Completeness` as the home of completeness.

**Code.** `Completeness` keeps the direct proof for the interaction-layer honest prover.
`LegacyCompleteness` holds `legacyProver_perfectCompleteness`, the transfer of the legacy
`Spec.oracleReduction_perfectCompleteness`.

**Why.** `LegacyEquivalence` imports `Completeness`, and the transfer needs `LegacyEquivalence`,
so it cannot live in `Completeness`. The two theorems state different things: the direct one is
for the interaction-layer honest prover and every challenge implementation; the transferred one is
for the embedded legacy honest prover with uniform challenges, and judges the output witness.

### 18. The verifier has no interval start

**Migration.** The migration list of the frozen Sumcheck tests restates several assertions on a run that
starts at round `i`: a single round of a multi-round statement, and the split of `n + 1` rounds
into one round appended to `n` rounds.

**Code.** `verifier R deg n D ambient` decides rounds `0` to `n` from `Spec.StatementRound R n 0`.
The first-round relation transport is stated on the verifier's round-`0` check, `roundCheck`:
from the round-`0` relation, the check on the honest first message accepts a statement in the
round-`1` relation (`firstRound_relation` in the `Rounds` test). This is a statement about the
round check, which keeps the original input polynomial; it is not an execution through the
projection map. D7 now states the split of `n + 1` rounds as `run_append_verifier` and adds the standalone
`projectedVerifier` at arbitrary round `i`.

**Why.** A general interval runner changes the statement types of the composition and needs its
own equivalence with the legacy interval verifiers. OQ11 permits the full-`n` restatement.
Protocol #7 and the projection execution are now covered; see
[Migration disposition](#migration-disposition) and departure
[20](../interaction-rebuild/IMPLEMENTATION-NOTES.md#20-sumcheck-ports).
