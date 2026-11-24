# Sumcheck in the interaction layer

The Sumcheck core has two verifiers. `indexedVerifier` in `Indexed` is the interaction-layer
verifier over an arbitrary finite indexed domain `D : Fin d → R`. The compatibility `verifier` in
`Execution` runs the legacy decision fold with routed message queries over an injective domain
`D : Fin d ↪ R`. Public theorems about `indexedVerifier` start with `indexedVerifier_`. Results
about the compatibility `verifier` start with `verifier_`, and those transferred from the legacy
soundness theorem end in `_of_legacy`.

`Sumcheck.Core.Soundness` proves full-run soundness of `indexedVerifier`. The verifier sums over
indices. In particular, the constant polynomial one has sum two over `[0, 0]`; neither the
verifier nor its proof deduplicates the list.

The argument is the sum-check analysis of [LFKN92](https://lance.fortnow.com/papers/files/ip.pdf),
as presented in [Thaler, §4.1](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf#page=37)
(Proposition 4.1 for the Boolean domain, Remark 4.1 for a finite subset). The specialization
differs as follows. `D : Fin d → R` counts repeated points with multiplicity. The message type
`R⦃≤ deg⦄[X]` enforces the degree bound, so the verifier makes no degree check. The output
relation `indexedOutputProblem` performs the final evaluation check. The error denominator is the
size of the uniformly sampled challenge type `R`.

The proof first bounds a false-to-true transition of the remaining-sum relation at each fresh
challenge. `indexedVerifier_rbrSoundness` packages these bounds as a core state function.
`indexedVerifier_soundness` then applies the parent stack's
`OracleVerifier.soundness_of_rbrSoundness_uniform`, using exactly one challenge per round.
For every ambient-effectful prover and every output family, the probability that the run
returns a claim satisfying the final evaluation relation, from a false input claim, is at most
`n * (deg / |R|)`. The ring assumptions are a finite
commutative semiring with `IsDomain`; the domain map need not be injective or nonempty.

## Modules and ownership

| Module | Contents |
|---|---|
| `Types` | Interaction layer round statements, polynomial oracle data and prefix/suffix coordinates. `roundSuffix` is the interaction layer's only suffix definition; `roundSuffix_eq_spec` shows it is the frozen `Spec.SingleRound.roundSuffix`. |
| `SingleRound`, `Tree` | The oracle-message/challenge round, the fixed full-run tree, transcript access and sampling. `Tree` owns the decision lift `decisionLift` and its answer law `simulateQ_decisionLift_monad`, which both verifiers use. |
| `Domain` | Indexed remaining sums, honest projected polynomials, the successor identity and final evaluation relation. |
| `Indexed` | The interaction layer indexed verifier, its actual-run equation, the state function and interaction layer local-to-global soundness proof. |
| `Soundness` | `indexedVerifier` full-run, arbitrary-list and injective corollaries; actual-run committed and randomized bounds in probability and measure form. |
| `DomainEquivalence` | Agreement of the honest projected polynomials and sum relations with the injective legacy `Spec` representation. It is not a verifier bridge. |
| `Protocol`, `Execution`, `Completeness` | Compatibility honest prover and decision, closed-form runs and direct completeness. |
| `LegacyEquivalence`, `LegacySoundness`, `LegacyCompleteness` | Separate execution and security comparisons with embedded legacy Sumcheck. |
| `Knowledge`, `RoundByRound` | Compatibility knowledge and round-by-round transfers. |

The interaction layer import graph is `Soundness → Indexed → Domain / Tree → Types`. It does
not import `Sumcheck.Spec`, the compatibility execution or a legacy security transfer. `DomainEquivalence`
and `LegacyEquivalence` check agreement separately. The compatibility `verifier` keeps its old
name; the interaction layer verifier is `indexedVerifier`. The two verifiers share `decisionLift`
in `Tree` and `roundSuffix` in `Types`, which do not depend on the legacy modules.

## The interaction layer verifier and its bound

`protocol R deg n` has exactly `n` rounds. Each sends a degree-bounded polynomial and draws a
challenge in `R`. Neither the oracle message nor the challenge selects shape (P2).
The verifier is passive: it queries the messages and decides after the interaction (P1).
A failed sum check skips the remaining decision queries. All prover effects and challenge draws
have already run. Its output oracle is the original input polynomial.

`indexedRelation D i stmt p` states that the indexed remaining sum equals `stmt.target`.
At the last round, `indexedRelation_last` identifies this with polynomial evaluation at the
full challenge vector. If a false current relation passes the message's indexed sum check,
the honest and sent round polynomials differ. A successor relation can hold only at one of
their agreement points, whose uniform mass is at most `deg / |R|`.

| Interaction layer theorem | Exact scope |
|---|---|
| `indexed_round_soundness` | One false-to-true indexed round, including the sum check. |
| `indexedVerifier_rbrSoundness` | Every full execution prefix, with local error `deg / |R|`. |
| `indexedVerifier_soundness`, `indexedVerifier_soundness_nsmul` | The actual full run, for every prover, with `n` times that error. |
| `indexedVerifier_soundness_list` | `D = domain.get` for any list, retaining repetitions. |
| `indexedVerifier_soundness_injective` | The same interaction layer bound for an embedding. |
| `indexedVerifier_run_soundness` | Probability that the actual run returns a claim satisfying the final evaluation relation. |
| `indexedVerifier_committed_soundness`, `indexedVerifier_committed_measureSoundness` | An arbitrary polynomial committed before the one-round challenge. |
| `indexedVerifier_randomized_soundness`, `indexedVerifier_randomized_measureSoundness` | An ambient, possibly failing commitment before the fresh challenge, including shared state. |

These bounds concern returned claims that satisfy the final evaluation relation. They do not
assert that every returned claim is valid. A dishonest message can pass a sum check while the
retained input polynomial fails the final relation. Tests retain this distinction.

The final decision of `indexedVerifier` queries the oracle messages in a fixed order. Each
attempted sum check queries the round message once per domain index, in index order and
including repeats. A successful check adds one query at the challenge. A rejection ends the
decision's queries, although every interaction round has already run. The soundness bound
certifies neither a query charge nor an execution cost. #1488 and #1487 must preserve this order
when they share the decision code.

## Equivalence with the legacy Sumcheck

Every result in this section concerns the compatibility `verifier`, not `indexedVerifier`.
`DomainEquivalence` relates only the honest projected polynomials and sum relations of the two
representations over an injective domain. No theorem relates `indexedVerifier` to the legacy
verifier. A closed-verdict bridge would compare the two decisions after interpreting the
messages. A security transfer would also need the corresponding relations, output maps and
challenge draws, and a comparison of open query traces would need a program law.

The equivalence runs through three correspondences:

- **Tree and transcripts.** `protocol_eq` identifies `protocol R deg n` with the oracle tree of
  `Spec.pSpec R deg n`, and `oracleDecode_eq_decodeTranscript` identifies the two transcript
  decodings.
- **Decision.** `decide_eq_legacy`: on every completed run, the decision of the compatibility
  `verifier` and that of the embedded legacy verifier `legacyVerifier` are the same `OracleComp` program,
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

- `run_eq_legacy`: the reindexed and finalized run of the compatibility `verifier` is the
  reindexed and finalized run of the embedded legacy verifier, as a program. It covers every
  prover whose output is a final statement, its oracle data and a witness of some type `WitOut`.
  It assumes inhabited ambient response types, which the embedding requires. It includes every ambient query of
  the prover and the decision, and keeps the decoded transcript, the prover's output and the
  accepted statement apart.
- `run_legacyProver`: for the embedded legacy honest prover `legacyProver`, with `Unit`
  witnesses and inhabited ambient response types, that program is the legacy run
  `OracleReduction.run`. It requires the legacy honest prover's challenge slots to be `pure`,
  which `legacyProver_pureChallengeSlots` proves. That is the hypothesis of the program-equality
  exchange between challenge sampling and the prover's challenge step.

`OracleVerifier.Agrees` in `ArkLib/Interaction/Core/Security/Agreement.lean` collects what
decision agreement gives: equal runs and logged runs, and equal completeness, soundness, knowledge
soundness and round-by-round forms. The `*_cast` lemmas there and in
`Core/Legacy/OracleKnowledge.lean` carry each notion along `protocol_eq`. The chain and routing
lemmas for appended legacy oracle specifications are in `Core/Legacy/OracleAppend.lean`, and the
purity of challenge slots under appending is in `Core/Legacy/PureSlots.lean`.

## Compatibility security and completeness

The compatibility knowledge theorems concern the compatibility `verifier` and retain the legacy
relations and injective domain. `verifier_knowledgeSoundness` quantifies over legacy-compatible
output statements and witnesses. `verifier_rbrKnowledgeSoundness` is a local certificate with
`Unit` input and output witnesses: it quantifies over statements, receiver prefixes, histories
and challenges, not over provers. The claim about every prover belongs to the run soundness
theorems `verifier_soundness_of_legacy` and `indexedVerifier_soundness`.
`verifier_rbrSoundness` is the separate compatibility round-by-round transfer, also a local
certificate. The interaction layer round-by-round theorem is `indexedVerifier_rbrSoundness`.
`verifier_soundness_of_legacy` in `LegacySoundness` and its rounds form
`verifier_soundness_rounds_of_legacy` preserve the old transfer for the compatibility `verifier`
as a comparison check. The interaction layer security statements do not use them.

`perfectCompleteness` proves completeness directly for the compatibility honest prover and
every challenge implementation. `legacyProver_perfectCompleteness` concerns the embedded legacy
honest prover with uniform challenges and also judges its output witness. The compatibility
round-by-round transfers use the guarded certificates of departure 15
(`StateTerminalCertificate.of_guarded` and `KnowledgeTerminalCertificate.of_guarded`). No transfer
requires inhabited ambient response types: `supportedAnswer` obtains answers from support.
The knowledge transfers extract the constant `Unit` output witness from the prover's output.

## Tests

The files under `ArkLibTest/ProofSystem/Sumcheck/Core/` retain the existing acceptance, rejection,
exact-probability, adaptive-message, effect-order, routing and axiom checks. Compatibility tests
import the comparison modules explicitly. Interaction layer tests add arbitrary maps and lists,
committed and randomized actual runs, and an actual final decision with constant message one and target
two over `[0, 0]`. `IndexedSoundnessTest.repeated_run` checks the complete accepting program
on that repeated domain, including the transcript and retained input oracle.
`IndexedSoundnessTest.exact_success_probability` runs `indexedVerifier` over `ZMod 5` with
domain `[0, 0]`, input polynomial zero, target two and committed message `X + 1`. The sum check
passes at every challenge, and `verdict_at_zero` shows the run returns a claim at challenge zero
that fails the final relation (`claim_at_zero_false`). Only challenge `-1` gives a valid final
claim (`success_iff`), so the success event has probability exactly `1/5`. `Domain` also checks the repeated-point sum, its deduplicated contrast and a
two-coordinate indexed sum. Axiom checks permit only `propext`, `Classical.choice` and `Quot.sound`.

`Rounds` keeps the two- and three-round examples, including the bilinear input and challenge
order. `Effects` checks ambient effects, routed polynomial answers over every commutative
semiring, the `Nat` instance, and decision-query short circuiting after a bad first check.
`SingleRound` keeps honest, dishonest and rejected outputs. `Soundness` retains the exact repair
probability, the challenge-first attack, empty-domain rejection and the degree-carrier check.

## Migration disposition

The test inventory below identifies each frozen test file, migration-list row and source line.
The production inventory that follows lists every source declaration separately. `T/` means
`ArkLibTest/ProofSystem/Sumcheck/Core/`; `C/` means `ArkLib/ProofSystem/Sumcheck/Core/`.
Unqualified target declarations are in `Sumcheck.Core`; test namespaces follow their file names.
The source prefix for the test tables is `ArkLibTest/ProofSystem/Sumcheck/Interaction/`.
Production rows use their complete source paths.
Each row has exactly one migration disposition. The dispositions record how each frozen
assertion maps to the interaction layer. The frozen `Sumcheck.Interaction` modules and their
tests still ship unchanged.

- **equivalent**: the target preserves the source assertion's scope.
- **premise-required (P1)**: the source changes because the passive verifier sends only
  challenges and makes every bundle query in the final decision.
- **premise-required (P2)**: the source changes because challenges and oracle messages never
  select shape.
- **retired**: the interaction layer does not port the row's mechanism, rather than claiming a
  narrower equivalent. This is a migration disposition: the frozen source still ships.
- **child-owned (#1488)**: the child owns interval endpoints `start`, `count` and
  `start + count = n`, including its `intervalVerifier` built from `foldVerifier`.
- **unresolved**: the row names a missing parent interface. A carrier fact cannot close a
  behavior-guarantee assertion.

Compatibility comparisons do not close interaction layer soundness rows. The full-run bounds
above close those rows; interval completeness and projection executions remain with #1488.

### ArbitraryCompleteness

| Exact source | Exact target | Status |
|---|---|---|
| `ArbitraryCompleteness.lean` #1, L12 `#print axioms executeRoundsSampled_perfectCompleteness` | #1488: `Sumcheck.Core.intervalVerifier` completeness and final evaluation | child-owned (#1488) |
| `ArbitraryCompleteness.lean` #2, L13 `#print axioms executeRoundsSampled_measureCompleteness` | #1488: `Sumcheck.Core.intervalVerifier` completeness and final evaluation | child-owned (#1488) |
| `ArbitraryCompleteness.lean` #3, L14 `#print axioms executeRounds_uniform_measureCompleteness` | #1488: `Sumcheck.Core.intervalVerifier` completeness and final evaluation | child-owned (#1488) |
| `ArbitraryCompleteness.lean` #4, L15 `#print axioms executeRounds_evaluation` | #1488: `Sumcheck.Core.intervalVerifier` completeness and final evaluation | child-owned (#1488) |

### ArbitraryRounds

| Exact source | Exact target | Status |
|---|---|---|
| `ArbitraryRounds.lean` #1, L50 example (zero rounds) | #1488: `Sumcheck.Core.intervalVerifier`, zero-count and honest interval execution | child-owned (#1488) |
| `ArbitraryRounds.lean` #2, L55 `three_rounds` | T/Rounds.lean: `RoundsTest.run_three` and recording example | premise-required (P2) |
| `ArbitraryRounds.lean` #3, L85 example (record) | T/Rounds.lean: `RoundsTest.run_three` and recording example | premise-required (P2) |
| `ArbitraryRounds.lean` #4, L93 example (rejection) | T/Rounds.lean: `RoundsTest.run_three_wrong`; T/Effects.lean: `EffectsTest.decide_log_badFirst` | premise-required (P1) |
| `ArbitraryRounds.lean` #5, L105 `#print axioms executeRounds_honest` | #1488: `Sumcheck.Core.intervalVerifier`, zero-count and honest interval execution | child-owned (#1488) |
| `ArbitraryRounds.lean` #6, L106 `#print axioms closedRelation_last_iff` | #1488: `Sumcheck.Core.intervalVerifier`, arbitrary original behavior at `start = n`, `count = 0` | child-owned (#1488) |

### Closing

| Exact source | Exact target | Status |
|---|---|---|
| `Closing.lean` #1, L17 example | Parent counterpart of `OracleModel.satisfies_guarantee`; degree subtype alone is narrower | unresolved (missing parent behavior-guarantee interface) |
| `Closing.lean` #2, L20 example | C/Indexed.lean: `Sumcheck.Core.indexedExecuteAt_univariate_honest`; T/Domain.lean: execution clients and axiom checks | equivalent |
| `Closing.lean` #3, L28 example | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_complete` (challenge `pure r`); T/Domain.lean: execution clients and axiom checks | equivalent |
| `Closing.lean` #4, L36 example | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_perfectCompleteness` (arbitrary challenge); T/Domain.lean: execution clients and axiom checks | equivalent |
| `Closing.lean` #5, L43 example | T/SingleRound.lean:235, dishonest output retaining input zero | equivalent |
| `Closing.lean` #6, L80 `#print axioms executeCore_closed` | C/Indexed.lean: `Sumcheck.Core.indexedExecuteAt_univariate_honest`; T/Domain.lean: execution clients and axiom checks | equivalent |
| `Closing.lean` #7, L81 `#print axioms executeCore_degree_complete` | Parent counterpart of `OracleModel.satisfies_guarantee` plus completeness | unresolved (missing parent behavior-guarantee interface) |
| `Closing.lean` #8, L82 `#print axioms executeSampled_eq` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_honest_eq` (arbitrary challenge); T/Domain.lean: execution clients and axiom checks | equivalent |
| `Closing.lean` #9, L83 `#print axioms executeSampled_perfectCompleteness` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_perfectCompleteness` (arbitrary challenge); T/Domain.lean: execution clients and axiom checks | equivalent |

### Legacy

| Exact source | Exact target | Status |
|---|---|---|
| `Legacy.lean` #1, L29 `prover_generates_transcript` | C/LegacyEquivalence.lean: `Sumcheck.Core.simpleLegacyProver_run`; T/Soundness.lean: axiom check | equivalent |
| `Legacy.lean` #2, L41 example | C/LegacyEquivalence.lean: `Sumcheck.Core.simpleLegacyProver_run`; T/Soundness.lean: axiom check | equivalent |

### Projection

| Exact source | Exact target | Status |
|---|---|---|
| `Projection.lean` #1, L50 `domain_points` | T/Rounds.lean: `RoundsTest.domain_points` | equivalent |
| `Projection.lean` #2, L57 `suffix_points` | T/Rounds.lean: `RoundsTest.suffix_points` | equivalent |
| `Projection.lean` #3, L73 `derived_eval` | #1488: `Sumcheck.Core.intervalVerifier`, projected oracle map, answer law and standalone run | child-owned (#1488) |
| `Projection.lean` #4, L92 `input_sum` | T/Rounds.lean: `RoundsTest.bilinear_relation` | equivalent |
| `Projection.lean` #5, L99 `projected_eval` | T/Rounds.lean: `RoundsTest.projected_eval` | equivalent |
| `Projection.lean` #6, L105 `projected_sum` | T/Rounds.lean: `RoundsTest.projected_sum` | equivalent |
| `Projection.lean` #7, L119 `execute_closed` | #1488: `Sumcheck.Core.intervalVerifier`, projected oracle map, answer law and standalone run | child-owned (#1488) |
| `Projection.lean` #8, L139 `execute_related` | #1488: `Sumcheck.Core.intervalVerifier`, projected oracle map, answer law and standalone run | child-owned (#1488) |

### ProjectionTransport

| Exact source | Exact target | Status |
|---|---|---|
| `ProjectionTransport.lean` #1, L19 `input_relation` | T/Rounds.lean: `RoundsTest.bilinear_relation` | equivalent |
| `ProjectionTransport.lean` #2, L36 example | #1488: `Sumcheck.Core.intervalVerifier`, standalone run through its projected input handler | child-owned (#1488) |
| `ProjectionTransport.lean` #3, L44 example | T/Rounds.lean:370, next-round bilinear relation example | equivalent |

### Protocol

| Exact source | Exact target | Status |
|---|---|---|
| `Protocol.lean` #1, L78 `two_rounds` | T/Effects.lean: `EffectsTest.two_rounds` and recording client | premise-required (P2) |
| `Protocol.lean` #2, L93 example (record) | T/Effects.lean: `EffectsTest.two_rounds` and recording client | premise-required (P2) |
| `Protocol.lean` #3, L101 `abort_response` | T/Effects.lean: `EffectsTest.bad_first_rounds`, `EffectsTest.runWithLog_wrong` | premise-required (P1) |
| `Protocol.lean` #4, L107 example | T/Effects.lean: `EffectsTest.bad_first_rounds`, `EffectsTest.runWithLog_wrong` | premise-required (P1) |
| `Protocol.lean` #5, L113 example | T/Effects.lean: `EffectsTest.target_seven_not_final` | equivalent |
| `Protocol.lean` #6, L144 example | C/Soundness.lean: `indexedVerifier_run_soundness`; C/Indexed.lean: `indexedVerifier_soundness`; interaction layer axiom checks | premise-required (P2) |
| `Protocol.lean` #7, L171 example | #1488: `Sumcheck.Core.intervalVerifier`, appended first-round and remaining intervals | child-owned (#1488) |
| `Protocol.lean` #8, L196 `#print axioms execute_soundness` | C/Soundness.lean: `indexedVerifier_run_soundness`; C/Indexed.lean: `indexedVerifier_soundness`; interaction layer axiom checks | premise-required (P2) |
| `Protocol.lean` #9, L197 `#print axioms execute_support_completeness` | C/Completeness.lean: `perfectCompleteness`; T/Completeness.lean: axiom checks | premise-required (P2) |
| `Protocol.lean` #10, L198 `#print axioms execute_perfectCompleteness` | C/Completeness.lean: `perfectCompleteness`; T/Completeness.lean: axiom checks | premise-required (P2) |

### RoundByRound

| Exact source | Exact target | Status |
|---|---|---|
| `RoundByRound.lean` #1, L22 example | C/Indexed.lean: `indexedVerifier_rbrSoundness`; C/Soundness.lean: `indexedVerifier_run_soundness` | premise-required (P2) |

### Sequential

| Exact source | Exact target | Status |
|---|---|---|
| `Sequential.lean` #1, L24 `second_eval` | T/Rounds.lean: `RoundsTest.second_eval` | equivalent |
| `Sequential.lean` #2, L36 example | T/Rounds.lean: `RoundsTest.run_two_bilinear` and challenge-order client | premise-required (P2) |
| `Sequential.lean` #3, L59 `second_sum` | T/Rounds.lean: `RoundsTest.second_sum` | equivalent |
| `Sequential.lean` #4, L79 example | T/Rounds.lean: `RoundsTest.run_two_bilinear` and challenge-order client | premise-required (P2) |
| `Sequential.lean` #5, L92 example | T/Rounds.lean: `RoundsTest.run_two` with a wrong target; `verdict_foldTranscript` | premise-required (P1) |
| `Sequential.lean` #6, L108 `#print axioms executeTwo_complete` | #1488: `Sumcheck.Core.intervalVerifier` completeness | child-owned (#1488) |

### SingleRound

| Exact source | Exact target | Status |
|---|---|---|
| `SingleRound.lean` #1, L23 example | T/SingleRound.lean: `SingleRoundTest.msgX_sum` | equivalent |
| `SingleRound.lean` #2, L27 example | T/SingleRound.lean:209; `SingleRoundTest.run_oneRound` | equivalent |
| `SingleRound.lean` #3, L34 example | T/SingleRound.lean:224; `SingleRoundTest.verdict_fail` | equivalent |
| `SingleRound.lean` #4, L52 example | T/SingleRound.lean:235, dishonest constant-message output | equivalent |
| `SingleRound.lean` #5, L58 `#print axioms executeAt_eq` | C/Indexed.lean: `Sumcheck.Core.indexedExecuteAt_list_eq`; T/Domain.lean: arbitrary-list and `[0, 0]` clients and axiom checks | equivalent |
| `SingleRound.lean` #6, L59 `#print axioms executeAt_honest` | C/Indexed.lean: `Sumcheck.Core.indexedExecuteAt_univariate_honest`; T/Domain.lean: arbitrary-list and `[0, 0]` clients and axiom checks | equivalent |

### Soundness

| Exact source | Exact target | Status |
|---|---|---|
| `Soundness.lean` #1, L29 example | T/SingleRound.lean:253, collision-zero example | equivalent |
| `Soundness.lean` #2, L35 example | T/SingleRound.lean:266, collision-one example | equivalent |
| `Soundness.lean` #3, L41 example | C/Soundness.lean: `indexedVerifier_committed_soundness`; T/Soundness.lean: interaction layer arbitrary-list client and axiom check | equivalent |
| `Soundness.lean` #4, L49 example | T/SingleRound.lean:277, rejection at the collision challenge | equivalent |
| `Soundness.lean` #5, L66 `rejection_probability` | T/Soundness.lean: `SoundnessTest.rejection_probability` | equivalent |
| `Soundness.lean` #6, L77 `exact_repair_probability` | T/Soundness.lean: `SoundnessTest.exact_repair_probability` | equivalent |
| `Soundness.lean` #7, L93 `excludes_quadratic` | T/Soundness.lean: `SoundnessTest.excludes_quadratic` | equivalent |
| `Soundness.lean` #8, L112 `adaptive_endpoints` | T/Soundness.lean: `SoundnessTest.adaptive_endpoints` | equivalent |
| `Soundness.lean` #9, L119 `adaptive_hits` | T/Soundness.lean: `SoundnessTest.adaptive_hits` | equivalent |
| `Soundness.lean` #10, L123 `challenge_first_probability` | T/Soundness.lean: `SoundnessTest.challenge_first_probability` | equivalent |
| `Soundness.lean` #11, L143 `fresh_bound_lt_one` | T/Soundness.lean: `SoundnessTest.fresh_bound_lt_one` | equivalent |
| `Soundness.lean` #12, L148 `empty_domain_rejection` | T/Soundness.lean: `SoundnessTest.empty_domain_rejection` | equivalent |
| `Soundness.lean` #13, L155 `#print axioms zeroPolynomial` | T/Soundness.lean: `SingleRoundTest.poly0` axiom check | equivalent |
| `Soundness.lean` #14, L156 `#print axioms linearPolynomial` | T/Soundness.lean: `CompletenessTest.polyX`, `SoundnessTest.polyXK` axiom check | equivalent |
| `Soundness.lean` #15, L157 `#print axioms rejection_probability` | T/Soundness.lean: `SoundnessTest.rejection_probability` axiom check | equivalent |
| `Soundness.lean` #16, L158 `#print axioms exact_repair_probability` | T/Soundness.lean: `SoundnessTest.exact_repair_probability` axiom check | equivalent |
| `Soundness.lean` #17, L159 `#print axioms excludes_quadratic` | T/Soundness.lean: `SoundnessTest.excludes_quadratic` axiom check | equivalent |
| `Soundness.lean` #18, L160 `#print axioms adaptivePolynomial` | T/Soundness.lean: `SoundnessTest.adaptive` axiom check | equivalent |
| `Soundness.lean` #19, L161 `#print axioms adaptive_endpoints` | T/Soundness.lean: `SoundnessTest.adaptive_endpoints` axiom check | equivalent |
| `Soundness.lean` #20, L162 `#print axioms adaptive_hits` | T/Soundness.lean: `SoundnessTest.adaptive_hits` axiom check | equivalent |
| `Soundness.lean` #21, L163 `#print axioms challenge_first_probability` | T/Soundness.lean: `SoundnessTest.challenge_first_probability` axiom check | equivalent |
| `Soundness.lean` #22, L164 `#print axioms fresh_bound_lt_one` | T/Soundness.lean: `SoundnessTest.fresh_bound_lt_one` axiom check | equivalent |
| `Soundness.lean` #23, L165 `#print axioms empty_domain_rejection` | T/Soundness.lean: `SoundnessTest.empty_domain_rejection` axiom check | equivalent |
| `Soundness.lean` #24, L169 `#print axioms executeCommitted_eq` | T/SingleRound.lean: `SingleRoundTest.run_oneRound`; C/Indexed.lean: `indexedVerifier_run` | equivalent |
| `Soundness.lean` #25, L170 `#print axioms executeCommitted_soundness` | C/Soundness.lean: `indexedVerifier_committed_soundness`; T/Soundness.lean: interaction layer arbitrary-list client and axiom check | equivalent |
| `Soundness.lean` #26, L171 `#print axioms executeRandomCommitment_soundness` | C/Soundness.lean: `indexedVerifier_randomized_soundness`; T/Soundness.lean: interaction layer arbitrary-list client and axiom check | equivalent |
| `Soundness.lean` #27, L172 `#print axioms executeCommitted_measureSoundness` | C/Soundness.lean: `indexedVerifier_committed_measureSoundness`; interaction layer axiom check | equivalent |
| `Soundness.lean` #28, L173 `#print axioms executeRandomCommitment_measureSoundness` | C/Soundness.lean: `indexedVerifier_randomized_measureSoundness`; interaction layer axiom check | equivalent |

### SourceRouting

| Exact source | Exact target | Status |
|---|---|---|
| `SourceRouting.lean` #1, L34 private `eval_affine` | T/Effects.lean: `EffectsTest.eval_affine`, `EffectsTest.answer_affine`, `EffectsTest.route_affine` over semirings and `Nat` | equivalent |
| `SourceRouting.lean` #2, L37 private `answer_affine` | T/Effects.lean: `EffectsTest.eval_affine`, `EffectsTest.answer_affine`, `EffectsTest.route_affine` over semirings and `Nat` | equivalent |
| `SourceRouting.lean` #3, L48 example | C/Tree.lean: `protocol_succ`; removed `Option` challenge and abort-selected suffix | retired (`Option` challenge/abort shape) |
| `SourceRouting.lean` #4, L153 `accepted` | #1488: `Sumcheck.Core.intervalVerifier`, append with an exported polynomial oracle | child-owned (#1488) |
| `SourceRouting.lean` #5, L198 `abort` | #1488: `Sumcheck.Core.intervalVerifier`, append with an exported polynomial oracle | child-owned (#1488) |
| `SourceRouting.lean` #6, L241 `suffix_rejected` | #1488: `Sumcheck.Core.intervalVerifier`, append with an exported polynomial oracle | child-owned (#1488) |
| `SourceRouting.lean` #7, L285 `accepted_relation` | #1488: `Sumcheck.Core.intervalVerifier`, append with an exported polynomial oracle | child-owned (#1488) |

### Generic soundness implication

These four source rows are in `ArkLibTest/Interaction/Oracle/Security/Soundness.lean`.
The exact parent dispositions, including freshness and failure scope, are in
[soundness-implication-disposition.md](soundness-implication-disposition.md).

| Exact source | Exact target in `ArkLib/Interaction/Core/Security/Implications.lean` | Status |
|---|---|---|
| #3, L54 `executeStrategies_soundness` | `OracleVerifier.soundness_of_rbrSoundness` | equivalent |
| #4, L55 `executeStrategies_soundness_uniform` | `OracleVerifier.soundness_of_rbrSoundness_uniform` | equivalent |
| #5, L57 `OrdinaryState.exists_verifier_escape` | `StateFunction.escapeAlong` | equivalent |
| #6, L58 `LocalSoundness.random_prefix` | `flip_random_prefix_le` | equivalent |

## Remaining work

#1488 owns interval verifiers and their endpoint-dependent composition and projection clients.
The behavior-guarantee rows remain unresolved until the parent exposes the corresponding
interface. The fixed protocol is not generic in its message carrier; the computable-carrier
sharing question OQ17 remains open. The interaction layer full-run soundness proof needs neither an
interval verifier nor a legacy fold-to-sequential bridge.

## Departures

These are the two departures of entry 22 in [`departures.md`](departures.md).

### The transferred completeness is in its own module

**Plan.** The implementation plan puts completeness in `Completeness`.

**Code.** `Completeness` keeps the direct proof for the compatibility honest prover.
`LegacyCompleteness` holds `legacyProver_perfectCompleteness`, the transfer of
`Spec.oracleReduction_perfectCompleteness`.

**Why.** `LegacyEquivalence` imports `Completeness`, so a transfer that needs
`LegacyEquivalence` cannot live there. The direct theorem accepts every challenge implementation;
the transferred theorem uses the embedded legacy honest prover, uniform challenges and an
output witness. Both statements remain available.

### The verifier has no interval start

**Migration.** Several frozen assertions execute one round inside a multivariate statement or
split an interval into a first round and a suffix.

**Code.** `indexedVerifier R deg n D ambient` and the compatibility `verifier` cover the full
run from zero to `n`. `firstRound_relation` in the `Rounds` test checks relation transport while
retaining the input polynomial. It does not execute the projected output oracle or an interval.

**Intervals.** #1488 builds `intervalVerifier` from its `foldVerifier` and adds `start`, `count`
and `start + count = n`. The interval rows above remain unresolved by the full-run results. The
interaction layer full-run soundness proof uses the generic soundness implication from #1486
directly.

## Agreement universes and parent limits

`Interaction.Core.OracleVerifier.Agrees` and every law in `Security/Agreement.lean` accept
path-dependent output statements `T p`, oracle indices `J p`, carriers `B p j` and interfaces
`outputs p`. Outcomes and output problems use `OracleVerifier.Output T B`. The decision and
output-map cast laws retain the verifier owner's independent ambient and output-index universes;
ordinary runs retain its move/response universe `u`. `cast_const` identifies the general
transport with ordinary equality substitution for constant output families. Ordinary substitution
keeps those output carriers fixed while changing the tree. Classical probability interfaces specialize
the move and returned-value universe to zero, as their owners require.

Agreement accepts general `OracleBundle.{u, uI, dI}` inputs, with independent query and data
universes. Family-shaped inputs specialize this API through `OracleBundle.ofFamily`.
Round-by-round knowledge agreement and transport retain `Win stmt`, `W stmt tr`, and relations
`relOut stmt tr output witness`, with independent witness universes. They also preserve the
parent's full-prefix challenge distributions and local errors. Sumcheck's compatibility theorem
uses `rbrKnowledgeSoundnessOfNodes`, the parent specialization that ignores prefix history.

| Reviewed contract | Status | Evidence |
|---|---|---|
| F7: path-dependent outputs throughout Agreement | equivalent | `Agrees`, all agreement consequences and every `*_cast` law reindex the statement and oracle families together. No constant-output replacement remains. |
| 3A: statement-dependent knowledge witnesses and relations | equivalent | `Agrees.rbrKnowledgeSoundness_iff` and `rbrKnowledgeSoundness_cast` use the unchanged owner's argument shapes. Sumcheck passes `fun _ _ t w => (t, w) ∈ Spec.relationRound R n deg D (Fin.last n)`. |

`ArkLibTest/Interaction/Core/AgreementUniverses.lean` imports the public API with statement,
input-index, input-query, output-query and oracle-node-query universes 2, 1, 3, 4 and 5. Its
knowledge client uses statement-dependent input witnesses in `Type 6` and
statement-and-transcript-dependent output witnesses in `Type 7`. Output families depend on the
shape path. Further clients exercise general move, ambient-index and output-index universes.

The remaining restrictions come from these parent interfaces:

| New API | Parent interface | Required restriction |
|---|---|---|
| `OracleVerifier.runWithLog_eq_of_decide_eq` | `OracleVerifier.runWithLog` in `Security/Knowledge.lean` | Bundle-query indices and oracle-node queries are small because the full log is a small run output. Input data and output queries remain independent. |
| `Agrees.run_eq` and `run_cast` | `OracleVerifier.run` in `Core/OracleVerifier.lean` | Ambient and output indices share the move/response universe `u`. Output statements and oracle data are values in `Type u`; node and output queries remain independent. |
| Extraction and classical security laws | `classicalModel`, `extractionGame`, `classicalStraightLine`, `validAcceptance` and the RBR wrappers | Probability computations return small values, including output statements, output indices and extracted witnesses. Input data and queries remain independent. Pure RBR witness carriers retain the owner's independent universes. |
| Legacy tree relation adapter `treeRelationProblem` | `Legacy.relProblem` in `Core/Legacy/Security.lean` | The parent convenience adapter fixes claims to `Type 0`; the tree adapter accepts larger claims. The underlying `Problem` and classical security interfaces already accept larger claims. |

## Production declaration inventory

This inventory covers all 19 production modules in
`ArkLib/ProofSystem/Sumcheck/Interaction/`, including private source declarations and explicit
structure fields. The named sources below are fully qualified. The one anonymous local instance
has no user-facing declaration name; its row identifies its namespace and exact source location.
Compiler-generated recursors, constructors and equation lemmas are not separate source declarations.
`C/` retains the Core source prefix defined above. A target qualified by #1488 is a child interface,
not a claim that this branch implements its interval contract. Each such row retains the source
`start`/`count` scope, including arbitrary prefixes and the full endpoint `start + count = n`.
For generic and computable carriers, the child must preserve message interpretation and ambient
effects as well as endpoints. Restricting those rows to this branch’s mathematical polynomial
carrier would not close them.

The one-round execution targets below use arbitrary maps or `domain.get`, without a sampling
assumption. `univariateData` embeds the original univariate input into the interaction layer one-variable
polynomial data and `univariateData_eval` identifies every evaluation. The execution equations
retain that original data independently of the sent message. The interaction layer total-mass equation and
explicit rejection are separate contracts. `ProbComp` is lossless in the pinned VCVio model;
neither the old nor the new total-mass equation asserts a positive probability of failure.

### Production: ArbitraryCompleteness

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.MultivariateRound.executeRoundsSampled_support_completeness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryCompleteness.lean:35` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeRoundsSampled_perfectCompleteness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryCompleteness.lean:87` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeRoundsSampled_measureCompleteness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryCompleteness.lean:102` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeRounds_uniform_perfectCompleteness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryCompleteness.lean:118` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeRounds_uniform_measureCompleteness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryCompleteness.lean:131` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |

### Production: ArbitraryRounds

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.MultivariateRound.roundInterfaces`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:33` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.roundStages`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:44` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.roundStages_run`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:60` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeRoundsSampled`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:83` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeRounds`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:95` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeRoundsSampled_zero`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:108` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeRoundsSampled_one`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:118` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeRoundsSampled_two`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:134` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeRounds_two`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:158` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.honestMessages`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:178` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.roundStages_honest`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:184` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeRounds_honest`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:205` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeRounds_evaluation`, `ArkLib/ProofSystem/Sumcheck/Interaction/ArbitraryRounds.lean:262` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |

### Production: Closing

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.SingleRound.outputFamily`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:27` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier` (`outputMap := OracleMap.fst`; retained original data) | equivalent |
| `Sumcheck.Interaction.SingleRound.outputOracle`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:31` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier` (`outputMap := OracleMap.fst`; retained original data) | equivalent |
| `Sumcheck.Interaction.SingleRound.outputClaim`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:35` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier` (`outputMap := OracleMap.fst`; retained original data) | equivalent |
| `Sumcheck.Interaction.SingleRound.degreeModel`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:40` | `Interaction.Core` counterpart of `OracleModel.satisfies_guarantee` | unresolved (missing parent `OracleModel.satisfies_guarantee` behavior-guarantee interface) |
| `Sumcheck.Interaction.SingleRound.degreeGuarantee`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:53` | `Interaction.Core` counterpart of `OracleModel.satisfies_guarantee` | unresolved (missing parent `OracleModel.satisfies_guarantee` behavior-guarantee interface) |
| `Sumcheck.Interaction.SingleRound.message_degree`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:56` | `Interaction.Core` counterpart of `OracleModel.satisfies_guarantee` | unresolved (missing parent `OracleModel.satisfies_guarantee` behavior-guarantee interface) |
| `Sumcheck.Interaction.SingleRound.claimVerifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:62` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier`; C/Indexed.lean: `Sumcheck.Core.indexedExecute` | premise-required (P1) |
| `Sumcheck.Interaction.SingleRound.claimReduction`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:76` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier`; C/Indexed.lean: `Sumcheck.Core.indexedExecute` | premise-required (P1) |
| `Sumcheck.Interaction.SingleRound.honestRun`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:86` | C/Indexed.lean: `Sumcheck.Core.indexedRoundResult` (`data := fun _ => univariateData p`, `msg := p`) | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCore_honest`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:95` | C/Indexed.lean: `Sumcheck.Core.indexedExecuteAt_univariate_honest` (including unchanged original data) | equivalent |
| `Sumcheck.Interaction.SingleRound.honestClaim`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:117` | C/Indexed.lean: `Sumcheck.Core.indexedRoundResult` (`data := fun _ => univariateData p`, `msg := p`) | equivalent |
| `Sumcheck.Interaction.SingleRound.honestRun_closed`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:121` | C/Indexed.lean: `Sumcheck.Core.indexedRoundResult`; C/Indexed.lean: `Sumcheck.Core.univariateData_eval` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCore_closed`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:126` | C/Indexed.lean: `Sumcheck.Core.indexedExecuteAt_univariate_honest` (including unchanged original data) | equivalent |
| `Sumcheck.Interaction.SingleRound.closedOutputRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:136` | C/Domain.lean: `Sumcheck.Core.behaviorOutputRelation` (`point := r`, arbitrary evaluation behavior) | equivalent |
| `Sumcheck.Interaction.SingleRound.closedInputRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:140` | C/Domain.lean: `Sumcheck.Core.behaviorInputRelation` (arbitrary evaluation behavior) | equivalent |
| `Sumcheck.Interaction.SingleRound.honestRun_closed_related`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:145` | C/Indexed.lean: `Sumcheck.Core.indexedRoundResult_univariate_honest` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCore_complete`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:151` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_complete` (monad `OracleComp ambient`, challenge `pure r`) | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCore_degree_complete`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:161` | Parent behavior-guarantee interface plus C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_complete` | unresolved (missing parent `OracleModel.satisfies_guarantee` behavior-guarantee interface) |
| `Sumcheck.Interaction.SingleRound.sampledClaimVerifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:171` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier`; C/Indexed.lean: `Sumcheck.Core.indexedExecute` | premise-required (P1) |
| `Sumcheck.Interaction.SingleRound.sampledClaimReduction`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:187` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier`; C/Indexed.lean: `Sumcheck.Core.indexedExecute` | premise-required (P1) |
| `Sumcheck.Interaction.SingleRound.simulate_challenge`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:197` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_eq` (arbitrary lawful monad and challenge computation) | equivalent |
| `Sumcheck.Interaction.SingleRound.executeSampled`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:207` | C/Indexed.lean: `Sumcheck.Core.indexedExecute` (`data := fun _ => univariateData p`, `msg := p`) | equivalent |
| `Sumcheck.Interaction.SingleRound.executeSampled_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:214` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_honest_eq` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeSampled_support`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:243` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_support` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeSampled_perfectCompleteness`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:258` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_perfectCompleteness` | equivalent |
| `Sumcheck.Interaction.SingleRound.prEvent_eq_evalDist_map_unifSpec` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:268` | `prEvent_eq_evalDist_map` | retired (monad-specific probability wrapper) |
| `Sumcheck.Interaction.SingleRound.executeSampled_measureCompleteness`, `ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:273` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_univariate_measureCompleteness` | equivalent |

### Production: Composition

| Exact source | Exact target | Status |
|---|---|---|
| `Interaction.Oracle.executeStrategiesCore_closed_eq_run` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:27` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.midpointStatement`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:58` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.firstRoundFragment`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:65` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.remainingVerifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:91` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.composedVerifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:107` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.firstRound_closingImpl`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:123` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.firstRound_closingImpl_literal` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:131` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.onAppendedRuntime_native` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:142` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.splitPrefix_native` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:151` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.exportedPrefixRun_firstRound`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:179` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.execute_appendExported_succ`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:232` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.execute_eq_appendExported`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:337` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.exportedSuffixRun_some`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:369` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.exportedSuffixRun_none`, `ArkLib/ProofSystem/Sumcheck/Interaction/Composition.lean:398` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |

### Production: Computable

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.Computable.FinalStatement`, `ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:29` | C/Types.lean: `Sumcheck.Core.RoundStatement` at `Fin.last n` | equivalent |
| `Sumcheck.Interaction.Computable.outputRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:31` | C/Domain.lean: `Sumcheck.Core.behaviorOutputRelation` (arbitrary original evaluation behavior) | equivalent |
| `Sumcheck.Interaction.Computable.protocol`, `ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:34` | #1488: `Sumcheck.Core.foldVerifier` / `Sumcheck.Core.intervalVerifier` with interpreted computable messages | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Computable.verifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:39` | #1488: `Sumcheck.Core.foldVerifier` / `Sumcheck.Core.intervalVerifier` with interpreted computable messages | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Computable.execute`, `ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:42` | #1488: `Sumcheck.Core.foldVerifier` / `Sumcheck.Core.intervalVerifier` with interpreted computable messages | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Computable.interpretProver`, `ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:48` | #1488: `Sumcheck.Core.foldVerifier` / `Sumcheck.Core.intervalVerifier` with interpreted computable messages | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Computable.execute_eq_native`, `ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:54` | #1488: `Sumcheck.Core.foldVerifier` / `Sumcheck.Core.intervalVerifier` with interpreted computable messages | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |

### Production: ComputableCompleteness

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.Computable.honestProver`, `ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean:37` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Computable.interpretProver_honestProver`, `ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean:51` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Computable.execute_honestProver_eq_native`, `ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean:81` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Computable.execute_support_completeness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean:95` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Computable.execute_perfectCompleteness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean:116` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |

### Production: ComputableSoundness

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.Computable.execute_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ComputableSoundness.lean:31` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |

### Production: Legacy

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.SingleRound.<anonymous-instance>`, `ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean:31` | `Interaction.Core.Legacy.oracleChallengeImpl` | retired (local legacy challenge-interface override) |
| `Sumcheck.Interaction.SingleRound.legacy_output_iff`, `ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean:35` | C/Indexed.lean: `Sumcheck.Core.univariateData_eval` | equivalent |
| `Sumcheck.Interaction.SingleRound.legacy_input_iff`, `ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean:43` | C/Domain.lean: `Sumcheck.Core.sum_domain_embedding`; C/Indexed.lean: `Sumcheck.Core.univariateData_eval` | equivalent |
| `Sumcheck.Interaction.SingleRound.legacyTranscript`, `ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean:53` | C/LegacyEquivalence.lean: `Sumcheck.Core.simpleLegacyTranscript` | equivalent |
| `Sumcheck.Interaction.SingleRound.legacyTranscript_message`, `ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean:58` | C/LegacyEquivalence.lean: `Sumcheck.Core.simpleLegacyTranscript_message` | equivalent |
| `Sumcheck.Interaction.SingleRound.legacyTranscript_challenge`, `ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean:62` | C/LegacyEquivalence.lean: `Sumcheck.Core.simpleLegacyTranscript_challenge` | equivalent |
| `Sumcheck.Interaction.SingleRound.legacy_prover_run`, `ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean:66` | C/LegacyEquivalence.lean: `Sumcheck.Core.simpleLegacyProver_run` (separate Simple-protocol compatibility check) | equivalent |
| `Sumcheck.Interaction.SingleRound.legacy_verifier_correspondence`, `ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean:109` | C/LegacyEquivalence.lean: `Sumcheck.Core.simpleLegacyVerifier_correspondence` (separate Simple-protocol compatibility check) | equivalent |

### Production: MultivariateRound

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.MultivariateRound.access`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:32` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.outputOracle`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:36` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.sumQueries`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:44` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.terminal`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:53` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.verifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:66` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.reduction`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:75` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.acceptedRun`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:85` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.simulate_sumQueries`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:96` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.simulate_terminal`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:116` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeCore_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:132` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeCore_accepted`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:158` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.acceptedRun_closed`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:167` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeCore_closed`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:174` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.sampledVerifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:185` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.sampledReduction`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:197` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.simulate_challenge`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:208` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeCore_sampled_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:220` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.closedRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:248` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.honestNext`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:255` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeCore_honest`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:262` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.honestNext_related`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:276` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.closedRelation_last_iff`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:285` | #1488: `Sumcheck.Core.intervalVerifier` boundary `start = n`, `count = 0`, for arbitrary original oracle behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |

### Production: MultivariateSoundness

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.MultivariateRound.executeCore_sampled_closed_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateSoundness.lean:36` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.acceptedRun_closedRelation_iff`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateSoundness.lean:54` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.projected_sum_iff_closedRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateSoundness.lean:65` | C/Domain.lean: `Sumcheck.Core.sum_projectedRoundPolynomial`; C/DomainEquivalence.lean: `Sumcheck.Core.indexedRelation_embedding` | equivalent |
| `Sumcheck.Interaction.MultivariateRound.executeCore_sampled_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateSoundness.lean:77` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.prEvent_eq_evalDist_map_unifSpec` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateSoundness.lean:104` | `prEvent_eq_evalDist_map` | retired (monad-specific probability wrapper) |
| `Sumcheck.Interaction.MultivariateRound.executeCore_sampled_measureSoundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateSoundness.lean:109` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |

### Production: Projection

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.SingleRound.projectionOracle`, `ArkLib/ProofSystem/Sumcheck/Interaction/Projection.lean:25` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.SingleRound.projectionOracle_eval`, `ArkLib/ProofSystem/Sumcheck/Interaction/Projection.lean:30` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.SingleRound.projectedInput`, `ArkLib/ProofSystem/Sumcheck/Interaction/Projection.lean:38` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.SingleRound.projectedInput_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/Projection.lean:44` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.SingleRound.executeCore_projected_closed`, `ArkLib/ProofSystem/Sumcheck/Interaction/Projection.lean:52` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.SingleRound.executeCore_projected`, `ArkLib/ProofSystem/Sumcheck/Interaction/Projection.lean:67` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |

### Production: ProjectionTransport

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.SingleRound.executeCore_projected_of_relationRound`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProjectionTransport.lean:27` | #1488: `Sumcheck.Core.intervalVerifier`, one round starting at `i` (`start = i`, `count = 1`), with projected input behavior | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |

### Production: Protocol

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.Native.Core.messageInterface`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:35` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.Core.protocol`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:41` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.Core.firstRoundProtocol`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:50` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.Core.remainingProtocol`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:54` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.Core.protocol_succ_eq_append`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:61` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.Core.FinalStatement`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:74` | C/Types.lean: `Sumcheck.Core.RoundStatement` at `Fin.last n` | equivalent |
| `Sumcheck.Interaction.Native.Core.latest`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:79` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.Core.latestSum`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:86` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.Core.verifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:98` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.Core.execute`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:123` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.Core.outputRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:137` | C/Domain.lean: `Sumcheck.Core.behaviorOutputRelation` (arbitrary original evaluation behavior) | equivalent |
| `Sumcheck.Interaction.Native.Core.simulate_latest`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:142` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.Core.simulate_latestSum`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:152` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.Core.execute_zero`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:165` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.Core.execute_succ`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:181` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.Core.execute_eq_of_originalOracle_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:235` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.Core.transportProver`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:271` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.Core.execute_transport`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:290` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.protocol`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:333` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.firstRoundProtocol`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:335` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.remainingProtocol`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:337` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.FinalStatement`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:339` | C/Types.lean: `Sumcheck.Core.RoundStatement` at `Fin.last n` | equivalent |
| `Sumcheck.Interaction.Native.latest`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:344` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.latestSum`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:346` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.verifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:348` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.execute`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:351` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.outputRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:354` | C/Domain.lean: `Sumcheck.Core.behaviorOutputRelation` (arbitrary original evaluation behavior) | equivalent |
| `Sumcheck.Interaction.Native.protocol_succ_eq_append`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:358` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.simulate_latest`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:369` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.simulate_latestSum`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:378` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.execute_zero`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:387` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.execute_succ`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:401` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.execute_eq_of_originalOracle_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:427` | #1488: `Sumcheck.Core.foldVerifier` and `Sumcheck.Core.intervalVerifier`, including generic message interpretation | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |

### Production: ProtocolCompleteness

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.Native.honestProver`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolCompleteness.lean:36` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.execute_support_completeness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolCompleteness.lean:52` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.execute_perfectCompleteness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolCompleteness.lean:110` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |

### Production: ProtocolSoundness

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.MultivariateRound.uniform_successor_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean:40` | C/Indexed.lean: `Sumcheck.Core.indexed_round_soundness` | equivalent |
| `Sumcheck.Interaction.Native.midpointRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean:71` | #1488: `Sumcheck.Core.intervalVerifier` prefix/export and interval soundness | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.midpointOracleRealized`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean:81` | #1488: `Sumcheck.Core.intervalVerifier` prefix/export and interval soundness | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.exportedPrefixRun_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean:89` | #1488: `Sumcheck.Core.intervalVerifier` prefix/export and interval soundness | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.exportedPrefixRun_admissibility`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean:145` | #1488: `Sumcheck.Core.intervalVerifier` prefix/export and interval soundness | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.execute_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean:201` | #1488: `Sumcheck.Core.intervalVerifier` prefix/export and interval soundness | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |

### Production: RoundByRound

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.Native.CurrentClaim` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:38` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.PendingMessage` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:41` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.PrefixData` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:44` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.PrefixData.claim` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:45` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree transcript-observer record fields) |
| `Sumcheck.Interaction.Native.PrefixData.pending` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:46` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree transcript-observer record fields) |
| `Sumcheck.Interaction.Native.PrefixData.rank` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:47` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree transcript-observer record fields) |
| `Sumcheck.Interaction.Native.PrefixData.step` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:48` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree transcript-observer record fields) |
| `Sumcheck.Interaction.Native.TranscriptObserver` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:50` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.rootData` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:57` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.restrictObserver` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:62` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.prefixData` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:71` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.prefixData_root` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:75` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.prefixData_public` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:78` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.prefixData_oracle` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:85` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.restrictObserver_comp` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:92` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.prefixData_comp` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:109` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.transcriptObserver` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:117` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.observer_root_rank` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:132` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.observer_root_claim` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:137` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.nextChallenge`, `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:146` | #1488: `Sumcheck.Core.intervalVerifier` round-by-round implication with `count` challenges | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.samplePending` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:151` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.modelOf` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:157` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.stateOf` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:164` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.rankOf` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:172` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.nextChallenge_local_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:176` | #1488: `Sumcheck.Core.intervalVerifier` round-by-round implication with `count` challenges | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.Native.transcriptObserver_prover` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:198` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.transcriptObserver_schedule` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:224` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.rootBound` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:257` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.LocalCertificate` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:264` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.localCertificate_restrict` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:273` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.localCertificate_root` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:289` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.localCertificate_bound` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:299` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.transcriptObserver_local` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:319` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.fresh_prependPublic` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:360` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.fresh_prependOracle` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:392` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.transcriptObserver_fresh` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:425` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.executeStrategies_succ` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:495` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.closeExecution` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:549` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.executeStrategies_terminal` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:559` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.execute_eq_closeExecution` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:635` | C/Indexed.lean: `Sumcheck.Core.foldPrefix`; `Interaction.Core.StateFunction` | retired (TypeTree runtime, transcript observer and run-closing proof scaffolding) |
| `Sumcheck.Interaction.Native.roundByRound_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/RoundByRound.lean:659` | #1488: `Sumcheck.Core.intervalVerifier` round-by-round implication with `count` challenges | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |

### Production: Sequential

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.MultivariateRound.executeTwo`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:31` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeTwo_accepted`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:47` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeTwo_rejected`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:67` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeTwo_second_rejected`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:78` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeTwoSampled`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:96` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeTwoSampled_accepted`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:114` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeTwoSampled_rejected`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:144` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeTwo_honest`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:161` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |
| `Sumcheck.Interaction.MultivariateRound.executeTwo_complete`, `ArkLib/ProofSystem/Sumcheck/Interaction/Sequential.lean:181` | #1488: `Sumcheck.Core.intervalVerifier` and its interval execution/completeness/soundness equations | child-owned (#1488: `start`, `count`; endpoint `start + count ≤ n`, full endpoint `start + count = n`) |

### Production: SingleRound

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.SingleRound.Message`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:32` | `Polynomial.degreeLE` (the same message subtype) | equivalent |
| `Sumcheck.Interaction.SingleRound.polynomialInterface`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:36` | `inferInstance : OracleInterface R⦃≤ deg⦄[X]`, used by C/SingleRound.lean: `Sumcheck.Core.round` | equivalent |
| `Sumcheck.Interaction.SingleRound.inputSpec`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:42` | C/Indexed.lean: `Sumcheck.Core.univariateData_eval`; C/Types.lean: `Sumcheck.Core.polyFamily` | equivalent |
| `Sumcheck.Interaction.SingleRound.protocol`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:45` | C/SingleRound.lean: `Sumcheck.Core.round` | premise-required (P2) |
| `Sumcheck.Interaction.SingleRound.access`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:50` | `Interaction.Core.pathBundle` (input family and sent oracle messages) | equivalent |
| `Sumcheck.Interaction.SingleRound.sumQueries`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:56` | C/Indexed.lean: `Sumcheck.Core.indexedDecision` | premise-required (P1) |
| `Sumcheck.Interaction.SingleRound.terminal`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:65` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier` | premise-required (P1) |
| `Sumcheck.Interaction.SingleRound.verifier`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:75` | C/Indexed.lean: `Sumcheck.Core.indexedVerifier` | premise-required (P1) |
| `Sumcheck.Interaction.SingleRound.prover`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:88` | C/Indexed.lean: `Sumcheck.Core.committedProver` | equivalent |
| `Sumcheck.Interaction.SingleRound.inputImpl`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:93` | C/Indexed.lean: `Sumcheck.Core.univariateData_eval`; C/Types.lean: `Sumcheck.Core.polyFamily` | equivalent |
| `Sumcheck.Interaction.SingleRound.simulate_sumQueries`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:96` | C/Indexed.lean: `Sumcheck.Core.simulateQ_indexedSumQueries_monad` (no `DecidableEq` or sampler) | equivalent |
| `Sumcheck.Interaction.SingleRound.simulate_terminal`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:114` | C/Indexed.lean: `Sumcheck.Core.indexedRoundResult`; C/Indexed.lean: `Sumcheck.Core.indexedVerifier_run_one` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeAt`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:128` | C/Indexed.lean: `Sumcheck.Core.indexedExecute` (challenge `pure r`; data `univariateData p`) | equivalent |
| `Sumcheck.Interaction.SingleRound.executeAt_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:134` | C/Indexed.lean: `Sumcheck.Core.indexedExecuteAt_list_eq` (arbitrary original input, arbitrary sent message) | equivalent |
| `Sumcheck.Interaction.SingleRound.executeAt_honest`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:149` | C/Indexed.lean: `Sumcheck.Core.indexedExecuteAt_univariate_honest` | equivalent |
| `Sumcheck.Interaction.SingleRound.honest_outputRelation`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:157` | C/Indexed.lean: `Sumcheck.Core.univariateData_eval` | equivalent |
| `Sumcheck.Interaction.SingleRound.legacy_input_sum`, `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:162` | C/Domain.lean: `Sumcheck.Core.sum_domain_embedding`; C/Domain.lean: `Sumcheck.Core.sum_domain_list` | equivalent |

### Production: Soundness

| Exact source | Exact target | Status |
|---|---|---|
| `Sumcheck.Interaction.SingleRound.committedRun`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:35` | C/Indexed.lean: `Sumcheck.Core.indexedRoundResult` (`data := fun _ => univariateData p`, `msg := q`) | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCommitted`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:45` | C/Indexed.lean: `Sumcheck.Core.indexedExecute` (arbitrary challenge; original `p`, sent `q`) | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCommitted_eq`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:52` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_eq` | equivalent |
| `Sumcheck.Interaction.SingleRound.committedRun_true_iff`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:91` | C/Indexed.lean: `Sumcheck.Core.indexedRoundResult_true_iff`; C/Indexed.lean: `Sumcheck.Core.univariateData_eval` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCommitted_failure`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:103` | C/Indexed.lean: `Sumcheck.Core.indexedExecute_failure` (specialize `D := domain.get`) | equivalent |
| `Sumcheck.Interaction.SingleRound.committedRun_rejects`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:110` | C/Indexed.lean: `Sumcheck.Core.indexedRoundResult_rejects`; C/Domain.lean: `Sumcheck.Core.sum_domain_list` | equivalent |
| `Sumcheck.Interaction.SingleRound.prEvent_eq_evalDist_map_unifSpec` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:118` | `prEvent_eq_evalDist_map` | retired (monad-specific probability wrapper) |
| `Sumcheck.Interaction.SingleRound.prEvent_bind_le_of_forall_le_unifSpec` (private), `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:123` | `prEvent_bind_le_of_forall_le` | retired (monad-specific probability wrapper) |
| `Sumcheck.Interaction.SingleRound.executeCommitted_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:131` | C/Soundness.lean: `Sumcheck.Core.indexedVerifier_committed_soundness`; C/Domain.lean: `Sumcheck.Core.sum_domain_list` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeRandomCommitment_soundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:158` | C/Soundness.lean: `Sumcheck.Core.indexedVerifier_randomized_soundness`; C/Domain.lean: `Sumcheck.Core.sum_domain_list` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeCommitted_measureSoundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:169` | C/Soundness.lean: `Sumcheck.Core.indexedVerifier_committed_measureSoundness` | equivalent |
| `Sumcheck.Interaction.SingleRound.executeRandomCommitment_measureSoundness`, `ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:179` | C/Soundness.lean: `Sumcheck.Core.indexedVerifier_randomized_measureSoundness` | equivalent |
