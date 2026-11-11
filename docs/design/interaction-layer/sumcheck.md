# Sumcheck in the interaction layer

`Sumcheck.Core.Soundness` proves full-run soundness natively over an arbitrary finite indexed
domain `D : Fin d → R`. The verifier sums over indices. In particular, the constant polynomial
one has sum two over `[0, 0]`; neither the verifier nor its proof deduplicates the list.

The proof first bounds a false-to-true transition of the remaining-sum relation at each fresh
challenge. `indexedVerifier_rbrSoundness` packages these bounds as a core state function.
`indexedVerifier_soundness` then applies the parent stack's
`OracleVerifier.soundness_of_rbrSoundness_uniform`, using exactly one challenge per round.
For every ambient-effectful prover and every output family, the probability of a valid accepted
output from a false input is at most `n * (deg / |R|)`. The ring assumptions are a finite
commutative semiring with `IsDomain`; the domain map need not be injective or nonempty.

## Modules and ownership

| Module | Contents |
|---|---|
| `Types` | Native round statements, polynomial oracle data and prefix/suffix coordinates. |
| `SingleRound`, `Tree` | The oracle-message/public-challenge round, the fixed full-run tree, transcript access and sampling. |
| `Domain` | Indexed remaining sums, honest projected polynomials, the successor identity and final evaluation relation. |
| `Indexed` | The native indexed verifier, its actual-run equation, the state function and native local-to-global soundness proof. |
| `Soundness` | Full-run, arbitrary-list and injective corollaries; actual-run committed and randomized bounds in probability and measure form. |
| `DomainEquivalence` | Separate agreement checks with the injective legacy `Spec` representation. |
| `Protocol`, `Execution`, `Completeness` | Compatibility honest prover and decision, closed-form runs and direct completeness. |
| `LegacyEquivalence`, `LegacySoundness`, `LegacyCompleteness` | Separate execution and security comparisons with embedded legacy Sumcheck. |
| `Knowledge`, `RoundByRound` | Compatibility knowledge and round-by-round transfers. |

The native import graph is `Soundness → Indexed → Domain / Tree → Types`. It does not import
`Sumcheck.Spec`, the compatibility execution or a legacy security transfer. `DomainEquivalence`
and `LegacyEquivalence` check agreement separately. The compatibility `verifier` keeps its old
name; the native verifier is `indexedVerifier`.

## The native verifier and its bound

`protocol R deg n` has exactly `n` rounds. Each sends a degree-bounded polynomial and draws a
public challenge in `R`. Neither the oracle message nor the challenge selects shape (P2).
The verifier is passive: it queries the messages and decides after the interaction (P1).
A failed sum check skips the remaining decision queries. All prover effects and challenge draws
have already run. Its output oracle is the original input polynomial.

`indexedRelation D i stmt p` states that the indexed remaining sum equals `stmt.target`.
At the last round, `indexedRelation_last` identifies this with polynomial evaluation at the
full challenge vector. If a false current relation passes the message's indexed sum check,
the honest and sent round polynomials differ. A successor relation can hold only at one of
their agreement points, whose uniform mass is at most `deg / |R|`.

| Native theorem | Exact scope |
|---|---|
| `indexed_round_soundness` | One false-to-true indexed round, including the sum check. |
| `indexedVerifier_rbrSoundness` | Every full execution prefix, with local error `deg / |R|`. |
| `verifier_soundness`, `verifier_soundness_rounds` | The actual full run, for every prover, with `n` times that error. |
| `verifier_soundness_list` | `D = domain.get` for any list, retaining repetitions. |
| `verifier_soundness_injective` | The same native bound for an embedding. |
| `verifier_run_soundness` | Probability that the actual run returns a verdict satisfying the final evaluation relation. |
| `committed_soundness`, `committed_measureSoundness` | An arbitrary polynomial committed before the one-round challenge. |
| `randomized_soundness`, `randomized_measureSoundness` | An ambient, possibly failing commitment before the fresh challenge, including shared state. |

These bounds concern valid accepted outputs. They do not assert that every accepted verdict is
valid. A dishonest message can pass a sum check while the retained input polynomial fails the
final relation. Tests retain this distinction.

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

## Compatibility security and completeness

The compatibility knowledge theorems retain the legacy relations and injective domain:
`verifier_knowledgeSoundness` quantifies over legacy-compatible output statements and witnesses;
`verifier_rbrKnowledgeSoundness` quantifies over all provers with `Unit` witnesses.
`verifier_rbrSoundness` is the separate compatibility round-by-round transfer.
The native round-by-round theorem is `indexedVerifier_rbrSoundness`.
`legacyVerifier_soundness` in `LegacySoundness` and its rounds form preserve the old transfer as a
comparison check. The native security statements do not use them.

`perfectCompleteness` proves completeness directly for the compatibility honest prover and
every challenge implementation. `legacyProver_perfectCompleteness` concerns the embedded legacy
honest prover with uniform challenges and also judges its output witness. The compatibility
round-by-round transfers use the guarded terminal certificates of departure 15. No transfer
requires inhabited ambient response types: `supportedAnswer` obtains answers from support.
The knowledge transfers extract the constant `Unit` output witness from the prover's output.

## Tests

The files under `ArkLibTest/ProofSystem/Sumcheck/Core/` retain the existing acceptance, rejection,
exact-probability, adaptive-message, effect-order, routing and axiom checks. Compatibility tests
import the comparison modules explicitly. Native tests add arbitrary maps and lists, committed
and randomized actual runs, and an actual final decision with constant message one and target
two over `[0, 0]`. `NativeSoundnessTest.repeated_run` checks the complete accepting program
on that repeated domain, including the transcript and retained input oracle. `Domain` also checks the repeated-point sum, its deduplicated contrast and a
two-coordinate indexed sum. Axiom checks permit only `propext`, `Classical.choice` and `Quot.sound`.

`Rounds` keeps the two- and three-round examples, including the bilinear input and challenge
order. `Effects` checks ambient effects, routed polynomial answers over every commutative
semiring, the `Nat` instance, and decision-query short circuiting after a bad first check.
`SingleRound` keeps honest, dishonest and rejected outputs. `Soundness` retains the exact repair
probability, the challenge-first attack, empty-domain rejection and the degree-carrier check.

## Migration disposition

Each source below identifies a frozen test file, migration-list row and source line. `T/` means
`ArkLibTest/ProofSystem/Sumcheck/Core/`; `C/` means `ArkLib/ProofSystem/Sumcheck/Core/`.
Unqualified target declarations are in `Sumcheck.Core`; test namespaces follow their file names.
The source prefix for the Sumcheck tables is `ArkLibTest/ProofSystem/Sumcheck/Interaction/`.
Each row has exactly one status:

- **equivalent**: the target preserves the source assertion's scope.
- **premise-required (P1)**: the source changes because the passive verifier sends only public
  coins and makes every resource query in the final decision.
- **premise-required (P2)**: the source changes because challenges and oracle messages never
  select shape.
- **retired**: the row names the removed mechanism, rather than claiming a narrower equivalent.
- **child-owned (#1488)**: the child owns interval endpoints `start`, `count` and
  `start + count = n`, including its `intervalVerifier` built from `foldVerifier`.
- **unresolved**: the row names a missing parent interface. A carrier fact cannot close a
  behavior-guarantee assertion.

Compatibility comparisons do not close native soundness rows. The native full-run bounds above
close those rows; interval completeness and projection executions remain with #1488.

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
| `ArbitraryRounds.lean` #6, L106 `#print axioms closedRelation_last_iff` | C/Domain.lean: `indexedRelation_last`; T/Rounds.lean: `RoundsTest.relationLast_iff_eval` | equivalent |

### Closing

| Exact source | Exact target | Status |
|---|---|---|
| `Closing.lean` #1, L17 example | Parent counterpart of `OracleModel.satisfies_guarantee`; degree subtype alone is narrower | unresolved (missing parent behavior-guarantee interface) |
| `Closing.lean` #2, L20 example | T/SingleRound.lean:209, honest output; `SingleRoundTest.run_oneRound` | equivalent |
| `Closing.lean` #3, L28 example | T/SingleRound.lean:218, honest final relation | equivalent |
| `Closing.lean` #4, L36 example | C/Completeness.lean: `perfectCompleteness_uniform`; T/Completeness.lean: uniform clients | equivalent |
| `Closing.lean` #5, L43 example | T/SingleRound.lean:235, dishonest output retaining input zero | equivalent |
| `Closing.lean` #6, L80 `#print axioms executeCore_closed` | T/SingleRound.lean: `SingleRoundTest.run_oneRound`, honest output and axiom checks | equivalent |
| `Closing.lean` #7, L81 `#print axioms executeCore_degree_complete` | Parent counterpart of `OracleModel.satisfies_guarantee` plus completeness | unresolved (missing parent behavior-guarantee interface) |
| `Closing.lean` #8, L82 `#print axioms executeSampled_eq` | T/SingleRound.lean: `SingleRoundTest.run_oneRound`, honest output and axiom checks | equivalent |
| `Closing.lean` #9, L83 `#print axioms executeSampled_perfectCompleteness` | C/Completeness.lean: `perfectCompleteness_uniform`; T/Completeness.lean: uniform clients | equivalent |

### Legacy

| Exact source | Exact target | Status |
|---|---|---|
| `Legacy.lean` #1, L29 `prover_generates_transcript` | T/LegacyEquivalence.lean: `LegacyEquivalenceTest.legacy_prover_run`, `LegacyEquivalenceTest.embedded_prover_generates` and wrong-target client | equivalent |
| `Legacy.lean` #2, L41 example | T/LegacyEquivalence.lean: `LegacyEquivalenceTest.legacy_prover_run`, `LegacyEquivalenceTest.embedded_prover_generates` and wrong-target client | equivalent |

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
| `Protocol.lean` #6, L144 example | C/Soundness.lean: `verifier_run_soundness`, `verifier_soundness_rounds`; native axiom checks | premise-required (P2) |
| `Protocol.lean` #7, L171 example | #1488: `Sumcheck.Core.intervalVerifier`, appended first-round and remaining intervals | child-owned (#1488) |
| `Protocol.lean` #8, L196 `#print axioms execute_soundness` | C/Soundness.lean: `verifier_run_soundness`, `verifier_soundness_rounds`; native axiom checks | premise-required (P2) |
| `Protocol.lean` #9, L197 `#print axioms execute_support_completeness` | C/Completeness.lean: `perfectCompleteness`; T/Completeness.lean: axiom checks | premise-required (P2) |
| `Protocol.lean` #10, L198 `#print axioms execute_perfectCompleteness` | C/Completeness.lean: `perfectCompleteness`; T/Completeness.lean: axiom checks | premise-required (P2) |

### RoundByRound

| Exact source | Exact target | Status |
|---|---|---|
| `RoundByRound.lean` #1, L22 example | C/Indexed.lean: `indexedVerifier_rbrSoundness`; C/Soundness.lean: `verifier_run_soundness` | premise-required (P2) |

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
| `SingleRound.lean` #5, L58 `#print axioms executeAt_eq` | T/SingleRound.lean: `SingleRoundTest.run_oneRound`, verdict/output examples and axiom checks | equivalent |
| `SingleRound.lean` #6, L59 `#print axioms executeAt_honest` | T/SingleRound.lean: `SingleRoundTest.run_oneRound`, verdict/output examples and axiom checks | equivalent |

### Soundness

| Exact source | Exact target | Status |
|---|---|---|
| `Soundness.lean` #1, L29 example | T/SingleRound.lean:253, collision-zero example | equivalent |
| `Soundness.lean` #2, L35 example | T/SingleRound.lean:266, collision-one example | equivalent |
| `Soundness.lean` #3, L41 example | C/Soundness.lean: `committed_soundness`; T/Soundness.lean: native arbitrary-list client and axiom check | equivalent |
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
| `Soundness.lean` #25, L170 `#print axioms executeCommitted_soundness` | C/Soundness.lean: `committed_soundness`; T/Soundness.lean: native arbitrary-list client and axiom check | equivalent |
| `Soundness.lean` #26, L171 `#print axioms executeRandomCommitment_soundness` | C/Soundness.lean: `randomized_soundness`; T/Soundness.lean: native arbitrary-list client and axiom check | equivalent |
| `Soundness.lean` #27, L172 `#print axioms executeCommitted_measureSoundness` | C/Soundness.lean: `committed_measureSoundness`; native axiom check | equivalent |
| `Soundness.lean` #28, L173 `#print axioms executeRandomCommitment_measureSoundness` | C/Soundness.lean: `randomized_measureSoundness`; native axiom check | equivalent |

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
sharing question OQ17 remains open. The native full-run soundness proof needs neither an
interval verifier nor a legacy fold-to-sequential bridge.

## Departures

These entries continue the numbering of [`departures.md`](departures.md).

### 20. The transferred completeness is in its own module

**Plan.** The implementation plan puts completeness in `Completeness`.

**Code.** `Completeness` keeps the direct proof for the compatibility honest prover.
`LegacyCompleteness` holds `legacyProver_perfectCompleteness`, the transfer of
`Spec.oracleReduction_perfectCompleteness`.

**Why.** `LegacyEquivalence` imports `Completeness`, so a transfer that needs
`LegacyEquivalence` cannot live there. The direct theorem accepts every challenge implementation;
the transferred theorem uses the embedded legacy honest prover, uniform challenges and an
output witness. Both statements remain available.

### 21. The verifier has no interval start

**Migration.** Several frozen assertions execute one round inside a multivariate statement or
split an interval into a first round and a suffix.

**Code.** `indexedVerifier R deg n D ambient` and the compatibility `verifier` cover the full
run from zero to `n`. `firstRound_relation` in the `Rounds` test checks relation transport while
retaining the input polynomial. It does not execute the projected output oracle or an interval.

**Ownership.** #1488 builds `intervalVerifier` from its `foldVerifier` and owns `start`, `count`
and `start + count = n`. Its rows above remain child-owned. Full-run results do not close them.
The native full-run soundness proof uses the parent #1486 implication directly.
