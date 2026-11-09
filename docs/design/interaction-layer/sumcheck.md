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
- **Decision.** `verifier_agrees`: on every completed run, the decision of the Sumcheck verifier
  and that of the embedded legacy verifier `legacyVerifier` are the same program in every lawful
  monad, and both keep the input polynomial as output oracle. `decide_trace` states the query
  trace: both decisions are `pure` of the legacy verdict, so neither makes an ambient query.
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

`Agrees` collects what decision agreement gives: equal runs, and equal completeness, soundness,
knowledge soundness and round-by-round forms. The `*_cast` lemmas carry each notion along
`protocol_eq`.

## Security

Each transfer starts from the stated legacy theorem and goes through the legacy embedding's
transfer theorem, the cast lemmas and `Agrees`. It covers every prover and every prover output
type, and keeps the legacy error.

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
| `SingleRound` | One-round runs: accepting, rejecting, a dishonest message that passes, distributions of one-round runs. |
| `Soundness` | Soundness against any one-round prover; exact probabilities over `ZMod 5` and `ZMod 17`. |
| `RoundByRound` | Clients of the round-by-round, knowledge and completeness transfers. |
| `Rounds` | Two- and three-round runs: challenge draws in round order, the accepted claim, a wrong target that still runs every round and rejects; the first-round relation transport. |
| `Effects` | A prover with ambient effects before each message and after the last challenge: the run executes them in protocol order, a recording handler observes the order, a false first claim still runs both rounds and rejects; the round message's oracle interface. |

## Open

- The verifier covers rounds `0` to `n`. There is no verifier for an interval of rounds starting
  at round `i`, so a run that starts mid-protocol, and the split of `n + 1` rounds into an
  appended first round and `n` rounds, are not stated. The first-round relation transport is
  stated on the round-`0` check instead (departure 18).
- A two-round composition through an exported oracle, with `OracleVerifier.append` and a
  first-round verifier exporting a transformed oracle, is not ported.
- The projection of the input polynomial to the round polynomial as an `OracleMap` is not
  defined.

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
round-`1` relation (`firstRound_relation` in the `Rounds` test). The split of `n + 1` rounds is
not stated.

**Why.** A verifier for an interval of rounds changes the statement types of the composition and
needs its own equivalence with the legacy single-round verifiers. It is left for the port of the
remaining checks.
