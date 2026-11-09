# Embedding the legacy layer into the interaction layer

The modules under `ArkLib/Interaction/Core/Legacy/` embed legacy protocol specifications,
provers, verifiers and oracle verifiers into the interaction layer. They also relate the two
executions and transfer completeness, soundness, knowledge soundness and their round-by-round
forms between the layers. Nothing here changes the legacy layer. The embedding reads legacy definitions and reuses their meaning.

## Modules

| Module | Contents |
|---|---|
| `Protocol` | `protocol pSpec`, the plain tree of a legacy specification, and `oracleProtocol pSpec`, its oracle tree. Also `transcriptEquiv`, which identifies runtime paths with legacy full transcripts. |
| `Prover` | `embedProver`, which turns a legacy prover into a focal strategy slot for slot. Also `legacySampler`, the public-coin sampler indexed by legacy challenge rounds. |
| `Verifier` | `embedVerifier` and `embedReduction`. The verifier decides on the decoded transcript. |
| `OracleReduction` | `embedOracleProver` and `embedOracleVerifier` on the oracle tree, for both legacy oracle-output representations. `OracleMap.ofLegacySimulation` turns a legacy output-oracle simulation into an oracle map. |
| `Execution` | The common observation, the execution correspondence and its logged form. |
| `OracleExecution` | The execution correspondence on the oracle tree: transport of oracle-tree strategies to the plain tree, the transcript read off a run, and `oracleFinalize`. |
| `Security` | The completeness, soundness and knowledge-soundness transfers, the legacy transcript prefix of a full prefix, and the round-by-round transfers. |
| `OracleSecurity` | The completeness, soundness and round-by-round transfers for the embedded oracle verifier on the oracle tree. |
| `OracleKnowledge` | The straight-line knowledge-soundness transfers for the embedded oracle verifier on the oracle tree, with the logged form of the oracle execution correspondence. |

## The common observation

An interaction-layer run of a plain tree produces an `Observation`: the runtime path, the
prover's output and the verdict `Option T`. A legacy run produces a value of `OptionT`, where
rejection is missing mass. The two are compared through

```lean
finalize : Observation plainSig (protocol pSpec) (fun _ => StmtOut × WitOut) StmtOut →
  LegacyResult pSpec StmtOut WitOut
-- LegacyResult = Option ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut)
```

`finalize` decodes the transcript of an accepted run and maps a rejected run to `none`. Each
security transfer compares the legacy probability of an event with the interaction-layer measure
of the event "accepted, and the legacy event holds". Rejection is never treated as missing mass.

Challenges are routed through `challengeReindex`, which answers the challenge node of each
interaction-layer round with the legacy challenge oracle of the same round. Its probabilistic
form is `plainChallengeImpl chImpl`.

## Execution correspondence

- `finalize_observeWith_counterpartFirst` is a program equality. In the counterpart-first
  schedule, the finalized interaction-layer run of an embedded reduction is the legacy run after
  reindexing. It holds for every legacy prover.
- `simulateQ_finalize_observe` gives the same program equality in the default schedule. It
  assumes `PureChallengeSlots`: every `receiveChallenge` is `pure`.
- `experiment_finalize_observe_evalDistEq` and `evalDist_experiment_finalize_observe` hold for
  every prover. They state the equality in distribution and as measures, under any measurable
  structure. The proof moves challenge draws past the prover's effects, which works because
  `plainChallengeImpl` is stateless.
- `runEq_ambientLogged_prover` is the logged form of the prover phase. `ambientLogged` logs a
  program's queries and keeps the shared-oracle entries. `run_ambientLogged` shows that this log
  is the one that `logImpl impl` keeps in the experiment state. The logged prover-sampler run of
  an embedded prover therefore has the distribution of the legacy logged prover run, jointly with
  its shared-oracle log and the final state, from every state. The proof reuses the
  challenge-moving argument with `logImpl impl` as the shared implementation.

## Security transfers

Legacy relations and languages become statement problems with trivial admissibility,
`relProblem` and `langProblem`.

**Completeness** (`completeness_iff`). For a legacy reduction `R`, the following are equivalent:

- `(embedReduction R).completeness init impl (plainChallengeImpl challengeQueryImpl)
  (relProblem relIn) (relProblem relOut) (fun _ o => o.1) (fun obs _ _ => obs.2.1.2)
  (fun _ w => w) ε`
- `R.completeness init impl relIn relOut ε`

The interaction-layer judgement reads the prover's output statement and witness, and
requires the verifier's statement to equal the prover's. This matches the legacy event
`(stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut`.

**Soundness** (`soundness_iff`). For a legacy verifier `V`, the following are equivalent:

- `(embedVerifier V).soundness init impl (plainChallengeImpl challengeQueryImpl)
  (langProblem langIn) (langProblem langOut) ε`
- `V.soundness init impl langIn langOut ε`

Each direction translates every adversary of one layer into the other.

- A legacy prover becomes an interaction-layer prover through `embedProver`.
- An interaction-layer prover with any output family first has its outputs replaced by a fixed
  statement `t₀` and the trivial witness (PolyFun's `Strategy.mapOutput`). It then becomes the legacy prover
  `translate`, whose state is the remaining strategy and whose output is the strategy's output.
  `embedProver_translate` shows that embedding the translation gives back the strategy. If
  `StmtOut` is empty, nothing is accepted and the bound holds trivially.

Neither transfer needs `PureChallengeSlots`, because both use the distributional correspondence.

**Knowledge soundness** (`knowledgeSoundnessWith_iff`, `knowledgeSoundness_iff`). For a legacy
verifier `V` and a legacy straight-line extractor `E`, the following are equivalent:

- `knowledgeSoundnessWith ((embedVerifier V).classicalModel init impl
  (plainChallengeImpl challengeQueryImpl)) (relProblem relIn) (relProblem relOut)
  (knowledgeJudgement relOut) (classicalStraightline (fun _ => WitIn) (embedVerifier V) init
  impl (plainChallengeImpl challengeQueryImpl) (fun _ o => o.2)) (liftExtractor E) ε`
- `V.knowledgeSoundnessWith init impl relIn relOut E ε`

The observation and witness types carry the discrete measurable structure. The prover's output
family is `fun _ => StmtOut × WitOut`. `knowledgeJudgement relOut` judges the verifier's
statement with the prover's output witness, as the legacy bad event does, and the extractor
reads that witness. `liftExtractor E` runs `E` on the decoded transcript, and
`lowerExtractor` is its inverse, so the existential notions are also equivalent.

Both layers' games end with the same phase, `knowledgeTail`: the logged verifier run, then the
extractor after acceptance. `legacy_exec_run` and `extractionGame_embed` are the program
equalities that split each game into its logged prover phase and `knowledgeTail`.
`prEvent_legacy_knowledge` combines them with `runEq_ambientLogged_prover`. It shows that the
legacy probability of the bad event equals the interaction-layer measure of the bad set.
Interaction-layer adversaries are translated with `translate`, which keeps their outputs.

Neither transfer needs a hypothesis on the extractor. Different schedules interleave
challenge entries and shared-oracle entries in a run's log differently. An extractor that read
the interleaving could tell the two executions apart, and a transfer would need it to be
`ChallengeMoveInvariant`. Both layers, however, give the extractor only the shared-oracle part
`QueryLog.fst` of the prover's log. Every such function is invariant
(`challengeMoveInvariant_comp_fst`, `challengeMoveInvariant_extractor`).

### Round-by-round soundness and knowledge soundness

The interaction layer states round-by-round notions over full prefixes `(sp, hist)`: a cursor
spine `sp` into `protocol pSpec` with the runtime moves `hist : PrefixMoves plainSig sp`. The
legacy layer states them over transcript prefixes `Transcript j pSpec`.

`legacyPrefix sp hist : (j : Fin (n + 1)) × Transcript j pSpec` is the legacy transcript prefix
that a full prefix decodes to. Its lemmas carry the correspondence:

- `legacyPrefix_root`: the empty full prefix is round `0` with the empty transcript.
- `legacyPrefix_complete`: a terminal full prefix is round `n` with the decoded transcript.
- `prefixFrom_step`: a full prefix ending at a node is at some round `j < n` with that node's
  move type. One move `x` extends the legacy transcript to `tr.concat (plainMoveEquiv _ _ x)`.
  At a challenge node, `challengeRound 0 n _` sends the node's challenge to the legacy
  challenge index `⟨j, _⟩`. The draw `sampleAt` at the node under
  `plainChallengeImpl challengeQueryImpl` is the legacy draw `$ᵗ pSpec.Challenge ⟨j, _⟩`,
  transported along the move type (`sampleAt_plainChallengeImpl`).

Each transfer reads the interaction-layer error at challenge node `c` as
`ε (challengeRound 0 n (Nat.zero_add n) c)`, the legacy error of that node's round.

**Round-by-round soundness** (`embedVerifier_rbrSoundness`, `rbrSoundness_of_embedVerifier`,
`rbrSoundness_iff`). For a legacy verifier `V` and `ε : pSpec.ChallengeIdx → ℝ≥0`:

- `V.rbrSoundness init impl langIn langOut ε` and
  `hcert : ∀ S : V.StateFunction init impl langIn langOut, StateTerminalCertificate S` give
  `(embedVerifier V).rbrSoundness impl (langProblem langIn) (langProblem langOut)
  (plainChallengeImpl challengeQueryImpl) (fun c => ε (challengeRound 0 n _ c))`.
- The converse holds for every `init`, without a certificate.

`embedStateFunction S hS` sends a legacy state function `S` with an all-state terminal
certificate `hS` to the state at the legacy prefix.
`legacyStateFunction` sends an interaction-layer state function to the legacy state "every full
prefix with this legacy prefix is in the state". Each per-prefix bound is the other layer's bound
at the corresponding prefix: the event is the image of the legacy event under the reindexed
challenge draw.

**Round-by-round knowledge soundness** (`embedVerifier_rbrKnowledgeSoundness`,
`rbrKnowledgeSoundness_of_embedVerifier`, `rbrKnowledgeSoundness_iff`). The interaction-layer
instance has trivial admissibility, input relation `fun stmt w => (stmt, w) ∈ relIn`, and output
relation `fun _ t w => (t, w) ∈ relOut`, at the constant output witness family `fun _ => WitOut`.

- `V.rbrKnowledgeSoundness init impl relIn relOut ε` and a `KnowledgeTerminalCertificate` for
  every legacy knowledge state function give
  `(embedVerifier V).rbrKnowledgeSoundness impl (fun _ => True) (fun stmt w => (stmt, w) ∈ relIn)
  (fun _ t w => (t, w) ∈ relOut) (plainChallengeImpl challengeQueryImpl)
  (fun c => ε (challengeRound 0 n _ c))`. `embedKnowledgeStateFunction` uses
  `WitMid (legacyPrefix sp hist).1` as the witness at a full prefix, and reindexes the legacy
  extractor `E` to give the interaction-layer extraction functions.
- With `[Nonempty WitIn]`, the converse holds for every `init`. It does not transport extractors
  (departure 16).

**All-state terminal certificates** (`Security.lean`). The terminal obligation of an
interaction-layer state function quantifies over every ambient state; the legacy one is stated
for a fresh `init` state (departure 15). The certificates restate the legacy terminal field for
every ambient state:

- `StateTerminalCertificate S`: on a full transcript where `S` is false, legacy `verify` accepts
  into no output in `langOut` from any ambient state.
- `KnowledgeTerminalCertificate K`: if legacy `verify` can accept an output related to `wo` from
  some ambient state, then `K` holds at the full transcript of the witness extracted from `wo`.

Each certificate holds for every state function in three cases:

| Constructor | Hypothesis | `init` |
| --- | --- | --- |
| `of_support_init` | `∀ st, st ∈ support init` | full support |
| `of_stateIndependent` | the legacy verdict is the same from every ambient state | any |
| `of_guarded` | a `Verifier.GuardedForm` of the legacy verifier | any |

`Layout.rbrSoundness_of_legacyWith` and `Layout.rbrKnowledgeSoundness_of_legacyWith` take one
certified state function, or one certified extractor and knowledge state function, with its
bound. The existential transfers take a certificate for every state function. The test
`ArkLibTest/Interaction/Core/Legacy/Security.lean` instantiates them for a guarded verifier with
`σ = Bool` and `init := pure false`, which does not produce the state `true`.

## Oracle reductions

The oracle tree `oracleProtocol pSpec` records each prover message as an oracle: the verifier's
view holds the challenges only, and the decision reads messages and input oracle statements
through the oracle families. The results below are stated on that tree, for
`embedOracleVerifier V` and `embedOracleProver P`. They are not consequences of the plain
transfers applied to `V.toVerifier`; the plain transfers are an ingredient of their proofs.

### Execution correspondence

The oracle tree and the plain tree have the same rounds, owners and runtime moves.
`toPlainFrom` sends an oracle-tree strategy of either participant to the plain tree, and
`toOraclePath` sends a plain runtime path back. The runner commutes with the transport
(`runWith_toPlainFrom`), as do `Prover.simulate` and the sampler. The transport of the embedded
oracle prover is the embedded plain prover (`toPlainFrom_embedOracleProver`).

On the runtime path `tr` of an actual run:

- `viewChallenges_toView`: the challenges in the verifier's view are
  `(oracleDecode pSpec tr).challenges`.
- `pathMessages_payloads`: the data of the message oracles are
  `(oracleDecode pSpec tr).messages`.
- `simulateQ_embedOracleVerifier_decide`: the routed decision, answered from the input data and
  the path's payloads, is legacy `verify` on the decoded challenges under
  `simOracle2 oSpec oStmt (oracleDecode pSpec tr).messages`. The ambient queries go to any
  implementation in a lawful monad: the identity, a stateful implementation, or a logging one.
- `embedOracleVerifier_outputMap_f`: the output data are
  `V.materializeOutput (oracleDecode pSpec tr).challenges oStmt (oracleDecode pSpec tr).messages`.

The common result is

```lean
oracleFinalize : Observation oracleSig (oracleProtocol pSpec)
    (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut) (StmtOut × (∀ i, OStmtOut i)) →
  LegacyResult pSpec (StmtOut × (∀ i, OStmtOut i)) WitOut
```

It keeps the prover's output statement, output oracle data and witness, and the verifier's output
statement and output oracle data, as legacy `OracleReduction.run` does. The verifier's output
data come from its output map, so both legacy output-oracle representations are covered.

- `oracleFinalize_observeWith_counterpartFirst` is the program equality for every legacy oracle
  reduction `R`: the finalized counterpart-first oracle observation of
  `embedOracleVerifier R.verifier` against `embedOracleProver R.prover stmt oStmt wit` is
  `(R.run stmt oStmt wit).run`.
- `simulateQ_oracleFinalize_run` gives the same equality for the default run
  `(embedOracleVerifier R.verifier).run`, after `oracleChallengeReindex`, under
  `PureChallengeSlots R.prover`.
- `experiment_oracleFinalize_run_evalDistEq` and `evalDist_experiment_oracleFinalize_run` state
  the equality in distribution and as measures, under `oracleChallengeImpl chImpl`, for every
  reduction.
- `oracleObserveWith_embed`, `simulateQ_embedOracleVerifier_run` and
  `experiment_embedOracleVerifier_run` compare an oracle run against any oracle-tree prover with
  the plain run of `embedVerifier V.toVerifier` against the transported prover. The oracle
  observation is the plain observation with its path read back by `toOracleObservation`.

### Security transfers

The oracle notions use `OracleVerifier.classicalModel` with
`oracleChallengeImpl challengeQueryImpl`. Statements are pairs `(stmt, oStmt)`; legacy oracle
notions are defined through `V.toVerifier`.

- `oracleCompleteness_iff`: completeness of the embedded oracle reduction for the honest-output
  judgement is legacy `R.completeness`.
- `oracleSoundness_iff`: soundness of `embedOracleVerifier V` against every oracle-tree prover is
  legacy `V.soundness`. An oracle-tree prover is transported to the plain tree; a legacy prover
  embeds as `embedOracleProver`.
- `oracleAcceptanceAgrees`: the oracle verifier's `validAcceptance` agrees with legacy `verify`
  on the decoded transcript. The generic round-by-round transfers of `Layout` then give
  `embedOracleVerifier_rbrSoundness`, `rbrSoundness_of_embedOracleVerifier`,
  `embedOracleVerifier_rbrKnowledgeSoundness` and
  `rbrKnowledgeSoundness_of_embedOracleVerifier`, with the certificate hypotheses of the plain
  transfers, for the state functions of `V.toVerifier`.

### Straight-line knowledge soundness

`OracleKnowledge` states the straight-line transfers for `embedOracleVerifier V`, in the classical
straight-line oracle interface `OracleVerifier.classicalStraightline`, with the judgement
`oracleKnowledgeJudgement relOut`: the verifier's output statement and output oracle data, with the
prover's output witness. The oracle extraction game logs the decision before its input-oracle and
message queries are answered, and gives the extractor the ambient part of that log.

- `runEq_ambientLogged_oracleProver`: for every starting state, the decoded logged prover-sampler
  run on the oracle tree agrees in distribution with the decoded logged run of the transported
  prover on the plain tree, including the transcript, prover output, shared-oracle log and final
  shared state. With
  `runEq_ambientLogged_prover` it reaches the legacy logged prover run.
- `oracleExtractionGame_embed`: the oracle extraction game with a lifted legacy extractor, read as
  a legacy result, is that logged run followed by `knowledgeTail` for `V.toVerifier`. The ambient
  part of the decision log is the log of the legacy decision, in which `simOracle2` answers the
  input-oracle and message queries without ambient queries. The proof uses the core's
  `OracleVerifier.runWithLog_fst` and `simulateQ_embedOracleVerifier_decide` with a logging
  implementation.
- `liftOracleExtractor` decodes the oracle transcript with `oracleDecode`; `lowerOracleExtractor`
  reads a legacy transcript back with `(oracleTranscriptEquiv pSpec).symm`.
- `oracleKnowledgeSoundnessWith_iff`: a legacy straight-line extractor `E` certifies knowledge
  soundness of `embedOracleVerifier V` exactly when it certifies legacy
  `V.knowledgeSoundnessWith`, with the same relations and error. A rejected run yields no witness
  and an explicit extraction failure stays in the bad event, in both layers.
  `oracleKnowledgeSoundness_iff` is the existential form.

The observation-marginal obligation is the core's `OracleVerifier.classicalStraightline_marginal`.

### Output-oracle simulations

`OracleMap.ofLegacySimulation S challenges p` is the oracle map of a legacy
`OracleOutputSimulation`. Its data map is the legacy materialization and its queries follow
`S.simulateOutputQuery`. `simulateQ_ofLegacySimulation_impl` states that answering a query from
realized data is answering `simulateOutputQuery` under `simOracle2`. `legacyOutputMap V` is the
oracle map of `V`'s output semantics read as a simulation.

## Departures

These entries continue the numbered departures of
[`IMPLEMENTATION-NOTES.md`](../interaction-rebuild/IMPLEMENTATION-NOTES.md) for the security
transfers of this embedding. They state each hypothesis or choice beyond the legacy statement.
[`departures.md`](departures.md) indexes all entries, and records the oracle correspondence gap
and its resolution.

### 14. The knowledge transfer needs no extractor-invariance premise

The plan for the legacy embedding expected the knowledge-soundness transfer to assume that the
extractor is invariant when challenge queries move relative to shared-oracle queries in the
prover's log. Two executions of the same run under different schedules interleave the two kinds of
entries differently, and the transfer moves challenge draws past the prover's effects. The code
states this property as `ChallengeMoveInvariant` (`Legacy/Execution.lean`). It does not assume it,
because both layers hand the extractor only `QueryLog.fst` of the prover's log: legacy
`knowledgeSoundnessWith` passes `proveQueryLog.fst`, and the core's `Verifier.runWithLog` passes
`proveLog.fst` (see `runWithLog_fst`). Every function of that projection is invariant
(`challengeMoveInvariant_comp_fst`, `challengeMoveInvariant_extractor`). The proof keeps the
shared-oracle log in the experiment state (`logImpl`), so the challenge-moving argument of the
unlogged correspondence applies unchanged (`runEq_ambientLogged_prover`).

`knowledgeSoundnessWith_iff` and `knowledgeSoundness_iff` therefore have the legacy statement's
hypotheses only. They fix an instantiation of the core notion: the prover's output family is
`fun _ => StmtOut × WitOut`, the judgement is `knowledgeJudgement relOut` (the verifier's
statement with the prover's output witness), the extractor reads that witness, and the
observation and witness types carry the discrete measurable structure. The access budget is `0`,
which the classical straight-line interface meets. The qualification of entry 6 does not arise,
because `classicalStraightline_marginal` gives marginal preservation for every extractor.

### 15. Round-by-round transfers into the interaction layer assume all-state terminal certificates

`embedVerifier_rbrSoundness`, `embedVerifier_rbrKnowledgeSoundness`, `rbrSoundness_iff`,
`rbrKnowledgeSoundness_iff`, their oracle forms and the `Layout` transfers assume an all-state
terminal certificate (`StateTerminalCertificate`, `KnowledgeTerminalCertificate`). The terminal
obligation of an interaction-layer state function, `leaf`, refutes `validAcceptance`. That
predicate holds when the verifier can accept *from some ambient state*. The legacy terminal
obligation, `toFun_full`, bounds the acceptance probability from a fresh state drawn by `init`.
A legacy state function therefore says nothing about states that `init` cannot produce, and the
leaf obligation needs them covered. The certificate is the legacy terminal field restated for
every ambient state; the core terminal obligation is unchanged.

The certificate holds when `init` can produce every ambient state (`of_support_init`), when the
legacy verdict does not depend on the ambient state (`of_stateIndependent`), and for every
guarded verifier (`of_guarded`). The last two hold for any `init`, such as `init := pure false`
on `Bool`.

The transfers out of the interaction layer need no certificate: an interaction-layer leaf
obligation covers every ambient state, hence every state that `init` draws.

### 16. Round-by-round knowledge soundness out of the interaction layer goes through induced languages

`rbrKnowledgeSoundness_of_embedVerifier` and `rbrKnowledgeSoundness_iff` assume
`[Nonempty WitIn]`, and the converse direction does not transport the extractor. Interaction-layer
witnesses are indexed by full prefixes. Protocols live in `Type 1`, so a legacy intermediate
witness family `WitMid : Fin (n + 1) → Type` cannot quantify over the spines that decode to a
round. The proof therefore discards the witnesses. `languageStateFunction` sends a knowledge
state function to a state function for the induced languages `relIn.language` and
`relOut.language`, whose round-by-round soundness transfers by `rbrSoundness_of_embedVerifier`.
The legacy `Verifier.rbrSoundness_implies_rbrKnowledgeSoundness` then gives round-by-round
knowledge soundness with a classically chosen extractor. That lemma needs `Nonempty WitIn`.

Neither layer constrains its round-by-round extractor beyond the state-function obligations, so
the existential notions are still equivalent. A statement that names a particular
interaction-layer extractor is not transported back.
