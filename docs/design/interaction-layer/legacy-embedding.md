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
| `OracleReduction` | `embedOracleProver` and `embedOracleVerifier` on the oracle tree, for both legacy oracle-output representations. |
| `Execution` | The common observation, the execution correspondence and its logged form. |
| `Security` | The completeness, soundness and knowledge-soundness transfers, the legacy transcript prefix of a full prefix, and the round-by-round transfers. |

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

- `V.rbrSoundness init impl langIn langOut ε` and `hinit : ∀ st, st ∈ support init` give
  `(embedVerifier V).rbrSoundness impl (langProblem langIn) (langProblem langOut)
  (plainChallengeImpl challengeQueryImpl) (fun c => ε (challengeRound 0 n _ c))`.
- The converse holds for every `init`, without `hinit`.

`embedStateFunction` sends a legacy state function to the state at the legacy prefix.
`legacyStateFunction` sends an interaction-layer state function to the legacy state "every full
prefix with this legacy prefix is in the state". Each per-prefix bound is the other layer's bound
at the corresponding prefix: the event is the image of the legacy event under the reindexed
challenge draw.

**Round-by-round knowledge soundness** (`embedVerifier_rbrKnowledgeSoundness`,
`rbrKnowledgeSoundness_of_embedVerifier`, `rbrKnowledgeSoundness_iff`). The interaction-layer
instance has trivial admissibility, input relation `fun stmt w => (stmt, w) ∈ relIn`, and output
relation `fun t w => (t, w) ∈ relOut`.

- `V.rbrKnowledgeSoundness init impl relIn relOut ε` and `hinit` give
  `(embedVerifier V).rbrKnowledgeSoundness impl (fun _ => True) (fun stmt w => (stmt, w) ∈ relIn)
  (fun t w => (t, w) ∈ relOut) (plainChallengeImpl challengeQueryImpl)
  (fun c => ε (challengeRound 0 n _ c))`. `embedKnowledgeStateFunction` uses
  `WitMid (legacyPrefix sp hist).1` as the witness at a full prefix, and reindexes the legacy
  extractor `E` to give the interaction-layer extraction functions.
- With `[Nonempty WitIn]`, the converse holds for every `init`. It does not transport extractors
  (departure 16).

## Departures

These entries continue the numbered departures of
[`IMPLEMENTATION-NOTES.md`](../interaction-rebuild/IMPLEMENTATION-NOTES.md) for the security
transfers of this embedding. They state each hypothesis or choice beyond the legacy statement.

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

### 15. Round-by-round transfers into the interaction layer assume `init` reaches every state

`embedVerifier_rbrSoundness`, `embedVerifier_rbrKnowledgeSoundness`, `rbrSoundness_iff` and
`rbrKnowledgeSoundness_iff` assume `hinit : ∀ st, st ∈ support init`. The terminal obligation of
an interaction-layer state function, `leaf`, refutes `validAcceptance`. That predicate holds when
the verifier can accept *from some ambient state*. The legacy terminal obligation, `toFun_full`,
bounds the acceptance probability from a fresh state drawn by `init`. A legacy state function
therefore says nothing about states that `init` cannot produce, and the leaf obligation needs
them covered. `hinit` holds whenever the ambient state type has a single value, as for
`init := pure ()` on `Unit`, or when `init` samples with full support.

The transfers out of the interaction layer need no such hypothesis: an interaction-layer leaf
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

## Not covered

The oracle-tree analogue of the execution correspondence is not stated.
