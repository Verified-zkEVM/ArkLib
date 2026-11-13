# D7. Security experiments, adversaries, admissibility, and transfers

**Status:** Proposed: awaiting maintainer approval.
**Implemented by:** ArkLib PR A (commit 1, neutral relations; commit 5, definitions), ArkLib PR B
(commit 4, transfers from the legacy layer), ArkLib PR C (commit 4, Sumcheck transfers), ArkLib
PR D (ported knowledge-composition, measured-resource and state-restoration support).

## Decision

**Experiment.** Every notion is a probability over `Reduction.run` (record D4) in the ambient
monad `OracleComp (oSpec + chal)`, interpreted by an ambient implementation `impl` (stateful, in
`StateT σ ProbComp`) together with a challenge implementation, exactly as the legacy experiment
interprets `QueryImpl.addLift impl challengeQueryImpl` (`OracleReduction/Security/Basic.lean:95`).
The run's outcome is `none` (the decision rejected) or the accepted output statement with the
prover's output. Rejection and missing probability mass are kept distinct.

**Claims and admissibility.** Input and output claims are judged by a problem with an explicit
admissibility boundary, moved to the neutral module `ArkLib/Relation/Basic.lean`:

```lean
-- intended, not existing (moved from ArkLib/Interaction/Oracle/Claim.lean:165–208)
structure Problem (S : ClaimFamily PublicCtx) where
  Witness        : ∀ ctx, S.Claim ctx → Type w
  admissible     : ∀ ctx, S.Claim ctx → Prop
  rel            : ∀ ctx claim, Witness ctx claim → Prop
  rel_admissible : ∀ ctx claim wit, rel ctx claim wit → admissible ctx claim
```

Composition theorems charge an explicit `δ` for intermediate outputs that are false and
inadmissible for the suffix theorem, giving `ε₁ + δ + ε₂` as described in
`docs/design/03-adversarial-oracle-execution.md` (section 4.1).

**Adversary class.** An adversarial prover is any focal strategy `Strat l .focal s Out` whose
slots are computations in `OracleComp oSpec`, lifted into the run's monad
`OracleComp (oSpec + chal)` (record D4), with arbitrary private memory in its continuations and any
output type the notion allows. As in the legacy layer, where the prover's fields live in
`OracleComp oSpec` (`OracleReduction/Basic.lean:158–173`), the prover does not query the challenge
oracle itself; it sees challenges only as moves. Security statements quantify over this whole
class.

This class is the *classical adversary model*. Completeness, soundness and knowledge soundness are
defined once, against an adversary model (record D9): a class of adversaries together with the
distribution each one induces on the observation (transcript, verdict, prover output). The
classical model is the default and the one every legacy transfer below targets. Record D9 adds a
quantum model after milestone 1 without changing these definitions. The round-by-round notions
take no model, because their errors bound flips over a fresh challenge for a fixed prefix.

**Notions** (intended definitions in `ArkLib/Interaction/Core/Security/`):

- *Completeness* (`Completeness.lean`): for every input in the input relation, with probability at
  least `1 - ε` the honest run accepts, the prover's and verifier's output statements agree, and
  the output pair is in the output relation. As legacy `completeness` (`Security/Basic.lean:87`).
- *Soundness* (`Soundness.lean`): for every input outside the input language and every
  adversary, the probability that the decision accepts an output in the output language is at
  most `ε`. As legacy `soundness` (line 266).
- *Knowledge soundness* (`Knowledge.lean`): with a named straightline extractor, as in legacy
  `knowledgeSoundnessWith` (line 298). The extractor receives the input statement, the
  adversary's output witness, the full transcript and the query logs, as `Extractor.Straightline`
  (line 242) does. The notion takes an extraction interface over the adversary model (record D9,
  section 4), which fixes what the extractor sees, whether it may re-enter the adversary, and the
  bound it must meet. A takes the classical straight-line interface with query logs, matching
  legacy; the transcript-only and rewinding interfaces are the other classical ones. A quantum
  model has no query-log interface, since superposition queries leave no log.
- *Round-by-round soundness and knowledge* (`RoundByRound.lean`): a state function on full-
  transcript prefixes, false on false inputs at the root, preserved across prover nodes, and
  forcing rejection at the leaf when false; the error is indexed by *challenge nodes* and bounds,
  for each fixed prefix ending at that node, the probability over the fresh challenge alone that
  the state flips from false to true.

```lean
-- intended, not existing
structure StateFunction (V : Verifier l s) (langIn langOut) where
  toFun      : StmtIn → (p : Prefix s) → PathAlong l p → Prop
  toFun_root : ∀ stmt, toFun stmt root ⟨⟩ → stmt ∈ langIn
  toFun_send : ∀ p (h : owner l (pos p) = .sender) stmt tr x, ¬ toFun stmt p tr → ¬ toFun stmt (p.snoc x) (tr.snoc x)
  toFun_leaf : ∀ stmt tr, ¬ toFun stmt (full tr) tr → V.rejectsOrOutside langOut stmt tr
def rbrSoundness (V) (ε : ChallengeNode s → ℝ≥0∞) : Prop :=
  ∃ S : StateFunction V langIn langOut, ∀ stmt ∉ langIn, ∀ (c : ChallengeNode s) (tr : prefix to c),
    Pr[ ¬ S stmt c tr ∧ S stmt (c.next x) (tr.snoc x) | x ← challenge at c ] ≤ ε c
```

Round-by-round state functions and extractors read the full transcript, including prefix oracle
payloads, as data (record D3). The default names (`rbrSoundness`, `rbrKnowledgeSoundness`) are the
worst-case-per-prefix forms, as in legacy `rbrSoundness` (`Security/RoundByRound.lean:464`) and
`rbrKnowledgeSoundness` (line 487).

**Translating adversaries to the legacy layer.** The legacy layer is not changed. Security
transfer needs every interaction-layer adversary translated into a legacy prover. By the slot
correspondence of record D4 this translation is exact, slot for slot, against
`runWith .counterpartFirst`, the schedule legacy execution uses (`Prover.processRound`,
`OracleReduction/Execution.lean:47–61`), for every protocol shape. B's execution equivalence
(record D8) is likewise a program equality against `runWith .counterpartFirst`.

What remains is the move from that schedule to the default `run`, by the exchange lemma of record
D4:

- *Program equality* when the prover's slots at challenge nodes are `pure`. This covers the honest
  Sumcheck prover, whose `receiveChallenge` is `pure fun chal => …`
  (`Sumcheck/Spec/SingleRound.lean:236–238`).
- *Equality in distribution* for an arbitrary prover, when the challenge implementation is
  stateless and separate from the shared-oracle state. ArkLib's uniform sampler satisfies it: the
  legacy experiment's `QueryImpl.addLift impl challengeQueryImpl` (`Security/Basic.lean:95`) draws
  challenges in `ProbComp`, lifted without touching the state `σ` of `impl`.

Soundness, completeness and round-by-round transfers for arbitrary adversaries use the
distributional form. Knowledge transfer additionally needs the extractor to give the same result
when challenge-oracle queries move relative to `oSpec` queries in the prover's log. For the legacy
straightline extractor this holds automatically: the knowledge game records the prover's log over
`oSpec + [pSpec.Challenge]ₒ` (`Reduction.runWithLog`, `OracleReduction/Execution.lean:356–360`) but
passes the extractor only `proveQueryLog.fst` (`Security/Basic.lean:313`), the `oSpec` part
(VCVio `QueryLog.fst`, a filter on left-summand queries), together with the verifier's `oSpec`
log. Exchanging a challenge draw with a prover slot does not reorder the prover's `oSpec` queries
among themselves.

**Transfer obligations** (PR B, used by PR C). Each transfer from the legacy layer states its
hypotheses. Equality of terminal distributions alone proves none of the last three:

- *Completeness:* the embedded honest parties produce matching outputs, and the relations
  correspond.
- *Soundness:* every adversary in the new class is translated to a legacy prover with the same
  acceptance probability, not only embedded legacy honest provers.
- *Knowledge:* the extractor and the witness relation are preserved by the translation, including
  the query logs the extractor reads.
- *Round-by-round:* a correspondence of prefixes and state functions, and equal challenge
  distributions at corresponding challenge nodes.

## Why

The legacy layer indexes round-by-round error by `pSpec.ChallengeIdx` (`RoundByRound.lean:464`),
a round number that exists because the shape is fixed in advance. With message-dependent shape
(record D1) there is no global round index; a challenge node, reached by a public prefix, is the
right index, and record D1 guarantees that the set of challenge nodes does not depend on challenge
values. Legacy `StateFunction` (`RoundByRound.lean:188`, laws `toFun_empty`, `toFun_next`,
`toFun_full`) supplies the three laws above, restated over tree prefixes.

Admissibility is currently owned by the frozen `Oracle/Claim.lean` and is tree-independent
mathematics; ConstraintSystem and Spartan clients need it without importing the interaction
layer, hence the neutral owner.

## Alternatives considered

- **Errors indexed by round.** No round index exists for message-dependent trees.
- **Transfer by terminal distribution equality only.** Insufficient for soundness over arbitrary
  adversaries, knowledge, and round-by-round notions.

## Consequences

- Existing legacy security theorems are reference material; new claims are not proved by
  importing frozen-layer theorems.
- PR D ports the existing measured assertions (knowledge composition, measured resources, state
  restoration and its budget) with their concrete game, replay and budget checks. Broader
  extractor-cost and state-restoration theory is later work.

**Acceptance tests.** In A: core examples of each notion. In B: adversarial and rejection clients,
including effects at an empty protocol's terminal boundary. In C: a bad round followed by good
rounds still runs every round and rejects.

## Open points

None.
