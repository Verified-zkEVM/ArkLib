# Limitations of the legacy layer

ArkLib has two layers for interactive oracle reductions: the legacy layer
([`ArkLib/OracleReduction/`](../../ArkLib/OracleReduction/)) and the interaction layer
([`ArkLib/Interaction/Core/`](../../ArkLib/Interaction/Core/)), which is meant to replace it. The legacy
layer is sorry-free and carries the formalized protocols, but its representation has limits that
the interaction layer removes. This page lists them, each with the source that shows it and what
the interaction layer does instead. One limitation, a verifier that acts only after the
interaction, remains in the interaction core, which uses passive verifiers.

For what each layer has formalized, read the [roadmap](../../ROADMAP.md) and the
[current status](00-current-status.md). The [roadmap](../../ROADMAP.md#priority-replace-the-legacy-layer)
also holds the migration plan.

## The limitations

- **The protocol shape is fixed in advance.** A protocol is a `ProtocolSpec n`: `n`
  message/challenge steps, with the direction and the type of each step given as functions of the
  step index only. The number of steps, who speaks, and the message and challenge types cannot
  depend on earlier messages or challenges, so dependent protocols cannot be expressed directly.
  In the interaction layer a protocol is a PolyFun free-monad tree
  (`Interaction/Core/Protocol.lean`), and the rest of the tree, including its roles, may depend
  on the public messages so far. Challenges and oracle messages are recorded in the full
  transcript but have a single continuation, so they do not select the next branch
  (`Interaction/Core/Signature.lean`). Sequential composition (`Interaction/Core/Composition.lean`)
  appends a suffix that may depend on the prefix path.
- **Provers are round-indexed state machines.** A legacy prover has one state type per round
  (`PrvState : Fin (n + 1) → Type`) and round-indexed `sendMessage` and `receiveChallenge`
  functions. Composing two provers concatenates their state families with `Fin.append` and moves
  states between them with dependent casts (`dcast`, in `Composition/Sequential/Append/Basic.lean`);
  reductions over protocol specs that are equal but not definitionally equal are related by the
  cast lemmas in `OracleReduction/Cast.lean` and `ProtocolSpec/Cast.lean`. In the interaction layer
  a prover is a PolyFun focal strategy on the tree (`Prover`, in `Interaction/Core/Reduction.lean`)
  whose continuation keeps its private memory, and composition avoids concatenating round-indexed
  prover-state families. The legacy receiver's effectful computation returns a pure
  challenge-to-state function, so challenge-dependent effects must be deferred to a later action.
  An interaction-layer prover has an effect slot at every boundary, so it can perform effects
  depending on a received challenge immediately.
- **The verifier acts only after the interaction.** A legacy verifier is one function of the full
  transcript (`Verifier.verify`), and each challenge is sampled uniformly from its type by the
  execution (`ProtocolSpec.challengeQueryImpl`). The verifier cannot stop the protocol early. The
  interaction core keeps this limitation: its verifiers are passive. A sampler draws each
  challenge, and the verifier decides once, from the completed transcript
  (`Interaction/Core/Reduction.lean`, `Interaction/Core/OracleVerifier.lean`). The challenge draws
  may still depend on the earlier public messages and challenges. The deleted generic layer let
  the verifier act at each of its nodes; the
  [migration list](interaction-layer/migration-list.md) records which of its results needed the
  passive premise.
- **Oracles are concrete data.** The security of an oracle verifier is defined through
  `OracleVerifier.toVerifier`, which receives the oracle statements and the prover's messages in
  the clear, and relations range over these values. Every output oracle must therefore have a
  concrete value (`materializeOutput`), even when the verifier defines it only through queries to
  other oracles. In the interaction layer an oracle verifier's decision sees its input oracles and
  the oracle messages only through queries, and its output is an `OracleMap`
  (`Interaction/Core/OracleVerifier.lean`): concrete output data, a simulation of each output query
  by input queries, and a law that the two agree. The next stage of a composition queries the
  routed bundle (`Interaction/Core/Oracle/Routing.lean`).
- **The default verifier result has one explicit failure case.** A legacy verifier returns
  `OptionT`, whose `none` does not distinguish rejection from different reported faults. Missing
  probability mass in the underlying computation is a separate phenomenon. The interaction core
  also returns an `Option` verdict, but keeps rejection separate from a failure of the ambient
  oracle computation (`Interaction/Core/Execution.lean`).
  `OracleVerifier.decideCatching` (`Interaction/Core/Oracle/LoggedExecution.lean`) runs a decision
  under a handler with labelled failures and keeps the label of a failure apart from rejection.
  The deleted generic layer had a `Terminal` result with named fault cases; the core does not.
- **Composition needs a bound from every oracle state.** A legacy security game draws the shared
  oracle state from an initialization and discards the final state. In a composed protocol the
  second reduction starts from whatever state the first leaves, which its own game does not cover.
  Sequential composition of soundness (`Verifier.append_soundness`) therefore needs a guarded
  first verifier and a second-stage bound that holds from every fixed oracle state. This premise
  cannot justify a second-stage bound that relies on the prover not knowing the sampled oracle
  state, for example a hidden trapdoor or an eagerly sampled random function. The interaction
  layer proves composition from a suffix bound averaged over the actual distribution of the
  boundary, which includes the ambient state the prefix leaves
  (`Verifier.append_soundness_weighted_ae` and `OracleVerifier.append_soundness_weighted_ae`, in
  `Interaction/Core/Security/CompositionSoundness.lean`). Its runtime results
  (`OracleVerifier.append_soundness_runtime`) transport such a bound to a run inside one
  persistent `OracleRuntime`. The client must prove the averaged suffix bound.
