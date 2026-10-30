# Limitations of the legacy layer

ArkLib has two layers for interactive oracle reductions: the legacy layer
([`ArkLib/OracleReduction/`](../../ArkLib/OracleReduction/)) and the interaction layer
([`ArkLib/Interaction/`](../../ArkLib/Interaction/)), which is meant to replace it. The legacy
layer is sorry-free and carries the formalized protocols, but its representation has limits that
the interaction layer removes. This page lists them, each with the source that shows it and what
the interaction layer does instead.

For what each layer has formalized, read the [roadmap](../../ROADMAP.md) and the
[current status](00-current-status.md). The [roadmap](../../ROADMAP.md#priority-replace-the-legacy-layer)
also holds the migration plan.

## The limitations

- **The protocol shape is fixed in advance.** A protocol is a `ProtocolSpec n`: `n`
  message/challenge steps, with the direction and the type of each step given as functions of the
  step index only. The number of steps, who speaks, and the message and challenge types cannot
  depend on earlier messages or challenges, so dependent protocols cannot be expressed directly.
  In the interaction layer a protocol is a PolyFun `Interaction.TypeTree`, and the rest of the
  tree, including its roles, may depend on the path so far. `Reduction.then`
  (`Interaction/Reduction.lean`) appends a second reduction whose tree depends on the complete
  first path. For oracle protocols, `Interaction.Oracle.TypeTree` permits structural dependence
  on the public `BranchPath`; concrete oracle messages remain in the `ExecutionPath` but do not
  directly select the next branch. Oracle composition uses this public-path restriction.
- **Provers are round-indexed state machines.** A legacy prover has one state type per round
  (`PrvState : Fin (n + 1) → Type`) and round-indexed `sendMessage` and `receiveChallenge`
  functions. Composing two provers concatenates their state families with `Fin.append` and moves
  states between them with dependent casts (`dcast`, in `Composition/Sequential/Append/Basic.lean`);
  reductions over protocol specs that are equal but not definitionally equal are related by the
  cast lemmas in `OracleReduction/Cast.lean` and `ProtocolSpec/Cast.lean`. In the interaction layer
  a prover is a strategy on the tree (`Interaction.Oracle.Prover.Strategy`) whose continuation
  keeps its private memory, and composition avoids concatenating round-indexed prover-state
  families; dependent transports still occur in oracle composition. The legacy receiver's
  effectful computation returns a pure challenge-to-state function, so challenge-dependent
  effects must be deferred to a later action. Interaction-layer receiver continuations can
  perform effects depending on the received move immediately.
- **The verifier acts only after the interaction.** A legacy verifier is one function of the full
  transcript (`Verifier.verify`), and each challenge is sampled uniformly from its type by the
  execution (`ProtocolSpec.challengeQueryImpl`). The verifier cannot stop the protocol early. In
  the interaction layer the verifier is a strategy that acts at each of its nodes; for example, the
  Sum-check verifier can reject publicly in any round instead of sending a challenge.
- **Oracles are concrete data.** The security of an oracle verifier is defined through
  `OracleVerifier.toVerifier`, which receives the oracle statements and the prover's messages in
  the clear, and relations range over these values. Every output oracle must therefore have a
  concrete value (`materializeOutput`), even when the verifier defines it only through queries to
  other oracles. The interaction layer separates an oracle's query program from its behavior: a
  reduction returns an open claim whose oracles are query programs over the available sources
  (`Interaction/Oracle/Claim.lean`, `Interaction/Oracle/Virtual.lean`), relations consume the
  behavior of the closed claim, and the next stage queries only an exported interface
  (`Verifier.appendExported`, in `Interaction/Oracle/SourceRouting.lean`).
- **The default verifier result has one explicit failure case.** A legacy verifier returns
  `OptionT`, whose `none` does not distinguish rejection from different reported faults. Missing
  probability mass in the underlying computation is a separate phenomenon. The interaction layer
  provides an explicit `Terminal` result with accept, reject and named fault cases
  (`Interaction/Oracle/Terminal.lean`) through `executeTerminal`
  (`Interaction/Oracle/TerminalRun.lean`); its core optional-claim API remains available.
  `Terminal.observe` (`Interaction/Oracle/TerminalMeasure.lean`) assigns missing runtime mass to
  a caller-named fault while preserving acceptance and rejection probabilities.
- **Composition needs a bound from every oracle state.** A legacy security game draws the shared
  oracle state from an initialization and discards the final state. In a composed protocol the
  second reduction starts from whatever state the first leaves, which its own game does not cover.
  Sequential composition of soundness (`Verifier.append_soundness`) therefore needs a guarded
  first verifier and a second-stage bound that holds from every fixed oracle state. This premise
  cannot justify a second-stage bound that relies on the prover not knowing the sampled oracle
  state, for example a hidden trapdoor or an eagerly sampled random function. The interaction
  layer runs setup and every stage inside one persistent runtime
  (`Interaction/Oracle/Runtime.lean`) and proves composition from a suffix bound averaged over
  the actual distribution of the prefix, for the fixed prover
  (`executeStrategiesWithRuntime_appendExported_soundness`, in
  `Interaction/Oracle/RuntimeSoundness.lean`). The client of that theorem must prove the averaged
  suffix bound.
