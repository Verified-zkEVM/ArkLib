# Legacy sequential composition

This page covers `ArkLib/OracleReduction/`, the legacy layer. For composition in the interaction
layer, read the [current results](../design/00-current-status.md) and
[composition design](../design/02-oracle-reduction-core.md#5-composition). The
[roadmap](../design/05-roadmap.md) tracks the remaining interaction-layer oracle and runtime
theorems.

Sequential composition uses `Prover.append`, `Verifier.append`, and `Reduction.append` in
`ArkLib/OracleReduction/Composition/Sequential/Append/`. Oracle reductions have corresponding
operations. Import the module containing the theorem you need; `Append.lean` is the binary umbrella.

## Execution

`Prover.append_run_of_seam` factors raw prover execution under any of these conditions:

- The left prover has `Prover.OutputIsPure`.
- The right protocol starts with a prover message; later challenges are allowed.
- The right protocol is empty.

`Prover.append_run` is the pure-output specialization for arbitrary suffix protocols.
`ProtocolSpec.liftAppendLeft` and `liftAppendRight` distinguish the two challenge routes, including
when the component specifications coincide. `Append/Simulation.lean` transports these routes
through simulation and retains the final shared oracle state.

## Choosing a completeness theorem

All completeness theorems below require suffix correctness at every deterministic shared oracle
state. A suffix starts in the state left by the prefix, so correctness only at the original
initial distribution is insufficient. Component errors add, and the perfect-completeness
corollaries set those errors to zero.

| Verifiers and prover execution | Binary theorem in namespace `Reduction` |
| --- | --- |
| Pure verifier forms; exact simulated prover factorization | `append_completeness_of_prover_factorization` |
| Pure verifier forms; one of the execution conditions above | `append_completeness_of_pure_verifiers` |
| Pure verifiers and pure left output, supplied by typeclasses | `append_completeness_of_pure` |
| Guarded verifier forms; exact simulated prover factorization | `append_completeness_of_guarded_prover_factorization` |
| Guarded verifier forms; one of the execution conditions above | `append_completeness_of_guarded_verifiers` |

Pure verifier forms describe deterministic verifiers that do not reject. A
`Verifier.GuardedForm` describes a deterministic verifier with an explicit acceptance check;
rejection contributes to the completeness error. The form itself is defined in
`Security/Guarded.lean`; the guarded completeness theorems live in
`Sequential/GuardedCompleteness.lean`, imported separately from the binary umbrella.

`Prover.SimulatedAppendFactorization` equates the simulated prover programs for every input
statement, witness, and deterministic initial state. The equality is between `ProbComp` programs
after `StateT.run`, including transcript, output statement, witness, and final state. It can hold
even when raw execution does not factor. The completeness proof also checks agreement between
the prover's and verifier's intermediate statements.

`completeness_of_pure_states` lifts correctness from deterministic states to arbitrary initial
distributions. The factorization-based perfect-completeness wrapper accepts suffix correctness
from every initial distribution and specializes it to `pure s`.

`Append/OneMessage.lean` supplies `append_perfectCompleteness_of_oneMessage` for two one-message
protocols with pure verifiers, allowing effectful prover outputs. `Sequential/Completeness.lean`
supplies `seqCompose_completeness_of_pure` for finite chains with pure prover outputs and verifiers,
requiring each component to be complete from every deterministic state.
The ordinary pure-verifier binary theorems have oracle-reduction wrappers in
`Append/Completeness.lean`, using `OracleReduction.append_toReduction`.

For guarded finite chains, import `Sequential/GuardedNary.lean` and use
`seqCompose_completeness_of_guarded_verifiers`. Each component must have pure prover output,
a guarded verifier form, and completeness from every deterministic state.
`Sequential/OracleCompleteness.lean` supplies the binary and finite-chain oracle-reduction wrappers.

With an empty ambient oracle, `Sequential/NoAmbient.lean` derives pure prover output by
eliminating impossible queries. `Verifier.GuardedForm.ofEmpty` constructs a verifier form from
an explicit fallback map `StmtIn → StmtOut`, used only on rejection. The map avoids imposing
inhabitedness on arbitrary output oracle families; an always-rejecting verifier from `Unit` to
`Empty` has no such form. `LiftContext/Purity.lean` transports output purity and guarded forms
through ordinary context lifting.

## Ordinary soundness

`Append/Security.lean` proves `append_soundness` for a guarded first verifier and
`General.lean` proves `seqCompose_soundness` for guarded chains. Both soundness interfaces
use `IsGuarded` instances. The second-stage bound must hold from every fixed oracle state:
the intermediate statement is chosen adaptively after oracle answers. This rules out states
hiding a trapdoor or an eagerly sampled random function from the prover; lazy sampling supports
this contract. The first binary bound may use the original initialization distribution.

The `append_knowledgeSoundnessWith` and `seqCompose_knowledgeSoundnessWith` interfaces compose
pure transcript-and-output extractors (`ofTranscriptAndOutput`), retaining explicit guarded
forms to define the composed extractor. Their existential counterparts have the same restriction.
The suffix extractor is fixed uniformly over starting states. All errors add without changing
the component bounds.

`Append/ProverSplit.lean` restricts arbitrary adversaries at the seam.
`Append/OrdinaryComposition.lean` supplies prefix extraction and its bad-event bound, along
with `OracleComp.prEvent_bind_split_le`. `Append/NoAmbient.lean` specializes these results to
empty ambient oracles, where both bounds can use one initialization. Its soundness theorem
requires no fallback, including when the intermediate statement type is empty.
`ArkLibTest/OracleReduction/Composition/Sequential/OrdinaryComposition.lean` checks these APIs,
extractor execution, exact axiom dependencies, and a suffix that queries a shared counter.

## Round-by-round soundness

`Verifier.append_rbrSoundness_of_pure_first` composes bounds that hold for each fixed
transcript prefix, under a pure first verifier. Each round retains its component error.

For knowledge soundness, `Verifier.append_rbrKnowledgeSoundnessWith_of_guarded_first`
(`Append/GuardedRoundByRound.lean`) composes round-by-round component bounds under a *guarded* first
verifier (`Verifier.GuardedForm`), at the composed extractor `Extractor.RoundByRound.append` and
the knowledge state function `KnowledgeStateFunction.appendGuarded`. The components share only
the intermediate relation. `append_rbrKnowledgeSoundness_of_guarded_first` is the
existential form. `Sequential/GuardedRoundByRound.lean` gives the finite-chain form
`seqCompose_rbrKnowledgeSoundness_of_guarded`. Each has an `OracleVerifier` wrapper. Over an empty
ambient oracle `Verifier.GuardedForm.ofEmpty` supplies
the guarded form of any verifier. A named form is preferable where one exists, since the first
factor's verdict map enters the composed extractor. For oracle verifiers,
`OracleVerifier.appendGuardedForm` and `OracleVerifier.seqComposeGuardedForm`
(`Sequential/GuardedNary.lean`) build the composite's guarded form from the components', and
`OracleVerifier.castIdxGuardedForm` (`OracleReduction/CastIdx.lean`) moves one along an index cast;
Binary Basefold's core interaction composes all its rounds this way.

`Security/GuardedBridges.lean` derives ordinary knowledge
soundness from a guarded verifier's round-by-round knowledge guarantee, with the sum of the
per-challenge errors. Sumcheck, Packing, Binary Basefold, Spartan and Plonk use the proved
completeness interfaces above. Each client supplies its own component and honest-oracle premises.
Binary Basefold's `General.lean` composes its actual core and query through the proved guarded
completeness and RBR interfaces. Its completeness premise is strict honest encoding;
its RBR guarantee uses the relaxed relation. `ArkLibTest/ProofSystem/Binius/BinaryBasefold/General.lean`
checks an inhabited full initial premise, sampled acceptance and the actual append boundary.

## Clients and validation

Hachi's nonrecursive chain uses pure verifier forms for its prefix and guarded forms for
sumcheck. `Hachi/HonestChain.lean` contains the prefix certificates; `Hachi/Correctness.lean`
composes the commitment-input adapter, chain, and terminal check. Its folded-witness width `τ`
and bounded decomposition are parameters of these certificates.

Spartan composes its seven stages with `OracleReduction.seqCompose` and
`OracleVerifier.seqComposeGuardedForm` (`ProofSystem/Spartan/Protocol.lean`).
`Spartan.perfectCompleteness` is perfect completeness for the original R1CS relation, and
`Spartan.knowledgeSoundness` gives ordinary knowledge soundness with error
`Spartan.totalError ℓ_m ℓ_n |R| = (4 * ℓ_m + 2 * ℓ_n + 1) / |R|`, where `ℓ_m` and `ℓ_n` count the
row and column variables, through the guarded bridge.

Plonk composes its four stages the same way (`ProofSystem/Plonk/Assembly/Reduction.lean`).
`Plonk.Assembly.oracleReduction_completeness` has completeness error `3n / |F|`, and
`Plonk.Assembly.oracleVerifier_knowledgeSoundnessWith` has knowledge error `(7n - 3) / |F|` with the
designated table extractor. `Plonk.Assembly.Circuit.oracleVerifier_knowledgeSoundnessWith` extracts
the original circuit witness with error `(7(ℓ + n) - 3) / |F|`.

Binius derives ordinary knowledge soundness from its guarded round-by-round results:
`Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_knowledgeSoundness` for Binary
Basefold, and `Binius.FRIBinius.RingSwitch.fullVerifier_knowledgeSoundness` for the ring switch
followed by Binary Basefold (see [ring-switching consumers](ring-switching-consumers.md)).

Run `./scripts/validate.sh --axioms` for the library, compile-time tests, runtime checks, and
axiom regression gate. `ArkLibTest/OracleReduction/Composition/Sequential/` covers challenge
routing, rejecting verifiers, raw query-order failure, and the need for suffix correctness at
the state left by the prefix. It also contains a simulated factorization example outside the
raw execution conditions. `RetiredCompleteness.lean` checks that the unsupported fixed-initial-state
completeness names are absent. Hachi's tests check its composed theorem dependencies; the default
runtime exercises bounded decomposition but does not execute the expensive complete opening run.
