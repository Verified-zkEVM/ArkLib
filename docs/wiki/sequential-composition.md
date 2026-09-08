# Sequential composition

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
rejection contributes to the completeness error. Guarded theorems live in
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

## Round-by-round soundness

`Verifier.append_rbrSoundnessWorstCase_of_pure_first` composes bounds that hold for each fixed
transcript prefix, under a pure first verifier. Each round retains its component error.
`append_rbrSoundness_of_worst_case_of_pure_first` derives the prover-averaged conclusion from
these hypotheses. Prover-averaged component bounds alone do not supply this contract.

The fixed-initial-state completeness declarations in `Append/Security.lean` and
`Sequential/General.lean` are false and remain admitted; use the proved completeness interfaces
above. Generic soundness composition and the implication from round-by-round to ordinary
soundness remain admitted.

## Clients and validation

Hachi's nonrecursive chain uses pure verifier forms for its prefix and guarded forms for
sumcheck. `Hachi/HonestChain.lean` contains the prefix certificates; `Hachi/Correctness.lean`
composes the commitment-input adapter, chain, and terminal check. Its folded-witness width `τ`
and bounded decomposition are parameters of these certificates.

Run `./scripts/validate.sh --axioms` for the library, compile-time tests, runtime checks, and
axiom regression gate. `ArkLibTest/OracleReduction/Composition/Sequential/` covers challenge
routing, rejecting verifiers, raw query-order failure, and the need for suffix correctness at
the state left by the prefix. It also contains a simulated factorization example outside the
raw execution conditions. Hachi's tests check its composed theorem dependencies; the default
runtime exercises bounded decomposition but does not execute the expensive complete opening run.
