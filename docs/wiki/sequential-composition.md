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

## Round-by-round soundness

`Verifier.append_rbrSoundnessWorstCase_of_pure_first` composes bounds that hold for each fixed
transcript prefix, under a pure first verifier. Each round retains its component error.
`append_rbrSoundness_of_worst_case_of_pure_first` derives the prover-averaged conclusion from
these hypotheses. Prover-averaged component bounds alone do not supply this contract.

Generic soundness composition and the implication from round-by-round to ordinary soundness
remain admitted. Legacy Sumcheck, Packing, and Binius clients use the proved completeness
interfaces above but retain separate component and context-lifting admissions. The generic
`Packing/Tail/` pipelines have proved completeness and round-by-round knowledge contracts
under their explicit commitment and challenge hypotheses.

## Round-by-round knowledge soundness

Import `Append/Knowledge.lean` explicitly. It cannot be exported by `Append.lean` while the
canonical `GuardedForm` owner transitively imports that umbrella.

`KnowledgeStateFunction.appendGuarded` constructs the knowledge state for the existing
`Extractor.RoundByRound.append`. The first verifier must have `GuardedForm`; the second may
perform arbitrary shared-oracle queries. The state retains the first component through the seam
and carries its guard in every state strictly after the seam. A first right-hand transition runs
the actual left output extractor on the witness supplied by the right predecessor state.

`append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first` preserves the exact component
extractors and knowledge states. Each challenge retains its component error, with the existential
successor witness inside the sampled event, so it may depend on the challenge. Both protocol
lengths may be zero. The `_With`
averaged wrapper preserves these objects; the existential wrappers hide them. The oracle-verifier
wrapper uses actual oracle materialization through `append_toVerifier`.

Both component hypotheses are **worst-case per prefix**. Averaged wrappers retain these premises;
commitment, sumcheck and opening obligations belong to the component proofs.

For finite guarded chains, import `Sequential/KnowledgeNary.lean`.
`Verifier.KnowledgeSeqCompose` exposes the recursive `Witness`, `extractor`, `state` and `error`
used by `seqCompose_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_verifiers`. Every component
supplies its own exact extractor, knowledge state, guarded form and worst-case bound. The empty
sequence uses identity extraction; successor steps use the proved guarded append theorem.
`error_component` and `error_eq_sigma` identify each challenge with the existing public
component-and-local-challenge decoder. The averaged wrapper preserves the same objects.

The unrestricted knowledge-composition theorem remains admitted. A final verifier with arbitrary
effects can use the binary guarded-first theorem.

## Clients and validation

Hachi's nonrecursive chain uses pure verifier forms for its prefix and guarded forms for
sumcheck. `Hachi/HonestChain.lean` contains the prefix certificates; `Hachi/Correctness.lean`
composes the commitment-input adapter, chain, and terminal check. Its folded-witness width `τ`
and bounded decomposition are parameters of these certificates.

Run `./scripts/validate.sh --axioms` for the library, compile-time tests, runtime checks and
axiom regression gate. `ArkLibTest/OracleReduction/Composition/Sequential/` covers challenge
routing, rejection, stateful suffixes and simulated factorization. Hachi's tests check its composed
theorem dependencies; its default runtime exercises bounded decomposition.
