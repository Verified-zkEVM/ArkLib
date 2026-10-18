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

### Simplifying component guarded-verifier proofs

`ArkLib.ToVCVio.Simulation.Basic` provides `vcv_guard [run_eq] at h` for a
positive-probability hypothesis about a deterministic guarded verifier. Supply an equation
identifying its run as `if check then pure output else failure`; the tactic replaces the
hypothesis with `check ∧ R output`. It preserves the guard and leaves the mathematical
relation `R` opaque. It does not unfold protocol definitions or prove relation implications.

The supporting lemmas are `OptionT.mem_support_simulateQ_run'_guarded_iff` and
`OptionT.prEvent_simulateQ_run'_guarded_pos_iff`. They work for arbitrary initial `ProbComp`
states and stateful handlers because the normalized computation makes no oracle queries.
Use the existing `Verifier.GuardedForm` certificates for composition; this tactic is only
component-level proof plumbing, not a replacement completeness interface.

### Composition interfaces

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

Unrestricted ordinary-soundness composition and the corresponding RBR-to-ordinary-soundness
implication remain admitted. This is distinct from the proved knowledge-soundness interfaces
below. Binius and RingSwitching's packing results use proved completeness and context-lifting
interfaces; the legacy simple-Sumcheck completeness proofs still have separate lens obligations.

## Round-by-round knowledge soundness

`Verifier.rbrKnowledgeSoundness` bounds the bad transition at every fixed transcript prefix,
over only the fresh challenge. `rbrKnowledgeSoundnessAveraged` instead averages over the prefix
generated by an arbitrary prover. The former implies the latter with the same error; an
averaged certificate must not be silently used as a fixed-prefix certificate.
`IsRBRKnowledgeSoundAveraged` names the legacy `IsRBRKnowledgeSound` class without changing
its instances. `IsRBRKnowledgeSoundFixedPrefix` packages the stronger contract separately.

The following theorems retain the original per-component, per-round error bounds.
Names in this table are in namespace `Verifier`.

| Available component certificates | Composition theorem and additional conditions |
| --- | --- |
| Both fixed-prefix | `append_rbrKnowledgeSoundness_of_guarded_first`: guarded first verifier; arbitrary second verifier |
| Finite fixed-prefix chain | `seqCompose_rbrKnowledgeSoundness_of_guarded`: every component guarded |
| Guarded fixed-prefix chain followed by an arbitrary fixed-prefix tail | `seqCompose_append_rbrKnowledgeSoundness_of_guarded_prefix`: only the prefix must be guarded |
| Fixed-prefix first, averaged second | `append_rbrKnowledgeSoundnessAveraged_stateless`: stateless ambient implementation, guarded first verifier, inhabited intermediate witness type |
| Both averaged | `append_rbrKnowledgeSoundnessAveraged_of_averaged_stateless`: the same conditions and an inhabited intermediate statement type |
| Stateful implementations of guarded references | `append_rbrKnowledgeSoundness_of_acceptingRefinement` and its sequential counterpart: prove accepting refinement at every shared state |

The guarded append theorem is in `Append/KnowledgeState.lean`; finite composition is in
`Sequential/GuardedKnowledge.lean`. The stateless theorems are in `Append/AveragedStateless.lean`.
The historical empty-oracle wrapper remains in `Append/AveragedEmpty.lean`.
Stateless answers may be freshly randomized and the query specification need not be empty.
They cannot depend on a persistent shared-state table: a lazy random oracle is not covered by
the stateless theorem without a separate justification.

`Sequential/StatefulKnowledge.lean` supplies accepting refinement. Every accepted output must
agree with a guarded reference's output and satisfy its check. The actual verifier may mutate
state or reject with a different probability; this transfers knowledge soundness, not
completeness. It is not an unrestricted composition theorem for state-dependent outputs.

### Converting RBR knowledge soundness to plain knowledge soundness

Import `Security/ActualExtraction.lean`. The terminal knowledge condition must hold at the
state in which the verifier actually starts, including effects of an adversarial prover's
output action. A certificate only about fresh initialization is insufficient.

Use `rbrKnowledgeSoundnessAveraged_implies_knowledgeSoundness_of_guarded` for a guarded verifier.
For state-dependent outputs, use the exact-certificate theorem
`rbrKnowledgeSoundnessAveragedWith_implies_knowledgeSoundnessWith_of_reachable`, or its
`_of_invariant` wrapper. The invariant must cover states reached by every adversarial prover,
not merely honest execution. These results preserve the total error $\sum_i \varepsilon_i$.
An invariant-based extraction theorem does not by itself prove shared-state composition.

## Clients and validation

Hachi's nonrecursive chain uses pure verifier forms for its prefix and guarded forms for
sumcheck. `Hachi/HonestChain.lean` contains the prefix certificates; `Hachi/Correctness.lean`
composes the commitment-input adapter, chain, and terminal check. Its folded-witness width `τ`
and bounded decomposition are parameters of these certificates.

Run `./scripts/validate.sh --axioms` for the library, compile-time tests, runtime checks, and
axiom regression gate. `ArkLibTest/OracleReduction/Composition/Sequential/` covers challenge
routing, rejecting verifiers, raw query-order failure, and the need for suffix correctness at
the state left by the prefix. It also contains a simulated factorization example outside the
raw execution conditions. `RetiredCompleteness.lean` checks that the unsupported fixed-initial-state
completeness names are absent. Hachi's tests check its composed theorem dependencies; the default
runtime exercises bounded decomposition but does not execute the expensive complete opening run.

The knowledge-soundness tests also check shared-state counterexamples, nonempty stateless
ambient oracles, accepting refinements that mutate state, and the historical Binius and
RingSwitching theorem interfaces. Their axiom checks exclude admissions in the repaired
proofs; they do not claim that every unrelated theorem in OracleReduction is admission-free.
