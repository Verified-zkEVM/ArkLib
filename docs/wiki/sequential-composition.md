# Sequential composition contracts

Binary composition lives in `ArkLib/OracleReduction/Composition/Sequential/Append/`.
The `Append.lean` umbrella exports both proved interfaces and legacy admitted interfaces.
Import a specific module when auditing its dependency boundary.

## Execution and simulation

`Prover.append_run_of_seam` factors raw execution when the left prover has `OutputIsPure`,
or the right protocol starts with a prover message. An empty right protocol needs no restriction
on left output. Later challenges are permitted in the message-opening case.
`Prover.append_run` supplies the pure-output convenience form.

`ProtocolSpec.liftAppendLeft` and `liftAppendRight` pin the challenge routes explicitly, including
when component specifications coincide. `Append/Simulation.lean` proves that both inclusions
preserve simulation, with all shared effects and final oracle state retained.

## Completeness

The underlying interface is `Reduction.append_completeness_of_proverFactorization`. It requires:

- Pure verifier forms for both components: deterministic, non-failing verdicts.
- `Prover.SimulatedAppendFactorization`: equality of the simulated prover programs for every
  input statement, witness, and deterministic starting state.
- First-stage completeness for the chosen initial distribution.
- Second-stage completeness from every deterministic shared oracle state.

The factorization equality retains the transcript, output statement and witness, and final state.
It is equality of `ProbComp` programs after simulation and `StateT.run`, not merely equality of
probability distributions. The suffix receives the state left by the prefix. The proof retains
intermediate prover/verifier statement agreement on the successful event.

The resulting error is the sum of the component errors. The perfect-completeness wrapper
`append_perfectCompleteness_of_proverFactorization` accepts suffix correctness from every initial
state distribution; specializing to `pure s` supplies the deterministic-state premise. Conversely,
`completeness_of_pure_states` lifts deterministic-state correctness to arbitrary mixtures.

The seam-based `append_completeness_of_pure_verifiers` derives factorization from the structural
execution theorem. Its `_of_pure` convenience form uses purity typeclasses; perfect-completeness
corollaries set both errors to zero. The oracle-reduction wrappers use the converted ordinary
verifiers and the proved `append_toReduction` equality.

For deterministic verifiers that may reject, use
`append_completeness_of_guarded_proverFactorization` or its seam corollary
`append_completeness_of_guarded_verifiers` in `Sequential/GuardedCompleteness.lean`.
Supply `Verifier.GuardedForm` data. The success event requires both checks to pass, so rejection
contributes failed mass. This module stays outside the `Append.lean` umbrella to avoid an import
cycle through guarded-verifier infrastructure.

`Append/OneMessage.lean` provides `ProtocolSpec.oneMessage` and the short
`append_perfectCompleteness_of_oneMessage` specialization. Component provers may query oracles
in their outputs; pure verifier forms and state-uniform suffix completeness remain required.

`Sequential/Completeness.lean` provides `seqCompose_completeness_of_pure` and its perfect
corollary. Every component has pure output and verdict, and is complete from every deterministic
state. The total error is the sum of component errors.

`Sequential/GuardedNary.lean` provides `seqCompose_completeness_of_guarded_verifiers`
and its perfect-completeness corollary. Every component has pure output, a guarded verifier form,
and completeness from every deterministic state. Rejection remains part of the failure event;
the total error is the sum of the component errors. `Sequential/OracleCompleteness.lean` exports
binary and finite-chain guarded wrappers for oracle reductions using their proved conversions.

For empty ambient oracles, `Sequential/NoAmbient.lean` derives `Prover.OutputIsPure` by structural
elimination of impossible queries. `Verifier.GuardedForm.of_empty` additionally requires an explicit
input-to-output fallback map for rejecting executions. This premise avoids imposing an inhabitance
assumption on arbitrary statement or oracle families. An always-rejecting verifier from `Unit` to
`Empty` has no guarded form. `LiftContext/Purity.lean` preserves output purity and guarded forms
under context lifting without additional lens laws or assumptions about oracle state.

## Round-by-round soundness

`Verifier.append_rbrSoundnessWorstCase_of_pure_first` composes fixed-prefix
`rbrSoundnessWorstCase` contracts under a pure first verifier. Each round keeps its component
error. The second-component proof fixes the intermediate statement and transcript prefix before
sampling its challenge, and proves that statement lies outside the second language when a bad
transition is possible.

`append_rbrSoundness_of_worstCase_of_pure_first` derives the prover-averaged contract from those
stronger hypotheses. It does not prove composition from prover-averaged component bounds alone.
The legacy implication from round-by-round soundness to ordinary soundness remains admitted.

## Counterexamples and trust boundary

`ArkLibTest/OracleReduction/Composition/Sequential/` contains two complementary counterexamples.
`RawExecutionCounterexample.lean` distinguishes raw query order at a challenge-opening seam.
`SharedStateCounterexample.lean` refutes fixed-initial-state completeness composition, even with
pure verifiers and pure left output. `SimulatedFactorization.lean` uses the raw counterexample's
provers with a pure ambient implementation: raw programs differ, yet simulated programs agree
and the factorization completeness theorem applies outside the structural seam restriction.

The eight fixed-init completeness declarations have been removed: `append_completeness`,
`append_perfectCompleteness`, `seqCompose_completeness`, and `seqCompose_perfectCompleteness`
in both `Reduction` and `OracleReduction`. The maintained Sumcheck, Packing, and Binius callers
use the proved guarded interfaces without changing their public hypotheses or protocol definitions.
Their independent component admissions remain: removing the false composition contracts does not
make these callers axiom-clean. The unused experimental Sumcheck completeness claim is also removed.

Generic soundness and knowledge-soundness admissions and their inherited wrappers remain in the
legacy API. They require separate proofs; execution factorization supplies neither claim.

## Hachi caller migration

The nonrecursive Hachi chain uses the proved composition interfaces: pure verifier forms for the
prefix, guarded forms for sumcheck, and state-uniform completeness for each suffix. Nine composed
completeness/correctness declarations, through `hachiNonrecursiveConcrete_perfectCorrectness`,
have standard-only axiom dependencies. The permanent Hachi test also checks the seven added
verifier/output certificates and the two supported-profile relation-coupling theorems.

The public theorem hypotheses and protocol definitions are preserved, including `hInit`/`hKeygen`,
`relPolyEvalMsgShort`, the commitment-input adapter, independent folded-witness width `τ`, and the
bounded decomposition. Recursive opening and general security composition remain separate work.
The default runtime gate covers the supported `τ = 1 < δ = 2` profile and decomposition checks;
it does not execute the expensive complete opening run.

## Validation

Run `./scripts/validate.sh --axioms`. The normal `lake test` gate includes the composition tests:
execution routes, both counterexamples, the positive simulated-factorization case, empty and
state-mutating completeness, rejecting verifiers, specialization checks, and the empty-oracle
fallback boundary. `RetiredCompleteness.lean` checks that all eight retired declaration names
are absent from the imported environment. Named proved results have permanent standard-axiom
assertions. The library axiom sweep covers the production declarations and remaining admission debt.
