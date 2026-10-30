# Roadmap

This page is ArkLib's public status and direction: what is complete, what is in progress, and where
the library is going. Use [open issues](https://github.com/Verified-zkEVM/ArkLib/issues) for
assignments and [CONTRIBUTING.md](CONTRIBUTING.md) for the development and review process. The
[design roadmap](docs/design/05-roadmap.md) owns the implementation plan for the interaction
layer; this page does not repeat it.

## Priority: replace the legacy layer

ArkLib has two layers: the legacy layer (`ArkLib/OracleReduction/`) and the interaction layer
(`ArkLib/Interaction/`), which is meant to replace it.
[README.md](README.md#two-layers) gives an overview, and
[Limitations of the legacy layer](docs/design/legacy-layer-limitations.md) explains why the
replacement is needed.

The legacy layer is sorry-free and reasonably stable. Every protocol and commitment scheme under
[Complete](#complete) is formalized in it, with sequential composition, context lifting
(`liftContext`, in [`OracleReduction/LiftContext/`](ArkLib/OracleReduction/LiftContext/)) and
the [legacy security notions](#framework). The interaction layer is not yet ready to replace it:
it has generic execution, composition and security theory, and one protocol, Sum-check
([`ProofSystem/Sumcheck/Interaction/`](ArkLib/ProofSystem/Sumcheck/Interaction/)).

Developing the interaction layer is now the project's priority. The migration has three stages.

1. **Feature parity.** Give the interaction layer every framework feature that the legacy
   protocols use. For example, lifting a reduction into a larger context
   (`OracleReduction/LiftContext/`) has no interaction-layer counterpart yet. The
   [design roadmap](docs/design/05-roadmap.md) sequences this work.
2. **Port protocols one at a time, each with a proved equivalence.** For each ported protocol,
   prove a theorem that relates the legacy protocol, embedded into the interaction layer, to the
   interaction-layer protocol, so that the port is checked to be faithful. The single-round
   Sum-check correspondence
   ([`Sumcheck/Interaction/Legacy.lean`](ArkLib/ProofSystem/Sumcheck/Interaction/Legacy.lean)) is
   the first instance. `legacy_input_iff` and `legacy_output_iff` show that the two layers' input
   and output relations agree in both directions, and `legacy_verifier_correspondence` shows that
   the two single-round verifiers return the same output statement for every round message and
   challenge, including rejection. It covers one round and compares the two directly: it does not
   relate the full protocol, the provers or the security games, and no general embedding of the
   legacy layer exists yet. Spartan and Plonk are complete in the legacy layer (below); their
   interaction-layer versions are not yet written.
3. **Delete the legacy layer.** Once the protocols are ported, delete the legacy layer as a whole.

Until the port is complete, ArkLib makes no backward-compatibility guarantees and does not
promise deprecation periods; see the [compatibility policy](CONTRIBUTING.md#compatibility-policy).

## Complete

Every result below is on `main` and depends only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). Theorem names are full Lean names. Each theorem's docstring
states its hypotheses; read them before relying on a result. The interaction-layer status page,
[`docs/design/00-current-status.md`](docs/design/00-current-status.md), records that layer's APIs
and remaining proof gaps in detail.

### Protocols and commitments

The following protocols have formal specifications and the security results listed below.
Executable implementations are available for selected protocols; each entry names them. Unless an
entry says so, the specification is not claimed to be executable.

- **Sum-check** ([`ProofSystem/Sumcheck/`](ArkLib/ProofSystem/Sumcheck/)). In the legacy
  layer: `Sumcheck.Spec.oracleReduction_perfectCompleteness`;
  `Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness`, with error `deg / |R|` per challenge;
  `Sumcheck.Spec.oracleVerifier_knowledgeSoundness`, with the sum of those errors. The reduction
  `Sumcheck.Spec.oracleReduction` is noncomputable; `Sumcheck.Impl.Computable.generalOracleProver`
  computes the same messages and outputs as its honest prover. In the interaction layer
  ([`Sumcheck/Interaction/`](ArkLib/ProofSystem/Sumcheck/Interaction/)):
  `Sumcheck.Interaction.Native.execute_perfectCompleteness`,
  `Sumcheck.Interaction.Native.execute_soundness` and
  `Sumcheck.Interaction.Native.roundByRound_soundness`, with a CompPoly-backed computable honest
  prover, `Sumcheck.Interaction.Computable.honestProver`.
- **FRI** ([`ProofSystem/Fri/`](ArkLib/ProofSystem/Fri/)): perfect and noisy-input completeness,
  soundness, round-by-round soundness, and knowledge soundness for a named straightline
  extractor: `Fri.Spec.perfect_completeness`, `Fri.Spec.soundness` and
  `Fri.Spec.knowledge_soundness_with`. `Fri.Spec.knowledgeSoundnessWithResources_extract`
  ([`Fri/Spec/MeasuredKnowledgeSoundness.lean`](ArkLib/ProofSystem/Fri/Spec/MeasuredKnowledgeSoundness.lean))
  bounds the extractor's operation counts; the
  [extractor-efficiency design](docs/design/03a-extractor-efficiency.md) states what such budgets
  do and do not certify.
- **Batched FRI** ([`ProofSystem/BatchedFri/`](ArkLib/ProofSystem/BatchedFri/)): a batching round
  followed by FRI. `BatchedFri.Spec.batchedFRI_perfectCompleteness`;
  `BatchedFri.Spec.batchedFRI_soundness`, with error the batching error plus the FRI error.
  Instances cover affine-space, power and multilinear generators.
- **Binary Basefold** ([`ProofSystem/Binius/BinaryBasefold/`](ArkLib/ProofSystem/Binius/BinaryBasefold/)):
  perfect completeness, round-by-round knowledge soundness and ordinary knowledge soundness of
  the full protocol, with headline theorem
  `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness_and_knowledgeSoundness`.
  The full oracle reduction is a noncomputable specification.
- **Ring switching** ([`ProofSystem/RingSwitching/`](ArkLib/ProofSystem/RingSwitching/)): shared
  head, product-sumcheck and terminal phases.
  `RingSwitching.Packing.RingSwitch.perfectCompleteness_and_knowledgeSoundness` gives perfect
  completeness and knowledge soundness with error `bat.error + 2m / |C|`. It is instantiated at
  Binius's tensor profile and composed with Binary Basefold as FRI-Binius
  ([`Binius/FRIBinius/`](ArkLib/ProofSystem/Binius/FRIBinius/)):
  `Binius.FRIBinius.RingSwitch.fullReduction_perfectCompleteness_and_knowledgeSoundness` proves
  perfect completeness on exact encodings and ordinary knowledge soundness, obtained from
  round-by-round knowledge soundness through the proved guarded bridge
  `Verifier.GuardedForm.knowledgeSoundness_of_rbrKnowledgeSoundness`. The fused FRI-Binius
  protocol is not yet formalized. The
  [consumer guide](docs/wiki/ring-switching-consumers.md) records the interfaces.
- **Spartan** ([`ProofSystem/Spartan/`](ArkLib/ProofSystem/Spartan/)): a seven-stage oracle
  reduction for R1CS. `Spartan.perfectCompleteness`; `Spartan.knowledgeSoundness`, with error
  `(4s + 2t + 1) / |R|` where `s = Nat.clog 2 m` and `t = Nat.clog 2 (max n_x n_w) + 1`. The
  reduction `Spartan.oracleReduction` and the straightline extractor
  `Spartan.straightlineExtractor` are executable.
- **Plonk** ([`ProofSystem/Plonk/`](ArkLib/ProofSystem/Plonk/)): an end-to-end oracle reduction
  assembled from grand-product, residual-batching and quotient stages.
  `Plonk.Assembly.oracleReduction_completeness`, with failure probability at most `3n / |F|`;
  `Plonk.Assembly.oracleVerifier_knowledgeSoundnessWith`, with error `(7n - 3) / |F|`. The
  reduction `Plonk.Assembly.oracleReduction` is executable.
- **Toy problem** ([`ProofSystem/ToyProblem/`](ArkLib/ProofSystem/ToyProblem/)):
  `ToyProblem.Spec.oracleReduction_perfectCompleteness`;
  `ToyProblem.Spec.oracleVerifier_knowledgeSoundness_winningSetUpperBound`. Executable IRS and FRS
  implementations are in [`ToyProblem/Impl/`](ArkLib/ProofSystem/ToyProblem/Impl/).
- **KZG** ([`Commitments/Functional/KZG/`](ArkLib/Commitments/Functional/KZG/)): correctness, and
  binding stated as reductions: `KZG.CommitmentScheme.binding_reduces_to_tSdh` (evaluation binding
  from t-SDH) and `KZG.CommitmentScheme.function_binding_reduces_to_arsdh` (function binding from
  ARSDH). The hardness-based corollaries quantify over explicit adversary classes.
- **Hachi** ([`Commitments/Functional/Hachi/`](ArkLib/Commitments/Functional/Hachi/)): the
  nonrecursive opening argument, with coordinate-wise special soundness of each iteration
  (`ArkLib.Lattices.Ajtai.InnerOuter.hachi_iteration_coordinateWiseSpecialSoundWithEscape`) and a
  computable honest run. At the formalized parameter profile the inner Module-SIS target is
  trivially solvable, so the weak-binding reduction gives no concrete binding guarantee there
  (`Commitments/Functional/Hachi/Params.lean`).
- **STIR components** ([`ProofSystem/Stir/`](ArkLib/ProofSystem/Stir/)): the proximity gap
  (`STIR.proximity_gap`, Theorem 4.1 of [ACFY24stir]), out-of-domain sampling, quotienting and
  combination. The STIR protocol and its round-by-round soundness theorem are not yet formalized.

### Framework

- **Legacy-layer security theory**
  ([`OracleReduction/Security/`](ArkLib/OracleReduction/Security/)): completeness, soundness,
  knowledge soundness and round-by-round soundness notions; one round-by-round knowledge
  soundness notion under the default names `rbrKnowledgeSoundness` and
  `rbrKnowledgeSoundnessWith`, proved bridges from round-by-round to ordinary knowledge soundness
  for guarded verifiers (`GuardedBridges.lean`), characterizations of unbounded extraction
  (`UnboundedExtraction.lean`) and of when round-by-round soundness and round-by-round knowledge
  soundness coincide (`Implications.lean`), and guarded sequential composition and context
  lifting.
- **Coordinate-wise special soundness** and transcript trees, with computable tree-based
  extractors ([`CoordinateWiseSpecialSoundness/`](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/),
  [`TranscriptTree/`](ArkLib/OracleReduction/Security/TranscriptTree/)).
- **Reusable components** ([`ProofSystem/Component/`](ArkLib/ProofSystem/Component/)), including
  one witness-sending stage shared by Plonk and Spartan (`SendWitness.lean`) and batched quotient
  zero tests.
- **Fiat-Shamir**: the basic transform and its completeness under fixed tables and a lazy random
  oracle ([`OracleReduction/FiatShamir/`](ArkLib/OracleReduction/FiatShamir/)).
- **Interaction layer** ([`ArkLib/Interaction/`](ArkLib/Interaction/)): execution,
  soundness, round-by-round soundness, generic knowledge certificates and their composition, and
  state-restoration knowledge soundness for fixed-round public-coin protocols with error
  `(Q + k) * error`. No concrete protocol consumes the knowledge certificates yet, and randomized
  state restoration is in progress (below). The
  [interaction-layer status page](docs/design/00-current-status.md) has the details.
- **Measured extraction**: measured programs and operation-count budgets
  ([`Data/OracleComp/MeasuredProgram.lean`](ArkLib/Data/OracleComp/MeasuredProgram.lean)), their use
  in knowledge soundness ([`OracleReduction/Security/Resources.lean`](ArkLib/OracleReduction/Security/Resources.lean)),
  and measured stages for interaction-layer knowledge and state-restoration certificates
  (`Interaction/Oracle/Security/{KnowledgeResources,StateRestorationResources}.lean`). The
  [extractor-efficiency design](docs/design/03a-extractor-efficiency.md) states what these budgets
  do and do not certify.
- **Commitment games**: binding and extractability experiments that keep the oracle state left by
  setup ([`Commitments/Functional/Basic.lean`](ArkLib/Commitments/Functional/Basic.lean)).
- **Algebraic group model**: group representations for algebraic adversaries
  ([`ArkLib/AGM/`](ArkLib/AGM/)).

## In progress

- **Solicited proofs.** Five coding-theory declarations, covering lower bounds, separations and a
  random-domain list-size upper bound, are stated faithfully and left open for contributors. They are the only admitted statements in the library, and nothing
  else depends on them
  ([#1352](https://github.com/Verified-zkEVM/ArkLib/issues/1352)).
- **Rewinding knowledge soundness.** A shared rewinding engine with legacy-layer and
  interaction-layer instances
  ([#1410](https://github.com/Verified-zkEVM/ArkLib/issues/1410)).
- **Randomized state restoration.** Restoration modelled with actual cached query budgets
  ([#1267](https://github.com/Verified-zkEVM/ArkLib/pull/1267)).
- **Akita.** A recursive lattice polynomial commitment with checkpoint extraction
  ([#1378](https://github.com/Verified-zkEVM/ArkLib/issues/1378)).
- **Reusable ring switching and Flock.** Interaction-layer reference-Flock conformance and the Flock
  instance used by leanerVM
  ([#1286](https://github.com/Verified-zkEVM/ArkLib/issues/1286),
  [leanerVM#3](https://github.com/Verified-zkEVM/leanerVM/issues/3)).
- **Binius.** The remaining Binius interfaces, rejection semantics and proofs
  ([#893](https://github.com/Verified-zkEVM/ArkLib/issues/893)).
- **STIR protocol.** Construction 5.2 and its round-by-round soundness (Lemma 5.4, Theorem 5.1),
  tied to a concrete prover and verifier
  ([#1292](https://github.com/Verified-zkEVM/ArkLib/issues/1292)).
- **BitZ.** The general relation over a finitely generated ring and a relaxed overflow bound
  ([#1331](https://github.com/Verified-zkEVM/ArkLib/issues/1331),
  [#1307](https://github.com/Verified-zkEVM/ArkLib/issues/1307)).
- **Group models.** ArkLib's side of the generic and algebraic group model consolidation in VCVio
  ([#1310](https://github.com/Verified-zkEVM/ArkLib/issues/1310)).

## Directions

- **Cryptographic compilation.** Turn oracle guarantees into commitment and opening obligations
  through the BCS transform, and connect protocols to concrete opening arguments, Merkle
  commitments and Fiat-Shamir transcripts. The
  [compiler design](docs/design/04-oracle-elimination-compiler.md) and
  [issue #627](https://github.com/Verified-zkEVM/ArkLib/issues/627) describe the approach. The
  duplex-sponge variant of Fiat-Shamir is not yet formalized.
- **Hachi recursion.** The recursive opening of [NOZ26] is not formalized, and an earlier
  unfinished implementation was removed. Any recursive opening would be new work; the
  [audit](docs/kb/audits/noz26-recursion-z-packing.md) records the obstacle.
- **Further protocols and properties.** WHIR, zero knowledge, pairing-based systems,
  Twist/Shout, IVC folding and a mechanized PCP theorem, as concrete clients require them.
- **Implementations.** Prove optimized algorithms agree with their specifications, exercise honest
  and rejecting runs, and measure actual workloads. Computable polynomials, fields and NTT kernels
  belong in [CompPoly](https://github.com/Verified-zkEVM/CompPoly); generic probability, oracle games
  and resource accounting in [VCVio](https://github.com/Verified-zkEVM/VCVio); interaction
  structure in [PolyFun](https://github.com/Verified-zkEVM/PolyFun).

## What counts as complete

A delivery names its theorem, hypotheses, concrete consumer and transitive axiom report. Keep
mathematical security, legacy-to-interaction correspondence, execution tests and compiled
implementation claims
distinct. The [axiom regression gate](docs/wiki/quickstart.md#filling-a-sorry-or-work-that-must-stay-axiom-clean)
rejects new admissions; a successful build or a deleted declaration alone does not close a proof
obligation.
