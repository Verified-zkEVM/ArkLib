# Roadmap

This page is ArkLib's public status and direction: what is complete, what is in progress, and where
the library is going. Use [open issues](https://github.com/Verified-zkEVM/ArkLib/issues) for
assignments and [CONTRIBUTING.md](CONTRIBUTING.md) for the development and review process. The
[native-layer design roadmap](docs/design/05-roadmap.md) owns the implementation plan for the
typed interaction framework; this page does not repeat it.

## Complete

Every result below is on `main` and depends only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). [README.md](README.md#what-is-formalized) names the headline
theorem of each protocol.

### Protocols and commitments

- **Sum-check**: completeness, round-by-round knowledge soundness and ordinary knowledge soundness
  in the oracle-reduction layer; completeness, soundness and round-by-round soundness in the native
  layer, with a CompPoly-backed computable honest prover.
- **FRI**: perfect and noisy-input completeness, soundness, round-by-round soundness, and knowledge
  soundness for a named straightline extractor whose operation counts are certified
  ([`Fri/Spec/MeasuredKnowledgeSoundness.lean`](ArkLib/ProofSystem/Fri/Spec/MeasuredKnowledgeSoundness.lean)).
- **Batched FRI**: perfect completeness and soundness of a batching round followed by FRI, with
  instances for affine-space, power and multilinear generators.
- **Binary Basefold**: perfect completeness, round-by-round knowledge soundness and ordinary
  knowledge soundness of the full protocol.
- **Ring switching**: shared head, product-sumcheck and terminal phases with perfect completeness
  and knowledge soundness, instantiated at Binius's tensor profile and composed with Binary
  Basefold as FRI-Binius ([`Binius/FRIBinius/`](ArkLib/ProofSystem/Binius/FRIBinius/)). The
  [consumer guide](docs/wiki/ring-switching-consumers.md) records the interfaces.
- **Spartan**: a seven-stage oracle reduction for R1CS with perfect completeness and knowledge
  soundness with error `(4s + 2t + 1) / |R|` (`s` and `t` are the logarithms of the constraint
  and variable counts), using an executable straightline extractor.
- **Plonk**: an end-to-end oracle reduction with completeness and knowledge soundness, assembled
  from grand-product, residual-batching and quotient stages.
- **Toy problem**: completeness and knowledge soundness of the toy IOR, with executable IRS and FRS
  implementations.
- **KZG**: correctness, and evaluation and function binding stated as reductions to t-SDH and ARSDH.
  The hardness-based corollaries quantify over explicit adversary classes.
- **Hachi**: the nonrecursive opening argument, with coordinate-wise special soundness of each
  iteration and a computable honest prover. At the formalized parameter profile the inner Module-SIS
  target is trivially solvable, so the weak-binding reduction gives no concrete binding guarantee
  there (`Commitments/Functional/Hachi/Params.lean`).
- **STIR components**: the proximity gap (Theorem 4.1 of [ACFY24stir]), out-of-domain sampling,
  quotienting and combination.

### Framework

- **Oracle-reduction security theory**
  ([`OracleReduction/Security/`](ArkLib/OracleReduction/Security/)): one round-by-round knowledge
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
- **Native typed interactions** ([`ArkLib/Interaction/`](ArkLib/Interaction/)): execution,
  soundness, round-by-round soundness, knowledge certificates and their composition, and
  state-restoration knowledge soundness for fixed-round public-coin protocols with error
  `(Q + k) * error`.
- **Measured extraction**: measured programs and operation-count budgets
  ([`Data/OracleComp/MeasuredProgram.lean`](ArkLib/Data/OracleComp/MeasuredProgram.lean)), their use
  in knowledge soundness ([`OracleReduction/Security/Resources.lean`](ArkLib/OracleReduction/Security/Resources.lean)),
  and measured stages for native knowledge and state-restoration certificates
  (`Interaction/Oracle/Security/{KnowledgeResources,StateRestorationResources}.lean`). The
  [extractor-efficiency design](docs/design/03a-extractor-efficiency.md) states what these budgets
  do and do not certify.
- **Commitment games**: binding and extractability experiments that keep the oracle state left by
  setup ([`Commitments/Functional/Basic.lean`](ArkLib/Commitments/Functional/Basic.lean)).
- **Algebraic group model**: group representations for algebraic adversaries
  ([`ArkLib/AGM/`](ArkLib/AGM/)).

## In progress

- **Solicited proofs.** Five coding-theory lower bounds and separations are stated faithfully and
  left open for contributors. They are the only admitted statements in the library, and nothing
  else depends on them
  ([#1352](https://github.com/Verified-zkEVM/ArkLib/issues/1352)).
- **Rewinding knowledge soundness.** A shared rewinding engine with legacy and native instances
  ([#1410](https://github.com/Verified-zkEVM/ArkLib/issues/1410)).
- **Randomized state restoration.** Restoration modelled with actual cached query budgets
  ([#1267](https://github.com/Verified-zkEVM/ArkLib/pull/1267)).
- **Akita.** A recursive lattice polynomial commitment with checkpoint extraction
  ([#1378](https://github.com/Verified-zkEVM/ArkLib/issues/1378)).
- **Reusable ring switching and Flock.** Native reference-Flock conformance and the Flock
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

- **Native migration.** Port protocol clients to the native layer, starting with small FRI and
  Spartan slices, and prove correspondence with their oracle-reduction versions. The
  [design roadmap](docs/design/05-roadmap.md) sequences this work.
- **Cryptographic compilation.** Turn oracle guarantees into commitment and opening obligations
  through the BCS transform, and connect protocols to concrete opening arguments, Merkle
  commitments and Fiat-Shamir transcripts. The
  [compiler design](docs/design/04-oracle-elimination-compiler.md) and
  [issue #627](https://github.com/Verified-zkEVM/ArkLib/issues/627) describe the approach. The
  duplex-sponge variant of Fiat-Shamir is not yet formalized.
- **Hachi recursion.** The recursive opening of [NOZ26] is not formalized; the
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
mathematical security, native correspondence, execution tests and compiled implementation claims
distinct. The [axiom regression gate](docs/wiki/quickstart.md#filling-a-sorry-or-work-that-must-stay-axiom-clean)
rejects new admissions; a successful build or a deleted declaration alone does not close a proof
obligation.
