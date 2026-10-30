# ArkLib: Formally Verified Arguments of Knowledge

ArkLib is a Lean 4 library for formally verifying **succinct non-interactive arguments of
knowledge** (SNARKs). It specifies interactive (oracle) reductions and proves their completeness
and security properties in Lean, from generic theorems about composition and lifting. ArkLib is part of the [verified-zkEVM effort](https://verified-zkevm.org/).

The API documentation and the blueprint are published at
[verified-zkevm.github.io/ArkLib](https://verified-zkevm.github.io/ArkLib/).

## How the library is organized

ArkLib has two layers for describing protocols. They coexist; a security theorem in one layer does
not by itself prove a theorem about the other.

- **Oracle reductions** ([`ArkLib/OracleReduction/`](ArkLib/OracleReduction/)). An interactive
  oracle reduction (IOR, `OracleReduction`) is a protocol between a prover and a verifier that
  reduces a relation on statements and witnesses to another relation. The verifier reads prover
  messages only through oracle queries, for example evaluations of a sent polynomial. The layer
  provides sequential composition, lifting into a larger context (`liftContext`), and the security
  notions: completeness, soundness, knowledge soundness, round-by-round knowledge soundness and
  coordinate-wise special soundness. Every protocol in the
  [status catalog](ROADMAP.md#complete), except native Sum-check, is stated in this layer. The project calls it the legacy layer because new framework work
  happens in the native layer.
- **Native typed interactions** ([`ArkLib/Interaction/`](ArkLib/Interaction/)). Protocols are
  trees of moves, built on the interaction structures of
  [PolyFun](https://github.com/Verified-zkEVM/PolyFun), and run with the prover's actual
  continuation and oracle resources. The layer proves soundness, round-by-round soundness,
  knowledge certificates and their composition, state-restoration knowledge soundness, and
  measured extraction costs. The native Sumcheck protocol lives in
  [`ArkLib/ProofSystem/Sumcheck/Interaction/`](ArkLib/ProofSystem/Sumcheck/Interaction/). The
  [design documents](docs/design/README.md) specify this layer.

Around the two layers:

- [`ArkLib/ProofSystem/`](ArkLib/ProofSystem/) holds protocols and reusable protocol components.
- [`ArkLib/Commitments/`](ArkLib/Commitments/) holds commitment schemes and opening arguments.
- [`ArkLib/Data/`](ArkLib/Data/) holds supporting mathematics: coding theory, proximity gaps,
  polynomials, probability and measured programs.
- [`ArkLib/AGM/`](ArkLib/AGM/) holds algebraic group model representations.
- [`ArkLib/ToCompPoly/`](ArkLib/ToCompPoly/) and [`ArkLib/ToMathlib/`](ArkLib/ToMathlib/) hold
  local bridges to, and extensions of, ArkLib's dependencies.
- [`ArkLibTest/`](ArkLibTest/) holds compile-time acceptance tests.

ArkLib depends on [Mathlib](https://github.com/leanprover-community/mathlib4),
[VCVio](https://github.com/Verified-zkEVM/VCVio) (oracle computations, probability and
cryptographic games), [CompPoly](https://github.com/Verified-zkEVM/CompPoly) (computable
polynomials and fields) and, through VCVio, PolyFun. [`lake-manifest.json`](lake-manifest.json)
records the exact revisions.

## What is formalized

[ROADMAP.md](ROADMAP.md) is the status catalog. It lists each formalized protocol and commitment
scheme (Sum-check, FRI, batched FRI, Binary Basefold, ring switching, FRI-Binius, Spartan, Plonk,
KZG, Hachi and STIR components) with its headline theorems, error bounds and known limitations,
says which implementations are executable, and lists the work in progress and planned directions.

## Build and check

Prerequisites: [elan](https://github.com/leanprover/elan), which installs the Lean toolchain named
in [`lean-toolchain`](lean-toolchain), and Python 3 for the validation scripts.

1. Clone the repository and enter it.
2. Fetch the precompiled Mathlib cache:

   ```bash
   lake exe cache get
   ```

3. Build the library:

   ```bash
   lake build
   ```

4. Run the full local validation, which is what CI runs:

   ```bash
   ./scripts/validate.sh
   ```

   It builds the library and the acceptance tests, fails on any warning other than an admitted
   proof, and runs the source-policy gate and the compiled runtime checks.

[`docs/wiki/quickstart.md`](docs/wiki/quickstart.md) explains each check and which one to run for
which change.

## Where to go next

- Learn the legacy API from the
  [interactive oracle reductions concept page](docs/kb/concepts/interactive-oracle-proofs.md).
- Learn the native layer from the [design documents](docs/design/README.md).
- Find where a topic lives with the [repository map](docs/wiki/repo-map.md).
- Look up a paper's formalization status in the [knowledge base](docs/kb/README.md).
- Read the [agent and contributor wiki](docs/wiki/README.md) for conventions and workflows.

Background reading on the theory:

- Ben-Sasson, Chiesa and Spooner, *Interactive Oracle Proofs* [BCS16]
  ([KB page](docs/kb/papers/BCS16.md)), which introduced IOPs and the BCS transform.
- Ben-Sasson, Chiesa, Goldberg, Gur, Riabzev and Spooner,
  [*Linear-Size Constant-Query IOPs for Delegating Computation*](https://eprint.iacr.org/2019/1230),
  which introduced interactive oracle reductions.
- Chiesa and Yogev, [*Building Cryptographic Proofs from Hash Functions*](https://snargsbook.org/).

## Contributing

Contributions are welcome. Start with [CONTRIBUTING.md](CONTRIBUTING.md) for the review process,
style and naming, and [AGENTS.md](AGENTS.md) for the one-screen guide to the repository. Open
tasks are in the [issue tracker](https://github.com/Verified-zkEVM/ArkLib/issues).

No admitted proof may merge into `main`. The only admitted statements in the library are
*solicited proofs*: true, faithfully stated external results whose research-sized proofs are open
for contributors. They are listed in
[`scripts/axiom_baseline.json`](scripts/axiom_baseline.json) and tracked in
[issue #1352](https://github.com/Verified-zkEVM/ArkLib/issues/1352); no other declaration may
depend on them.

To discuss larger contributions, open an issue or contact
[the maintainers](mailto:qvd@andrew.cmu.edu).

## Releases

Releases follow the Lean and Mathlib stable release cycles. A tag is created when the Lean
toolchain changes on `main`.

## License

ArkLib is licensed under the [Apache License 2.0](LICENSE).
