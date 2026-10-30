# ArkLib: Formally Verified Arguments of Knowledge

ArkLib is a Lean 4 library for formally verifying **succinct non-interactive arguments of
knowledge** (SNARKs). It specifies interactive (oracle) reductions and proves their completeness
and security properties in Lean, from generic theorems about composition and lifting. ArkLib is part of the [verified-zkEVM effort](https://verified-zkevm.org/).

The API documentation and the blueprint are published at
[verified-zkevm.github.io/ArkLib](https://verified-zkevm.github.io/ArkLib/).

## Library structure

The core of our library is a mechanized theory of **interactive oracle reductions**. The concepts
below describe the IOR theory shared by ArkLib's [two layers](#two-layers); their implemented
interfaces and results differ.

1. An **IOR** (interactive oracle reduction) is an interactive protocol between a prover and a
   verifier that reduces a relation $R_1$ on a public statement and a private witness to another
   relation $R_2$.
2. The verifier need not see the messages sent by the prover in the clear. It can instead make
   oracle queries to these messages through a specified oracle interface.
   - For example, one can view a message as a vector and query entries of that vector.
     Alternatively, one can view the message as a polynomial and query its evaluation at given
     points.
3. **Sequential composition** combines IORs with compatible relations (for example
   $R_1 \implies R_2$ and $R_2 \implies R_3$), preserving their security properties under the
   hypotheses of the relevant composition theorem. **Lifting** places an IOR's input and output
   statements and witnesses in a larger context, creating a **virtual** oracle reduction.
   - Sequential composition and lifting let us build existing protocols (for example Plonk) from
     common sub-protocols (for example zero check, permutation check and quotienting), and derive
     the security of the constructed protocol from that of its components.
4. Once we have specified the desired IOR, the next step is to turn it into a **non-interactive**
   argument of knowledge. This is often done in two steps:
   - We first apply the **(interactive) BCS transform**, which materializes the message oracles of
     an IOR using **(functional) commitment schemes**. A functional commitment scheme consists of
     a commitment algorithm and an opening argument for the correctness of the specified oracle
     interface. The transform replaces every oracle message from the prover with a commitment to
     that message, and runs an opening argument for each oracle query that the verifier makes to
     the prover's messages. These opening arguments may be batched.
   - We then apply the **Fiat-Shamir transform**, which removes interaction: the prover derives
     the verifier's random challenges by querying a hash function, modeled as a random oracle.

   [ROADMAP.md](ROADMAP.md) records which composition, lifting and transform interfaces are
   formalized in each layer.
5. Our formalization follows the view of IORs as the central information-theoretic object
   underlying modern SNARKs, and the current abstractions of the interactive BCS and Fiat-Shamir
   transforms. The scope also includes interactive arguments and commitment schemes whose security
   is computational: it rests on discrete-logarithm or pairing assumptions, on lattice assumptions
   such as Module-SIS, or on collision resistance of a hash function, or on an idealized model such
   as a hash function modeled as a random oracle.
   [BACKGROUND.md](BACKGROUND.md) surveys both the information-theoretic proof models and these
   computational arguments and commitments, with their security notions, the compilers that combine
   them into SNARKs, and the planned post-quantum and universally composable security results. It
   also compares ArkLib's interactive oracle reductions with the definitions in the literature.

Using this theory, we formalize proof systems in [`ArkLib/ProofSystem/`](ArkLib/ProofSystem/) and
commitment schemes in [`ArkLib/Commitments/`](ArkLib/Commitments/).

## Two layers

ArkLib has two layers that formalize the objects above. They coexist, and a theorem in one layer
does not by itself prove a theorem about the other.

- The **legacy layer**, [`ArkLib/OracleReduction/`](ArkLib/OracleReduction/), is the original
  formalization, in which an IOR is an `OracleReduction`.
- The **interaction layer**, [`ArkLib/Interaction/`](ArkLib/Interaction/), represents a protocol
  as an interaction tree, built on the polynomial functors and interaction trees of
  [PolyFun](https://github.com/Verified-zkEVM/PolyFun). It avoids the legacy layer's limitations
  and can express more protocols, in particular protocols whose shape depends on earlier
  messages. It is meant to replace the legacy layer.

[ROADMAP.md](ROADMAP.md#priority-replace-the-legacy-layer) records what each layer formalizes and
how far the migration has progressed. [Current status](docs/design/00-current-status.md) records the
interaction layer's implemented interfaces and remaining gaps, and the
[design documents](docs/design/README.md) specify it.

The legacy layer has structural limits that the interaction layer removes: the protocol shape is
fixed in advance, provers are round-indexed state machines composed with casts, the verifier acts
only after the interaction, oracles must be concrete data, the verifier's result has a single
failure case, and composition needs a bound from every oracle state.
[Limitations of the legacy layer](docs/design/legacy-layer-limitations.md) explains each one and
what the interaction layer does instead.

Developing the interaction layer is the project's priority. The migration proceeds in three
stages: feature parity, then porting protocols one at a time with a proved equivalence to the
legacy version, then deleting the legacy layer. The
[roadmap](ROADMAP.md#priority-replace-the-legacy-layer) details the plan and its progress. Until
the port is complete, ArkLib makes no backward-compatibility guarantees and does not promise
deprecation periods.

## Repository layout

Around the core:

- [`ArkLib/OracleReduction/`](ArkLib/OracleReduction/) and [`ArkLib/Interaction/`](ArkLib/Interaction/)
  hold the [two layers](#two-layers).
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
- Learn the interaction layer from the [design documents](docs/design/README.md).
- Find where a topic lives with the [repository map](docs/wiki/repo-map.md).
- Look up a paper's formalization status in the [knowledge base](docs/kb/README.md).
- Read the [agent and contributor wiki](docs/wiki/README.md) for conventions and workflows.

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
