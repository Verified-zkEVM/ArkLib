# ArkLib: Formally Verified Arguments of Knowledge

ArkLib is a Lean 4 library for formally verifying **succinct non-interactive arguments of
knowledge** (SNARKs). It specifies interactive (oracle) reductions and proves their completeness
and security properties in Lean, from generic theorems about composition and lifting. ArkLib is part of the [verified-zkEVM effort](https://verified-zkevm.org/).

The API documentation and the blueprint are published at
[verified-zkevm.github.io/ArkLib](https://verified-zkevm.github.io/ArkLib/).

## Library structure

The core of our library is a mechanized theory of **interactive oracle reductions**. The concepts
below apply to both of ArkLib's [layers](#two-layers). The layers are two representations of the
same objects, and the interaction layer is the better one.

1. An **IOR** (interactive oracle reduction) is an interactive protocol between a prover and a
   verifier that reduces a relation $R_1$ on a public statement and a private witness to another
   relation $R_2$.
2. The verifier need not see the messages sent by the prover in the clear. It can instead make
   oracle queries to these messages through a specified oracle interface.
   - For example, one can view a message as a vector and query entries of that vector.
     Alternatively, one can view the message as a polynomial and query its evaluation at given
     points.
3. We can **sequentially compose** IORs with compatible relations (for example $R_1 \implies R_2$
   and $R_2 \implies R_3$), preserving their security properties under the conditions that each
   composition theorem states. We can also **lift** an IOR from a simple context (the input and
   output statement and witness) into a larger, more complex context, creating a **virtual**
   oracle reduction.
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

   [ROADMAP.md](ROADMAP.md) records which parts of these transforms are formalized.
5. Our formalization follows the view of IORs as the central information-theoretic object
   underlying modern SNARKs, and the current abstractions of the interactive BCS and Fiat-Shamir
   transforms. [BACKGROUND.md](BACKGROUND.md) surveys the information-theoretic proof models, their
   security notions and the compilers to SNARKs, and compares ArkLib's interactive oracle
   reductions with the definitions in the literature.

Using this theory, we formalize proof systems in [`ArkLib/ProofSystem/`](ArkLib/ProofSystem/) and
commitment schemes in [`ArkLib/Commitments/`](ArkLib/Commitments/).

## Two layers

ArkLib has two layers that formalize the objects above. They coexist, and a theorem in one layer
does not by itself prove a theorem about the other.

- The **legacy layer**, [`ArkLib/OracleReduction/`](ArkLib/OracleReduction/), is the original
  formalization. An IOR is an `OracleReduction`. The layer is sorry-free. It contains sequential
  composition, lifting into a larger context (`liftContext`), and the security notions:
  completeness, soundness, knowledge soundness, round-by-round knowledge soundness and
  coordinate-wise special soundness. Every protocol and commitment scheme in the
  [status catalog](ROADMAP.md#complete) is built on this layer.
- The **interaction layer**, [`ArkLib/Interaction/`](ArkLib/Interaction/), represents a protocol
  as an interaction tree, built on the polynomial functors and interaction trees of
  [PolyFun](https://github.com/Verified-zkEVM/PolyFun). It avoids the limitations listed below
  and can express more protocols, in particular protocols whose shape depends on earlier
  messages. It is meant to replace the legacy layer, but it is not ready to do so: it has generic
  execution, composition and security theory, and one protocol, Sum-check
  ([`ArkLib/ProofSystem/Sumcheck/Interaction/`](ArkLib/ProofSystem/Sumcheck/Interaction/)).
  [Current status](docs/design/00-current-status.md) records what the layer has and lacks, and
  the [design documents](docs/design/README.md) specify it.

### Limitations of the legacy layer

The legacy layer works and carries many protocols, but its representation has limits that the
interaction layer removes.

- **The protocol shape is fixed in advance.** A protocol is a `ProtocolSpec n`: `n` rounds, with
  the direction and the type of each round given as functions of the round index only. The number
  of rounds, who speaks, and the message and challenge types cannot depend on earlier messages or
  challenges, so dependent protocols cannot be expressed directly. In the interaction layer a protocol is a
  PolyFun `Interaction.TypeTree`, and the rest of the tree, including its roles, may depend on the
  path so far. `Reduction.then` (`Interaction/Reduction.lean`) appends a second reduction whose
  tree depends on the complete first path.
- **Provers are round-indexed state machines.** A legacy prover has one state type per round
  (`PrvState : Fin (n + 1) → Type`) and round-indexed `sendMessage` and `receiveChallenge`
  functions. Composing two provers concatenates their state families with `Fin.append` and moves
  states between them with dependent casts (`dcast`, in `Composition/Sequential/Append/Basic.lean`);
  reductions over protocol specs that are equal but not definitionally equal are related by the
  cast lemmas in `OracleReduction/Cast.lean` and `ProtocolSpec/Cast.lean`. In the interaction layer
  a prover is a strategy on the tree (`Interaction.Oracle.Prover.Strategy`) whose continuation
  keeps its private memory, and composition acts on trees and strategies without round-index
  arithmetic or casts.
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
- **There is one failure outcome.** A verifier returns `OptionT`, so `none` must stand for every
  kind of failure. The interaction layer returns accept, reject or fault
  (`Interaction/Oracle/Terminal.lean`) and accounts separately for probability mass lost when a
  computation does not return (`Interaction/Oracle/TerminalMeasure.lean`).
- **Composition needs a bound from every oracle state.** A legacy security game draws the shared
  oracle state from an initialization and discards the final state. In a composed protocol the
  second reduction starts from whatever state the first leaves, which its own game does not cover.
  Sequential composition of soundness (`Verifier.append_soundness`) therefore needs a guarded
  first verifier and a second-stage bound that holds from every fixed oracle state. This excludes
  oracles whose state hides a secret from the prover, such as a trapdoor or an eagerly sampled
  random function. The interaction layer runs setup and every stage inside one persistent runtime
  and proves composition from a bound over the actual distribution of the prefix
  (`Interaction/Oracle/Runtime.lean`, `Interaction/Oracle/RuntimeSoundness.lean`).

### Migration plan

Now that the legacy layer is sorry-free and reasonably stable, the project prioritizes developing
the interaction layer. The migration has three stages:

1. **Feature parity.** The interaction layer gains every framework feature that the legacy
   protocols use.
2. **Ports with a proved equivalence.** Protocols move to the interaction layer one at a time. For
   each ported protocol, a theorem relates the legacy protocol, embedded into the interaction
   layer, to the interaction-layer protocol, so the port is checked to be faithful.
3. **Deletion.** The legacy layer is then deleted as a whole.

[ROADMAP.md](ROADMAP.md#priority-replace-the-legacy-layer) tracks this plan.

ArkLib makes no backward-compatibility guarantees and does not promise deprecation periods,
in particular until the port is complete. Declarations in either layer can change or disappear
without a deprecation warning.

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
