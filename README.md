# Formally Verified Arguments of Knowledge

ArkLib is a Lean library for the theory and components of succinct non-interactive arguments
of knowledge (SNARKs), developed as part of the [verified-zkevm effort](https://verified-zkevm.org/).
It is intended for researchers and developers formalizing cryptographic proof systems.

We aim to specify protocols modularly, prove completeness and soundness or knowledge soundness,
and derive security through composition and cryptographic transformations. The long-term target
includes the Chiesa–Yogev textbook pipeline in ArkLib's own terminology and generality, together
with later work on interactive oracle reductions, accumulation, and duplex-sponge Fiat–Shamir.
These are coverage goals, not a claim that the complete pipeline is already formalized.

## Current development

**Updated October 3, 2026.** New general theory is developed in
[`ArkLib/Interaction/`](ArkLib/Interaction). It represents protocols as typed interaction trees,
with prover and verifier strategies, private prover continuations, restricted oracle access,
and explicit execution and security statements. An oracle reduction returns a statement and an
oracle interface that the next reduction can query without seeing the underlying messages.

[`ArkLib/OracleReduction/`](ArkLib/OracleReduction) is the legacy layer. Existing protocol clients
still depend on it. We intend to replace it with the interaction layer after proving the needed
theory and protocol correspondences. The migration is incomplete; native proofs do not discharge
admissions in legacy declarations automatically.

Native composition and Sumcheck already provide substantial proved foundations. Reviewed open
PRs extend these with round-by-round knowledge composition, randomized state-restoration bounds,
and terminal Merkle verification with adaptive query choices. See the
[current status](docs/design/00-current-status.md) for revision scope and the
[roadmap](ROADMAP.md) for remaining work. The linked integration records include open PRs; those results are not yet available on `main`.

## Library structure

| Area | Responsibility |
|---|---|
| [Interaction](ArkLib/Interaction) | Current typed interaction and oracle-reduction theory |
| [OracleReduction](ArkLib/OracleReduction) | Legacy protocol interfaces and security results |
| [ProofSystem](ArkLib/ProofSystem) | Sumcheck, FRI, WHIR, Binius, Spartan, ring switching, and other protocol developments |
| [Commitments](ArkLib/Commitments) | Commitment interfaces, KZG, lattice-based constructions, and opening arguments |
| [Data](ArkLib/Data) | Coding theory, algebra, lattices, and supporting mathematics |
| [VCVio](https://github.com/Verified-zkEVM/VCVio) | Probabilistic oracle computations, random-oracle query bounds, and Merkle constructions and security |
| [CompPoly](https://github.com/Verified-zkEVM/CompPoly) | Computable polynomials and finite-field infrastructure |

ArkLib's Merkle interaction adapters use VCVio's construction and security theorem. They supply
protocol execution and real-to-ideal transfer proofs; they do not implement a second Merkle tree.
The full oracle-elimination and Fiat–Shamir pipeline remains a development target.

## Getting started and contributing

Start with the [quickstart](docs/wiki/quickstart.md) for setup and validation, then use the
[repository map](docs/wiki/repo-map.md) to find the relevant source. See
[CONTRIBUTING.md](CONTRIBUTING.md) for contribution conventions and the
[roadmap](ROADMAP.md) for current priorities and migration requirements.

The [design suite](docs/design/README.md) explains the interaction framework;
[BACKGROUND.md](BACKGROUND.md), the [research knowledge base](docs/kb/README.md), and the
[blueprint sources](blueprint/src) record mathematical context and literature.
Some formalizations contain existing admissions. Evaluate a security claim against its exact
theorem assumptions and axiom dependencies, not just the presence of a protocol definition.

Future implementation work includes proving correspondence to optimized executable protocols
and, where appropriate, Rust implementations extracted through
[hax](https://github.com/cryspen/hax). These are separate obligations from mathematical soundness.
