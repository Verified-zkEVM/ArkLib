# Roadmap

**Last checked: 2026-10-04**, against `main` at `ace55c3e`.

This page is the project-wide index. Areas with a link in the first column have their own page
in the [`roadmap/`](roadmap/README.md) folder, with the details, the open pull requests, and the
next step. The other areas are summarized here until someone writes their page.

Each result is described as **merged** (on `main`), in an **open PR** (proved on a branch, not
yet merged), or **planned**. The [`roadmap/` README](roadmap/README.md) defines the terms used
below, such as *Interaction framework*, *legacy framework*, and *port*.

## Current focus

The main effort is the Interaction framework in [`ArkLib/Interaction/`](ArkLib/Interaction): the
general theory of interactive oracle reductions that protocols are built on. Existing protocols
still use the legacy framework in [`ArkLib/OracleReduction/`](ArkLib/OracleReduction) and will be
ported one at a time. See [Moving protocols to the Interaction framework](roadmap/interaction-migration.md)
for what is proved and what a port must show, and the
[implementation plan](docs/design/05-roadmap.md) for the order of work.

## Areas

| Area | On `main` | In open PRs | Next |
|---|---|---|---|
| [Interaction framework](roadmap/interaction-migration.md) | Sequential composition of oracle reductions with additive soundness error. Execution against a shared stateful oracle, with query-cost bounds. | Round-by-round soundness implies soundness. Knowledge soundness under composition. State-restoration knowledge soundness. | Merge the open PRs. Port FRI and Spartan. |
| [Sum-check and Spartan](roadmap/proof-systems/sumcheck-spartan.md) | [Sum-check](ArkLib/ProofSystem/Sumcheck) in the Interaction framework: completeness, soundness error $$k \cdot d / \lvert F \rvert$$, executable verifier and honest prover. [Spartan](ArkLib/ProofSystem/Spartan) in the legacy framework, with incomplete proofs. | Sum-check soundness derived round by round, and under state restoration. | Port Spartan. Prove an efficient multilinear sum-check prover correct. |
| [Merkle commitments](roadmap/commitments/merkle-trees.md) | Merkle trees and their random-oracle security are in VCVio. | ArkLib protocols that open Merkle commitments, with security reduced to VCVio's theorem. | Openings interleaved with the protocol. The general BCS transform. |
| FRI, STIR, WHIR, and coding theory | Reed–Solomon codes and proximity gaps in [CodingTheory](ArkLib/Data/CodingTheory). [FRI](ArkLib/ProofSystem/Fri), [batched FRI](ArkLib/ProofSystem/BatchedFri), and [STIR](ArkLib/ProofSystem/Stir) in the legacy framework, with incomplete proofs. | | Port FRI to the Interaction framework. |
| Binius and ring switching | [Binius](ArkLib/ProofSystem/Binius) and [ring switching](ArkLib/ProofSystem/RingSwitching) in the legacy framework, with incomplete proofs. See the [repository map](docs/wiki/repo-map.md). | | |
| KZG and polynomial commitments | [KZG](ArkLib/Commitments/Functional/KZG): correctness and binding, with no `sorry` in that directory. Check each theorem for its assumptions. | | Connect KZG to the Interaction framework's oracle interfaces. |
| Lattices and Hachi | [Lattice theory](ArkLib/Data/Lattices), and the Ajtai and Hachi schemes in [Commitments](ArkLib/Commitments). See the blueprint's lattice chapter and the [repository map](docs/wiki/repo-map.md). | | |
| Computable polynomials and fields | Developed in [CompPoly](https://github.com/Verified-zkEVM/CompPoly). ArkLib's additions are in [ToCompPoly](ArkLib/ToCompPoly). | | Track this work in CompPoly. |

"Folding" in the FRI and STIR code means folding a codeword. Folding schemes for incrementally
verifiable computation, as in Nova, are a separate topic listed below.

## Longer-term targets

None of the following is scheduled. For each one, the protocol definition, the security proof,
and any efficient implementation are separate pieces of work.

- **The BCS transform in general.** Replace every oracle in a reduction with a commitment and
  opening proofs, and carry the security bounds through.
- **Fiat–Shamir**, including the duplex-sponge variant used in practice.
- **Zero knowledge.**
- **Knowledge soundness by rewinding**, and extraction in the algebraic group model.
- **Adversary running time**, stated and tracked through reductions.
- **More protocols:** Plonk and its variants, Twist and Shout, and folding schemes for
  incrementally verifiable computation.
- **Textbook coverage.** We aim to recover the results of the Chiesa–Yogev textbook
  [Building Cryptographic Proofs from Hash Functions](https://snargsbook.org/) in the
  Interaction framework, with an explicit correspondence to the book's definitions.
- **The PCP theorem.** It would be nice to use ArkLib to prove foundational results such as the
  PCP theorem, starting from the original proofs (sum-check, low-degree tests, and proof
  composition).
