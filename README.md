# Formally Verified Cryptographic Arguments

This library aims to provide a modular and composable framework for formally verifying (succinct) cryptographic arguments (e.g. SNARKs) based on Interactive (Oracle) Proofs. This is done as part of the [verified-zkevm effort](https://verified-zkevm.org/).

In the first stage of this library's development, we plan to formalize interactive (oracle) reductions (a modular way of stating IOPs) and prove information-theoretic completeness and soundness for a select list of protocols (see the list of active formalizations below).

For each protocol, we aim to provide:

- A specification based on `Mathlib` polynomials,
- An implementation of the prover and verifier using computable representations of polynomials,
- Proofs of completeness and round-by-round knowledge soundness for the specification, and proofs that the implementations refine the specifications.

## Library Structure

The core of our library is a mechanized theory of **$$\mathcal{F}$$-Interactive Oracle Reductions** (see [OracleReduction](ArkLib/OracleReduction)):
1. An **$$\mathcal{F}$$-IOR** is an interactive protocol between a prover and a verifier to reduce a relation $$R_1$$ on some public statement & private witness to another relation $$R_2$$.
2. The verifier may _not_ see the messages sent by the prover in the clear, but can make oracle queries to these messages using a specified oracle interface;
  - For example, one can view the message as a vector, and query entries of that vector. Alternatively, one can view the message as a polynomial, and query for its evaluation at some given points.
3. We can **compose** multiple $$\mathcal{F}$$-IORs with _compatible_ relations together (e.g. $$R_1 \implies R_2$$ and $$R_2 \implies R_3$$), allowing us to build existing protocols (e.g. Plonk) from common sub-routines (e.g. zero check, permutation check, quotienting).
4. We can also carry out the **BCS transform**, which takes an $$\mathcal{F}$$-IOR and compose it with **$$\mathcal{F}$$-commitment schemes** to result in an interactive argument.
  - Roughly speaking, an $$\mathcal{F}$$-commitment scheme is a commitment scheme with an associated opening argument for the correctness of the specified oracle interface.
  - The BCS transform then replaces every oracle message from the prover with a commitment to that message, and runs an opening argument for each oracle query the verifier makes to the prover's messages.
5. $$\mathcal{F}$$-IOR is a natural notion and related versions have appeared in various places in the literature (see [BACKGROUND](./BACKGROUND.md) for a detailed comparison). Our library takes these existing threads and formalizes them into a cohesive theory.

Using the theory of $$\mathcal{F}$$-IOR, we then formalize various proof systems in [ProofSystem](ArkLib/ProofSystem).

## Active Formalizations (last updated: 1 June 2025)

The library is currently in development. Alongside general development of the library's underlying theory, the following cryptographic components are actively being worked on:
- The sumcheck protocol
- Spartan
- Merkle Trees
- A blueprint for FRI and coding theory pre-requisites
- A blueprint for STIR and WHIR
- Binius

[VCV-io](https://github.com/dtumad/VCV-io), ArkLib's main dependency alongside [mathlib](https://github.com/leanprover-community/mathlib4) is also being developed in parallel.

## Roadmap & Contributing

We welcome outside contributions to the library! Please see [CONTRIBUTING](./CONTRIBUTING.md) and, the list of issues for immediate tasks, and the [ROADMAP](./ROADMAP.md) for a list of desired contributions.

If you're interested in working on any of the items mentioned in the list of issues or the roadmap, please see [verified-zkevm.org](https://verified-zkevm.org/), contact [the authors](mailto:qvd@andrew.cmu.edu), or open a new issue.

## Release Schedule
New releases are planned every first of the month, accompanied by an update to the latest versions of Lean and Mathlib.
