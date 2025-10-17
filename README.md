# Formally Verified Arguments of Knowledge

This library aims to provide a modular and composable framework for formally verifying **succinct non-interactive arguments of knowledge** (SNARKs). This is done as part of the [verified-zkevm effort](https://verified-zkevm.org/).

In the first stage of this library's development, we plan to formalize interactive (oracle) reductions (the information-theoretic core of almost all SNARKs today), and prove completeness and soundness for a select list of protocols (see the list of active formalizations below).

For each protocol, we aim to provide:

- An executable specification of the protocol, constructed modularly using our composition and lifting interfaces,
- Proofs of completeness & round-by-round knowledge soundness via generic theorems about composition and lifting.

In the future, we plan to verify functional equivalence of the executable spec (or modifications thereof) for certain protocols (e.g., sum-check, FRI, or WHIR), with the extracted code from Rust (via [hax](https://github.com/cryspen/hax)) implementations of the same protocols.

## Library Structure

The core of our library is a mechanized theory of **Interactive Oracle Reductions** (see [OracleReduction](ArkLib/OracleReduction)):
1. An **IOR** (called `OracleReduction` in our formalization) is an interactive protocol between a prover and a verifier to reduce a relation $$R_1$$ on some public statement & private witness to another relation $$R_2$$.
2. The verifier may _not_ see the messages sent by the prover in the clear, but can make oracle queries to these messages using a specified oracle interface;
  - For example, one can view the message as a vector, and query entries of that vector. Alternatively, one can view the message as a polynomial, and query for its evaluation at some given points.
3. We can **(sequentially) compose** multiple IORs with _compatible_ relations together (e.g. $$R_1 \implies R_2$$ and $$R_2 \implies R_3$$), preserving the security properties in most cases. We can also **lift** an IOR from a simple context (i.e., the input & output pairs of statement & witness) into a larger, more complex context, creating a **virtual** oracle reduction.
  - These two operations, sequential composition and lifting, allow us to build existing protocols (e.g. Plonk) from common sub-routines (e.g. zero check, permutation check, quotienting), and derive security of the constructed protocol from that of the components.
4. Once we have specified the desired IOR, the next step is to turn it into a **non-interactive** arguments of knowledge. This is often achieved in two steps:
  - We first apply the **(interactive) BCS transform**, which materializes the message oracles in an IOR using appropriate **(functional) commitment schemes**. Roughly speaking, a functional commitment scheme consists of a commitment algorithm, along with an associated opening argument for the correctness of the specified oracle interface.
  - The interactive BCS transform then replaces every oracle message from the prover with a commitment to that message, and runs an opening argument for each oracle query the verifier makes to the prover's messages. These opening arguments may be batched.
  - We then apply the **Fiat-Shamir transform**, which collapses interaction via letting the prover derive the verifier's random challenges through querying a hash function (modeled as a random oracle). We will formalize the **duplex-sponge** version of Fiat-Shamir, which utilizes cryptographic sponges for efficiency in practice.
5. Our formalization follows the emerging view of IORs as the central information-theoretic object underlying modern SNARKs. We also follow the latest understanding & abstraction for the interactive BCS and Fiat-Shamir transformation. See [BACKGROUND](./BACKGROUND.md) for an (in-progress) summary of the relevant history.

Using the theory of interactive oracle reductions, we then formalize various proof systems in [ProofSystem](ArkLib/ProofSystem).

## Active Formalizations (last updated: 7 August 2025)

The library is currently in development. Alongside general development of the library's underlying theory, the following cryptographic components are actively being worked on:
- The Sum-Check Protocol
- Spartan
- Merkle Trees
- FRI and coding theory pre-requisites
- STIR and WHIR
- Binius

[VCV-io](https://github.com/dtumad/VCV-io), ArkLib's main dependency alongside [mathlib](https://github.com/leanprover-community/mathlib4) is also being developed in parallel. We are also starting work on the [Bluebell](https://arxiv.org/pdf/2402.18708) probabilistic program logic in (our fork of) [iris-lean](https://github.com/Verified-zkEVM/iris-lean).

## Roadmap & Contributing

We welcome outside contributions to the library! Please see [CONTRIBUTING](./CONTRIBUTING.md) and, the list of issues for immediate tasks, and the [ROADMAP](./ROADMAP.md) for a list of desired contributions.

If you're interested in working on any of the items mentioned in the list of issues or the roadmap, please see [verified-zkevm.org](https://verified-zkevm.org/), contact [the authors](mailto:qvd@andrew.cmu.edu), or open a new issue.

## Release Schedule
New releases are planned in line with the Lean and mathlib stable release cycles. 
