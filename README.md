# Formally Verified Arguments of Knowledge

ArkLib is a Lean 4 library for specifying succinct non-interactive arguments of knowledge (SNARKs)
and proving them secure. It is developed as part of the
[verified-zkevm effort](https://verified-zkevm.org/), for researchers and engineers who want
machine-checked security proofs of cryptographic proof systems.

The library is under active development. Some results are fully proved. Others are stated with
part of the proof still missing. [What to trust](#what-to-trust) explains how to tell them apart.

## How a SNARK is built

Most modern SNARKs are built in three steps. ArkLib aims to formalize each step once, in general
form, so that individual protocols can reuse it.

1. **Interactive oracle reductions.** A prover and a verifier exchange messages to reduce a claim
   about a statement and witness in a relation $$R_1$$ to a simpler claim in a relation $$R_2$$.
   The verifier does not read the prover's messages in full. It queries them through an oracle
   interface: for example, it reads one entry of a vector, or evaluates a polynomial at one point.
   A reduction should be *complete* (an honest prover turns a true claim into a true claim),
   *sound* (no prover turns a false claim into a true one, except with small probability), and
   often *knowledge sound* (a witness for the input claim can be extracted from a witness for
   the output claim, except with small probability).
2. **Composition.** Reductions whose relations match are run one after another, and their error
   bounds add. This lets us build a large protocol from small ones, such as sum-check or a zero
   check, and derive its security from theirs.
3. **Compilation to a non-interactive argument.** The *BCS transform* replaces each oracle
   message with a commitment (for example a Merkle root or a polynomial commitment) and answers
   each verifier query with an opening proof. The *Fiat–Shamir transform* then removes
   interaction: the prover derives the verifier's random challenges from a hash function, which
   the security proof models as a random oracle.

## Two frameworks

ArkLib currently contains two formalizations of steps 1 and 2.

New general theory is developed in [`ArkLib/Interaction/`](ArkLib/Interaction), the *Interaction
framework*. A protocol is a tree of prover and verifier moves. The prover keeps private state
between rounds, and the verifier sees prover messages only through oracle queries. Each reduction
outputs a statement together with oracles that the next reduction may query. On `main`, this
framework has sequential composition with additive soundness error, and the sum-check protocol
with completeness, soundness, and an executable verifier and honest prover. These files contain
no `sorry`.

[`ArkLib/OracleReduction/`](ArkLib/OracleReduction) is the older *legacy framework*. Most
protocols in [`ArkLib/ProofSystem/`](ArkLib/ProofSystem) are still written against it, and so are
the existing definitions of the BCS and Fiat–Shamir transforms. Several of its general theorems
have incomplete proofs. We plan to port protocols to the Interaction framework one at a time,
each with a proof that the port matches the original. Until a protocol is ported, any `sorry` in
its legacy proofs remains: a theorem in the Interaction framework does not remove it.

Step 3 is not yet available in the Interaction framework. The [roadmap](ROADMAP.md) lists what
is merged, what is in open pull requests, and what is planned.

## Library structure

| Area | Contents |
|---|---|
| [Interaction](ArkLib/Interaction) | The Interaction framework: protocols, oracle reductions, composition, execution, and security definitions |
| [OracleReduction](ArkLib/OracleReduction) | The legacy framework, including the BCS and Fiat–Shamir transforms |
| [ProofSystem](ArkLib/ProofSystem) | Protocols: sum-check, Spartan, FRI, STIR, Binius, ring switching, and small building blocks |
| [Commitments](ArkLib/Commitments) | Commitment scheme interfaces, KZG, and the lattice-based Ajtai and Hachi schemes |
| [Data](ArkLib/Data) | Supporting mathematics: coding theory, polynomials, lattices, and probability |
| [VCVio](https://github.com/Verified-zkEVM/VCVio) (dependency) | Probabilistic computations with oracle access, random-oracle query bounds, and Merkle trees with their security proofs |
| [CompPoly](https://github.com/Verified-zkEVM/CompPoly) (dependency) | Computable polynomials and finite fields |
| [PolyFun](https://github.com/Verified-zkEVM/PolyFun) (dependency) | The generic interaction trees that the Interaction framework is built on |

ArkLib does not implement its own Merkle trees. It uses VCVio's construction and security theorem.

## What to trust

A protocol definition is not a security proof, and a theorem whose proof contains `sorry` is not
yet proved. Before relying on a result:

- Read the hypotheses of the theorem. They state the assumptions and the exact event whose
  probability is bounded.
- Run `#print axioms` on the theorem. A complete proof depends only on Lean's standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`). If `sorryAx` appears, some step is unproved.

Proving that an optimized implementation, for example Rust code extracted through
[hax](https://github.com/cryspen/hax), matches a specification in ArkLib is planned work. It is a
separate obligation from the security proofs above.

## Getting started and contributing

Start with the [quickstart](docs/wiki/quickstart.md) for setup and validation, then use the
[repository map](docs/wiki/repo-map.md) to find the relevant source. See
[CONTRIBUTING.md](CONTRIBUTING.md) for contribution conventions and the [roadmap](ROADMAP.md)
for current priorities.

For background, the [design documents](docs/design/README.md) explain the Interaction framework,
[BACKGROUND.md](BACKGROUND.md) lists the literature we follow, and the
[blueprint sources](blueprint/src) and [research knowledge base](docs/kb/README.md) record the
mathematics behind individual formalizations.
