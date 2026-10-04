# Moving protocols to the Interaction framework

**Page status:** active.
**Last checked:** 2026-10-04, against `main` at `ace55c3e29da1fc55a321378ada55ea4f7ed8790`.
**Contact:** [@quangvdao](https://github.com/quangvdao).
**Blueprint:** none yet. The [design documents](../docs/design/README.md) describe the framework.

The [folder README](README.md) defines the terms used on this page.

## Where things stand

ArkLib has two general theories of interactive protocols. New theory is developed in the
Interaction framework (`ArkLib/Interaction/`). Most protocols still use the legacy framework
(`ArkLib/OracleReduction/`), where several general theorems have incomplete proofs. The plan is
to port each protocol to the Interaction framework, with a proof that the port matches the
original, and to keep the legacy version usable until then.

Merged on `main`, with no `sorry` in `ArkLib/Interaction/`:

- Sequential composition of oracle reductions. Completeness is preserved, and soundness errors
  add: composing reductions with errors $$\varepsilon_1$$ and $$\varepsilon_2$$ gives error at
  most $$\varepsilon_1 + \varepsilon_2$$.
- Execution of a protocol against a shared stateful oracle, such as a random oracle, with
  bounds on the number and cost of queries.
- The sum-check protocol. See [Sum-check and Spartan](proof-systems/sumcheck-spartan.md).

These were merged as [#1231](https://github.com/Verified-zkEVM/ArkLib/pull/1231) through
[#1238](https://github.com/Verified-zkEVM/ArkLib/pull/1238). The
[design status page](../docs/design/00-current-status.md) lists them one by one.

## Open PRs

All of the following are by [@quangvdao](https://github.com/quangvdao). None is merged, and
statements may change in review. Below, $$k$$ is the number of verifier challenges, $$Q$$ is the
prover's query budget, and $$\varepsilon_j$$ is the round-by-round error of challenge $$j$$.

| Result | Statement | PRs | Limits |
|---|---|---|---|
| Round-by-round soundness implies soundness | A protocol with round-by-round errors $$\varepsilon_1, \dots, \varepsilon_k$$ has soundness error at most $$\sum_j \varepsilon_j$$. | [#1261](https://github.com/Verified-zkEVM/ArkLib/pull/1261) | Each verifier challenge must be sampled exactly as the protocol declares, whatever came before. Verifiers that keep other state between rounds are not covered. |
| Knowledge soundness under composition | The extractor of a composed reduction runs the second extractor, then the first. If both reductions are knowledge sound, so is their composition. | [#1259](https://github.com/Verified-zkEVM/ArkLib/pull/1259), [#1260](https://github.com/Verified-zkEVM/ArkLib/pull/1260) | No bound yet on the total extraction error or on the extractor's running time. |
| State-restoration knowledge soundness | Round-by-round knowledge soundness with error $$\varepsilon$$ per challenge implies state-restoration knowledge soundness with error at most $$(Q + k) \cdot \varepsilon$$. With different errors per challenge, the bound is $$Q \cdot \max_j \varepsilon_j + \sum_j \varepsilon_j$$. | [#1263](https://github.com/Verified-zkEVM/ArkLib/pull/1263), [#1264](https://github.com/Verified-zkEVM/ArkLib/pull/1264) | A fixed number of rounds. Each challenge is uniform over a finite set that does not depend on the input or on earlier challenges. The prover is deterministic. |
| The same, for randomized provers | The prover may use private randomness. The bound charges each *distinct* query once, in expectation. | [#1267](https://github.com/Verified-zkEVM/ArkLib/pull/1267), [#1268](https://github.com/Verified-zkEVM/ArkLib/pull/1268) | Same round and challenge restrictions. Needs [VCVio #824](https://github.com/Verified-zkEVM/VCVio/pull/824), which proves the bound on distinct queries. |
| Sum-check under state restoration | Sum-check with $$k$$ variables and individual degree $$d$$ over a field $$F$$ has state-restoration soundness error at most $$(Q + k) \cdot d / \lvert F \rvert$$. | [#1269](https://github.com/Verified-zkEVM/ArkLib/pull/1269) | Soundness only. The polynomial is an input oracle, so there is no witness to extract. |
| Merkle openings | See [Merkle commitments](#merkle-commitments) below. | [#1270](https://github.com/Verified-zkEVM/ArkLib/pull/1270), [#1271](https://github.com/Verified-zkEVM/ArkLib/pull/1271) | |

The PRs depend on each other in two chains, and each must merge after the one before it:

- #1259 → #1260 → #1263 → #1264 → #1267 → #1268 → #1269
- #1270 → #1271

#1261 depends only on `main`.

## What a port must show

A protocol in the legacy framework can be replaced by its port once the port does the following.
A PR that ports a protocol should name the declarations it replaces and say which of these
steps it completes.

1. **State the same claim.** The port has the same statements, witnesses, oracle interfaces,
   challenge distributions, and accept/reject behavior as the original. If it generalizes the
   original, the PR says how. Otherwise a port could quietly prove something weaker.
2. **Prove that the executions match.** Running the port gives the same result as running the
   original, including the prover's private state and the state of any shared oracle. Equal
   outputs are not enough: two executions can agree on outputs and still differ in the queries
   they make, and security bounds count queries.
3. **Prove security for the ported protocol.** Completeness, and soundness or knowledge
   soundness, with explicit assumptions and error bounds. If the original extracts a witness,
   the port must too. A soundness theorem with a trivial witness does not replace an extraction
   theorem.
4. **Account for oracle queries.** Say which random-oracle queries the theorem counts and what
   they cost. If the protocol opens commitments, prove the real-to-ideal transfer for those
   openings.
5. **Check the result and move its users.** Run `#print axioms` and the full build, compare the
   statement with the literature, and update the code that used the legacy version. Remove a
   legacy declaration only when nothing depends on it.

Porting one protocol does not justify removing the legacy framework. Each protocol is replaced
on its own.

## Merkle commitments

Merkle trees and their security live in VCVio, under `VCVio/CryptoFoundations/MerkleTree/`.
VCVio defines the trees, opening proofs, and batch verification, and proves the extraction
theorem in the random oracle model: from the prover's oracle queries at the time it commits,
one can recover the committed values, and any opening that later verifies agrees with those
values, except with a stated probability. ArkLib does not define its own Merkle trees or
re-prove this.

ArkLib adds the connection to protocols. The two open PRs define protocols in the Interaction
framework in which the prover sends a Merkle root, the verifier chooses positions, and the
prover opens them. They prove a real-to-ideal transfer:

Pr[the real verifier accepts] ≤ Pr[the ideal verifier accepts] + $$E / \lvert Y \rvert$$,

where the ideal verifier reads the values extracted when the prover committed, $$Y$$ is the set
of digests, and $$E$$ is an explicit function of the bounds on tree nodes, commitments, the
verifier's hash queries, and the prover's hash queries (`multiCheckpointROMErrorNumerator` in
the source).

- [#1270](https://github.com/Verified-zkEVM/ArkLib/pull/1270) proves this when the verifier's
  positions are fixed in advance.
- [#1271](https://github.com/Verified-zkEVM/ArkLib/pull/1271) allows each position to depend on
  earlier answers.

Both need [VCVio #825](https://github.com/Verified-zkEVM/VCVio/pull/825). Their limits:

- All openings arrive in one batch at the end of the protocol. Openings interleaved with later
  rounds are not covered.
- Leaves are raw digests. VCVio's encoded leaves and hash forests are not yet connected.
- Soundness of the ideal protocol is an assumption of the theorem, to be proved separately for
  each protocol.
- This is one step of the BCS transform, not the whole transform.

## Open gaps

- **Verifiers that reject early.** The state-restoration theorems assume a fixed number of
  rounds. A verifier that may stop early, or a protocol whose length varies, needs a different
  argument, and the right formulation is not settled.
- **Extracting a real witness.** The sum-check results are soundness only. The next ported
  protocol should come with an extraction theorem for a non-trivial witness, and a bound on the
  extractor's running time.
- **FRI and Spartan** have no port yet.
- **The rest of the compilation.** Replacing oracles with commitments in general, openings
  interleaved with the protocol, and Fiat–Shamir with a duplex sponge do not follow from the
  results above.
- **Auxiliary input.** The random-oracle theorems allow the oracle to start from a fixed table
  of answers. They do not cover an adversary whose input is correlated with the oracle. That
  model needs its own definition.

## Next step

Merge the open PRs in the order above. Then port FRI or Spartan, following
[What a port must show](#what-a-port-must-show). The
[design roadmap](../docs/design/05-roadmap.md) gives the order of implementation work.
