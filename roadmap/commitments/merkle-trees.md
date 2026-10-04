# Merkle commitments

**Page status:** active.
**Last checked:** 2026-10-04, against `main` at `ace55c3e29da1fc55a321378ada55ea4f7ed8790`.
**Contact:** [@quangvdao](https://github.com/quangvdao).
**Blueprint:** [Merkle chapter](../../blueprint/src/commitments/merkle.tex), currently a
placeholder. See also the
[oracle-elimination design](../../docs/design/04-oracle-elimination-compiler.md).

The [folder README](../README.md) defines the terms used on this page.

## Where things stand

ArkLib has no Merkle tree implementation of its own. Merkle trees, opening proofs, batch
verification, and their security in the random oracle model are in
[VCVio](https://github.com/Verified-zkEVM/VCVio), under `VCVio/CryptoFoundations/MerkleTree/`.

Nothing on ArkLib's `main` yet connects a protocol in the Interaction framework to VCVio's
security theorem. The open PRs below do this.

## Open PRs

All three are by [@quangvdao](https://github.com/quangvdao).

- [VCVio #825](https://github.com/Verified-zkEVM/VCVio/pull/825) restates VCVio's bound in the
  form ArkLib needs: the probability that some verified opening disagrees with the values
  extracted when the prover committed.
- [ArkLib #1270](https://github.com/Verified-zkEVM/ArkLib/pull/1270) defines a protocol in
  which the prover sends a Merkle root and later opens positions chosen by the verifier. It
  proves the real-to-ideal transfer
  Pr[the real verifier accepts] ≤ Pr[the ideal verifier accepts] + $$E / \lvert Y \rvert$$,
  where the ideal verifier reads the extracted values directly, $$Y$$ is the set of digests, and
  $$E$$ is an explicit function of the bounds on tree nodes, commitments, and hash queries.
- [ArkLib #1271](https://github.com/Verified-zkEVM/ArkLib/pull/1271) builds on #1270 and lets
  the verifier choose each position after seeing earlier answers.

The [Interaction framework page](../interaction-migration.md#merkle-commitments) describes the
division between VCVio and ArkLib in more detail.

## Open gaps

- **All openings arrive in one batch at the end.** A protocol that opens a commitment and then
  continues is not covered.
- **Leaves are raw digests.** VCVio's encoded leaves and hash forests are not yet connected.
- **The ideal protocol's soundness is assumed.** The transfer theorem bounds the gap between
  the real and ideal verifiers. Soundness of the ideal protocol is proved separately, per
  protocol.
- **Not the full BCS transform.** Replacing every oracle of a reduction with a commitment, and
  then applying Fiat–Shamir, is planned.

## Next step

Merge the three PRs. Then choose a protocol that needs Merkle openings, FRI being the natural
candidate, and write down when it opens commitments and what it needs from the extracted values
before generalizing the current theorems. Results about Merkle trees themselves belong in
VCVio. Results about protocols that use them belong in ArkLib.
