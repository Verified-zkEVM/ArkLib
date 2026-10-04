# Merkle commitments

**Status:** active. **Last checked:** October 3, 2026.
**Source:** ArkLib main `ace55c3e`; reviewed integration VCVio `6bf6c91b`.
**Contact:** unassigned in this roadmap; use the linked PR authors for specific changes.
**Blueprint:** no dedicated chapter identified here; see the
[oracle-elimination design](../../docs/design/04-oracle-elimination-compiler.md).

## Where things stand

VCVio owns Merkle constructions, openings, extraction, and shared-random-oracle security.
ArkLib's new interaction adapters connect native protocol execution to that security theorem.
The [ownership and migration page](../interaction-migration.md#merkle-ownership) records the
precise division and source evidence. There is no separate ArkLib Merkle-tree implementation
in these adapters.

## Active branches and PRs

- [VCVio #825](https://github.com/Verified-zkEVM/VCVio/pull/825) expresses the owning checkpoint
  disagreement bound using native measure probability.
- [ArkLib #1270](https://github.com/Verified-zkEVM/ArkLib/pull/1270) transfers native terminal-batch
  acceptance to an ideal verifier using extracted commitment-time values.
- [ArkLib #1271](https://github.com/Verified-zkEVM/ArkLib/pull/1271), on #1270, allows bounded
  answer-dependent query choices.

These are reviewed open PRs. Follow the PR pages for authors and merge status.

## Open gaps

The current adapters use raw digest leaves and one terminal opening batch. They require explicit
adversarial-query, honest-verification, node and checkpoint bounds, and a separate ideal soundness
premise. They do not provide online query/opening exchanges, general encoded-payload or forest
security, or a complete BCS/Fiat–Shamir compiler.

## Next step

Integrate the owning bound and native adapters, then choose a concrete oracle-elimination client.
State its required opening schedule and extracted-value guarantee before generalizing the adapter.
Keep cryptographic construction/security results in VCVio and native interaction correspondence
in ArkLib.
