# Sumcheck and Spartan

**Status:** active. **Last checked:** October 3, 2026.
**Merged source:** ArkLib `ace55c3e29da1fc55a321378ada55ea4f7ed8790`.
**Contact:** unassigned in this roadmap; use the linked PR authors for specific changes.
**Blueprint:** see [proof-system chapters](../../blueprint/src/proof_systems).

## Where things stand

[Native Sumcheck](../../ArkLib/ProofSystem/Sumcheck/Interaction) has full ordinary soundness and
honest completeness. The computable verifier and honest prover are merged in
[#1242](https://github.com/Verified-zkEVM/ArkLib/pull/1242) and
[#1243](https://github.com/Verified-zkEVM/ArkLib/pull/1243). The general finite-enumeration prover
is computable; this alone does not prove efficient multilinear performance.
[Spartan](../../ArkLib/ProofSystem/Spartan) still needs a native interaction migration.

## Active branches and PRs

- [#1261](https://github.com/Verified-zkEVM/ArkLib/pull/1261) adds native local-to-global soundness
  and its Sumcheck instance.
- [#1269](https://github.com/Verified-zkEVM/ArkLib/pull/1269) adds Sumcheck restoration soundness;
  it depends on the randomized game and knowledge theory in
  [#1267](https://github.com/Verified-zkEVM/ArkLib/pull/1267) and
  [#1268](https://github.com/Verified-zkEVM/ArkLib/pull/1268).

These are open-PR results, not merged capabilities. PR authors and review discussion are linked
on the PR pages. The [interaction roadmap](../../docs/design/05-roadmap.md) owns implementation order.

## Open gaps

The native oracle Sumcheck relation has a `Unit` witness. Recovery of a hidden polynomial or
committed witness needs a substantive witness relation and a new extraction proof. Optimized
message/update algorithms need correspondence and cost proofs. Legacy security claims need
explicit correspondence and axiom checks before replacement.

## Next step

Integrate the reviewed security stack, then select a concrete Spartan or further Sumcheck client.
Specify its statement, oracle interface, witness, execution correspondence and quantitative
security target before porting it. Apply the [migration gates](../interaction-migration.md).
