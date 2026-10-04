# Interaction development and legacy migration

**Status:** active. **Contact:** unassigned in this roadmap; see linked PR authors.
**Blueprint:** see the [design suite](../docs/design/README.md) for the native framework contract.

**Snapshot: October 3, 2026.** Merged baseline: ArkLib `ace55c3e29da1fc55a321378ada55ea4f7ed8790`.
Reviewed integration source: `e3a1793a45a461b42ab7b8845d6c3c8120ba0e75`, with VCVio
`6bf6c91b66dfa159342c355a4b81d65b55cb54a4`. The integration includes open PRs.
The [run record](https://github.com/quangvdao/ArkLib/blob/e52099a7e612d5fdffb5eb6ed892d40a60b15172/docs/design/interaction-security-second-night-results.md) owns exact heads,
validation and review evidence. This page owns migration gates, not another implementation schedule.

## Current direction

Develop reusable theory in `ArkLib/Interaction/` and migrate existing clients with proved
correspondences. Keep legacy clients usable until their replacements meet the gates below.
A theorem proved for a fixed-round protocol is useful progress without becoming a permanent
restriction on the framework's intended generality.

| Capability | Evidence and boundary |
|---|---|
| Native composition and Sumcheck | Merged C1–C8 foundations; see [current status](../docs/design/00-current-status.md). |
| Native local-to-global security and knowledge composition | Reviewed first-run PRs [#1259](https://github.com/Verified-zkEVM/ArkLib/pull/1259), [#1260](https://github.com/Verified-zkEVM/ArkLib/pull/1260), [#1261](https://github.com/Verified-zkEVM/ArkLib/pull/1261), [#1263](https://github.com/Verified-zkEVM/ArkLib/pull/1263), [#1264](https://github.com/Verified-zkEVM/ArkLib/pull/1264); exact statements in the [first-run record](https://github.com/quangvdao/ArkLib/blob/e52099a7e612d5fdffb5eb6ed892d40a60b15172/docs/design/interaction-security-night-results.md). |
| Randomized state restoration | Open [#1267](https://github.com/Verified-zkEVM/ArkLib/pull/1267) and [#1268](https://github.com/Verified-zkEVM/ArkLib/pull/1268): actual randomized games and knowledge bounds, with fixed finite rounds and explicit certificate assumptions. |
| Native Sumcheck restoration | Open [#1269](https://github.com/Verified-zkEVM/ArkLib/pull/1269): padded completion related to actual aborting output; `Unit` witness, not extraction of a hidden polynomial. |
| Terminal Merkle transfer | Open [#1270](https://github.com/Verified-zkEVM/ArkLib/pull/1270) and [#1271](https://github.com/Verified-zkEVM/ArkLib/pull/1271): fixed or bounded adaptive terminal query plans, with VCVio's exact shared-ROM error. Not a complete BCS compiler. |

## Gates for replacing a legacy client

1. **Specify the claim.** Match public statements, private witnesses, oracle interfaces, verifier
   access, challenge distributions, and acceptance or rejection behavior. Record any intended
   generalization instead of silently changing the legacy claim.
2. **Prove execution correspondence.** Relate the actual native protocol to the existing client,
   including private prover continuations and persistent oracle state. Output equality alone does
   not imply equality of query logs, costs, or final caches.
3. **Prove security at that boundary.** Supply completeness and the required soundness or knowledge
   theorem under explicit assumptions. Preserve extractor access and timing, local-prefix
   quantifiers, and quantitative errors. A `Unit`-witness theorem cannot replace substantive
   witness extraction.
4. **Connect concrete resources.** Identify the actual random-oracle queries and costs charged by
   the theorem. For commitment-backed clients, connect the native execution to the upstream
   security game and prove the real-to-ideal transfer.
5. **Validate and migrate dependents.** Check axioms and full builds, review the statement and its
   literature correspondence, and migrate callers. Remove legacy declarations only after their
   callers and required guarantees have replacements. No global retirement is authorized by a
   single successful client port.

These gates define readiness; they do not settle the open research choices below. A migration PR
should name the declarations it replaces and show which gates it discharges.

## Merkle ownership

VCVio owns `VCVio/CryptoFoundations/MerkleTree/`: typed inductive trees, addressed hashing,
batch verification, hash forests, checkpoint extraction, and shared-random-oracle security.
The former `Vector/` directory is not present at the pinned revision. The
[source audit](https://github.com/quangvdao/ArkLib/blob/e52099a7e612d5fdffb5eb6ed892d40a60b15172/docs/design/reviews/merkle-ownership-audit.md) records exact declarations and limits.

ArkLib owns [MerkleTerminalBatch](https://github.com/quangvdao/ArkLib/blob/e52099a7e612d5fdffb5eb6ed892d40a60b15172/ArkLib/Interaction/Oracle/MerkleTerminalBatch.lean) and
[MerkleAdaptiveTerminal](https://github.com/quangvdao/ArkLib/blob/e52099a7e612d5fdffb5eb6ed892d40a60b15172/ArkLib/Interaction/Oracle/MerkleAdaptiveTerminal.lean): native
commitment/opening protocols, declared query plans, execution correspondence, and acceptance
transfer to an ideal verifier using commitment-time extracted values. These use VCVio's bound
rather than re-proving Merkle security.

These adapters use raw digest leaves and explicit adversarial-query, honest-verification,
node and checkpoint bounds. They do not yet cover the richer encoded-payload or hash-forest APIs.

The adaptive result allows each next query choice to depend on earlier answers, with a uniform
depth bound. Openings are still submitted as a terminal batch; this is not an online exchange of
queries and openings. Ideal soundness remains a separate premise. Full oracle elimination needs
additional compiler passes, protocol correspondences, and capability-specific security proofs.

## Open questions and next priorities

First integrate the reviewed security PRs and their dependency pins, preserving their exact
statements and validation evidence. Then follow the
[implementation roadmap](../docs/design/05-roadmap.md) rather than reopening completed tasks.

- General early-rejecting or variable-length restoration needs a justified stopped-game or
  completion construction, with explicit cost accounting. The
  [guarded-restoration note](https://github.com/quangvdao/ArkLib/blob/e52099a7e612d5fdffb5eb6ed892d40a60b15172/docs/design/guarded-restoration-open-questions.md) keeps alternatives open.
- Substantive witness extraction, extractor running time, and access restrictions need explicit
  theorem targets for the next real protocol client.
- FRI and Spartan need native correspondence proofs before their legacy interfaces can retire.
- General oracle elimination, online openings, and duplex-sponge Fiat–Shamir are not implied by
  the terminal Merkle adapters or the restoration theorems.
- A fixed initial cache theorem does not justify an arbitrary correlated auxiliary-input model.
  Such a model needs its own distribution and independence conditions.

Update this page when a gate or PR status changes. Keep architectural decisions in the design
chapters, source comparisons in the research notes, and exact validation snapshots in run records.

## Upstream query-bound integration

[VCVio #824](https://github.com/Verified-zkEVM/VCVio/pull/824) supplies the expected
sum of per-key errors over distinct actual random-oracle queries, with interleaved private
randomness and arbitrary query domains. Existing per-occurrence query counts do not replace
that statement. The [integration audit](https://github.com/quangvdao/ArkLib/blob/e52099a7e612d5fdffb5eb6ed892d40a60b15172/docs/design/reviews/expected-query-integration-audit.md)
identifies an unused pure-table proof route that can be removed or separated, generic probability
lemmas to move to their owner modules, and a larger possible finite-support transport refactor.
These are proposed cleanups, not implemented changes or prerequisites imposed on the full stack.
