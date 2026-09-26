# Foundation implementation record

AR-0 through AR-10B are the completed foundation sequence. This page preserves those identifiers
and their implementation PRs so older discussions remain readable. It is historical reference;
[the roadmap](05-roadmap.md) owns all remaining work, including the Merkle adapter formerly called
AR-11. [Current status](00-current-status.md) records the supported APIs and later security results.

## Completed foundation slices

| Slice | Status | PR |
|---|---|---|
| AR-0 alignment | landed | #811 |
| AR-1 plain reductions | landed | #851 |
| AR-2A oracle type trees | landed | #852 |
| AR-2B decorations | landed | #853 |
| AR-3A accumulated access | landed | #861 |
| AR-3B oracle execution | landed | #862 |
| AR-4A sources and routing | landed | #863 |
| AR-4B named contexts | landed | #864 |
| AR-5 virtual substitution | landed | #869 |
| AR-6A open and closed claims | landed | #870 |
| AR-6B core run and closing | landed | #871 |
| AR-7 one-round Sumcheck | landed | #872 |
| AR-8 legacy correspondence | landed; verifier correspondence is honest-only | #874 |
| AR-9A logged world-backed execution | landed | #884 |
| AR-9B terminal outcomes | landed | #886 |
| AR-10A structural full prefixes | landed | #880 |
| AR-10B prefixes and execution artifacts | landed | #889 |

## What this sequence established

The structural slices introduced typed oracle interactions, public branch paths, concrete execution
paths, and oracle access derived from earlier messages. The verifier can query an oracle payload
through its interface without inspecting the payload itself. These obligations now belong to the
[access and execution contract](01c-access-execution-contract.md).

The source and claim slices introduced virtual oracle programs, named resources, and interpretation
of an output claim using the resources returned by its execution. The common origin of the claim
and resources follows from the runner, not merely from constructing a `CoreRun` record. The
[core design](02-oracle-reduction-core.md) owns these contracts and their composition conditions.

The first Sumcheck slice proved one-round honest completeness. The legacy bridge proved both
relation directions, but verifier correspondence is honest-execution only. Later multi-round and
native security results are listed in [current status](00-current-status.md).

The execution slices added concrete prefixes, logging, persistent world state, and distinct
accept/reject/fault outcomes. Their existence does not establish general soundness composition in
a persistent world. That theorem is part of the active roadmap; its intended assumptions belong
to [execution and security](03-adversarial-oracle-execution.md).

## Dependency lineage

PolyFun supplied cursors ([#43](https://github.com/Verified-zkEVM/PolyFun/pull/43)),
cursor restriction ([#58](https://github.com/Verified-zkEVM/PolyFun/pull/58)), append decomposition
([#59](https://github.com/Verified-zkEVM/PolyFun/pull/59)), the `TypeTree` rename
([#64](https://github.com/Verified-zkEVM/PolyFun/pull/64)), and dependent chains
([#66](https://github.com/Verified-zkEVM/PolyFun/pull/66)). VCVio's resumable runtime and
failure-to-return observation supported AR-9A and AR-9B. These are completed dependencies,
not proposed upstream PRs.

The original slice-by-slice goals and acceptance plans remain in Git history. New implementation
work should use the current contracts and roadmap rather than repeat that completed sequence.
