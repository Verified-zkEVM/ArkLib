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

AR-3A and AR-3B were additive: neither changed the legacy `OracleReduction` layer, dependency
pins, source-policy exceptions, or the axiom baseline. Each reported its validated head and
separated static inspection, Lean compilation, acceptance tests, and the full validation and axiom
gate.

The oracle-composition milestones C1–C8 that followed were delivered in #1231–#1238.
[Current status](00-current-status.md#arklib) lists each resulting module with its PR.

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
interaction-layer security results are listed in [current status](00-current-status.md).

The execution slices added concrete prefixes, logging, persistent world state, and distinct
accept/reject/fault outcomes. Their existence did not by itself establish soundness composition
in a persistent world; that theorem was proved later and is listed in
[current status](00-current-status.md), with its assumptions in
[execution and security](03-adversarial-oracle-execution.md).

## Dependency lineage

PolyFun supplied cursors ([#43](https://github.com/Verified-zkEVM/PolyFun/pull/43)),
cursor restriction ([#58](https://github.com/Verified-zkEVM/PolyFun/pull/58)), append decomposition
([#59](https://github.com/Verified-zkEVM/PolyFun/pull/59)), the `TypeTree` rename
([#64](https://github.com/Verified-zkEVM/PolyFun/pull/64)), and dependent chains
([#66](https://github.com/Verified-zkEVM/PolyFun/pull/66)). VCVio's resumable runtime and
failure-to-return observation supported AR-9A and AR-9B. These are completed dependencies,
not proposed upstream PRs.

The alignment baseline was Lean 4.33.1 with VCVio `f9dc47d9` and PolyFun `c0c92369`. The
dependencies then advanced through the VCVio `Runtime` and `WithFailure` additions used by #884
and the Lean 4.34 native-measure upgrade (#903, #913); the
[native measure ledger](native-measure-ledger.md) records that conversion.

The original slice-by-slice goals and acceptance plans remain in Git history. New implementation
work should use the current contracts and roadmap rather than repeat that completed sequence.
