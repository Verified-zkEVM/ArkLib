# Interaction and oracle-reduction design

This suite explains how ArkLib's interaction layer (`ArkLib/Interaction/`) represents interactive
protocols, states their security, and plans the remaining formalization. It is written for
readers familiar with provers, verifiers, oracles, and soundness.

The interaction layer is meant to replace the legacy layer (`ArkLib/OracleReduction/`). The
[README](../../README.md#two-layers) gives an overview of the two layers,
[Limitations of the legacy layer](legacy-layer-limitations.md) explains why the replacement is
needed, and the public [roadmap](../../ROADMAP.md#priority-replace-the-legacy-layer) holds the migration
plan.

A protocol is an interaction tree with prover and verifier strategies. The prover's continuation
keeps its private memory. An oracle reduction returns a statement and an oracle interface: the
next reduction can query that interface without seeing the underlying prover messages. Security
relates the input claim to this output claim. When execution uses a persistent oracle, the same
world state and query history continue across the boundary.

## Start here

| Your question | Read |
|---|---|
| What is implemented and proved on main? | [Current status](00-current-status.md) |
| What should we implement next, and how will we check it? | [Roadmap](05-roadmap.md) |
| What does the full framework aim to cover? | [End state](00-end-state.md) |
| What does an oracle reduction return, and how do reductions compose? | [Claims, closing, and composition](02-oracle-reduction-core.md) |
| How do private memory, oracle state, and probability enter security? | [Execution and security](03-adversarial-oracle-execution.md) |

For a full design review, read the end state, foundations, access contract, core, execution, and
compiler chapters below; finish with the roadmap. File numbers identify chapters, not a second
implementation schedule.

## Chapters and their responsibilities

| Page | Owns |
|---|---|
| [Current status](00-current-status.md) | Supported dependency baseline, available APIs, proved results, and remaining proof gaps |
| [End state](00-end-state.md) | Intended coverage and what counts as completing the framework |
| [Limitations of the legacy layer](legacy-layer-limitations.md) | What the legacy layer cannot express or prove directly, and what the interaction layer does instead |
| [Foundations](01-foundations.md) | Division of responsibility between PolyFun, VCVio, and ArkLib |
| [Foundation implementation record](01a-foundation-pr-plan.md) | Historical AR slice identifiers and the PRs that delivered them |
| [Type-tree naming](01b-type-tree-rename-cutover.md) | The completed rename and correspondence between generic and oracle trees |
| [Access and execution contract](01c-access-execution-contract.md) | What the verifier can observe and query at each protocol position |
| [Claims, closing, and composition](02-oracle-reduction-core.md) | Output interfaces, their interpretation, and execution conditions for composition |
| [Execution and security](03-adversarial-oracle-execution.md) | Persistent worlds, security events, probability premises, extraction, and costs |
| [Extractor efficiency](03a-extractor-efficiency.md) | The implemented unbounded-game and measured-operation contracts for named extractors, the obligations of each extractor-bearing notion, and FRI and Toy requirements |
| [Extractor execution backends](03b-extractor-execution.md) | Proposed complete execution bounds, backend requirements, and uniform families for extractors |
| [Oracle-elimination compiler](04-oracle-elimination-compiler.md) | Backend obligations and how compilation preserves oracle guarantees |
| [Roadmap](05-roadmap.md) | Remaining interaction-layer work, dependencies, acceptance checks, and issue links |

Historical records keep the state of a finished campaign; their pins and status columns describe
the date they record.

| Page | Records |
|---|---|
| [Native measure ledger](native-measure-ledger.md) | The conversion to VCVio's native measure semantics (completed 2026-09-21) |
| [Reed–Solomon port](reed-solomon-port.md) | The port of the beyond-Johnson Reed–Solomon formalization: packages, destinations, deferrals |
| [Reed–Solomon port correspondence](reed-solomon-port-correspondence.md) | Source-to-destination declaration map of that port, as merged |

The [naming guide](../wiki/interaction-naming.md) governs declaration names, docstrings, and
explanations. State the mathematical result and its assumptions before implementation details.
Use familiar cryptographic terms, and explain additional terms where they first matter.

## How to maintain this suite

Record a design decision in its owning architecture chapter. Record a proposed PR and its
acceptance check in the roadmap. Update current status only when the corresponding API or theorem
lands. [Issue #1](https://github.com/Verified-zkEVM/ArkLib/issues/1) links the work items; their issues
record progress and implementation PRs. Do not add another parallel plan or repeat an issue's
progress log across chapters.

The pages distinguish three kinds of statement:

- **Implemented or proved:** supported by the source at the dependency pins in `lake-manifest.json`.
- **Planned:** an intended theorem or API, with its implementation work in the roadmap.
- **Conditional or deferred:** work needing a concrete client or a later milestone.

Architecture chapters specify intended contracts; a design signature is not evidence that the
corresponding declaration exists. Consult current status for the implemented boundary.

Earlier audits and prototypes remain on
[the preserved design archive](https://github.com/Verified-zkEVM/ArkLib/tree/archive/oracle-reduction-v2-pre-split/docs/design/archive)
and in Git history. They are historical evidence, not current implementation instructions.
