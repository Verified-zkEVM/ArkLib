# ArkLib typed interaction and oracle-reduction design

**Initial design:** 2026-07-13. **Last source audit:** 2026-08-29.
**Status:** normative architecture with a staged implementation.

ArkLib's current `OracleReduction` layer made ambitious formalizations possible, but its central
representation no longer matches the theory we need to prove. Protocol interaction is indexed by a
fixed round count, output oracles are eventually materialized into families, and composition crosses
heterogeneous transports whose security meaning is difficult to state. Meanwhile, PolyFun and
VCVio now provide most of the typed structural and probabilistic substrate that the replacement
originally had to invent.

This suite describes the replacement: reductions over typed interactions, source-scoped virtual
oracles, claims that close only through the run that produced them, and an oracle-elimination
compiler that turns ideal guarantees into explicit cryptographic obligations.

## How to use this suite

Start with [`00-current-status.md`](00-current-status.md). It is the operational source of truth for
the supported dependency revisions, available APIs, missing foundations, and next ArkLib slices.

The other pages have narrower jobs:

| Document | Purpose | Stability |
|---|---|---|
| [`00-current-status.md`](00-current-status.md) | Current baseline, capability status, and immediate work | operational |
| [`00-end-state.md`](00-end-state.md) | The ambition and coverage contract | directional |
| [`01-foundations.md`](01-foundations.md) | Library ownership and the current cross-library contract | normative |
| [`01a-foundation-pr-plan.md`](01a-foundation-pr-plan.md) | Live dependency gaps and ArkLib PR slices | operational |
| [`01b-type-tree-rename-cutover.md`](01b-type-tree-rename-cutover.md) | Landed generic names and planned ArkLib oracle names | normative |
| [`02-oracle-reduction-core.md`](02-oracle-reduction-core.md) | Claims, virtual oracles, closing, and composition | normative |
| [`03-adversarial-oracle-execution.md`](03-adversarial-oracle-execution.md) | Worlds, traces, games, state restoration, extractors, and budgets | normative core, fluid periphery |
| [`04-oracle-elimination-compiler.md`](04-oracle-elimination-compiler.md) | Compiler passes, backend capabilities, and guarantee transport | normative interfaces, fluid internals |
| [`05-roadmap.md`](05-roadmap.md) | Implementation phases, gates, and parallel upstream work | operational |

Read them in that order for a full architecture review. To start implementation, read `00`, the
relevant ArkLib slice in `01a`, and then the owning normative page.

## Status vocabulary

The suite uses three deliberately different kinds of claim:

- **Available at the supported pin** means the named declaration or law exists in the exact
  PolyFun or VCVio revision recorded in `00`.
- **Missing or client-gated** means no reusable supported API currently supplies the required
  boundary. A client-gated item is added only when a concrete consumer demonstrates the need.
- **Target architecture** describes the intended ArkLib contract. Record signatures remain
  provisional until the named acceptance client elaborates.

Historical PR proposals are not mixed into the live plan. The original Sol/Fable audits, proposed
PolyFun and VCVio slices, and broad ArkLib prototype remain on
[`archive/oracle-reduction-v2-pre-split`](https://github.com/Verified-zkEVM/ArkLib/tree/archive/oracle-reduction-v2-pre-split/docs/design/archive)
and in Git history. They are evidence and a source bank, not current implementation instructions.

## The design in one paragraph

An oracle reduction's output claim is a public statement plus source-scoped virtual oracles: typed
query programs over declared backing resources. Their extensional meaning is obtained under the
handler produced by the same execution. Relations consume closed claims and never see derivation
history. Composition is typed-tree append plus handler substitution and explicit context
morphisms. Extensional source semantics stay separate from resource identity, origin, aliasing,
and guarantees. PolyFun owns domain-independent interaction structure; VCVio owns oracle and
probability semantics, instrumentation, resources, and generic cryptographic games; ArkLib owns
protocol claims, security notions, backend adapters, and compilers. Compilation factors into
represent, lower, transport, and Fiat–Shamir passes whose invariant is **guarantee transport**:
every ideal oracle guarantee becomes an explicit commit, open, or link obligation.

## Resolved decisions

- **D1 — Guarantees travel with ideal oracle slots.** A slot may carry a reified promise such as a
  degree bound. Compilation must discharge that promise through an explicit backend obligation;
  it cannot silently erase it.
- **D2 — The design is split by concern.** Core claims, adversarial execution, and compilation are
  separate documents because they have different dependencies and acceptance evidence.
- **D3 — The first semantic milestone is small.** A single-round Sumcheck completeness theorem
  through run-derived closing precedes broad protocol migration.
- **D4 — Exact quantitative theorems are the target.** Error, query, and running-time transforms
  remain explicit from the first security-bearing slice.
- **D5 — State restoration precedes the compiler.** The compiler must consume a proved execution
  and trace calculus, not create one incidentally.
- **D6 — Interaction names describe what the objects are.** PolyFun's generic carrier is
  `Interaction.TypeTree` and its complete branch is `TypeTree.Path`. ArkLib's oracle refinement is
  `Interaction.Oracle.TypeTree`, with `BranchPath` for structural choices and `ExecutionPath` for
  concrete messages. The generic rename has landed; the ArkLib refinement remains an implementation
  contract.

## Ground rules

1. Extensional behavior is the relation carrier; derivation plans are not relation inputs.
2. Closing forgets presentation but preserves every resource needed to interpret the claim.
3. Operational machinery does not outrun theorem support.
4. Security notions expose quantifier order, observations, budgets, and failure boundaries.
5. A cryptographic capability is a complete game and reduction contract, never a bare `Prop` name.
6. Current PolyFun and VCVio APIs are reused at their owning layer; ArkLib does not shadow them.

Stable today are the architectural invariants: extensional closed claims, source-scoped virtual
programs, run-derived closing, explicit aliasing, guarantee transport, and the three-library
dependency direction. Lean record layouts such as `ClaimWith`, `SourceCtx`, `ResourceSchema`,
`CoreRun`, and the later execution artifact remain provisional until their acceptance clients land.
