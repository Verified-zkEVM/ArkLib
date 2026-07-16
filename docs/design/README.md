# ArkLib Oracle Reduction Design Suite (v2)

**Date:** 2026-07-13. **Status:** normative architecture, pre-implementation.
**Provenance:** the original Sol/Fable adversarial and literature audits plus a fresh source-level
audit of current ArkLib, VCVio, and PolyFun default branches. The raw audit history remains on the
preserved [`archive/oracle-reduction-v2-pre-split`](https://github.com/Verified-zkEVM/ArkLib/tree/archive/oracle-reduction-v2-pre-split/docs/design/archive)
branch; the current-tree findings are incorporated into `00`, `01`, and `01a`.

## The design in one paragraph

An oracle reduction's output claim is a **statement plus a source-scoped virtual oracle** — a typed
query program over declared backing resources whose extensional meaning is derived under the
handler produced by the *same* execution. Relations consume **closed claims** and never see
derivation history. Composition is handler substitution with explicit context morphisms. A separate
resource schema tracks real identity, origin, aliasing, and guarantees; a later backend assignment
is indexed by that schema. Generic
domain-independent cursor/run/trace/transducer algebra lives in PolyFun; VCVio supplies oracle/probability worlds,
instrumentation, resources, and games; ArkLib supplies protocol claims, security notions, and
compilers. Compilation factors into represent/lower/transport/Fiat–Shamir passes whose invariant is
**guarantee transport**: ideal slot guarantees become explicit commit/open/link obligations.

## Documents

| Doc | Contents | Stability |
|---|---|---|
| [`00-end-state.md`](00-end-state.md) | The ambition: all of SNARKs, and what we write down now to enable it | directional |
| [`01-foundations.md`](01-foundations.md) | Ownership by parametricity; current inventory; precise semantic deltas | **normative** |
| [`01a-foundation-pr-plan.md`](01a-foundation-pr-plan.md) | Exact PolyFun, VCVio, and ArkLib PR slices and release train | operational |
| [`01b-type-tree-rename-cutover.md`](01b-type-tree-rename-cutover.md) | Complete `TypeTree` / oracle branch-and-execution-path naming cutover | **normative** |
| [`02-oracle-reduction-core.md`](02-oracle-reduction-core.md) | Claims, virtual oracles, closing, composition, core security (Δ side) | **normative** |
| [`03-adversarial-oracle-execution.md`](03-adversarial-oracle-execution.md) | Worlds, traces, transducers, games, state restoration, extractors, budgets (Γ side) | normative core, fluid periphery |
| [`04-oracle-elimination-compiler.md`](04-oracle-elimination-compiler.md) | The compiler passes, commitment capability records, BCS/Nova, guarantee transport | normative interfaces, fluid internals |
| [`05-roadmap.md`](05-roadmap.md) | Phases, slices, gates, parallel tracks, risks, re-direction principles | fluid by design |

Reading order for a new contributor: 00 → 01 → 01a overview → 01b → 02 → 03 → 04 → 05.

## Resolved decisions (log)

- **D1 — Guarantees travel with oracles in the ideal model.** Prover-sent oracle message types MAY be refined (e.g. `degree ≤ d` polynomials). This is not a violation of "validity lives in relations": in the ideal model the verifier cannot inspect the object, so the *type* of the oracle slot is the interface guarantee — exactly as in the literature, where an IOP verifier is handed oracles *promised* to be codewords or bounded-degree polynomials, with soundness stated against that promise. Compilation is what takes guarantees "off the wire": the oracle-elimination compiler transfers each type-level guarantee into a commitment-scheme obligation (commit/open-phase degree or proximity enforcement). See `02` §3.3 and `04` §2 (GuaranteeTransport, with the reified `OracleGuarantee` descriptor). Input oracles in soundness games remain quantified as arbitrary behavior *for their interface*; the interface itself may encode the promise.
- **D2 — Three-document split**, plus foundations, end-state, and roadmap; recorded in ArkLib history on branch `design/oracle-reduction-v2`.
- **D3 — First milestone** is the minimum-viable slice (single-round sumcheck completeness through claim-closing), before the three-slice triple. See `05` Phase 2.
- **D4 — Exact quantitative theorems are the target.** Bounds must match or beat Chiesa–Yogev. The budget/error-functional algebra is therefore core (Γ side), not deferred; proof *strategies* may be refactored when consolidation is found.
- **D5 — State restoration and world traces are scheduled before the compiler**, in parallel with the core security cutover.
- **D6 — True-sight interaction names.** The generic sequential carrier is
  `Interaction.TypeTree`, with `TypeTree.Path` as its complete branch. Its oracle-reduction
  refinement is `Interaction.Oracle.TypeTree`, with `BranchPath` for structural continuation
  choices and `ExecutionPath` for concrete runtime messages. At an oracle node the message remains
  `x : X`; only the branch index is `PUnit`. `Protocol` is reserved for the decorated bundle. The
  cutover is complete, without historical aliases; see `01b`.

## Ground rules carried forward from the audits

1. Behavior is the unique extensional relation carrier; no quotients; two equivalences (`≈sem`, `≈op`) never conflated.
2. Closing forgets the presentation, not needed resources; needed resources are exported slots.
3. Operational machinery never outruns theorem support (the `main`-branch failure mode).
4. Security definitions are never weakened without an explicit, documented decision; quantifier order is part of a notion's name.
5. Every capability/property is a concrete game record (experiment, phases, trace inputs, budgets, error/time functions) — never a bare `Prop` name.

**Interface stability legend.** Stable today are architectural invariants (extensional closed claims,
source-scoped virtual programs, runner-derived closing, explicit aliasing, guarantee transport, and the
three-library dependency direction). Lean record signatures are provisional until their `01a`
client gates pass; in particular `ClaimWith`, `SourceCtx`, `ResourceSchema`, `RunCore`, and
`ExecutionArtifact` are signature sketches rather than frozen elaborated APIs. Compiler planning
types (`TypedPlan`, `TranscriptTransform`, `FiniteConsumer`, `CompilePolicy`) remain fluid until
their phase lands.
