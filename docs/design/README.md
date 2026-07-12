# ArkLib Oracle Reduction Design Suite (v2)

**Date:** 2026-07-12. **Status:** normative design, pre-implementation.
**Provenance:** four adversarial audit rounds (GPT 5.6 Sol at high/xhigh; Claude Fable 5 synthesis), a very-thorough autopsy of the retired `OracleReduction/` design on `main`, a 35-requirement literature catalog, and a per-theorem coverage audit against Chiesa–Yogev, *Building Cryptographic Proofs from Hash Functions* (2024). Full history in [`archive/`](archive/).

## The design in one paragraph

An oracle reduction's output claim is a **statement plus a source-scoped virtual oracle** — a typed query program over declared backing resources (input oracles, setup oracles, prover-sent oracle messages), whose extensional meaning is derived by interpretation under the handler produced by the *same* execution. Relations consume **closed claims** (statement + behavior) and never see derivation history. Composition is **handler substitution** with explicit context morphisms. Concrete data, provenance metadata, commitments, and cost are **optional strengthenings**, never the canonical carrier. Security games, extractors, and compilers live on top of a shared semantics of **adversarial oracle execution**: persistent worlds, identity-tagged query traces, trace transducers, typed budgets, and error/time functionals. Compilation to real argument systems factors into passes (represent, lower, transport, Fiat–Shamir) whose invariant is **guarantee transport**: ideal-model guarantees carried by oracle types become cryptographic obligations of commitment schemes.

## Documents

| Doc | Contents | Stability |
|---|---|---|
| [`00-end-state.md`](00-end-state.md) | The ambition: all of SNARKs, and what we write down now to enable it | directional |
| [`01-foundations.md`](01-foundations.md) | The sharp three-library split; named foundation requirements on PolyFun and VCVio | **normative** |
| [`02-oracle-reduction-core.md`](02-oracle-reduction-core.md) | Claims, virtual oracles, closing, composition, core security (Δ side) | **normative** |
| [`03-adversarial-oracle-execution.md`](03-adversarial-oracle-execution.md) | Worlds, traces, transducers, games, state restoration, extractors, budgets (Γ side) | normative core, fluid periphery |
| [`04-oracle-elimination-compiler.md`](04-oracle-elimination-compiler.md) | The compiler passes, commitment capability records, BCS/Nova, guarantee transport | normative interfaces, fluid internals |
| [`05-roadmap.md`](05-roadmap.md) | Phases, slices, gates, parallel tracks, risks, re-direction principles | fluid by design |

Reading order for a new contributor: 00 → 02 §1–2 → 01 → 02 rest → 03 → 04 → 05.

## Resolved decisions (log)

- **D1 — Guarantees travel with oracles in the ideal model.** Prover-sent oracle message types MAY be refined (e.g. `degree ≤ d` polynomials). This is not a violation of "validity lives in relations": in the ideal model the verifier cannot inspect the object, so the *type* of the oracle slot is the interface guarantee — exactly as in the literature, where an IOP verifier is handed oracles *promised* to be codewords or bounded-degree polynomials, with soundness stated against that promise. Compilation is what takes guarantees "off the wire": the oracle-elimination compiler transfers each type-level guarantee into a commitment-scheme obligation (commit/open-phase degree or proximity enforcement). See `02` §3.4 and `04` §2 (GuaranteeTransport). Input oracles in soundness games remain quantified as arbitrary behavior *for their interface*; the interface itself may encode the promise.
- **D2 — Three-document split**, plus foundations, end-state, and roadmap; recorded in ArkLib history on branch `design/oracle-reduction-v2`.
- **D3 — First milestone** is the minimum-viable slice (single-round sumcheck completeness through claim-closing), before the three-slice triple. See `05` Phase 2.
- **D4 — Exact quantitative theorems are the target.** Bounds must match or beat Chiesa–Yogev. The budget/error-functional algebra is therefore core (Γ side), not deferred; proof *strategies* may be refactored when consolidation is found.
- **D5 — State restoration and world traces are scheduled before the compiler**, in parallel with the core security cutover.

## Ground rules carried forward from the audits

1. Behavior is the unique extensional relation carrier; no quotients; two equivalences (`≈sem`, `≈op`) never conflated.
2. Closing forgets the presentation, not needed resources; needed resources are exported slots.
3. Operational machinery never outruns theorem support (the `main`-branch failure mode).
4. Security definitions are never weakened without an explicit, documented decision; quantifier order is part of a notion's name.
5. Every capability/property is a concrete game record (experiment, phases, trace inputs, budgets, error/time functions) — never a bare `Prop` name.
