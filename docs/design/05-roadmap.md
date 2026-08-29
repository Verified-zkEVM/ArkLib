# 05 — Implementation Roadmap

**Fluid by design.** Phases have exit gates, decision points, and fallbacks; the course is charted, not forced. Tracks run in parallel where dependencies allow. Effort words: S ≈ days, M ≈ 1–3 weeks, L ≈ 1–2 months, XL ≈ open-ended program.

## 0. Standing rules

- Nothing security-shaped changes without its bridge/comparison theorem (per protocol, not global — there is no generic legacy bridge).
- The legacy security namespace lives until the last consumer is bridged; new work in `Security.V2`-style parallel namespaces. **No flag days.**
- Foundation gaps found mid-phase are routed by `01`'s parametricity rule and added as explicit PR
  dependencies in `01a`. Temporary adapters need an upstream issue, no adapter-only theorems, and a
  deletion test.
- The design branch is documentation/prototype provenance. All implementation PRs start from the
  current default branch; there is no bulk merge of the prototype tree.
- `grep sorry ArkLib/Interaction/` budget: ≤ 1 (the pre-existing ClaimTree lemma) through Phase 4.
- Every phase ends with a short written retro appended to this file: what redirected, which interfaces moved.

## Tracks

- **T-F (Foundation train):** the exact PF/VCV PRs in `01a`, with existing APIs consolidated rather
  than rebuilt. [L, parallel where the dependency graph permits]
- **T-C (Core, ArkLib Δ):** `02` objects and laws.
- **T-X (Execution/Security, ArkLib Γ):** `03` objects and games.
- **T-K (Compiler):** `04`.
- **T-P (Protocols):** ports exercising everything above.

## Phase 0 — Release-train alignment [M]

The common toolchain is now Lean 4.33.1. The alignment PR pins ArkLib to VCVio
`f9dc47d9dacfc5cb51dae9f92f1e34cb5ce2cc24`; VCVio selects PolyFun
`c0c923693fc827a41d17116579a0c16ed4873b19`. ArkLib does not override that transitive revision.
The same PR refreshes this design suite because the supported API baseline and the design status
must agree.

**Gate:** a full ArkLib validation run; exactly one resolved PolyFun revision; no ArkLib override
inconsistent with VCVio; [`00-current-status.md`](00-current-status.md) identifies landed and
missing foundations without presenting target interfaces as implemented.

## Phase 1 — Elaborating substrate (T-C; AR-1 through AR-6B) [L]

Port the plain reduction kernel and oracle syntax/observation split onto current PolyFun
`TypeTree`, node contexts, strategies, and runners. Then add concrete message access, resource
schema/context morphisms, virtual substitution, and claims/runner-derived closing as separate AR
PRs. Reuse the archived prototype as a source bank, not a merge base. Adapt the current
`OracleOutputSimulation` surface into the new virtual-oracle representation so existing clients can
migrate without a flag day. `SourceCtx` stays extensional; resource identity/origin/guarantee
metadata lives in `ResourceSchema`.
**Gate:** each PR's local laws and client tests; zero new sorries; legacy untouched; record signatures
remain provisional until the sumcheck slice.

## Phase 2 — Minimum viable slice (AR-7/AR-8) [M] ← D3

**Programmatic single-round sumcheck perfect completeness through `closeWith`**: query-derived scalar `stmt`, passthrough oracle slot with its degree-bounded message type (D1 exercised), honest-data realization, real `TerminalOutput`. No Spartan, no FRI, no soundness, no associativity.
**Gate:** the theorem, sorry-free, with the D1 pattern documented in code.
**Decision point:** if `ClaimWith` indexing fights elaboration here, fall back to three concrete records + morphisms (the unification is a convenience, not a wall).

## Phase 3 — Two more semantic slices and composition [L; cost needs VCV-5A/B]

Build on AR-4A/B and AR-5 rather than adding the substitution algebra here. Add terminal-routing simplification
in programmatic composition and the Spartan/FRI slices. Semantic laws use extensional equivalence;
operational trace/cost preservation waits for VCV-3/5A/5B and the ArkLib execution-artifact adapter.
Land AR-10A and exercise PF-3 cursor/append decomposition in the two-round composite; Γ trace
alignment remains AR-10B in Phase 4.
**Gate:** boundary-as-`subst` demonstrated; constructors land with `eval` lemmas.
**Fallback:** if `retargetMonads`-as-`subst`-action fights Lean, keep it hand-written; the claim algebra carries the proofs regardless.

## Phase 4 — Execution artifact + outcomes + ordinary security [L]

Needs AR-9A/9B/10B and the still-missing generic runtime-artifact and outcome boundaries. PF-1/2/3
and substantial VCVio responder/resource foundations have landed; see `00-current-status.md` for
the exact reusable APIs.

Add or upstream the VCVio runner-produced artifact and outcome boundary; add cursor-backed reachable
prefixes;
`ClaimSchema`/`Problem`; closed-claim relations; completeness and **ordinary-soundness composition**
(output admissibility + conditional suffix theorem) in a parallel security namespace; per-protocol
bridges for the three slices. Use existing VCVio resource/cost carriers and the VCV-10 reduction
calculus rather than new ledger/characteristics types.
**Gate:** slice bridges proved two-way; soundness composition theorem sorry-free; no legacy consumer broken.
**Risk:** this is the semantic heart; if a bridge fails, *stop and diagnose the quantifier* — that is the audit's designed tripwire, not an obstacle.

## Phase 5 — State restoration + trace calculus [L] ← D5: before compiler

Needs PF-5, VCV-4/6/7A/7B/8A/8B/8C/10, and Phase 4. PF-4 is added only if a
PolyFun operational-machine adapter becomes an actual client.

Salted SR games and traces; ArkLib segmentation/backtracking/SR adapters over PolyFun transducers and
VCVio resource certificates; straightline and rewinding SRKS; extractor taxonomy; constrained
execution trees over `FreeM.Cursor`; `CY*` vs `Ark*` RBR notions and bridges. Dynamic programming and
conditioned ROM bounds come from the repaired VCVio APIs, not theorem-local worlds.
**Gate:** the full bridge set — `RBR→SR`; `ArkRBRK → CYRBRK → {ordinary KS, SRKS}`; single- and multi-round special soundness → ordinary KS and SRKS, each under explicit replay, entropy, budget, and error hypotheses; the KS-composition non-theorem documented with its three valid strengthenings.

## Phase 6 — Compiler, staged (T-K, needs Phases 3+5 and accepted backend adapters) [XL]

Order (**interfaces before passes**): capability/game adapters + guarantee descriptors/backend
assignment → typed read plans → represent/lower/transport passes → concrete adapters. The Merkle
adapter must consume VCVio's existing primitive extraction theorem rather than restating its game;
Pedersen uses the Nova conformance slice. Then iBCS transfer, Fiat–Shamir, exact BCS soundness, and
BCS-KS through the extractor pipeline.
**Gate per stage:** its row of the `04` security matrix plus the cross-library Checkpoint D in `01a`.
Guarantee-transport obligations are surfaced by backend assignment from the first stage.

## Phase 7+ — Widening [XL, prioritize by demand]

ZK/WI (programmable worlds, salting, local-view simulators); preprocessing/holography (five-phase games); parallel/shared-prefix combinators; **computational backends** (needs VCV-10): curve (KZG/Pedersen/IPA capability records — Nova generalizes) and lattice, with a gate: *one DLOG/AGM- or SIS-based backend theorem proved end-to-end through a `SecurityReduction`*; indifferentiability; full L6 refinement obligations from `00`; reduction-level associativity via gated PF-6B only if a client demands it.

## Dependency sketch

```
PF/VCV PR train → AR-0 → Phase 1 → 2 → 3
                       ↘ AR-9A/B, AR-10A/B → Phase 4 → 5 → 6 → 7+
                         (protocol slices feed every freeze gate)
```

## Risk register (top five)

1. **Phase-4 bridge failure** → designed tripwire; diagnose, don't route around.
2. **Runtime-boundary slippage** → typed claims and the first protocol slice proceed on the landed
   PolyFun/VCVio substrate; general security waits for the runner artifact and outcome boundary.
3. **`ClaimWith`/dependent-index friction** → Phase-2 fallback ready.
4. **Trace-slicing proof burden** (list-partition obligations everywhere) → use VCV-1 trace regions
   and PF-5/VCV-4 transducers; resist theorem-local plumbing.
5. **Scope gravity toward the compiler** → Phases 4–5 are the value; the compiler without them is the `main`-branch failure mode again.

## Re-direction principles

When implementation contradicts this plan: (a) accepted interfaces move only with a decision-log
entry; unvalidated signature sketches remain fluid; (b) consolidations that delete parallel objects
are favored; (c) if two phases want the same structure, route it by `01`'s parametricity rule.
