# 05 — Implementation Roadmap

**Fluid by design.** Phases have exit gates, decision points, and fallbacks; the course is charted, not forced. Tracks run in parallel where dependencies allow. Effort words: S ≈ days, M ≈ 1–3 weeks, L ≈ 1–2 months, XL ≈ open-ended program.

## 0. Standing rules

- Nothing security-shaped changes without its bridge/comparison theorem (per protocol, not global — there is no generic legacy bridge).
- The legacy security namespace lives until the last consumer is bridged; new work in `Security.V2`-style parallel namespaces. **No flag days.**
- Foundation gaps found mid-phase are filed upstream (PolyFun/VCVio) and stubbed as `FOUNDATION-DEBT(Vn/Pn)` with a migration obligation.
- `grep sorry ArkLib/Interaction/` budget: ≤ 1 (the pre-existing ClaimTree lemma) through Phase 4.
- Every phase ends with a short written retro appended to this file: what redirected, which interfaces moved.

## Tracks

- **T-F (Foundation, in PolyFun/VCVio):** V1–V9, P1–P3 per `01`. Owner-able independently; gated by `01` §2.3 acceptance tests. [L, parallel from day one]
- **T-C (Core, ArkLib Δ):** `02` objects and laws.
- **T-X (Execution/Security, ArkLib Γ):** `03` objects and games.
- **T-K (Compiler):** `04`.
- **T-P (Protocols):** ports exercising everything above.

## Phase 1 — Elaborating substrate (T-C) [M]

New `Interaction/Oracle/Virtual.lean` (+ neighbors): `OracleFamily` (+ explicit-instance `Behavior`), `SourceCtx`, `VirtualOracle`+`eval`, `ClaimWith` (open/closed/data), `closeWith`, `OracleMessagesAt`+`answerAt`+full-transcript conversion, honest-data embedding, `simulateQ_*` lemma home. Prototype claim packaging on `Verifier.TerminalOutput` (`simulate` = projection).
**Gate:** compiles green; zero new sorries; legacy untouched.

## Phase 2 — Minimum viable slice (T-C/T-P) [M] ← D3

**Programmatic single-round sumcheck perfect completeness through `closeWith`**: query-derived scalar `stmt`, passthrough oracle slot with its degree-bounded message type (D1 exercised), honest-data realization, real `TerminalOutput`. No Spartan, no FRI, no soundness, no associativity.
**Gate:** the theorem, sorry-free, with the D1 pattern documented in code.
**Decision point:** if `ClaimWith` indexing fights elaboration here, fall back to three concrete records + morphisms (the unification is a convenience, not a wall).

## Phase 3 — Substitution algebra + two more slices (T-C/T-P) [L; `≈op`/cost need V2/V4]

`tensor`/`asSource`/morphisms (`rename`/`weaken`/`share`)/`rebase`/`subst`; `eval_subst`; laws up to `SourceEquiv` under `≈sem`; terminal-routing simplification in programmatic composition (keep interactive retargeting); order-preserving execution decomposition for the pure case. `≈op` and cost-preservation statements **wait for V2/V4** (or ship as explicitly-marked drafts) — semantic skeletons and quantitative layers split cleanly here. Slices: **Spartan first-sumcheck boundary** (virtual polynomial + preserved total materializer) and **FRI fold phase** (fresh + derived coexistence; first `fold`/`linComb` constructors). Two-round pass-through composition with the closed-evaluator equation.
**Gate:** boundary-as-`subst` demonstrated; constructors land with `eval` lemmas.
**Fallback:** if `retargetMonads`-as-`subst`-action fights Lean, keep it hand-written; the claim algebra carries the proofs regardless.

## Phase 4 — Execution artifact + outcomes + V2 security (T-X, needs T-F: V1/V2/V4/V5/V7/V9 + P1 started) [L]

`ExecutionArtifact` over worlds/traces; `Terminal` outcomes with per-protocol `LegacyOutcome` decoders; `ClaimSchema`/`Problem`; closed-claim relations + generated adapters; completeness and **ordinary-soundness composition** (output admissibility + conditional suffix theorem) in `Security.V2`; per-protocol bridges for the three slices. Budget/error functionals (V4/V7) adopted in statements from the first theorem (D4).
**Gate:** slice bridges proved two-way; soundness composition theorem sorry-free; no legacy consumer broken.
**Risk:** this is the semantic heart; if a bridge fails, *stop and diagnose the quantifier* — that is the audit's designed tripwire, not an obstacle.

## Phase 5 — State restoration + trace calculus (T-X, needs V1–V8 complete + P1) [L] ← D5: before compiler

Salted SR game family + SR traces + move budgets; `TraceTransducer` instances (segmentation, backtracking, SR adapters); straightline + rewinding SRKS with V7-functional errors/times; extractor taxonomy records + transducer composition calculus + view reductions; RBR prefix objects on P1 cursors; the constrained execution tree; `CY*` vs `Ark*` RBR notions with the implication map and (B+r) bridges.
**Gate:** the full bridge set — `RBR→SR`; `ArkRBRK → CYRBRK → {ordinary KS, SRKS}`; single- and multi-round special soundness → ordinary KS and SRKS, each under explicit replay, entropy, budget, and error hypotheses; the KS-composition non-theorem documented with its three valid strengthenings.

## Phase 6 — Compiler, staged (T-K, needs Phases 3+5 and V4/V6/V7/V8/V9) [XL]

Order (**interfaces before passes**): capability/game interface records + `GuaranteeDesc`/`OracleGuarantee` + `BackendAssignment` → `ResourceMeta`/`BCSPublicView`/`TypedPlan` v1 (free typed read program; applicative fragment; certified `LinearForm`) → passes against *abstract* capabilities (`RepresentOracles` → `LowerAccesses` with fixed-consumer inlining + trace coherence → `TransportBoundary` with seal-and-link and `CommitAction`) → concrete instances (Merkle capability records CY-grade, replacing the `False` placeholder; Pedersen with the **Nova slice** as `CommitAction` conformance) → **iBCS** security transfer → `FiatShamir` (hash-chain; consumes Phase-5 SR) → **BCS soundness with CY's exact bound shape**, then BCS-KS via the extractor pipeline.
**Gate per stage:** its row of the `04` §7 matrix (now reproduced in `04`, no archive dependency). GuaranteeTransport obligations surfaced by `BackendAssignment` from the first stage.

## Phase 7+ — Widening [XL, prioritize by demand]

ZK/WI (programmable worlds, salting, local-view simulators); preprocessing/holography (five-phase games); parallel/shared-prefix combinators; **computational backends** (needs V10): curve (KZG/Pedersen/IPA capability records — Nova generalizes) and lattice, with a gate: *one DLOG/AGM- or SIS-based backend theorem proved end-to-end through a `SecurityReduction`*; indifferentiability; L6 refinement hooks (`ExecutableMaterialization` ↔ zkLean/Hax); reduction-level associativity via P2 only if a client demands it.

## Dependency sketch

```
T-F: V1..V9, P1..P3  ──────────────┐
Phase 1 → 2 → 3 ──────────────→ 4 → 5 → 6 → 7+
              (T-P slices feed every phase's gate)
```

## Risk register (top five)

1. **Phase-4 bridge failure** → designed tripwire; diagnose, don't route around.
2. **T-F slippage** → phases 1–2 don't depend on it; Phase 3's quantitative half and all of 4–6 do; keep `FOUNDATION-DEBT` honest and small.
3. **`ClaimWith`/dependent-index friction** → Phase-2 fallback ready.
4. **Trace-slicing proof burden** (list-partition obligations everywhere) → it's a *library* (V2/V3); resist theorem-local plumbing.
5. **Scope gravity toward the compiler** → Phases 4–5 are the value; the compiler without them is the `main`-branch failure mode again.

## Re-direction principles

When implementation contradicts this plan: (a) interfaces in `01`/`02` §§2–6/`03` §§2–5 move only with a decision-log entry; (b) everything else moves freely; (c) consolidations that *delete* objects are favored over additions; (d) if two phases want the same new object, it probably belongs in T-F.
