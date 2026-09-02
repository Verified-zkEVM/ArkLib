# Implementation roadmap

**Fluid by design.** The destination is ambitious, but each phase has a falsifiable exit gate and
a concrete reason to exist. When Lean or a real protocol contradicts a proposed record layout, the
architecture follows the evidence while preserving the semantic invariants in `02` through `04`.

Effort words are planning signals: S is days, M is roughly one to three weeks, L is roughly one to
two months, and XL is an open-ended program.

## 1. Standing rules

- Every implementation PR starts from current `main`; the archived prototype is a source bank.
- The legacy security namespace remains until each migrated protocol has a proved correspondence.
- Security-shaped changes include the exact game, observation, failure boundary, budget, and loss.
- Foundation gaps go to the lowest owning library. A temporary adapter names its upstream
  destination and includes a deletion test.
- A compiler pass does not land before the execution and trace facts used by its security proof.
- Each completed phase updates `00-current-status.md` and this roadmap in the same PR.

## 2. Starting point

The alignment slice fixes the supported train at Lean 4.33.1, VCVio
`f9dc47d9dacfc5cb51dae9f92f1e34cb5ce2cc24`, and the PolyFun revision selected by VCVio,
`c0c923693fc827a41d17116579a0c16ed4873b19`.

The key result is permission to start, not another planning dependency. `TypeTree`, cursors,
displayed restriction, append decomposition, strategies, handlers, and dependent chain
concatenation are available. The remaining upstream gaps are isolated to the later execution,
state-restoration, and compiler tracks.

**Alignment gate:** the exact dependency train validates; current and historical documentation are
separated; no new interaction-layer API is mixed into the pin change.

## 3. Parallel tracks

| Track | Purpose | Current dependency |
|---|---|---|
| Core semantics | typed reductions, oracle trees, sources, virtual claims, closing | unblocked |
| Protocol evidence | Sumcheck first, then FRI and Spartan | follows the relevant core slice |
| Execution and ordinary security | world-backed artifacts, outcomes, admissibility-aware composition | VCVio artifact and outcome gaps |
| State restoration | causal trace calculus, salted games, extractor views | PolyFun transducer and VCVio specialization/conditioning gaps |
| Compiler | guarantee transport and backend adapters | core composition plus state-restoration evidence |

The tracks are coordinated by consumers, not by waiting for a synchronized three-repository mega
release.

## Phase 1 — Typed core [L]

Land AR-1 through AR-6B in the order described in `01a`:

1. plain dependent reductions;
2. oracle type trees, path projections, and decorations;
3. accumulated oracle access and execution;
4. extensional sources and resource schemas;
5. virtual substitution;
6. open/closed claims and run-derived closing.

The archived implementation may donate proof ideas and small coherent definitions. Each port is
rewritten against the supported PolyFun API and reviewed at its new abstraction boundary.

**Gate:** public equations are usable; no new `sorry`; the legacy layer is unchanged; no caller can
close a claim with an unrelated handler.

## Phase 2 — Minimum viable protocol [M]

Port one programmatic single-round Sumcheck. Its output includes a query-derived scalar and a
degree-bounded oracle slot. Prove perfect completeness through the actual execution and closing
path, then prove a two-way protocol-specific bridge to the legacy presentation.

This is the first moment the new abstraction earns its name. Before this theorem, record layouts
are informed hypotheses. After it, they are an API with evidence.

**Gate:** AR-7 and AR-8 are sorry-free; the guarantee representation is exercised; the bridge is
two-way; no generic migration theorem is claimed.

**Fallback:** if a unified dependent claim record fights elaboration, use a small family of
concrete records connected by explicit morphisms. Uniform packaging is a convenience, not a reason
to obscure the semantics.

## Phase 3 — Composition and two contrasting protocols [L]

Add a two-round composite that exercises cursor decomposition, `TypeTree.Chain.then`, virtual
substitution, and explicit source routing. Then port one FRI slice and one Spartan-like slice so the
design sees both a derived virtual view and a fresh prover message.

Semantic composition is proved up to extensional equivalence. Operational trace and cost
preservation wait for the world-backed execution artifact; they are not asserted from syntax alone.

**Gate:** the middle boundary is visibly handler substitution; public constructors have evaluation
laws; a three-stage example uses existing chain reassociation or records the exact missing upstream
law.

## Parallel upstream lane — Close only demonstrated gaps [M–L]

The first downstream clients drive four focused foundation additions:

1. a VCVio runner-produced resumable artifact with state and named trace regions;
2. a VCVio accept/reject/fault materialization boundary;
3. a PolyFun causal finite-trace transducer plus VCVio query-log certificates;
4. VCVio conditioning/dynamic-programming and error-bearing reduction APIs required by the first
   state-restoration or compiler theorem.

Do not implement all four speculatively. The early typed-core work proceeds while these interfaces
are designed against their actual consumers.

**Gate per addition:** the owning repository's tests and laws pass, and the named ArkLib client uses
the API without a parallel local abstraction.

## Phase 4 — World-backed execution and ordinary security [L]

Add AR-9A, AR-9B, AR-10A, and AR-10B. One supported artifact now relates the core run, persistent
world state, ordered query trace, protocol prefix, and resource profile. Terminal decoding crosses
one named missing-mass boundary.

Prove ordinary soundness composition in its honest form:

- the first reduction is sound;
- its output is admissible except with explicit error;
- the suffix is sound for every reachable intermediate claim and actual prefix history;
- sequential execution preserves order and state;
- the total error includes soundness, inadmissibility, suffix, and fault terms.

**Gate:** the Sumcheck, FRI, and Spartan slices have two-way legacy bridges; the composition theorem
is sorry-free; no theorem recreates unrestricted stateful composition.

## Phase 5 — State restoration and extractor calculus [L]

Build salted state-restoration games, world-trace views, causal segmentation and backtracking,
straightline and rewinding extractors, and the exact implication map between ArkLib's stronger
round-by-round notions and the Chiesa–Yogev-compatible notions.

The transducer pipeline is explicit:

```text
segment Fiat–Shamir events
  → stateful multi-configuration Merkle extraction
  → hash-chain backtracking
  → state-restoration trace adaptation
  → inner IOP extractor
```

Each arrow carries causality, trace-order, resource, error, and running-time evidence. The
stateful online Merkle extractor remains a backend capability rather than being flattened into a
pure list pass.

**Gate:** prove the named RBR-to-SR and knowledge implications under explicit replay, entropy,
budget, and error hypotheses. Document the non-theorem that terminal offline knowledge soundness
does not compose without a stronger intermediate interface.

## Phase 6 — Oracle-elimination compiler [XL]

Land interfaces before passes:

1. reified oracle guarantees and resource metadata;
2. backend assignments and complete capability games;
3. typed finite or staged read plans;
4. represent, lower, and boundary-transport passes;
5. concrete Merkle and homomorphic adapters;
6. interactive BCS and Fiat–Shamir security transfer;
7. exact BCS knowledge soundness through the extractor pipeline.

The first Merkle adapter consumes VCVio's supported shared-ROM extraction theorem. The first
homomorphic conformance case uses Nova/Pedersen-style commitment action. Unsupported capabilities
remain absent rather than being filled with placeholder propositions.

**Gate per pass:** functional correctness, ordinary soundness, extraction, and privacy obligations
are classified exactly as in `04`; every ideal guarantee either reaches a backend proof or produces
an explicit assignment failure.

## Phase 7 and beyond — Widening [XL]

Widen only after the core compiler path works:

- zero knowledge and witness indistinguishability with programmable worlds and local-view
  simulators;
- preprocessing and holography with persistent five-phase games;
- parallel and shared-prefix combinators;
- KZG, Pedersen, IPA, and lattice-backed capability records;
- indifferentiability and alternative oracle models;
- executable refinement, representation correctness, and resource-trace correspondence;
- quantum access through a separate linear execution model.

A new backend is complete only when one scheme theorem travels end to end through its actual
security reduction and resource transform.

## 4. Current dependency sketch

```text
alignment
  → typed core → Sumcheck bridge → typed composition
                                      │
VCVio artifact + outcome ───────────┘→ ordinary security

PolyFun transducer
  → VCVio query-log certificates + conditioning
  → state restoration
  → compiler
  → widening
```

## 5. Risks and redirection

1. **Claim-index friction.** Prefer several honest records and explicit morphisms over one opaque
   dependent bundle.
2. **Runner-boundary slippage.** Early typed work proceeds, but general security waits for one
   execution-derived artifact.
3. **Trace plumbing growth.** Land generic causality and certified specialization before copying
   list-partition proofs across compiler passes.
4. **Security quantifier drift.** Treat a failed composition bridge as evidence about the theorem,
   not an invitation to weaken its name.
5. **Compiler gravity.** The compiler is valuable only after claims, closing, ordinary security,
   and state restoration are real APIs.
6. **Over-general upstream work.** Every new foundation names its first consumer and the mutation or
   counterexample its laws reject.

When implementation redirects the plan, preserve the reason in the owning normative document and
update the status page. Do not accumulate an alternative architecture beside the one the clients
actually use.
