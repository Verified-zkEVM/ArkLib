# Round-4 Audit: The Design vs. Chiesa–Yogev, and the Missing Half

**Date:** 2026-07-12 (evening). **Subject:** `ArkLib-Oracle-Reduction-Design.md` (post-round-3 version, 1288 lines).
**Method:** direct reading of the design; direct reading of the Chiesa–Yogev textbook TeX source (`~/Downloads/Papers/hash-based-snargs-book/snargs-book.tex`, 27,250 lines) — specifically the BCS construction/soundness chapter, the Merkle extractability section, and the BCS knowledge-soundness theorem; plus two independent GPT 5.6 Sol (high) reviews with full code and textbook access, archived as `arklib-design-reports/gpt-cy-coverage.md` (textbook coverage matrix, 27 areas) and `arklib-design-reports/gpt-fresh-critique.md` (internal consistency and Lean feasibility).

---

## 1. Verdict, in three parts

**1. The Δ-side core is right and converging.** Behavioral carrier, `AcceptedRun`-style closing, substitution-not-bind, `Γ`/`Δ` separation, the pipeline factoring — round 3 landed these correctly, and this round found no reason to reopen any of them. Strong independent confirmation: CY's own modular proof factors BCS *exactly* as the design predicts — `BCS = HashChainFS(iBCS)` (CY 17990–18006), i.e. `RepresentOracles`+`LowerAccesses`+`TransportBoundary` ≈ iBCS, then `FiatShamir`. The pipeline is not fighting the textbook.

**2. The document itself needs a repair-and-consolidation pass** — six critical internal defects (§3 below), several stale audit dispositions, and a structure that has outgrown one file.

**3. The headline finding: the design is half of the system, and the missing half now has a name.** The design describes *what reductions and compiled protocols are*. CY's security proofs live almost entirely in a layer the design only gestures at: **the semantics of adversarial oracle execution** — persistent joint worlds with ordered, identity-tagged query traces; trace slicing, projection, and transduction; state-restoration games; stateful online extractors; oracle reprogramming; typed query budgets; and error/time bounds as *functionals* of adversary characteristics. Your prediction — "once we get down to the precise cryptographic properties and reductions that's where a LOT of complications crop up" — is confirmed, and the complications are **structural, not proof-engineering overhead**. The coverage matrix verdict: of 27 CY result areas, roughly 8 are OK/OK-with-work under the current design and **19 are GAPs**, nearly all traceable to the missing execution layer, not to the claim layer.

The single most consequential recommendation:

> **Promote the Γ side from a sketch to a companion design document — "Adversarial Oracle Execution" — before stabilizing the security or compiler interfaces. Build it on VCVio's existing stateful-handler machinery rather than the doc's from-scratch `WorldSpec` runner.**

---

## 2. What CY actually requires (the evidence)

Read directly from the TeX; each item is a load-bearing object of the BCS chapters that the design currently lacks.

### 2.1 The state-restoration game is the *hypothesis* of BCS soundness — not an optional bridge

CY Theorem `bcs-soundness` (17834): adaptive NARG soundness ≤ **ε_SR(λ + s_FS, N, Q)** + Merkle multi-extraction error + hash-chain error. You cannot *state* the theorem without the SR game — and it must be the **salted** SR game (the reduction embeds `(Merkle root, FS salt)` into SR moves, which is why the SR error is evaluated at salt size `λ + s_FS`). The SR game itself (CY 16854–16877) is not a protocol run, not a transcript tree, and not checkpoint/restore: it is an oracle game whose *request type is an arbitrary purported transcript prefix* `(round j, x, π₁..π_j, s₁..s_j)`, answered by per-round random functions keyed on the whole prefix, with consistency on repeats and a move budget B. The design's §6.6.4 `CheckpointRestore` is a different object. **Design change: SR becomes a first-class game family, scheduled before the compiler — currently it sits behind RBRTE in migration step 9, which is the wrong order for CY.**

### 2.2 Merkle extraction is stateful, online, trace-based, multi-configuration

CY's Merkle extractor (Lemma `mt-extractability`, 13185) is deterministic, receives the **commitment-phase RO trace only**, reconstructs a partial tree by reverse lookup, fills missing leaves arbitrarily, and outputs a *total* vector + trapdoor; the bad event is disagreement with a *later* opening in the same world. The BCS-grade version (Lemmas 13534, 13874) is a **stateful transducer**: the adversary interleaves commitments across multiple Merkle configurations; each extractor call receives only the *trace increment since the last call*, filtered per configuration; repeated roots must re-extract identically; the error is *not* a naive union bound (collision events are global, guessing events are per-commitment). The design's §6.10.7 capability names ("multi-extractability") do not determine this interface. Two-phase adversaries (commit phase / open phase, state carried across, budget split Q₁+Q₂ ≤ Q) are the *game shape* of every commitment property.

### 2.3 The BCS reduction is a trace transducer

CY Construction `bcs-direct-reduction` (17901): the SR prover simulates the BCS adversary, **passes through** the Merkle oracles while **lazily sampling the FS oracles itself** (split-world simulation); on each FS query it takes the Merkle-trace segment since the previous FS query, hash-chain-backtracks the purported prior roots and salts, runs the stateful Merkle multi-extractor on the increment, and emits an SR move. The BCS *knowledge* extractor (18550) is the same pipeline feeding the IOP's SR extractor — not `E_IOP ∘ E_Merkle` but `trace segmentation → stateful multi-extraction → hash-chain backtracking → SR-trace adapter → E_IOP-SR`. **No object in the design composes extractors through trace adapters, transports black-box access through a prover wrapper, or accounts for the composite's error/time.**

### 2.4 Errors and times are functionals, budgets are vectors

CY Theorem `bcs-knowledge-soundness` (18423): the NARG KS error is `ε_IOP-SR(λ+s_FS, N, Q, **δ'_A**)` where δ'_A is the adversary's failure probability *inflated by* the Merkle+hash-chain error; extraction *time* is likewise a function of the adversary's (inflated) failure probability and running time. Budgets: one global Q with constrained splits (Q_MT + Q_FS ≤ Q), per-configuration lengths and opening counts, SR move budgets B, and bounds like (B+r)·ε_RBR for the RBR→SR bridge. The design's scalar `ε_s + ε_adm + ε_fault` and path-κ accounting cannot express substitution of inflated failure probabilities into another error function, expected-time recurrences, or budget-split optimization. **Needed: a typed budget ledger with a global sum constraint, and errors/times as functions of budgets and adversary characteristics.**

### 2.5 ZK, preprocessing, WI each add a distinct game shape

- BCS ZK (18957): programmable-RO simulator (programming lists, query-before-program bad events bounded by FS-salt entropy), Merkle *local-view* selective-opening privacy simulator, per-leaf salts. Deferring ZK is fine; the doc should record these as the objects salting forces.
- Preprocessing (24636): a five-phase chronology — adversary phase 1 → *honest indexer in the same world* → adversary phase 2 → verifier — with four separate traces handed to the extractor. `ResourceMeta.origin = setup/index` is metadata; the game needs *temporal placement* of the honest indexer inside the shared world.
- Also real: CY's indifferentiability chapter (oracle-distribution replacement with simulators and trace translators — *not* the same as compiler lowering), WI's paired experiments, and the "oracle-accessible verifier randomness" BCS variant.

### 2.6 One important correction to round 3

CY's general-oracle **straightline KS gives the extractor the adversary's RO trace and the verifier's RO trace** (5693–5716) — *not* the concrete IOP messages. ArkLib's current `Extractor.Straightline` (full concrete transcript) is a *different, information-theoretically stronger* input at the IOP layer; using it as-is at the argument layer would **assume away Merkle extraction**, which is the central theorem. The round-3 disposition ("full transcript is the literature default") was right for *IOP-layer* notions and wrong if applied at the *compiled* layer. The taxonomy needs `OfflineLoggedExecution` (trace-fed) as a distinct point, and the IOP-layer full-transcript extractor must never be silently reused as the NARG-layer one.

---

## 3. Critical internal defects (fix before any code)

From the fresh-eyes review, all verified against the document:

| # | Defect | Fix |
|---|---|---|
| C1 | `runClosed : Dist (Terminal (ClosedClaim …) Fault)` is not a type — drops the transcript index (Stmt/Out depend on pt), the prover payload/witness (used by the KS event two sections later!), honest data (used by completeness), Γ state/trace; `Dist` isn't the live layer (`OracleComp`/`SPMF` via `evalDist` is); fault-vs-`SPMF.none` mass is undecided | Define one dependent **`ExecutionArtifact`** (transcript, terminal output, env, prover payload, Γ trace, outcome) and make closing/extractor views/compiler traces *projections* of it |
| C2 | `AcceptedRun` neither transcript-indexes (Src/Stmt/Out can't be fixed before pt is known) nor enforces same-run (public constructor pairs any env with any claim) — audit disposition K overstates | Subsumed by `ExecutionArtifact`; env and claim become projections, "same run" becomes structural |
| C3 | **Contradiction:** the ontology says malicious backing behavior is arbitrary, but `OracleMessagesAt` stores concrete `x : X` and real protocols use *refined message types* (sumcheck sends `CDegreeLE R deg` — the degree bound is intrinsic to the type, exactly what "validity lives in relations" forbids) | A real decision (§5, D1). My recommendation: option (1) — message payloads stay concrete/typed (they're *physically sent*, representability is free), and the "arbitrary behavior" doctrine applies to input oracles and closed output claims only. Document the asymmetry honestly: prover-sent oracles are data-backed by construction; CY agrees (their IOP strings are literal strings) |
| C4 | `ClaimSchema` undefined; `Relation` vs `Problem` duplicated and used interchangeably | Define `ClaimSchema` + `Problem` once (promise-free = `admissible := True` abbreviation); decide whether oracle schemas are a specialization before step 7 |
| C5 | `OracleFamily.Behavior := QueryImpl [Out.Obj]ₒ Id` doesn't elaborate — `[…]ₒ` needs an instance, a structure field isn't one | Use ArkLib's explicit-interface notation `[Out.Obj]ₒ' Out.oracle` |
| C6 | The step-6 "comparison gate" cannot be generic: old `OutputRelation`s receive `inputImpl` and may be environment-sensitive; three slice equivalences do not authorize a global step-7 cutover | Per-protocol bridges (`old relation + Autonomous proof ↔ closed Problem`) in a parallel `Security.V2` namespace; legacy namespace stays until every consumer is bridged |

Plus editorial: the duplicated associativity paragraph in §6.5; the stale "two additional fields" rejection in §9 (contradicts the query-only `VirtualOracle`); `Src` naming split (`OracleSpec` vs `SourceCtx`); several audit dispositions marked "added" that are only "requested" (K, C, I, T, N, R) — the traceability table should distinguish *accepted / sketched / specified*; drifted line references (prefer declaration names).

---

## 4. The a-ha consolidations (adopt these)

1. **`ExecutionArtifact` as the master record.** One dependent artifact per run; `AcceptedRun`, extractor views, compiler traces, RBR prefixes, and reachability are all projections. This is what makes "same run" structural instead of documented, and it is *also* the object CY's reductions manipulate (their reductions are functions of the artifact).
2. **`ClaimWith Rep` — representation-indexed claims.** `OracleClaim = ClaimWith (VirtualOracle srcSpec)`, `ClosedClaim = ClaimWith Behavior`, `StatementWithOracles = ClaimWith (fun Out => ∀ i, Out.Obj i)`, and `HonestProverOutput = ClaimWith Data × Witness`. Evaluation and data-answering are representation morphisms into behavior; `ProverOutputRealizes` becomes a naturality statement. Deletes duplicated records, and makes the honest/verifier symmetry visible.
3. **Γ = VCVio.** The doc's `WorldSpec (State, Request, Response, step, initialDistribution, publicView)` re-invents `QueryImpl.Stateful` + VCVio's lazy-RO cache, logging, linking, state separation, and replay machinery. Package, don't rebuild: ArkLib adds initial-state distribution, public projection, trace policy, and — the genuinely new parts CY forces — **identity-tagged heterogeneous trace events, trace slicing/projection APIs, and trace transducers**. (Note: your own paper-note has `VCV-io-reduction-cost-accounting-design.md` and the interaction-redesign council notes — the budget-ledger work should link up with those.)
4. **`TraceTransducer` as a first-class object.** CY uses it implicitly *everywhere*: configuration filtering, FS-segmentation, hash-chain backtracking, BCS→SR trace adaptation, COS→BCS, multi-RO domain separation, indifferentiability simulators. One `(State, step : State → Event₁ → State × List Event₂, finish, coherence, cost)` record with composition covers all of them. This is the missing composition calculus for extractors too — CY's BCS extractor *is* a transducer pipeline ending in the IOP extractor.
5. **One constrained execution tree.** RBR state functions, `KnowledgeClaimTree`, special-soundness trees, and SR move logs are decorations of one tree object (shared prover prefixes, distinct sibling challenges from explicit kernels, Γ-history agreement, stable resource identity). Build the base tree once.
6. **Budgets and errors as typed resources.** `Budget = {totalQueries, perOracle, srMoves, commitments, configurations, openings}` with feasibility `Σᵢ Qᵢ ≤ Q`; errors and extraction times as *functions* of budgets and adversary characteristics (failure probability, running time), with two composition modes: additive union-bound and functional substitution. This is the only shape that can express CY's tables.
7. **Disambiguate "transcript" now.** `InteractionTranscript` (IOP messages) ≠ `VerifierLocalView` (queried positions+answers — what HVZK simulates) ≠ `WorldTrace` (RO query-answer log — what extractors eat) ≠ `SRMoveTrace`. The current code and doc overload "full transcript"; C-Y's proofs move data between all four via explicit conversions.
8. **CY-compatible security notions alongside ArkLib's stronger ones.** The design's edge-local prefix-witness RBRK is *stronger than* CY's whole-transcript RBRK (Def 23793). Keep both: `ArkRBRK → CYRBRK → {straightline KS, SRKS}` with the (B+r) losses. Do not force textbook theorems through the stronger local API — protocols satisfying CY's definition may not satisfy ArkLib's.

---

## 5. Decisions you need to make (nobody else can)

- **D1 (from C3):** malicious semantics of prover-sent oracle messages — concrete typed payloads (my recommendation, matches CY and the runtime) vs. behavior-generalized message slots vs. de-refining protocol message types. Affects every port.
- **D2:** adopt the three-document split (below) or keep one file.
- **D3:** the minimum viable slice — commit to "programmatic single-round sumcheck perfect completeness through `closeWith`" as the first end-to-end target (before Spartan/FRI/associativity/soundness), or keep the current step-3 triple.
- **D4:** whether ArkLib targets CY's *exact* quantitative theorems (then the budget/error algebra is near-term core) or qualitative analogues first (then it can trail by one phase — but the SR game still cannot, since BCS soundness is unstateable without it).
- **D5:** scheduling — SR game and `WorldTrace` before or after the closed-relation cutover (steps 6–7). Given CY, I'd pull SR + trace API *before* the compiler stage and in parallel with the cutover.

---

## 6. Recommended restructuring

Split into three documents with distinct lifecycles:

1. **`Oracle-Reduction-Core.md`** (the current doc, §§0–6.8 + 7, repaired per §3, consolidated per the fresh-eyes edit list — merge §2/§6.1, fold §7 into normative text, archive §10 audit ledgers, 8 success criteria instead of 15).
2. **`Adversarial-Oracle-Execution.md`** (new; the missing half): VCVio-packaged worlds, identity-tagged `WorldTrace`, slicing/projection, `TraceTransducer`, two-phase/multi-phase game shapes, SR game family (salted), reprogramming semantics, budget ledger, error/time functionals, `ExecutionArtifact`. This is a research-and-design effort comparable to rounds 1–3, and it gates every CY theorem.
3. **`Oracle-Elimination-Compiler.md`** (current §6.10, plus the CY-specific corrections: game-indexed Merkle capability records per §2.2, `BCSPublicView`, and the honest acknowledgment that pass-local syntax rewrites can't carry the security proofs — the proofs cross pass boundaries through the global trace, so passes must exchange proof-relevant execution artifacts).

Migration reordering (delta to the current 11 steps): insert "define `ExecutionArtifact` + repair C1–C6" as step 0; pull the minimum-viable sumcheck slice before the triple slice; run `Adversarial-Oracle-Execution` design in parallel from now; move SR + trace APIs ahead of RBRTE and the compiler; keep the legacy security namespace alive through per-protocol bridges (no flag day).

---

## 7. What survives unchanged

Worth stating so the repair pass doesn't over-rotate: the behavioral carrier; closing as abstraction; `subst` with explicit interfaces and the middle-carrier `asSource`; the fresh/derived origin distinction; Materialization as optional strengthening; the no-quotient policy; `TypedPlan` with certified fragments; the Nova case study (§6.10.6 remains an excellent test article); the choice of `TerminalOutput` as the migration seam; and the pipeline factoring — now *independently confirmed* by CY's own modular proof structure.

---

## 8. Sources

- Full coverage matrix (27 areas, per-theorem CY line references): `arklib-design-reports/gpt-cy-coverage.md`.
- Full internal critique (C1–C6, M1–M7, load-bearing-object classification, 23-item edit list, Lean spot-checks against VCVio): `arklib-design-reports/gpt-fresh-critique.md`.
- Textbook: `~/Downloads/Papers/hash-based-snargs-book/snargs-book.tex` (also `~/Documents/Textbooks/snargs-book.pdf`). Key anchors: BCS construction 17618, soundness theorem 17834, direct reduction 17901, KS theorem 18423, extractor 18550, ZK 18957, Merkle extractability 13185/13534/13874, SR game 16854, preprocessing 24636, RBR 23543/23793, error tables 26751.
- My direct-reading confirmations (independent of the delegates): split-world simulation, trace slicing, salted SR moves, oracle distributions `O(λ,n)`, failure-probability-parameterized KS error/time.
