# 01 — Foundations: The Three-Library Split

**Normative.** This document names the foundation ArkLib assumes at implementation start (D-note: "assume the base is adequate at the time we start"), specifies what must be built in PolyFun and VCVio to make it adequate, and draws the ownership boundary sharply.

## 0. The boundary rule

> **If it mentions prover, verifier, claim, reduction, commitment, or protocol — it is ArkLib's.
> If it is about running oracle computations: worlds, handlers, traces, budgets, probability — it is VCVio's.
> If it is about trees, paths, decorations, and lenses — it is PolyFun's.**

Corollaries: the `.public`/`.oracle` node distinction is ArkLib's (it encodes *prover/verifier visibility*, a protocol concept) even though it is built on PolyFun polynomial functors. The state-restoration *game* is ArkLib's (it is about public-coin protocols) but the *world* it runs in, and the trace it produces, are VCVio objects. Merkle trees as data are ArkLib/`Commitments`; the RO they query is a VCVio world.

## 1. PolyFun: interaction substrate

### 1.1 Already adequate (verify, don't rebuild)

- `Interaction.Spec` as free monad on a polynomial functor; `StrategyOver`, `TwoParty.run`, role/monad decorations, displayed families.
- `Spec.append`, transcript machinery, `Focal.comp` / `Counterpart.append`, mapOutput lemma set (used by ArkLib's proven `execute_comp`).
- Lens/`PathAlong` machinery (`executionLens` pattern used by `Oracle.Spec`).

### 1.2 Foundation requirements (build before/during Phase 3–4)

**P1 — Partial-path cursors ("frontiers").** A first-class object for *partial* executions of a `Spec`: a prefix path together with the residual spec, with (a) extension by one node, (b) inclusion of prefixes, (c) restriction of decorations along a prefix, (d) computation rules by structural recursion (no transports). Today `Path`/`Transcript` are complete root-to-leaf objects; RBR security, SR moves, and reachable-prefix quantification (`03`) all need the partial object. Deliverable: `PFunctor.FreeM.Cursor` (or equivalent) + a lemma kit (extension is associative; restriction commutes with extension).

**P2 — Presentation / normal forms for reassociation.** The prototyped `Spec.Presentation` layer (see paper-note `ArkLib-Refactor_raw_append_spec_exploration.md`): canonical n-ary presentations of appended specs so that reassociation of composites is a typed reindexing, not a cast. Needed the moment any client wants associativity of composed reductions (`02` §5); until then it stays a reserve.

**P3 — Decoration functoriality lemmas.** Reindexing maps for transcript-indexed families under prefix extension and presentation change, packaged once ("apparent cast problems are failed functoriality laws at the indexed boundary" — audit J/§6.5). Small but load-bearing.

## 2. VCVio: oracle computation and adversarial execution

### 2.1 Already adequate (verify, don't rebuild)

- `OracleComp`, `QueryImpl`, `simulateQ`, sum specs + `QueryImpl.add`, `SubSpec` lifts; `simulateQ_compose`-class lemmas.
- `evalDist : OracleComp → SPMF`, `ProbComp`; basic probability.
- Stateful handlers `QueryImpl E (StateT σ (OracleComp I))`, lazy random oracle via `QueryCache`, logging oracles, state separation; replay/fork basics.

### 2.2 Foundation requirements (the Γ contract)

These are the objects the Chiesa–Yogev coverage audit identified as the missing center. Each is general-purpose (nothing SNARK-specific), hence VCVio's domain. ArkLib consumes them; it must not define them privately.

**V1 — Packaged worlds.** `World` = a bundled stateful handler + initial-state *distribution* + public projection + trace policy. Explicitly a packaging of `QueryImpl.Stateful`, not a new semantics. Must support **joint/correlated worlds** (one world presenting an indexed family of logical oracles sampled jointly — CY's oracle distributions `O(λ, N)`); independence is a theorem about particular worlds, never a default. Include: lazy-table ↔ full-function sampling equivalence for finite ROs (needed for regularity/hiding arguments).

**V2 — WorldTrace.** Ordered, heterogeneous, **identity-tagged** query-answer logs as the canonical instrumentation of running any `OracleComp` against a world: events carry (stable oracle id, request, response, position); API: whole trace, prefix at an event, interval between marked events, projection to one logical oracle, concatenation laws ("phase traces concatenate to the global trace"). This is the single most-used object in CY-grade proofs (Merkle extraction, BCS segmentation, preprocessing phases).

**V3 — TraceTransducer.** `(State, step : State → Event₁ → State × List Event₂, finish, coherence, cost)` with sequential composition and a correctness discipline (the output trace is a function of an *ordered prefix* of the input trace). Instances live in ArkLib (hash-chain backtracking, configuration filtering, SR-move construction); the object and its algebra live here.

**V4 — Budgets.** Query-counting semantics (a worst-case budget certificate for an oracle algorithm, independent of answers); typed budget ledgers with per-oracle components and a global sum constraint (`Σᵢ Qᵢ ≤ Q`); budget transport under simulation/transduction ("the reduction's queries to oracle j are ≤ f(adversary budget)"). CY's bounds are unprovable without this.

**V5 — Phased adversaries.** Combinators for two-phase (commit/open) and n-phase (preprocessing's five-phase) executions in one persistent world: run phase, capture (output, trace-so-far, adversary state), continue. With the concatenation law from V2.

**V6 — Reprogramming, forking, replay.** Programmable-oracle worlds (programming lists; conflict policy; preservation of unprogrammed points; query-before-program events); relational fork/replay semantics saying exactly which world cells survive a fork (copy vs. reprogram-one-prefix vs. resample); lazy-sampling exchangeability/freshness lemmas over dependent request types.

**V7 — Error/time functionals.** `AdvCharacteristics` (failure probability, running time, budget) as first-class; error and extraction-time bounds as *functions* of them; two composition modes proven generically: additive (union bound) and **substitution** (feeding inflated failure probability / runtime into another bound's argument — the CY BCS-KS shape); expected-time recurrence support.

**V8 — Probability lemma kit.** Finite conditioning, hybrid arguments, statistical distance, per-event bad-event accounting over `SPMF`, and the specific ROM lemmas (unqueried-pair unpredictability, inversion, collision, hidden-salt bounds) as generic world lemmas parameterized by V4 budgets. Coordinate with the existing paper-note designs (`VCV-io-reduction-cost-accounting-design.md`, `vcvio-itree-oraclespec-lens-unification-plan.md`).

**V10 — Computational games and reductions.** Security-parameter-indexed game ensembles and a reduction calculus: `GameFamily` (`Params : ℕ → Type`, `experiment : ∀ λ, Params λ → Adversary λ → SPMF Bool`), adversary classes (PPT/uniform/nonuniform, with advice), advantage/negligibility, `SecurityReduction G H` (`mapAdversary`, advantage/time/budget bounds), setup/keygen distributions. Required before any curve/lattice backend theorem (DLOG, SIS, pairing assumptions are hardness predicates on `GameFamily`s); `AdvCharacteristics` (V7) supplies the resource vocabulary but not the ensemble/reduction structure. General-purpose, hence VCVio's (or a VCVio-adjacent crypto-foundations module).

**V9 — Failure discipline.** One decision, exported as a lemma kit: how explicit game outcomes (`accept/reject/fault`) interact with `SPMF` missing mass — either `NeverFails` proofs + explicit faults, or a specified interpreter converting monadic failure to `fault`. ArkLib's `Terminal` type (`03` §3) builds on whichever is chosen; it must not be decided twice.

### 2.3 Acceptance tests for the foundation

Each V/P item is "adequate" when its test passes, in VCVio/PolyFun with no ArkLib imports:

1. (V1/V2/V4/V8) A lazy-RO world with traces; the collision lemma `Q(Q−1)/2^{n+1}` proved against a budget, via a *conditioned* bad-event argument.
2. (V1) A **joint heterogeneous** world (two correlated logical oracles) with per-oracle trace projection; the lazy-table ↔ full-function equivalence for a finite RO.
3. (V5/V2) A two-phase adversary game with the trace-prefix concatenation law; a toy trace-based extractor in the CY commit/open shape.
4. (V3/V4) A transducer composed with a logged execution, with budget transport.
5. (V6) A fork/reprogram test: reprogram one point, prove preservation of unprogrammed answers and a query-before-program event bound.
6. (V7) Substitution composition on a toy: `ε'(δ_A) = ε(δ_A + c)`; one expected-time recurrence.
7. (V9) A theorem converting or excluding `SPMF` missing mass per the chosen policy.
8. (V10) One toy `SecurityReduction` with advantage and time transport.
9. (P1/P3) Cursor extension/restriction with decoration transport, cast-free by `#print axioms`-level inspection.
10. (P2, only when promoted from reserve) A reassociation of a three-fold append as typed reindexing.

## 3. ArkLib: everything oracle-reduction

Owns (building on the above): `Oracle.Spec` and its decorations; claims/virtual oracles/closing/composition (`02`); protocol security games including state restoration (`03`, over V1–V7); commitment backends and capability records, compiler passes (`04`); the protocol library (`ProofSystem/`); registry and implication maps.

Explicit *non*-ownership: ArkLib must not define private trace types, private world runners, private budget arithmetic, or private probability lemmas when a V-item covers them. Any gap found during implementation is filed upstream as a foundation issue first; local stubs are marked `-- FOUNDATION-DEBT(Vn):` and carry an obligation to migrate.

## 4. Interface freeze discipline

`01` (this file) is the contract. **Each V/P item freezes only after its acceptance test (§2.3) passes; changes to already-accepted items require a decision-log entry** (README). Unaccepted items may change freely — freezing unimplemented signatures would turn debt stubs into accidental API. The point is to let three libraries evolve in parallel without re-auditing the stack each time.
