# 03 — Adversarial Oracle Execution: Worlds, Games, Extractors, Budgets

**Normative core (§§1–5, 8–9), fluid periphery (§§6–7).** The Γ-side companion to `02`: the semantics in which security is stated and proved. Built on VCVio foundation items V1–V9 (`01` §2.2); ArkLib owns only the protocol-shaped games on top. The CY coverage audit (archive: `gpt-cy-coverage.md`) is the requirements document for this file: every GAP it lists is closed by an object here.

## 1. Worlds

`Γ` is a VCVio **World** (V1): packaged stateful handler + initial-state distribution + public projection + trace policy. Δ (claim resources, `02` §3.2) is read-only and per-reduction; Γ is persistent, shared by all parties and phases, threaded in execution order — never duplicated by `tensor`, never closed into a claim.

- ROM = the lazy-function world; CY's oracle distributions `O(λ, N)` = one **joint** world presenting an indexed family of logical oracles (2r ROs for BCS), sampled jointly; independence/domain-separation are theorems.
- AGM = adversary-class restriction + instrumented trace (basis ownership and extension rules specified per theorem); not a resource.
- Relativized relations (relation itself queries the model RO) are out of scope by decision (cf. 2024/728).
- The common theorem layer takes `Γ = ∅`; every Γ-theorem names its world family explicitly.

## 2. The execution artifact

One dependent record per run; everything else is a projection (round-4 repairs C1/C2):

```lean
structure ExecutionArtifact (…parameters: shared, world Γ…) where
  pt        : Spec.PublicTranscript (Context shared)       -- realized public path
  msgs      : Spec.OracleMessagesAt (Context shared) pt    -- prover oracle payloads
  inputEnv  : InputImpl …                                  -- the game's input behavior
  outcome   : Terminal (OracleClaim (srcSpecAt shared pt) (Stmt pt) (Out pt)) Fault
  proverOut : ProverPayload pt                             -- adversary's declared output/witness
  γState    : Γ.State
  γTrace    : WorldTrace Γ                                 -- V2 object
```

Derived projections: `closingEnv` (from `inputEnv`+`msgs`), `closed` (claim closed with `closingEnv` — "same run" is now structural), `VerifierLocalView` (queried positions + answers — the HVZK object), extractor views, RBR prefixes, compiler traces. Execution returns `OracleComp _ ExecutionArtifact`; probability via `evalDist`; the fault/missing-mass policy is V9's single decision, applied here once.

**Four transcripts, never conflated:** `InteractionTranscript` (protocol messages) / `VerifierLocalView` / `WorldTrace` / `SRMoveTrace` — with explicit conversions. "Full transcript" in legacy code means the first; extractors at the compiled layer eat the third.

## 3. Outcomes

```lean
inductive Terminal (Claim Fault) | accept : Claim → _ | reject | fault : Fault → _
```

Malformed parses/openings fail **closed** (reject); `fault` is model failure, `Pr[fault] ≤ ε_fault` (preferably 0) in every exported theorem; composition short-circuits on non-accept; extractor failure is *inside* the KS bad event. Migration note: legacy protocols encode rejection in `StatementOut` (`Option`, `Bool`); each port ships a `LegacyOutcome` decoder + correspondence lemma — outcomes are a per-protocol port, not a flag-day (round-4 H2).

## 4. Games

Quantifier order is part of a notion's identity and its **name**. The registry (per README ground rule 5) records for each game: sampling order, adversary phases, trace visibility, budget type, error/time functional signature.

- **Adaptive vs. static:** `H ← O; (x, π) ← A^H` vs. `x` fixed before sampling. Both constructors provided; NARG-level defaults to adaptive (CY).
- **Phased games** (V5): commitment games are two-phase (commit trace / open phase, state across, budget `Q₁+Q₂ ≤ Q`); preprocessing is five-phase with the *honest indexer running inside the same world* between adversary phases, four separate traces to the extractor. Temporal placement is game structure, not `ResourceMeta.origin` metadata.
- **Soundness:** `Pr[accept out ∧ out ∈ Language R_out]`-style events over artifact projections, for admissible false inputs; **output-admissibility** is a separate probabilistic obligation of each reduction (`ε_adm`), load-bearing for composition.
- **Knowledge:** the event includes extractor failure; no realization clause (coherence is completeness's). `KS → soundness` needs a causally-available witness supplier, not the bare existential.

## 5. State restoration (first-class, scheduled early — D5)

The SR game is ArkLib's but is *the* hypothesis of compiled-layer theorems (CY: BCS soundness is stated against ε_SR at salt size λ+s_FS — unstateable without it). Definition shape, faithful to CY 16854:

```lean
structure SRMove (Π : PublicCoinIOP) where
  round : Fin Π.rounds
  inst  : Π.Instance
  prfx  : Π.ProofPrefix round     -- all proof strings through the round
  salts : Π.SaltPrefix round      -- SALTED: moves carry salt strings

-- World: one random function per round, keyed on the ENTIRE move.
-- Prover: ≤ B moves, arbitrary purported prefixes (not one consistent execution),
--   consistent answers on repeats; final output re-derives every challenge.
-- SRTrace : the move-response log (a WorldTrace instance).
```

`SRSoundness(s, N, B)`, straightline and **rewinding** `SRKnowledgeSoundness` (extractor gets the SR trace; rewinding adds black-box access; error/time are V7 functionals of the prover's failure probability and runtime). SR is *not* checkpoint/restore (different request type); bridges from RBR (`(B+r)·ε_RBR`), from special soundness, and to Fiat–Shamir are registry entries with named losses.

## 6. Extractors: taxonomy + composition calculus

Axes (orthogonal, per round-3): adversary access / execution control / oracle evidence / output shape / algorithm class / model. Named points ArkLib defines:

- `Extractor.OfflineFullTranscript` — the current IOP-layer object (concrete `InteractionTranscript`); correct at L3.
- `Extractor.OfflineLoggedExecution` — eats `WorldTrace`s (adversary's and verifier's); the CY compiled-layer straightline notion. **Never silently substitute the former for the latter: doing so assumes away Merkle extraction** (round-4 correction).
- `Extractor.QueryOnly`, `BlackBox.{OnePass, PrefixOracle, CheckpointRestore}`, `PrefixWitnessTransport`, `SpecialSoundnessTree`, `RBRTranscriptTree` — each a capability-record product, with view-reduction implications proved where they exist.

**Composition calculus (the round-4 gap):** compiled-layer extractors are **TraceTransducer pipelines** (V3) ending in an inner extractor — CY's BCS-KS extractor is `segment-at-FS-events → stateful multi-config Merkle extraction → hash-chain backtrack → SR-trace adapter → E_IOP-SR`. ArkLib provides: transducer-composition of extractors; black-box transport through prover wrappers; and V7-substitution of inflated characteristics (`δ' = δ_A + ε_MT + ε_chain` fed into the inner error/time functional). Stateful *online* extraction (Merkle multi-config: state across calls, trace *increments*, per-configuration projection, repeated-root coherence, native multi-instance error — CY 13534/13874) is the canonical nontrivial instance and lives with the Merkle backend (`04`), on V2/V3 objects.

## 7. RBR, trees, and the implication map

- **One constrained execution tree** (on PolyFun P1 cursors): shared prover prefixes, verifier fork nodes with explicit conditional challenge kernels, pairwise-distinct sibling challenges, Γ-history agreement, stable resource identities. Decorations: CY state functions (RBRS), leaf language/witness data (special soundness), grafting data (RBRTE), `KState`+backward maps (ArkLib's strong RBRK).
- **CY-compatible notions coexist with ArkLib's stronger ones**: `CYStateFunction`/`CYRBRS`/`CYRBRK` (whole-transcript extractor) alongside `ArkRBRK` (edge-local prefix witnesses); proved: `ArkRBRK → CYRBRK → {straightline KS, SRKS}` with the (B+r) losses. Textbook theorems are never forced through the stronger API. The current `KnowledgeClaimTree` is renamed as the *reversible* strong variant; the relaxed probabilistic object replaces it as the RBRKS endpoint.
- RBR state is indexed by **full prefixes** (concrete messages included; public projection separate); `SourcesAt p` monotone under extension; no future resources at `p`.

## 8. Budgets, errors, time

Per D4 (exact bounds), all core from the start, on V4/V7:

```
Budget = { totalQueries, perOracle : ι → ℕ, srMoves, commitments, configurations, openings }
  with feasibility Σᵢ perOracle i ≤ totalQueries
ε, T : Budget → Params → AdvCharacteristics → ℝ≥0∞   -- functionals, not scalars
```

Composition modes: additive (union bound) and substitution (CY BCS-KS shape); expected-time recurrences (special-soundness extractors); per-configuration sums with heterogeneous parameters; budget transport through every reduction/transducer ("the SR prover makes ≤ Q_FS moves"). Reduction *running time* is part of every theorem statement, CY-style.

## 9. Deferred with named obligations

- **ZK/WI:** programmable worlds (V6), query-before-program events, Merkle local-view simulators, per-leaf + FS salts, paired WI experiments. Recorded; not in the first migration.
- **Indifferentiability** (oracle-distribution replacement): simulator + trace translator + view equivalence — a cryptographic theorem, *not* compiler lowering; needed for "general oracle settings" parity with CY.
- **Quantum:** separate linear execution model; explicitly out of the classical core.
