# 03 — Adversarial Oracle Execution: Worlds, Games, Extractors, Budgets

**Normative core (§§1–5, 8–9), fluid periphery (§§6–7).** The Γ-side companion to `02`: the
semantics in which security is stated and proved. Built on the PolyFun/VCVio deltas in `01` and
`01a`; ArkLib owns only the protocol-shaped games and views on top. The preserved
[CY coverage audit](https://github.com/Verified-zkEVM/ArkLib/blob/archive/oracle-reduction-v2-pre-split/docs/design/archive/gpt-cy-coverage.md)
is the requirements catalog, but current source inventories determine whether a requirement is a
new object, an adapter, or a theorem repair.

## 1. Worlds

`Γ` is a VCVio **oracle runtime** (V1), optionally interpreted through a traced artifact (V2) and resumed as a session (V5): a thin package over `QueryImpl.Stateful` with a setup computation and persistent state. Public observation and query-log instrumentation are orthogonal adapters, not fields of every runtime. Δ (claim resources, `02` §3.2) is read-only and per-reduction; Γ is persistent, shared by all parties and phases, threaded in execution order — never duplicated by claim-context tensor and never closed into a claim. No product-state runtime or independence theorem is assumed without explicit joint initialization and base semantics.

- ROM = the lazy-function world; CY's oracle distributions `O(λ, N)` = one **joint** world presenting an indexed family of logical oracles (2r ROs for BCS), sampled jointly; independence/domain-separation are theorems.
- AGM = adversary-class restriction + instrumented trace (basis ownership and extension rules specified per theorem); not a resource.
- Relativized relations (relation itself queries the model RO) are out of scope by decision (cf. 2024/728).
- The common theorem layer uses a trivial/no-extra-world runtime; every nontrivial Γ-theorem names
  its runtime family explicitly.

## 2. The execution artifact

The experiment has a staged, runner-controlled output. AR-6B first pairs the real resources and
virtual claim; AR-9A adds Δ logging and then asks the VCVio runtime to attach Γ state/query trace.
Security experiments are defined by the distribution `evalDist (Γ.runArtifact executeLogged)`.
Theorems do not quantify over arbitrary artifacts unless given a `GeneratedBy`/support-membership
witness. A paired output prevents accidental split-projection mixing; provenance comes from the
runner distribution, not from the carrier type:

```lean
structure CoreRun (path : Oracle.TypeTree.BranchPath (Context shared)) where
  msgs       : Oracle.TypeTree.OracleMessagesAt (Context shared) path
    -- prover oracle payloads
  inputEnv   : InputImpl shared                             -- the game's input behavior
  outcome    : Terminal (OracleClaim (srcSpecAt shared path) (Stmt path) (Out path)) Fault
  proverOut  : ProverPayload path

def executeCore … : OracleComp Γ.Surface ((path : _) × CoreRun path)

structure LoggedRun (path : _) where
  core       : CoreRun path
  deltaTrace : QueryLog (srcSpecAt shared path)

def executeLogged … : OracleComp Γ.Surface ((path : _) × LoggedRun path)

def OracleRuntime.runArtifact (Γ : OracleRuntime Import Surface) :
    OracleComp Surface α → OracleComp Import (RuntimeArtifact Γ α)

-- ArkLib dependent view of the VCVio artifact; constructor remains controlled
abbrev ExecutionArtifact := RuntimeArtifact Γ ((path : _) × LoggedRun path)
```

`executeCore`/`CoreRun` are trace-free and belong to AR-6B. `LoggedRun`, the runtime adapter, and the
security-game experiment belong to AR-9A. Pairing prevents accidental split-part use in supported
games; it is not a nominal run identifier or a proof of sampling provenance.

Derived projections: `closingEnv` (from one `CoreRun`'s `inputEnv`+`msgs`), `closed`, and `VerifierLocalView` — defined **from the enclosing `LoggedRun.deltaTrace`** (Δ-queries are not in the Γ trace; recovering the view by replay would need a determinism theorem, so it is logged, not asserted), extractor views, RBR prefixes, compiler traces. Probability is the evaluation distribution of the VCVio runtime runner. Missing `SPMF` mass retains VCVio's existing failure/nontermination meaning; explicit protocol `fault` is a returned value. Terminal decoding either proves `NeverFail` or invokes the one named VCVio outcome materialization.

Define `WorldTrace Γ` only as the named view/alias of `QueryLog Γ.Surface` equipped with ArkLib
resource-schema routing; it is not a parallel carrier. **Four execution records, never
conflated:** `ExecutionPath` / `VerifierLocalView` / `WorldTrace` / `SRMoveTrace`. “Full transcript”
in legacy code means `ExecutionPath`; compiled extractors consume `WorldTrace`.

## 3. Outcomes

```lean
inductive Terminal (Claim Fault) | accept : Claim → _ | reject | fault : Fault → _
```

Malformed parses/openings fail **closed** (reject); `fault` is model failure, `Pr[fault] ≤ ε_fault` (preferably 0) in every exported theorem; composition short-circuits on non-accept; extractor failure is *inside* the KS bad event. Migration note: legacy protocols encode rejection in `StatementOut` (`Option`, `Bool`); each port ships a `LegacyOutcome` decoder + correspondence lemma — outcomes are a per-protocol port, not a flag-day (round-4 H2).

## 4. Games

Quantifier order is part of a notion's identity and its **name**. The registry (per README ground rule 5) records for each game: sampling order, adversary phases, trace visibility, budget type, error/time functional signature.

- **Adaptive vs. static:** `H ← O; (x, π) ← A^H` vs. `x` fixed before sampling. Both constructors provided; NARG-level defaults to adaptive (CY).
- **Phased games**: PolyFun supplies generic machine wiring; ordinary VCVio oracle phases use
  `resume` plus monadic execution and `QueryLog.append` (PF-4 is needed only by a future operational
  machine adapter); ArkLib defines the commit/open or five-phase adversary game. Preprocessing keeps
  the *honest indexer inside the same runtime* between adversary phases.
- **Soundness:** `Pr[accept out ∧ out ∈ Language R_out]`-style events over artifact projections, for admissible false inputs; **output-admissibility** is a separate probabilistic obligation of each reduction (`ε_adm`). The exact composition contract (normative, common-case scope: finite classical trees, deterministic read-only Δ, no terminal-view Γ queries, explicit challenge kernels, order-preserving sequential decomposition, fail-closed parsing):

```text
Sound(r₁, R₀ → R₁, ε₁)
∧ OutputAdmissible(r₁, R₁, ε_adm)
∧ (∀ reachable mid, history, Sound(r₂[mid, history], R₁ → R₂, ε₂(mid, history)))
∧ SequentialDecomposition(r₁, r₂)
⇒ Sound(r₁ ; r₂, R₀ → R₂, ε₁ + ε_adm + sup ε₂ + ε_fault)
```

  proved by splitting the accepting event on the intermediate claim (true / false-but-admissible / inadmissible). With persistent Γ, the suffix theorem is parameterized by the actual prefix history; same-labeled ROs do not compose by label. Terminal offline KS does **not** generically compose — the valid routes remain prefix-measurable middle extraction, auxiliary-input-robust stage-one KS, or RBRTE grafting.
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

`SRSoundness(s, N, B)`, straightline and **rewinding** `SRKnowledgeSoundness` (extractor gets the SR trace; rewinding adds black-box access; error/time are explicit functions of the prover's experiment-specific failure probability and runtime, transported through VCV-10 reductions). SR is *not* checkpoint/restore (different request type); bridges from RBR (`(B+r)·ε_RBR`), from special soundness, and to Fiat–Shamir are registry entries with named losses.

## 6. Extractors: taxonomy + composition calculus

Axes (orthogonal, per round-3): adversary access / execution control / oracle evidence / output shape / algorithm class / model. Named points ArkLib defines:

- `Extractor.OfflineExecutionPath` — the current IOP-layer object (concrete
  `Oracle.TypeTree.ExecutionPath`); correct at L3.
- `Extractor.OfflineLoggedExecution` — eats `WorldTrace`s (adversary's and verifier's); the CY compiled-layer straightline notion. **Never silently substitute the former for the latter: doing so assumes away Merkle extraction** (round-4 correction).
- `Extractor.QueryOnly`, `BlackBox.{OnePass, PrefixOracle, CheckpointRestore}`, `PrefixWitnessTransport`, `SpecialSoundnessTree`, `RBRTranscriptTree` — each a capability-record product, with view-reduction implications proved where they exist.

**Composition calculus (the round-4 gap):** compiled-layer extractors are causal transducer pipelines ending in an inner extractor — CY's BCS-KS extractor is `segment-at-FS-events → stateful multi-config Merkle extraction → hash-chain backtrack → SR-trace adapter → E_IOP-SR`. The pure transducer and causality algebra is PolyFun PF-5; VCVio specializes it to query logs and supplies external resource certificates; ArkLib supplies the concrete adapters, extractor composition, black-box transport, and substitution of inflated error/time functions. Stateful *online* extraction remains with the Merkle backend (`04`) and consumes the shared runtime artifacts.

## 7. RBR, trees, and the implication map

- **One constrained execution tree** (on PolyFun `FreeM.Cursor` plus cursor-restricted decorations): shared prover prefixes, verifier fork nodes with explicit conditional challenge kernels, pairwise-distinct sibling challenges, Γ-history agreement, stable ArkLib resource identities. It is bridged to, but not identified with, `DynSystem.Prefix` and concurrent `Front`.
- **CY-compatible notions coexist with ArkLib's stronger ones**: `CYStateFunction`/`CYRBRS`/`CYRBRK` (whole-transcript extractor) alongside `ArkRBRK` (edge-local prefix witnesses); proved: `ArkRBRK → CYRBRK → {straightline KS, SRKS}` with the (B+r) losses. Textbook theorems are never forced through the stronger API. The current `KnowledgeClaimTree` is renamed as the *reversible* strong variant; the relaxed probabilistic object replaces it as the RBRKS endpoint.
- RBR state is indexed by **full prefixes** (concrete messages included; public projection separate); `SourcesAt p` monotone under extension; no future resources at `p`.

## 8. Budgets, errors, time

Per D4 (exact bounds), all core from the start, by extending VCVio's existing
`ResourceProfile`, query-bound, cost-model, and reduction APIs:

```
-- VCVio: existing generic resource profile / query-cost carriers
ResourceProfile Cost ProtocolResource
-- ArkLib: protocol-specific labels and feasibility refinements
ProtocolResource := oracleQuery (id) | srMove | commitment | configuration | opening
ProtocolBudget := ResourceProfile Cost ProtocolResource refined by feasibility predicates
ε, T : ProtocolBudget → Params → FailureRate → RuntimeBound → ℝ≥0∞
```

No parallel `Ledger` or universal `AdvCharacteristics` is introduced. Failure probability is
experiment-specific, while resource profiles and cost transforms reuse VCVio's existing carriers.
Composition modes are additive and substitution-style (the CY BCS-KS shape); concrete expected-time
recurrences remain ArkLib theorems until multiple clients justify a generic VCVio API. Budget
transport accompanies every reduction/transducer ("the SR prover makes ≤ Q_FS moves"), and
reduction running time remains explicit.

## 9. Deferred with named obligations

- **ZK/WI:** programmable worlds (V6), query-before-program events, Merkle local-view simulators, per-leaf + FS salts, paired WI experiments. Recorded; not in the first migration.
- **Indifferentiability** (oracle-distribution replacement): simulator + trace translator + view equivalence — a cryptographic theorem, *not* compiler lowering; needed for "general oracle settings" parity with CY.
- **Quantum:** separate linear execution model; explicitly out of the classical core.
