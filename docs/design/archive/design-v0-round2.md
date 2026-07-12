# The Oracle Reduction Layer: Finalized Design

**Status:** design handover document, finalized 2026-07-12 (post-audit).
**Scope:** the canonical definition of *oracle reduction* for ArkLib's new `Interaction` framework (worktree `ArkLib-core-rebuild`, branch `quang/core-rebuild`), replacing the retired `ArkLib/OracleReduction/` design on `main`.
**Inputs:** direct reading of both codebases; the design-consensus notes in `paper-note` (`ArkLib-Refactor_oracle_reduction_as_ior.md`, `arklib-ior-knowledge-soundness-survey.md`, `ArkLib-Refactor_raw_append_spec_exploration.md`); the ArkLib talks (King's College deck, Oct 2025); a very-thorough survey of the old design on `main`; two GPT 5.6 deep analyses (code-grounded design review + 35-requirement literature catalog); and a GPT 5.6 **xhigh adversarial audit** of the draft proposal, whose corrections are integrated throughout and tabulated in §10. Delegate reports are archived alongside this document's references (§13).

**How to read this document.** §§1–5 are diagnosis: what the object must be, why the old design failed, what the rebuild already solved, what the literature demands, and what is architecturally wrong with the current `simulate`-as-claim. §6 is the finalized design. §7 resolves the standing open questions. §8 is the migration plan. §§9–12 are risks, audit traceability, success criteria, and references.

---

## 0. Executive summary

An oracle reduction transforms a claim about some oracles into a new claim about (possibly new, possibly *derived*) oracles. The single most important design decision is **what the output claim is**. Three answers have been tried or proposed:

- The **old design** (`main`) answered: *a selection of existing oracles* (`embed : ιₛₒ ↪ ιₛᵢ ⊕ MessageIdx` + `hEq`). Provably too weak — it cannot express a folded, quotiented, or linearly-combined oracle — and it is the direct structural cause of essentially every unfinished proof on `main` (§2).
- The **current rebuild** answers: *a statement, plus a detached query-simulation program* (`simulate : QueryImpl [OStatementOut]ₒ (OracleComp ([OStatementIn]ₒ + transcript))`). The simulation idea is **correct** — it matches how FRI/STIR/WHIR/Ligero/ARC/WARP define output oracles and matches every canonical extractor definition. But the raw program as canonical claim leaves relations intensional, duplicates reification, and turns composition into unnamed plumbing (§5).
- The **finalized design** answers: *an `OracleClaim` — a public statement together with a **source-scoped virtual oracle***: a record bundling the query plan (the current `simulate`), a **total denotation into a broad semantic behavior carrier** (`Out.Sem`, defaulting to deterministic query behavior — *not* concrete oracle data), and the realization proof tying them. Concrete data materialization, provenance metadata, and compiler cost information are **separate, optional strengthenings** layered on top. `simulate` survives as a projection. Composition of virtual oracles becomes a named **resource-substitution** operation (`subst`, with tensoring and source-context equivalences) with algebraic laws up to equivalence. Security relations are stated once, semantically, on `Out.Sem`; impl-facing forms are generated adapters, not a second source of truth.

One sentence: **keep simulation as the operational semantics of output oracles; make the claim a typed object whose meaning is total into behavior; treat concrete data, provenance, and cost as strengthenings — never as the canonical carrier.**

Two important meta-points, established by the adversarial audit (§10):

1. The draft version of this design proposed `denote` into concrete oracle *data* (`Out.Data`). That is **wrong** for exactly the games ArkLib cares about: soundness and knowledge soundness quantify over *arbitrary input behaviors* (`QueryImpl [OStatementIn]ₒ Id`), which need not be realized by any concrete data (an arbitrary evaluation behavior need not come from any bounded-degree polynomial). The corrected target is a semantic carrier `Out.Sem` broad enough to include behavior. This **vindicates the design-consensus note's instinct** that behavior-level semantics is primary; what the note's architecture was missing is packaging, intrinsic totality, intrinsic coherence, and composition laws — not a reversal of its semantics.
2. The codebase is already converging on the right packaging: `Verifier.TerminalOutput` in the newer programmatic layer (`Oracle/Program.lean`) *already* bundles `stmt` with `simulate`. The migration therefore starts there, not at the legacy `Core.Verifier` seam.

The design keeps the entire `Oracle.Spec` interaction-tree layer unchanged — that layer already solved the hardest type-theoretic problem (dependent interaction with hidden-oracle noninterference, zero casts) and must not be rebuilt again.

---

## 1. What an oracle reduction must be

### 1.1 The conceptual object

The literature has converged (WHIR, STIR, ARC, WARP, folding/accumulation, and ArkLib's own talks) on the reduction-shaped view:

> An interactive oracle reduction (IOR) takes an input context — an explicit statement `𝕏₁`, oracle statements `𝕐₁`, and (for the honest prover) a witness `𝕎₁` — runs an interaction in which the prover may send both public values and oracle messages, and outputs a new context `((𝕏₂, 𝕐₂), 𝕎₂)`. Crucially, **`𝕐₂` is implicitly defined** in terms of `𝕏₁`, the challenges, and *oracle access to* `𝕐₁` and the prover's oracle messages.

An IOP is the degenerate case where the output relation is a decision. Completeness says honest execution lands in the output relation; knowledge soundness says a witness for the output claim can be pulled back to a witness for the input claim. Security composes by chaining reductions (with error accumulation), and whole SNARKs arise by compiling a composed chain (BCS/Merkle for vector oracles, PCS for polynomial oracles, Fiat–Shamir for interaction).

### 1.2 Why "implicit output" is not optional

Concrete instances of implicitly-defined output oracles, from the requirements catalog (§4):

- **FRI / STIR folding:** the next codeword claim is about `Fold(f, r)` — answered by querying `f` at the coset of the query point and combining with challenge `r`. STIR additionally forms *quotient* oracles.
- **WHIR constrained oracles:** batching by random linear combination produces a virtual oracle `g = Σ γᵏ·fₖ` that is never materialized.
- **Ligero / Brakedown row checks:** the claim is about `rᵀU` for the matrix oracle `U`.
- **Sumcheck:** each round reduces `Σₓ P(r₁..rᵢ₋₁, x) = Tᵢ₋₁` to the same shape with one variable fixed — the "output oracle" is the *same* `P`, but the claim about it changed; in Spartan-invoking-sumcheck the polynomial is itself virtual (`eq(τ,X)·(a·b−c)(X)`).
- **Accumulation (ARC, WARP):** output accumulators have short explicit parts and long oracle parts defined via prior oracles.

An output-as-data design either cannot express these (old ArkLib) or destroys succinctness by materializing them. An output-as-selection design (old ArkLib's `embed`) expresses *none* of the above except aliasing. Simulation-based output is the only shape that covers the literature. This was already the leaning in the ZKProof-era talks ("𝕐₂ implicitly defined…"), and it is correct.

### 1.3 Three notions that must not be conflated

The audit's sharpest framing. Around every output oracle there are three different things:

1. a **concrete oracle value** — e.g. a bounded-degree polynomial (an element of `Out.Obj i`);
2. an **arbitrary deterministic oracle behavior** — a `QueryImpl [Out.Obj]ₒ Id`, i.e. an assignment of answers to queries with no promise that any concrete value induces it;
3. a **typed query program over earlier resources** — a `QueryImpl [Out.Obj]ₒ (OracleComp Src.spec)`, the thing the verifier actually defines.

The current rebuild keeps (2) and (3) but leaves (1) as an optional bolt-on, causing the §5 problems. The draft of this design tried to make (1) canonical, which fails in malicious settings (§6.2). The finalized design orders them correctly:

> **(3) is the operational claim** the verifier outputs; **(2) is its total meaning** (the semantic carrier); **(1) is an optional strengthening** available in honest/complete executions and wherever a protocol proves it.

Security relations live at level (2). Compilation consumes level (3) plus explicit metadata. Level (1) appears in completeness (the honest prover *does* have concrete data) and in materialization for commitment.

### 1.4 Why implicit output alone is not enough

Three problems appear when the *raw simulation program* is the canonical claim — precisely the points that made this design "very difficult to hammer out":

1. **Well-definedness of relations.** Two `QueryImpl`s can answer every query identically yet be different programs (bind structure, query order, query count). A relation on programs is free to distinguish them; nothing forces it to respect observational equivalence. "The output claim" is then not a mathematical object.
2. **Meaning as an optional bolt-on.** If denotation is optional, games about *actual output oracles* must re-prove coherence (`OutputRealizes`) inside every statement, and the reification API duplicates (reduction-side and verifier-side), with existential adapters that drop the realization fact.
3. **Composition has no algebra.** Substituting one virtual oracle program into another is *the* fundamental composition operation, but with raw programs it appears as bespoke `simulateQ` routing at every site (sequential composition, boundary pullback, chains, choreographies), with no identity/associativity laws to reuse.

---

## 2. Autopsy of the old design (`main`, `ArkLib/OracleReduction/`)

This section records *why* the old design could not scale, so the failure mode is never reintroduced. (Very-thorough survey, 2026-07-12; paths relative to the `main` worktree.)

### 2.1 The structural flaw

`OracleVerifier` (`OracleReduction/Basic.lean:271-308`):

```lean
verify : StmtIn → pSpec.Challenges →
  OptionT (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ))) StmtOut
embed  : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx
hEq    : ∀ i, OStmtOut i = match embed i with
  | .inl j => OStmtIn j | .inr j => pSpec.Message j
```

Output oracle statements must be **literally equal to** (a cast of) an input oracle or a prover message. The design docs admit it: *"the oracle verifier cannot do anything more in returning the output oracle statements, other than specifying a subset of the ones it has received"* (`Basic.lean:268-269`). At execution time the output is reconstructed by rewriting along `hEq` with `▸` — runtime casts along equality proofs, the exact pattern the rebuild's guardrails now forbid.

The fix was already known and sits next to the definition, commented out (`Basic.lean:277-293`):

```lean
-- TODO: this seems like the right way for compositionality
-- simOStmt : QueryImpl [OStmtOut]ₒ (OracleComp ([OStmtIn]ₒ + [pSpec.Message]ₒ))
```

### 2.2 The measurable consequences

- **`OracleVerifier.append`'s `verify` field is a literal `sorry`** (`Composition/Sequential/Append.lean:152-158`) — composition of oracle verifiers is a hole, not an unproven theorem.
- **All five sequential-composition security theorems are `sorry`** (`append_completeness/_soundness/_knowledgeSoundness/_rbrSoundness/_rbrKnowledgeSoundness`, same file, lines 425-515). The N-ary `seqCompose_*` theorems call them in their induction step, so **every downstream "sorry-free" result is transitively backed by `sorryAx`** — including full-sumcheck completeness + RBR-KS in `ProofSystem/Sumcheck/Spec/General.lean`, whose own file greps clean.
- **`OracleStatement.Lens` was never designed**: `LiftContext/Lens.lean:60-94` has the needed `simOStmt`/`liftOStmt` fields *commented out* with "TODO: figure out the right way to define this … haven't figured it out" (recurring at 458, 505). Without oracle-statement lenses, virtualization (Spartan-invoking-sumcheck) cannot even be stated. Nearly all `liftContext_*` security transports are `sorry`.
- **Ambient pain:** 99 sorries in `OracleReduction/` alone; 65 `dcast`, 203 `cast`, 167 `Fin.cast*` occurrences; `Prover.append` needs ~10 manual `by_cases` over `Fin` arithmetic; instance-diamond workarounds baked into empty-protocol instances "to avoid diamonds later in sequential composition"; the flat `Fin n → Type` protocol shape forces all of this.
- Oracle security definitions are thin wrappers over non-oracle ones via `toReduction` — flagged as the wrong factoring by the design docs themselves (`Security/Basic.lean:44-63`).

### 2.3 The lesson

Three independent failures — output typing (`embed`), composition (`Fin` arithmetic + casts), and virtualization (no oracle lens) — trace to two roots: (a) output oracles as *selections of data* rather than *derived query behaviors*, and (b) flat round-indexed protocol shapes rather than dependent trees. The rebuild fixed (b) completely and fixed the expressiveness half of (a); what remains is giving (a)'s outputs their proper claim structure. A second lesson, reinforced by the audit: **never advance operational machinery faster than its theorem support** — the old branch's composition operators existed for years with their security theorems as sorries, poisoning everything downstream.

---

## 3. State of the rebuild (`ArkLib-core-rebuild`, `ArkLib/Interaction/`)

### 3.1 What is already right (do not touch)

- **`Oracle.Spec`** (`Interaction/Oracle/Spec.lean`): protocols as a free monad over a two-constructor polynomial functor — `.public X rest` (continuation may depend on the message) and `.oracle X cont` (continuation structurally constant: `B (.oracle X) = PUnit`). Hidden-oracle noninterference is **definitional**, not an invariant: the protocol tree *cannot* branch on an oracle message. The literature catalog rates exactly this ("transcript-dependent interaction + hidden-oracle noninterference") among the four hardest requirements; it is solved.
- **Two transcripts:** `PublicTranscript` (public moves + `PUnit` markers at oracle nodes — the verifier's view and the index for everything downstream) vs `FullTranscript` (actual oracle messages). Output statement/oracle/witness families are indexed by `PublicTranscript`, making them definitionally independent of oracle values.
- **Query infrastructure:** `QueryHandle s od pt` / `toOracleSpec s od pt` give the transcript-oracle spec along a public path; `answerQuery s od tr : QueryImpl (toOracleSpec …) Id` answers from a full transcript. `append` on specs/roles/decos computes by structural recursion.
- **`SharedIn` spine** (per the design-consensus note): `Context`, `Roles`, `OracleDeco`, and all statement/witness families depend on ambient `SharedIn`; `StatementIn` is the carried local claim inside that spine. Top-level protocols are `StatementIn := fun _ => PUnit`; mid-protocol suffixes put prefix data in `SharedIn`. This uniformity is what lets `Reduction.comp` type-check without casts.
- **Plain layer** (`Interaction/Reduction.lean`, `Interaction/Security/`): provers as monadic-setup strategies, verifiers as counterpart strategies, `Reduction.execute`, and a fully proven `execute_comp`. Plain security definitions and composition theorems exist.
- **The programmatic layer** (`Oracle/Program.lean`, `ProgramExecution`, `ProgramSpec`, `Oracle/Security/Program.lean`): notably, `Verifier.TerminalOutput` (`Program.lean:22`) **already packages `stmt` with `simulate`** — the codebase independently converged on the claim-packaging half of this design. This is the migration's entry seam (§8).
- **Measured health:** zero `cast`/`HEq`/proof-generated transports in the oracle composition files; exactly one `sorry` in all of `Interaction/` (`Security/ClaimTree.lean:150`, a probability lemma unrelated to oracles).

The old cast/`HEq` problem is *solved*. Every remaining issue is semantic architecture, not dependent equality.

### 3.2 What is unresolved (the subject of this document)

The oracle verifier (`Interaction/Oracle/Core.lean:155-188`):

```lean
structure Verifier.WithMonads … where
  toFun : (shared : SharedIn) → StatementIn shared → CounterpartStrategy … StatementOut
  simulate : (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
    QueryImpl [OStatementOut shared pt]ₒ
      (OracleComp ([OStatementIn shared]ₒ + (Context shared).toOracleSpec (OracleDeco shared) pt))
```

and the security layer (`Interaction/Oracle/Security/Basic.lean`):

```lean
InputImpl  := QueryImpl [OStatementIn shared]ₒ Id                       -- absolute, deterministic
OutputImpl := QueryImpl [OStatementOut shared pt]ₒ (OracleComp (input + transcript))  -- relative
OutputRealizes : … outputImpl … oStatementOut … : Prop                   -- query-level agreement
InputRelation  := stmt → InputImpl → wit → Prop
OutputRelation := inputImpl → pt → stmtOut → OutputImpl → witOut → Prop
```

with an optional, `Option`-valued reification layer (`Oracle/Reification.lean`, duplicated verifier-side at `:437`) and a boundary/lens layer (`Boundary/*.lean`) carrying separate access + reification + coherence data.

---

## 4. Requirements from the literature (condensed)

The full 35-requirement catalog with citations is in the archived delegate report (§13). The load-bearing subset:

| # | Requirement | Exemplars | Status in rebuild |
|---|---|---|---|
| R1 | Reductions between relations, not accept/reject | sumcheck, FRI, STIR, Nova, ARC, WARP | ✅ transcript-indexed `StatementOut`/`WitnessOut` |
| R3 | Multiple input/output claims (heterogeneous contexts) | WHIR batching, ProtoGalaxy | ✅ indexed families `ιₛ → Type` |
| R4 | Honest-prover witness forwarding ≠ verifier output | Nova, WARP split accumulators | ✅ `HonestProverOutput` vs verifier statement |
| R5–R7 | Heterogeneous interfaces; structured queries; adaptive query phases | point/poly/tensor/matrix oracles | ✅ `OracleInterface` + query-time simulation |
| R8, R12 | Mixed public/oracle messages; noninterference at type level | IPCP, STIR scalars | ✅ `.public`/`.oracle` |
| R9 | Holographic / preprocessed oracles, with **origin distinctions** | Marlin indexer | ⚠️ expressible via `SharedIn` + input slots, but origin (trusted setup vs indexer vs prover) is not recorded — needed for setup binding and Fiat–Shamir absorption (§6.8) |
| R11, R13, R14 | Dependent trees; arbitrary speaking order; private-coin allowed, public-coin as extra structure | FRI round counts; Marlin multi-oracle rounds | ✅ tree + role decorations + `PublicCoinVerifier` |
| **R17** | **Virtual outputs by query simulation** | FRI/STIR/WHIR/Ligero/ARC | ✅ `simulate` — the core insight |
| **R18** | **Fresh and virtual outputs coexist, with origins** | STIR: new codeword *and* fold view | ⚠️ needs origin-tagged resources (`input \| setup/index \| sent-at-node \| derived`) |
| **R19** | **Provenance as typed dependencies** | nested folds, accumulation | ❌ raw `QueryImpl` erases provenance; sum-position is *scoped access*, not provenance (§6.9) |
| **R20** | **Extensional vs intensional equality, no quotient** | same behavior, different cost | addressed by design (§6.3) |
| R21–R24 | Dependent sequential comp; lenses; recursion/IVC; algebraic laws | everything | ⚠️ comp exists; no laws; lens layer heavy |
| R25–R31 | Completeness w.r.t. output relations; KS; RBR (+ relaxed CDHZ 25/2166); special soundness/trees; state restoration; ZK views | — | ⚠️ defs exist at impl level; no oracle-level composition theorems; RBR needs prefix-scoped resources (§6.7) |
| R32–R35 | BCS from interfaces; PCS compilation; Fiat–Shamir; cost semantics | — | ⚠️ BCS stops at protocol messages; reduction-output compilation needs the metadata layer (§6.9) |

The catalog's "four hardest requirements to satisfy simultaneously":

1. dependent interaction ∧ hidden-oracle noninterference — **solved** by `Oracle.Spec`;
2. **virtual outputs ∧ provenance-safe composition — the single largest remaining gap**;
3. one executable semantics supporting incompatible extraction styles (straightline, RBR, relaxed-RBR, tree/special-soundness, state restoration);
4. general composition ∧ compiler-faithful cost/visibility.

The finalized design targets (2) in two stages — source-scoped claims now (§6.3–6.6), provenance metadata as a compiler-facing extension (§6.9) — and keeps (3), (4) satisfiable.

### 4.1 The extractor question (settled by the literature)

Across BCS16 §4.2, Block–Garreta–Tiwari–Zając 2023 Def 3.12, Chiesa–Di–Hu–Zheng 2025/2166 Def 3.6, and FICS/FACS 2025/737 Def 4.4: the extractor receives the statement, query/data access to input oracles, and the **concrete transcript** — prover oracle messages as full objects (or stronger: rewinding / partial-transcript / tree access); the output oracle is **determined by the verifier's simulation** and is never supplied by the prover as data. The rebuild's `Extractor.Straightline` (`Oracle/Security/Basic.lean:152`) already matches this. Consequently (audit finding 8, correcting the draft): the **full-transcript extractor is the literature-aligned default** and keeps the name `knowledgeSoundness`; a query-only extractor is a *stronger* notion worth having as `knowledgeSoundnessQueryOnly`, with the implication `queryOnly → fullTranscript` proven explicitly. The KS-survey note's remaining conclusions stand: no `OutputRealizes` in the KS event; the prover never outputs oracle data; coherence is a verifier property used by completeness.

---

## 5. Analysis: what is wrong with `simulate`-as-claim

The delegate design-review identified nine concrete pain points; the five structural ones:

1. **Detached pair.** The legacy verifier returns `StatementOut` through the strategy and `simulate` through a separate field, indexed only by `pt`. Nothing ties them together as one claim; every construction site (`Reduction.ofChain`, `Oracle/Chain.lean:329,337`; `Choreo.lean:346,360`) must supply both halves independently, and completeness must reconcile them later. (The programmatic `TerminalOutput` already fixes the packaging half — but not the semantics half.)
2. **Relations over programs.** `OutputRelation` takes the raw `OutputImpl`. Two observationally-equal programs can be distinguished; relations are well-defined only up to a discipline nobody enforces (`Oracle/Security/Basic.lean:105-128`). The reified adapters (`Oracle/Reification.lean:213,240,607`) existentially choose concrete data *without* the realization link, so the reified games must re-assert `OutputRealizes` inside the probability event (`Reification.lean:611`).
3. **Reification duplicated, partial, and vacuously satisfiable.** Two near-identical `Option`-valued APIs (reduction-side `Reification.lean:106`, verifier-side `:437`); correctness required only on `some` — an always-`none` reification satisfies `correct` vacuously. Notably (audit finding B): **no protocol in the repo actually needs the `none` branch** — the working Spartan boundaries use *total* materializers (`Boundary/Reification.lean:24`; `ProofSystem/Spartan/FirstSumcheck.lean:465`). `Option` was an architectural statement ("materialization is optional"), not evidence of essential partiality.
4. **Composition as plumbing.** `Reduction.comp`'s middle-oracle handling — `Verifier.retargetMonads` (`Oracle/Composition.lean:546`) plus hand-assembled `routeLeft`/`routeMid`/`routeRight` (`:790`), and `retargetAmbientWithRoute` in the programmatic layer (`Program.lean:324`) — *is* virtual-oracle substitution, implemented ad hoc, with no identity/associativity laws, and re-derived from scratch in the boundary layer (`routeInnerOutputQueries`, `Boundary/Oracle.lean:487`, with a long commuting proof). There is no associativity statement for `Reduction.comp` and no oracle-level security composition theorem at all (the plain layer has them; the oracle layer doesn't).
5. **Boundary layer disproportionately large.** An oracle boundary needs separate input/output simulation, input/output materialization, and two coherence clauses (`OracleStatementAccess`, `Boundary/Oracle.lean:319`; `OracleStatementReification`, `Boundary/Reification.lean:24`) — because the claim is not an object that can be transported functorially.

Additionally, the **`Id` / `OracleComp` asymmetry**: `InputImpl` is absolute (deterministic, `Id`-valued), `OutputImpl` is relative (a program over input + transcript sources). The asymmetry is *principled* — an input is a realized environment, an output is a claim relative to it — and the finalized design keeps it, but derives both from one notion instantiated twice (§6.5–6.6) instead of two unrelated abbreviations glued by ad-hoc routing.

**And yet:** operationally, everything works. Composition executes correctly, extraction is possible (full transcript + `answerQuery` lets the extractor evaluate any output query — documented at `Oracle/Security/Basic.lean:146`), and zero casts appear. The failure is architectural, not operational: *the pieces of the right object exist — `simulate`, `Reification.reify`, `OutputRealizes` — but they live in three places with the coherence proofs owed at every use site instead of once at the definition site.*

---

## 6. The finalized design

### 6.1 Overview of the objects

```
SourceCtx        — what a virtual oracle may read: an oracle spec + the type of
                   environments realizing it (behavioral, not concrete-data)
OracleFamily     — an interface family + a SEMANTIC CARRIER `Sem` (defaults to behavior)
VirtualOracle    — denote : Env → Sem;  query : plan over sources;  query_correct
OracleClaim      — stmt (public data, may depend on verifier's own queries) + VirtualOracle
subst / tensor   — composition as resource substitution, laws up to SourceEquiv
Materialization  — OPTIONAL: concrete data from concrete sources (absorbs reification)
ResourceMeta /
CompilableVirtualOracle — OPTIONAL, compiler-facing: identity, origin, plan, cost
```

### 6.2 Source contexts and environments

```lean
/-- A source context: what a virtual oracle may query, and what realizes it.
    `Env` is deliberately behavioral: concrete data embeds into it, arbitrary
    (malicious) behavior inhabits it too. -/
structure SourceCtx where
  ι    : Type
  spec : OracleSpec.{0, 0} ι
  Env  : Type
  impl : Env → QueryImpl spec Id
```

For a reduction at ambient input `shared` and public transcript `pt`, the environment has two halves, and each is defined **structurally** (audit findings 1–2):

**Transcript half.** Not a sigma over full transcripts with an equality witness (that reintroduces transports); instead the hidden-message fiber, by recursion on the tree:

```lean
/-- The oracle messages sent along a fixed public path: the hidden-data fiber
    of `FullTranscript` over `pt`, with the public part fixed definitionally. -/
def Spec.OracleMessagesAt : (s : Spec) → Spec.PublicTranscript s → Type
  | .done, _ => PUnit
  | .public _ rest, ⟨x, pt⟩ => OracleMessagesAt (rest x) pt
  | .oracle X cont, ⟨_, pt⟩ => X × OracleMessagesAt (cont ⟨⟩) pt
```

with the induced answerer `Spec.answerAt : OracleMessagesAt s pt → QueryImpl (toOracleSpec s od pt) Id` (structural sibling of the existing `answerQuery`, which stays for full-transcript call sites). This type is always inhabited in every game — the (even malicious) prover physically sends oracle messages.

**Input half.** *Behavior*, because that is what the security games quantify (`Soundness.lean:86`, `KnowledgeSoundness.lean:71` quantify arbitrary `InputImpl`, and an arbitrary evaluation behavior need not come from any bounded-degree polynomial):

```lean
def reductionSources (shared : SharedIn) (pt : Spec.PublicTranscript (Context shared)) :
    SourceCtx where
  spec := [OStatementIn shared]ₒ + (Context shared).toOracleSpec (OracleDeco shared) pt
  Env  := InputImpl OStatementIn shared × Spec.OracleMessagesAt (Context shared) pt
  impl := fun ⟨inImpl, msgs⟩ => QueryImpl.add inImpl (Spec.answerAt _ _ msgs)
```

Concrete honest data embeds via `simOracle0`:

```lean
def SourceCtx.ofData (oStmt : OracleStatement (OStatementIn shared)) (msgs : …) : Env :=
  ⟨OracleInterface.simOracle0 _ oStmt, msgs⟩
```

This preserves the current soundness quantification exactly — **no weakening of the adversary** — while giving `denote` a total domain.

### 6.3 The central object: source-scoped virtual oracles

```lean
/-- An interface family together with its SEMANTIC CARRIER.
    `Sem` is the mathematical meaning of "an oracle of this family";
    the default carrier is deterministic query behavior. Structured carriers
    (concrete data, quotients of data, …) may be chosen when a protocol can
    support them — validity properties (degree bounds, code membership,
    proximity) belong in RELATIONS, not in the carrier. -/
structure OracleFamily where
  ι         : Type
  Obj       : ι → Type
  oracle    : ∀ i, OracleInterface (Obj i)
  Sem       : Type
  answerSem : Sem → QueryImpl [Obj]ₒ Id

/-- Default: behavior is the meaning. Always available, always total. -/
def OracleFamily.behavioral (ι Obj oracle) : OracleFamily :=
  { ι, Obj, oracle, Sem := QueryImpl [Obj]ₒ Id, answerSem := id }

/-- A source-scoped virtual oracle: the canonical form of a derived oracle.
    - `denote`  : total mathematical meaning of the claim, per environment.
                  (Absorbs the role of `Reification.reify`, without partiality,
                   because the carrier is broad enough.)
    - `query`   : operational access — the current `simulate`.
    - `query_correct` : running the plan against a realized environment
                  computes the denoted behavior. (Absorbs `OutputRealizes`
                  on the verifier side, proven once per constructor.) -/
structure VirtualOracle (Src : SourceCtx) (Out : OracleFamily) where
  denote : Src.Env → Out.Sem
  query  : QueryImpl [Out.Obj]ₒ (OracleComp Src.spec)
  query_correct : ∀ (env : Src.Env) (h : ([Out.Obj]ₒ).Domain),
    simulateQ (Src.impl env) (query h) = pure (Out.answerSem (denote env) h)
```

Notes:

- With the behavioral carrier, `denote` is *derivable* from `query` (`denote env := fun h => (simulateQ (Src.impl env) (query h)).run`), and `query_correct` is `rfl`-adjacent. The field still earns its place: (a) protocols that *can* carry a structured `Sem` state their relations against it; (b) the record is uniform across both cases, so composition and security are written once; (c) `denote` is the unique point where "what does this claim mean" is answered, which is what makes relations well-defined (§6.6).
- **Degree/proximity/code-membership go in relations, not carriers.** Making `Out.Sem` a refinement type ("polynomials of degree < d") would bake validity into an object that must exist even for *invalid* malicious executions — the audit's refinement-failure mode. The carrier is what a claim *is about*; the relation is what makes it *true*.
- Two equivalences are maintained, no quotient taken (catalog R20): **extensional/semantic** (equal `denote`) for mathematics; **intensional/operational** (the `query` program, its query pattern and cost) for compilation. Quotienting by the first erases exactly what the second needs.

### 6.4 Claims, verifiers, honest output

```lean
/-- The canonical terminal output of an oracle verifier: one object.
    `stmt` is public explicit data — produced by the verifier's own
    (possibly query-dependent) terminal computation. Scalar outputs computed
    from oracle queries (STIR shift checks, sumcheck's `Tᵢ := sᵢ(rᵢ)`) live HERE,
    never in `denote`. -/
structure OracleClaim (Src : SourceCtx) (Stmt : Type) (Out : OracleFamily) where
  stmt    : Stmt
  oracles : VirtualOracle Src Out
```

**Where this lands in the code:** the programmatic layer's `Verifier.TerminalOutput` (`Program.lean:22`) already has this shape with `simulate` in place of `oracles`. The change is: `TerminalOutput.oracles : VirtualOracle (reductionSources shared pt) (outputFamily shared pt)`, with

```lean
def Verifier.TerminalOutput.simulate (t : TerminalOutput …) := t.oracles.query
```

retained as a projection so every existing call site keeps compiling. The legacy `Core.Verifier.simulate` field follows the same pattern once the programmatic layer is proven out. The **honest prover is unchanged**: concrete `StatementWithOracles` + witness, exactly as now.

### 6.5 Composition is resource substitution (not plain bind)

The draft proposed Kleisli-style `bind`. The audit is right that sequential composition has a different shape, because **the second stage's virtual output reads both the first stage's (virtual) middle context and *new* suffix transcript resources**:

```lean
/-- Tensor of source contexts: disjoint sources, paired environments. -/
def SourceCtx.tensor (S T : SourceCtx) : SourceCtx where
  spec := S.spec + T.spec
  Env  := S.Env × T.Env
  impl := fun ⟨s, t⟩ => QueryImpl.add (S.impl s) (T.impl t)

/-- The middle context induced by a virtual oracle: its output family,
    realized behaviorally by its denotation. This is how "the output claim of
    stage 1 becomes the input context of stage 2" — the Id/OracleComp asymmetry
    derived from one notion. -/
def VirtualOracle.asSources (v : VirtualOracle S A) : SourceCtx where
  spec := [A.Obj]ₒ
  Env  := S.Env
  impl := fun env => fun h => (Out.answerSem (v.denote env) h)

/-- Resource substitution:  (S → A) and (A ⊗ T → B)  give  (S ⊗ T → B).
    Denotation:  fun (s, t) => w.denote (v.denote s, t).
    Query: route A-queries through v.query (weakened into S ⊗ T),
           route T-queries by inclusion.
    Correctness: simulateQ_compose + both query_corrects. -/
def VirtualOracle.subst
    (v : VirtualOracle S A)
    (w : VirtualOracle (v.asSources.tensor T) B) :
    VirtualOracle (S.tensor T) B
```

**Laws, honestly stated.** Sum specs are left-associated by convention (`VerifierAccess.lean:38`); `simulateQ` over reassociated sums is only propositionally equal; and `PublicTranscript.split`/`append` are mutually inverse by theorem, not by reduction (`Spec.lean:771,825`). So the algebra is stated **up to explicit source-context equivalence**:

```lean
structure SourceEquiv (S T : SourceCtx) where
  envEquiv     : S.Env ≃ T.Env
  queryEquiv   : …   -- typed reindexing of the specs (sum associators/units)
  impl_natural : …

def VirtualOracle.rebase (e : SourceEquiv S T) : VirtualOracle S A → VirtualOracle T A

theorem VirtualOracle.subst_assoc :
  subst (subst v w) u ≈ rebase SourceEquiv.tensorAssoc (subst v (subst w u))
theorem VirtualOracle.subst_id_left / subst_id_right : …   -- with tensorUnit rebase
```

where `≈` is: equal `denote` modulo `envEquiv` (definitional where sums associate definitionally), extensional equality of `query` after reindexing. This is *strictly more* algebra than the current design has (which has none), and it is the honest amount: **reduction-level associativity of `Reduction.comp` is not promised by this design.** If cast-free reduction-level reassociation becomes load-bearing, the known-viable route is the `Spec.Presentation` layer prototyped in the raw-append note, and/or promoting an n-ary `Chain`/`Telescope` normal form to canonical status with binary `comp` as a view. An honest reduction-level statement would be an `ExecutionEquivalent` between reassociated composites, containing a transcript-presentation isomorphism, family reindexing, extensional output-behavior equality, and execution-distribution equality.

**What `subst` explains and what it does not.** The middle-oracle routing of `Reduction.comp` (`routeMid` interpreting `[OStmtMid]ₒ`-queries through stage 1's simulator, `routeLeft`/`routeRight` embedding transcript queries — `Composition.lean:790`) becomes the `subst` instance for sequential composition; boundary `pullback`'s `routeInnerOutputQueries` becomes another instance. But **`retargetMonads`/`retargetAmbientWithRoute` are not deleted**: they rewrite the *interactive-phase* verifier computations (every suffix receiver node's ambient access), which `subst` — a statement about terminal claims — does not cover. They remain, ideally re-derived as the strategy-level functorial action of the same substitution; if that abstraction fights Lean, they remain as-is, and the claim-level algebra still carries the security proofs. (Audit findings 3, 5, G.)

### 6.6 Security definitions

**One canonical relation layer, semantic** (audit amendment 3.6):

```lean
abbrev InputRelation :=
  (shared : SharedIn) → StatementIn shared →
  InputEnv shared →                         -- behavioral, as today
  WitnessIn shared → Prop

abbrev OutputRelation :=
  (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
  (env : (reductionSources shared pt).Env) →      -- NOTE: env now in signature
  StatementOut shared pt →
  (outputFamily shared pt).Sem →                  -- semantic carrier, not impl, not data
  WitnessOut shared pt → Prop
```

and games evaluate `relOut shared pt env claim.stmt (claim.oracles.denote env) witOut`. Adding `env` to the signature is itself a correction the audit forced: the *current* `OutputRelation` receives only `inputImpl` and `pt`, so it cannot even state environment-relative observational equivalence.

- **Completeness.** `query_correct` connects the *verifier's plan* to `denote`. It does **not** discharge the *prover-side* obligation (audit finding 4): honest concrete output data must still be shown to realize the denoted behavior:

```lean
def ProverOutputRealizes (sem : Out.Sem) (data : ∀ i, Out.Obj i) : Prop :=
  ∀ h, OracleInterface.answer (data h.1) h.2 = Out.answerSem sem h
```

  Completeness = statement agreement + `ProverOutputRealizes (claim.oracles.denote env) proverData` + `relOut … (claim.oracles.denote env) …`. The current `OutputRealizes` becomes a *derived lemma* (from `query_correct` + `ProverOutputRealizes`), *not* a dissolved one. Literal equality of concrete data is available only under an explicit faithfulness assumption, which does not currently exist in `OracleInterface` and must not be smuggled in:

```lean
class OracleFamily.Faithful (Out : OracleFamily) : Prop where
  eq_of_answers_eq : (∀ i q, answer (x i) q = answer (y i) q) → x = y
```

- **Soundness / knowledge soundness.** Events stated on `claim.oracles.denote env` where `env` is the game's realized environment — arbitrary `InputImpl` (unchanged quantification, no adversary weakening) plus the hidden messages the malicious prover actually sent. With the behavioral default carrier, the new statements are intertranslatable with the current ones; **the migration requires the comparison theorems** `behaviorSecurity → semanticSecurity` and (under explicit realizability/faithfulness hypotheses) the converse, *before* any cutover (§8, step 6). If the converse fails for some protocol class, the semantic notion is a new notion, not a replacement — this is the single riskiest point of the whole migration and is treated as such.
- **Knowledge-soundness extractor.** Literature-aligned default keeps the full transcript (§4.1): `knowledgeSoundness` = current `Extractor.Straightline` inputs, with `outputImpl` replaced by the claim (the extractor may evaluate `claim.oracles.query` since it holds the transcript). `knowledgeSoundnessQueryOnly` — extractor limited to query access on input oracles and the denoted output behavior — is defined as a *stronger* notion with the implication proven. The KS event contains no realization clause (per the KS survey); coherence lives in completeness.
- **RBR (knowledge) soundness.** State functions are indexed by transcript *prefixes* of the tree. The audit's constraint: a final-transcript `denote` is the wrong primitive for intermediate states — at a prefix, future resources do not exist. Therefore virtual oracles must be **prefix-scoped**: `reductionSources` is really a family over prefixes (monotone in prefix extension), and RBR states consult denoted behaviors of prefix-scoped virtual oracles. This costs nothing now (the `pt`-indexed definition *is* the full-prefix instance) but must be designed in before the RBR oracle file is written, not retrofitted. The relaxed CDHZ 2025/2166 Def 3.6 and FICS/FACS RBRTE (Def 4.4; composition-preserving, Lemma 4.7) layer on top and are the designated route for KS *composition*.
- **The impl-facing layer is generated, not authored.** One semantic relation is the source of truth; impl-facing predicates are produced by evaluation (`fun impl => relOut … (evalToSem impl env) …`); environment-relative observational equivalence is the invariance notion:

```lean
def ObsEqAt (env : Src.Env) (p q : QueryImpl [Out.Obj]ₒ (OracleComp Src.spec)) : Prop :=
  ∀ h, simulateQ (Src.impl env) (p h) = simulateQ (Src.impl env) (q h)
```

  Legacy handwritten impl predicates that must survive require an explicit equivalence theorem against the generated adapter — not a one-way `Respectful` marker (audit finding 9/F).

### 6.7 Constructors: leaves, combinators, escape hatch

The virtual-oracle *language* is a library of smart constructors, each carrying `query_correct` once. It is **not a closed AST**: the record is canonical; `ofPlan` keeps it open.

Initial set (deliberately minimal — audit §5 pruned the up-front zoo):

```lean
VirtualOracle.id / passthrough      -- alias the sources (sumcheck's P; old embed .inl/.inr)
VirtualOracle.reindex               -- selection / permutation / projection
VirtualOracle.tensorWeaken          -- use fewer sources
VirtualOracle.rebase                -- along SourceEquiv
VirtualOracle.subst                 -- §6.5
VirtualOracle.ofPlan                -- the escape hatch: (query, denote, proof)
```

Algebraic constructors — `linComb` (WHIR batching, Ligero rows), `fold` (FRI/STIR/WHIR), `quotient` (STIR; **with its validity predicate in the output relation**, since quotient semantics is conditional) — are added **when the first protocol port needs them**, each landing with its `query_correct` and (where applicable) a `Materialization`. The three vertical slices in the migration plan (§8) force exactly the right first ones.

**Lenses/boundaries.** The old, never-completed `OracleStatement.Lens` needed exactly `simOStmt` + `liftOStmt` + coherence; that *is* a `VirtualOracle` from the outer source context to the inner family (projection direction) plus `subst` for the lift direction. The boundary layer's `OracleStatementAccess` + `OracleStatementReification` + two coherence clauses collapse to: *a boundary carries a virtual oracle each way; `pullback` is substitution.* The existing total Spartan materializers (`FirstSumcheck.lean:465`) are preserved as `Materialization`s (§6.8), not deleted.

### 6.8 Materialization (optional strengthening; absorbs reification)

```lean
/-- Concrete data for a virtual oracle, from concrete sources. Optional:
    exists when a protocol proves it, required only by compilation that
    chooses to materialize. Replaces both duplicated reification APIs.
    (No classical choice: this is an executable artifact.) -/
structure Materialization (v : VirtualOracle Src Out)
    (ConcreteSrc : Type) (OutData : Type) where
  forget      : ConcreteSrc → Src.Env
  materialize : ConcreteSrc → OutData          -- total here; Option only if genuinely needed
  answerData  : OutData → QueryImpl [Out.Obj]ₒ Id
  correct     : ∀ src, answerData (materialize src) = Out.answerSem (v.denote (forget src))

structure ExecutableMaterialization (…) extends Materialization … where
  cost : CostModel
```

This is the honest home of the old `Reification` layer: total where protocols are total (all current uses are), partial only if a genuine case ever appears, and never load-bearing for security definitions — so the "always-`none` satisfies correctness" vacuity cannot recur.

### 6.9 Provenance and compilation (deferred, and honestly labeled)

The audit's finding 6 is accepted in full: **the sum-spec position of a query is scoped access, not provenance.** Nested sum positions change under reassociation, distinguish same-typed resources only by fragile injection paths, and tell a compiler nothing about binding time, commitment identity, opening plans, or cost. Therefore:

- The core abstraction of this document is named and documented as **source-scoped** virtual oracles. It fully serves definitions, composition, and security proofs.
- The **compiler-facing layer** is a separate extension, to be designed *before* BCS output-compilation is attempted (and before state-restoration/RBRTE machinery freezes resource identity semantics — replay must replay the *same* resources, not fresh same-typed ones):

```lean
structure ResourceMeta where
  id               : ResourceId          -- stable identity, survives reassociation
  origin           : ResourceOrigin      -- input | setup/index | sent-at-node | derived
  visibility       : Visibility
  bindingPoint     : ProtocolPosition
  commitmentPolicy : CommitmentPolicy
  encoding         : EncodingMeta

structure CompilableVirtualOracle (Src Out) extends VirtualOracle Src Out where
  dependencies : Finset ResourceId
  plan         : TypedPlan Src Out       -- inspectable operation structure
  erase_plan   : plan.erase = query
  cost         : PlanCost plan
```

- The **origin taxonomy** also answers the holographic requirement (R9): Marlin-style indexer oracles are input-slot *typed* but `setup/index`-*originated*, which is what statement/setup binding and Fiat–Shamir absorption ordering need. Fresh-vs-virtual coexistence (R18: STIR sends a new codeword *and* checks it against a virtual fold) is likewise an origin distinction (`sent-at-node` vs `derived`).
- Per-handle **inline vs materialize** BCS policy is real but gated on this layer plus `ExecutableMaterialization`: inlining compiles the plan into downstream checks (cost = source openings per virtual query); materializing commits `materialize`'s output and must prove observational equivalence of the two branches. PCS compilation consults `plan` for homomorphic discharge (`linComb` free under homomorphic commitments; `quotient` needs an opening argument).
- **Not covered by `subst` and deliberately separate** (R15): shared-prefix product, lock-step repetition, and batched-shared-challenge combinators. Sequential substitution must not be contorted to fake these; they are their own (later) combinators with their own challenge-scoping.

### 6.10 Universe discipline

`Oracle.Spec` is pinned (`Spec : Type 1`, messages in `Type`, ambient `OracleSpec.{0,0}`; `TerminalOutput` families in `Type` — `Program.lean:28`). The new records are introduced **at the same pinned universes** (`Src.Env : Type`, `Out.Sem : Type`). Universe polymorphization remains the tracked follow-up it already is in `Spec.lean`'s NOTE; a freely polymorphic `VirtualOracle` would escape the universe expected at terminal program leaves and force generalizing `Program`/`TerminalOutput`/output families wholesale.

---

## 7. Resolution of the open questions

From the design-consensus note (`ArkLib-Refactor_oracle_reduction_as_ior.md`, "What Still Remains Open") and the original uncertainty about oracle simulation:

1. **"Should the oracle input/output relations become more directly oracle-semantic?"** Resolved, with a precise split the note did not yet have vocabulary for. The note said *behavior primary, reification optional* — the audit confirmed this is correct for the **carrier** (soundness games quantify behaviors; concrete data cannot be canonical). What changes is that the *claim* becomes a typed object: total denotation into the behavioral carrier, coherence intrinsic, composition lawful. So: behavior remains the primary semantics (note vindicated); the raw `QueryImpl` stops being the primary *object* (note's architecture amended). Relations are stated once, semantically, with the environment in their signature; impl-facing forms are generated adapters.
2. **"How far to unify explicit and implicit output presentation?"** At the claim object: `stmt` + `oracles` are one record (`TerminalOutput` already is this); the honest prover's concrete data stays separate and meets the claim in completeness through `ProverOutputRealizes`. Full unification (claim carries concrete data) was considered and **rejected** — that is the draft's `denote`-into-data mistake.
3. **"Is `simulate` the right intuitive idea?"** Yes — validated independently by the literature (R17), by the old design's failure (its absence is why `main` is stuck), and by the extractor literature (the output oracle is verifier-determined). The difficulty in hammering it out was real and is now precisely diagnosable: the idea was right; the canonicalization was off by one level (program vs. claim-containing-program), and the first attempt to fix *that* overshot by one level in the other direction (data vs. behavior). The stable point is: **claim = statement + (plan, behavior-denotation, coherence)**.
4. **Naming:** follow the note (`OStatementIn`/`OStatementOut`; defer `ExplicitInstance`/`ImplicitInstance`). New objects: `SourceCtx`, `OracleFamily` (with `Sem`), `VirtualOracle`, `OracleClaim`, `VirtualOracle.subst`, `Materialization`, `CompilableVirtualOracle`. The document deliberately says "source-scoped virtual oracle," reserving "provenance-carrying" for the §6.9 extension.
5. **`Id` vs `OracleComp` asymmetry:** principled and kept; both sides now arise from one notion — a `SourceCtx` is a realized (behavioral) environment; a `VirtualOracle` is a claim relative to it; `asSources` + `subst` turn the output claim of one stage into the input context of the next.

---

## 8. Migration plan (revised per audit)

Ordered so the build stays green and **no security definition changes before its comparison theorem exists**. The entry seam is the programmatic layer, not legacy `Core`.

1. **Semantic substrate first, no semantics changes.** New `Interaction/Oracle/Virtual.lean`: `SourceCtx`, `OracleFamily` (+ `behavioral`), `VirtualOracle`, `OracleClaim`; `Spec.OracleMessagesAt` + `answerAt` + conversion lemmas to/from `FullTranscript`/`answerQuery`; honest-data embedding `ofData`. Move the `simulateQ_*` lemmas from `Boundary/Oracle.lean:31-125` to a neutral home. *Blast radius: none (new code).*
2. **Prototype on `Verifier.TerminalOutput`** (`Program.lean:22`): add `oracles : VirtualOracle …`, keep `simulate` as the projection. Legacy `Core.Verifier` untouched. *Blast radius: programmatic layer only.*
3. **Three vertical slices** (these force the right first constructors and expose problems early):
   - **programmatic single-round sumcheck** (`ProofSystem/Sumcheck/Interaction/SingleRoundProgram.lean`) — scalar-from-query outputs in `stmt`, passthrough oracle;
   - **Spartan first-sumcheck boundary** (`ProofSystem/Spartan/FirstSumcheck.lean:465`) — boundary-derived virtual polynomial; preserve its total materializer as a `Materialization`;
   - **FRI fold phase** (`ProofSystem/FRI/Interaction/FoldPhase.lean:528`) — multi-stage transcript sources, fresh + derived coexistence.
4. **Realization bridges.** Prove current `OutputRealizes` and programmatic completeness from `query_correct` + `ProverOutputRealizes`; add `OracleFamily.Faithful` where literal data equality is wanted. *Nothing deleted yet.*
5. **Substitution algebra.** `tensor`, `tensorWeaken`, `rebase`, `SourceEquiv`, `subst`, laws up to equivalence. Use it to simplify the *terminal-simulator* routing in programmatic composition (`Program.lean:324,446`); keep `retargetAmbientWithRoute`/`mapAmbientOracles` for the interactive phase.
6. **Security comparison theorems — the gate.** `behaviorSecurity → semanticSecurity` and, under explicit realizability/faithfulness hypotheses, the converse, for completeness / soundness / KS on the slice protocols. **If a converse fails, stop and reassess: the semantic notion is then a new notion, not a replacement.** This is the single riskiest step of the migration; it changes *meaning*, not code shape, and superficially-easier Lean goals are exactly the failure smell (non-realizable attacks silently dropped).
7. **Cut over oracle security** to the semantic relations (env in signature; carrier-valued; extractor default = full-transcript `knowledgeSoundness`, plus `knowledgeSoundnessQueryOnly` + implication). Then state and prove the **oracle-level composition theorems** (completeness first; KS via RBR/RBRTE per the KS survey). RBR files are written prefix-scoped from day one (§6.6).
8. **Associativity as equivalence/normalization.** Prefer `Chain`/`Telescope`/`Presentation`-based n-ary composition as the canonical associative interface; binary `comp` stays a view. Only attempt an `ExecutionEquivalent` reassociation theorem if a client needs it.
9. **Provenance layer, then BCS output compilation.** `ResourceMeta`/origins/`TypedPlan`/cost (§6.9) — designed before state-restoration/RBRTE freeze resource-identity semantics — then per-handle inline/materialize with the observational-equivalence obligation.
10. **Delete duplication last.** The two reification APIs, the split terminal-output adapters in `Security/Program.lean`, and `Boundary`'s parallel access/reification hierarchies are removed only when their replacement theorems exist (Spartan materialization proofs must never be orphaned).

**Blast-radius inventory for the eventual legacy cutover** (step 7's second half, from the audit): `Core.lean:155`, `Execution.lean:693`, `Composition.lean:605`, `Program.lean:28`, `ProgramExecution`/`ProgramSpec`/`VerifierAccess`, `Chain.lean:288`, `Choreo.lean:303`, FRI/sumcheck/Spartan construction sites, all oracle security files, boundary pullback/reification, BCS-facing adapters.

---

## 9. Risks and rejected alternatives

**Rejected: output as concrete data or as selection.** §2; destroys expressiveness (selection) or succinctness (eager data).

**Rejected: `denote` into concrete `Out.Data` as canonical** (the draft's version). Fails in malicious games (unrealizable behaviors), forces refinement-carrier paradoxes (an invalid execution would need a valid-typed denotation), collides with non-faithful interfaces (no canonical representative), and cannot host quotient/rational views with validity conditions. Concrete data lives in `Materialization` and in completeness.

**Rejected: quotient of implementations.** Extensionally clean, operationally useless: representatives, costs, provenance, serializability all die. A quotient may later exist as a *theorem-layer* device, never the carrier.

**Rejected: closed virtual-oracle AST.** A grammar of all derived-oracle forms is a second formalization project that will trail the literature forever. The record is canonical; `ofPlan` keeps it open; constructors are conveniences with pre-proved obligations. *The generality lives in the record, not the grammar.*

**Rejected: raw pair (statement, QueryImpl) with no denotation.** The minimal packaging fix (and `TerminalOutput` already is it) — but it leaves relations intensional and reification bolted on; strictly dominated at the cost of two fields.

**Rejected: plain Kleisli `bind` as the composition primitive.** Sequential composition introduces new suffix resources; the true shape is `(S→A) → (A⊗T→B) → (S⊗T→B)` with weakening and associators. Pretending otherwise would have hidden exactly the reassociation obligations that must be explicit.

**Risk: the semantic cutover (step 6/7).** Mitigated by the comparison-theorem gate and by doing slices first. This risk is *why* the migration refuses to change definitions before bridging theorems exist.

**Risk: `retargetMonads`-as-`subst`-action doesn't materialize.** Acceptable: the interactive-phase routing stays hand-written; the claim-level algebra still carries the security proofs. The composition *theorems* — the actual point — do not depend on winning that refactor.

**Risk: prefix-scoping arrives late.** If RBR files are written against final-transcript claims, retrofitting prefix scoping will be a second migration. Hence the §6.6 rule: RBR is written prefix-scoped from its first line, and resource identity (for replay/state-restoration) is settled in step 9 before RBRTE.

**Deferred, deliberately:** universe polymorphization; shared-prefix/lock-step/batched products; multiparty roles; quantum oracles (linear resources — out of scope, per the catalog's explicit classical boundary); ZK/view simulation (needs the visibility part of `ResourceMeta`); abort/failure outcome taxonomy (R16) — currently handled per-protocol via `StatementOut` choice, revisit when a client protocol needs uniform treatment.

---

## 10. Audit traceability

Findings of the adversarial audit (GPT 5.6 Sol, xhigh, full code access; archived as `gpt-audit.md`) and their disposition:

| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | Critical | `denote : Src.Data → Out.Data` unavailable in soundness/KS games (arbitrary `InputImpl` unrealizable as data); restricting quantification would weaken security | **Accepted; design changed.** Carrier `Out.Sem`, default behavioral (§6.3); `Env` behavioral (§6.2); adversary quantification unchanged |
| 2 | Critical | Transcript half of the environment undefined by the source spec; sigma-with-equality reintroduces transports | **Accepted.** Structural `Spec.OracleMessagesAt` fiber + `answerAt` (§6.2) |
| 3 | High | Composition is not Kleisli bind; it is substitution with new suffix resources, weakening, associators | **Accepted.** `tensor`/`asSources`/`subst`/`SourceEquiv`/`rebase`; laws up to equivalence; no reduction-level associativity promised (§6.5) |
| 4 | High | `query_correct` does not dissolve completeness realization; prover-side obligation remains; literal data equality needs faithfulness | **Accepted.** `ProverOutputRealizes` + `OracleFamily.Faithful`; `OutputRealizes` becomes derived, not deleted (§6.6) |
| 5 | High | Terminal-claim packaging does not eliminate interactive monad retargeting | **Accepted** (was a caveat in the draft; now a design statement, §6.5) |
| 6 | High | Sum-spec position is scoped access, not provenance; BCS per-handle policy not implementable from the record alone | **Accepted.** Renamed "source-scoped"; provenance/`ResourceMeta`/`TypedPlan`/cost as the §6.9 compiler-facing extension, gating BCS output compilation |
| 7 | High | Migration targeted an obsolete seam; `TerminalOutput` already merges the endpoint | **Accepted.** Migration re-anchored on the programmatic layer; three vertical slices (§8) |
| 8 | Medium | Query-only extractor is not the literature default; full transcript is | **Accepted.** Naming flipped: `knowledgeSoundness` (full transcript) default; `knowledgeSoundnessQueryOnly` stronger variant + implication (§4.1, §6.6) |
| 9 | Medium | `Respectful` underspecified; observational equivalence is environment-relative; current `OutputRelation` signature can't even state it | **Accepted.** `ObsEqAt env`; `env` added to relation signatures; impl layer generated-not-authored, legacy predicates need equivalence theorems (§6.6) |
| 10 | Medium | Universe polymorphism not free | **Accepted.** Pinned universes; polymorphization stays a tracked follow-up (§6.10) |

Audit recommendations also adopted: pruned up-front constructor zoo to identity/selection/weakening/rebase/subst + `ofPlan` (§6.7); reification consolidated into `Materialization` rather than deleted (§6.8); security comparison theorems as a migration gate (§8 step 6); prefix-scoped RBR from day one (§6.6); resource identity settled before state restoration/RBRTE (§6.9, §8 step 9).

The audit's endorsed core, verbatim: *"a terminal claim packages a public statement and a source-scoped virtual query program, with total semantics into a broad behavior carrier; concrete data, provenance DAGs, and compiler materialization are separate strengthenings."* That is this design.

---

## 11. Success criteria

1. `VirtualOracle` + `subst` + laws compile with no `sorry`; the terminal-simulator routing of programmatic composition and boundary `pullback` are its instances.
2. The security comparison theorems (step 6) close for the three slice protocols — or the failure is documented and the semantic layer re-scoped *before* any cutover.
3. Oracle-level completeness composition is a proved theorem (the first ever in ArkLib for oracle reductions), followed by KS composition via the RBR/RBRTE route.
4. Single-round sumcheck's completeness contains no hand-written `OutputRealizes` obligation — only constructor-supplied `query_correct` + one `ProverOutputRealizes`.
5. Spartan-invoking-sumcheck's boundary is a `VirtualOracle` + `subst`, with its existing total materializer preserved as a `Materialization`, and completeness transported through it.
6. WHIR-style `linComb` and FRI-style `fold` exist as constructors used by real ports, each with `query_correct` proven once.
7. The KS event mentions no `QueryImpl` — only the semantic carrier — and `knowledgeSoundness_implies_soundness` closes without vacuity tricks.
8. `grep -rn "sorry" ArkLib/Interaction/` stays ≤ 1 (the pre-existing ClaimTree lemma) through migration steps 1–7.
9. No security definition is ever weaker than its behavioral predecessor without an explicit, documented decision.

---

## 12. What the next person should know (handover notes)

- **The one-sentence design:** claim = statement + (query plan, total behavioral denotation, coherence proof), scoped to explicit sources; everything else — concrete data, provenance, cost, compilation — is a strengthening layered on top.
- **The two mistakes to not re-make:** (a) output-as-data/selection (old `main` — §2); (b) denotation-into-concrete-data as canonical (this design's own draft — §10 finding 1). The stable point sits exactly between the consensus note's behavior-primary instinct and the draft's demand for intrinsic meaning.
- **The order of operations is load-bearing:** substrate → prototype on `TerminalOutput` → slices → bridges → algebra → *comparison theorems* → cutover → provenance → compilation. Do not let operational machinery outrun theorem support; that is how `main` died.
- **Where the bodies are buried:** `PublicTranscript.split`/`append` invert only propositionally (`Spec.lean:771,825`) — this is why reduction-level associativity is deferred and why `Presentation` (raw-append note) exists as the reserve weapon. `retargetMonads` (`Composition.lean:546`) and `retargetAmbientWithRoute` (`Program.lean:324`) are interactive-phase, not claim-phase — `subst` does not subsume them. The `Option` in old reification was architecture, not necessity — all real materializers in the repo are total.
- **What to port first:** the three slices (§8.3) were chosen to surface every design pressure — scalar-from-query statements, boundary virtualization, multi-stage sources, fresh+derived coexistence — with the smallest surface area.

---

## 13. References and archived inputs

**Code:**
- Rebuild: `ArkLib-core-rebuild/ArkLib/Interaction/` — esp. `Oracle/Spec.lean`, `Oracle/Core.lean`, `Oracle/Program.lean` (`Verifier.TerminalOutput`), `Oracle/Security/Basic.lean`, `Oracle/Composition.lean`, `Oracle/Reification.lean`, `Boundary/Oracle.lean`.
- Old design: `ArkLib/ArkLib/OracleReduction/` on `main` — esp. `Basic.lean:268-313` (embed/hEq + the prophetic `simOStmt` comment), `Composition/Sequential/Append.lean`, `LiftContext/Lens.lean`.
- Slice targets: `ProofSystem/Sumcheck/Interaction/SingleRoundProgram.lean`, `ProofSystem/Spartan/FirstSumcheck.lean`, `ProofSystem/FRI/Interaction/FoldPhase.lean`.

**Notes (paper-note repo):**
- `notes/ArkLib-Refactor_oracle_reduction_as_ior.md` — design consensus: SharedIn spine, StatementIn, behavior-primary (vindicated with amendment, §7.1), open questions (resolved §7).
- `notes/arklib-ior-knowledge-soundness-survey.md` — extractor signatures across BCS16 / BGTZ23 (2023/1256) / CDHZ (2025/2166) / FICS-FACS (2025/737); implemented §4.1, §6.6.
- `notes/ArkLib-Refactor_raw_append_spec_exploration.md` — `Spec.Presentation` prototype (compiles; reserved for reduction-level associativity, §8 step 8).

**Talks:** "Compositional Verification of Cryptographic Proofs in Lean" (King's College, Oct 2025) — IOR framing, sequential composition, virtualization-as-lenses.

**Delegate reports (this design cycle, 2026-07-12; archived at `Lean/arklib-design-reports/`):**
- Old-design survey (Claude Sonnet, very thorough) — the §2 autopsy with file:line evidence.
- Design analysis (GPT 5.6 Sol, high) — `gpt-oracle-sim.md`: the §5 pain points; first `VirtualOracle` skeleton.
- Literature requirements catalog (GPT 5.6 Sol, high + web) — `gpt-literature.md`: R1–R35 with citations (WHIR 2024/1586, STIR 2024/390, FRI, Ligero 2022/1608, Marlin 2019/1047, Nova 2021/370, ProtoStar 2023/620, ProtoGalaxy 2023/1106, ARC 2024/1731, WARP 2025/753, IOP 2016/116, RBR-vs-state-restoration 2019/1261, soundness notions 2023/1256, VCVio 2026/899, quantum IOPs arXiv:2601.12874).
- Adversarial audit (GPT 5.6 Sol, xhigh) — `gpt-audit.md`: §10's table; amendments integrated throughout §6 and §8.

**Key papers for the security-layer follow-ups:** Chiesa–Di–Hu–Zheng 2025/2166 (relaxed RBR KS for IORs; post-quantum BCS for IORs); FICS/FACS 2025/737 (RBRTE Def 4.4, composition Lemma 4.7); Holmgren 2019/1261 (RBR ↔ state restoration); Block–Garreta–Tiwari–Zając 2023/1256 (soundness notions for IOPs); Chiesa–Yogev textbook (2024) chs. 30–31.
