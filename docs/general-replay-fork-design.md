# A General Round-Indexed Replay Fork (design note, implementation-ready)

Status: ready to implement; load-bearing lemmas audited against VCVio / ArkLib / Mathlib (§6.7).

A **protocol-generic forking method** for rewinding extractors in ArkLib's IOR execution model,
factored out of the CWSS-specific `CWSSStructure.cwssForkImpl`
([ForkOracle.lean](../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ForkOracle.lean)).
It is the ArkLib analog of VCVio's `ReplayFork`, re-cast for round-indexed, prover-driven execution,
with the **full-replay** suffix mode the additive `ε − κ` bound needs. It composes with the
`SeededReplay` oSpec-tape abstraction (the `seededOracle` analog) of
[cwss-seeded-replay-plan.md](cwss-seeded-replay-plan.md) §2.3.

CWSS ⇒ KS is the first client; plain special soundness and a multiplicative (Bellare–Neven) route are
further clients. Coordinate structure never appears in the method itself.

---

## 0. What is general vs client-specific

`cwssForkImpl` conflates five concerns; only two are CWSS-specific.

| Concern | General? | Today's home |
|---|---|---|
| 1. Rerun harness (rerun prover+verifier under a chosen challenge oracle → `SiblingRun`) | **yes** | inlined in `cwssForkImpl` |
| 2. Round-indexed challenge replay (replay prefix, edit fork round, suffix policy) | **yes** | `replayChallengeImpl` (+ `decompose`) |
| 3. Execution-semantics lemmas (`runToRound_couple`, `oracleComp_replay`, `run_pin`, …) | **yes** | `private` in `ForkOracle.lean` |
| 4. The *edit* at the fork round (`decompose`-based coordinate override) | no — CWSS | inside `replayChallengeImpl` |
| 5. The query datatype / collector (`ForkQuery`, `avoid`, sampling) | no — client | `ForkOracle.lean` |

The general method is concerns 1–3, parameterized by an opaque **replacement challenge** for the fork
round and a **suffix mode**. The CWSS coordinate edit (concern 4) is computed by the client and fed in
as the replacement; the query datatype and collector (concern 5) stay client-side.

**Key simplification.** Lifting the *replacement* to a plain value `pSpec.Challenge r` (rather than
`(coord, value)`) removes `decompose` from the kernel entirely; the CWSS `CoordEq` guarantee becomes a
one-line corollary of the general "fork-round value" lemma (G1).

---

## 1. Relocate the execution-semantics layer (no new theory)

The `ExecutionSemantics` section of `ForkOracle.lean`
([lines ~194–715](../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ForkOracle.lean#L194))
is already stated over an *arbitrary* challenge oracle `C : QueryImpl [pSpec.Challenge]ₒ ProbComp` and
mentions nothing about `D`/`decompose`/coordinates. **Move it verbatim** (dropping `private`) to
`Rewinding/Coupling.lean`, together with `SiblingRun`,
`FullTranscript.pinnedChallengeImpl`, and `Prover.Realizes`:

- `Prover.runToRound_succ`
- `simulateQ_addLift_getChallenge`, `simulateQ_addLift_left`  *(make **public** — `transport` uses them)*
- `runToRound_transcript_challenge_mem`, `run_transcript_challenge_mem`
- `reachable_trans`, `simulateQ_reachable`, `reachable_run`, `oracleComp_replay`
- `runToRound_pin`, `run_pin`, `runToRound_couple`

---

## 2. Component A — the round-indexed replay fork

### 2.1 Suffix policy and challenge oracle

```lean
/-- How a replay fork answers challenge rounds strictly after the fork round. -/
inductive ReplaySuffix | replay | resample

/-- Round-indexed challenge oracle for one fork: replay rounds `< r` from `parent`, answer round `r`
  with `replacement`, and handle rounds `> r` per `mode` (`replay` → from `parent` deterministically;
  `resample` → fresh uniform). No `decompose`, no coordinates. -/
def replayChallenge {n} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
    (parent : FullTranscript pSpec) (r : pSpec.ChallengeIdx)
    (replacement : pSpec.Challenge r) (mode : ReplaySuffix) :
    QueryImpl [pSpec.Challenge]ₒ ProbComp := fun q =>
  if h : q.1 = r then
    pure (cast (congrArg pSpec.Challenge h.symm) replacement)
  else if q.1.1 < r.1 then
    pure (parent.challenges q.1)
  else
    match mode with
    | .replay   => pure (parent.challenges q.1)
    | .resample => $ᵗ (pSpec.Challenge q.1)
```

The edit value is a parameter, not sampled — so this does **not** recover the deprecated sampling impl;
sampling/`avoid` move to the collector (§4). The seeded route uses `.replay` (see §5).

### 2.2 The fork (value-indexed, deterministic in the edit)

```lean
/-- Rerun the reduction with the round-`r` challenge edited to `replacement`, the prefix replayed
  from `parent`, and the suffix governed by `mode`; return the resulting sibling run (`none` if the
  rerun failed). Shares the ambient oracle state `σ` with the measured run via `impl`. -/
def replayForkImpl {ι} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut} {σ}
    {n} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (parent : FullTranscript pSpec) (r : pSpec.ChallengeIdx)
    (replacement : pSpec.Challenge r) (mode : ReplaySuffix) :
    StateT σ ProbComp (Option (SiblingRun pSpec StmtOut)) := do
  let result ← simulateQ (impl.addLift (replayChallenge parent r replacement mode))
      ((Reduction.mk prover verifier).run stmtIn witIn).run
  match result with
  | none => return none
  | some ⟨⟨transcript, _, _⟩, stmtOut⟩ => return some ⟨transcript, stmtOut⟩
```

A plain `StateT σ ProbComp` value, not a `QueryImpl`. The KS fork-oracle spec `F` and its `QueryImpl`
wrapper stay client-side (§4): the extractor's query datatype is whatever the collector finds ergonomic.

### 2.3 Structural guarantees (suffix-mode-generic)

Direct generalizations of `cwssForkImpl_{coordEq,prefix_eq,realizes,reachable,accepts}`, with
`replayChallengeImpl q.parent q.round q.coord u` replaced by `replayChallenge parent r replacement
mode`. Each proof goes through the §1 lemmas, which are edit- and mode-agnostic, so the generalization
is mechanical.

```lean
variable {…} (h : (some sib, s') ∈ support ((replayForkImpl impl verifier stmtIn witIn prover
    parent r replacement mode).run s))

-- (G1) the sibling's round-`r` challenge IS the replacement (from construction)
theorem replayForkImpl_forkRound : sib.transcript.challenges r = replacement

-- (G2) challenges of rounds `< r` are the parent's (from construction)
theorem replayForkImpl_prefix_replayed :
    ∀ i' : pSpec.ChallengeIdx, i'.1 < r.1 → sib.transcript.challenges i' = parent.challenges i'

-- (G3) under ReplayConsistent + realized parent, the WHOLE transcript agrees before `r`
theorem replayForkImpl_prefix_eq (hImpl : impl.ReplayConsistent)
    (hParent : ∃ s₀ s₁, prover.Realizes impl stmtIn witIn parent s₀ s₁ ∧ impl.Reachable s₁ s) :
    ∀ m : Fin n, m < r.1 → sib.transcript m = parent m

-- (G4) the sibling is itself realized (re-forkable; threads through the recursion)
theorem replayForkImpl_realizes :
    ∃ s₁, prover.Realizes impl stmtIn witIn sib.transcript s s₁ ∧ impl.Reachable s₁ s'

-- (G5) the sibling's transcript was accepted by the verifier (premise of DeterminateAcceptance)
theorem replayForkImpl_accepts :
    ∃ ss ss', (some sib.stmtOut, ss') ∈
      support ((simulateQ impl (verifier.run stmtIn sib.transcript).run).run ss)

-- (G6) the end state is reachable from the start (threads reachability through collection)
theorem replayForkImpl_reachable : impl.Reachable s s'

-- (G7) forking to the parent's OWN round-`r` value (`.replay`) reproduces the parent run:
--      lets the measured center and forked siblings be scored by one accept predicate in §5.
theorem replayForkImpl_self_reproduces (hImpl : impl.ReplayConsistent)
    (hParent : ∃ s₀ s₁, prover.Realizes impl stmtIn witIn parent s₀ s₁ ∧ impl.Reachable s₁ s)
    (h : (some sib, s') ∈ support ((replayForkImpl impl verifier stmtIn witIn prover
      parent r (parent.challenges r) .replay).run s)) :
    sib.transcript = parent
```

- `(G1)`+`(G2)`: pure construction facts (the challenge oracle returns `pure …`).
- `(G3)`–`(G6)`: reuse `runToRound_couple` / `run_pin` / `simulateQ_reachable` exactly as the CWSS
  proofs do.
- `(G7)`: `runToRound_couple` at `bound = n` — the full-replay-to-self oracle and the parent's pinned
  oracle agree on *every* round (since `replacement = parent.challenges r`), giving full-transcript
  equality via the same `run`→`runToRound` plumbing as `(G3)`. (Analog of the plan's
  `fork_at_realized_reproduces`.)

### 2.4 Determinism in the edit (the additive-route lemma)

The only genuinely new obligation. Factor it through a reusable determinism predicate.

```lean
/-- A `StateT σ ProbComp` query impl is deterministic: each query has subsingleton support per state. -/
def QueryImpl.IsDeterministic {ι σ} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) : Prop :=
  ∀ q st, (support ((impl q).run st)).Subsingleton

-- closure lemmas (proved once, reused):
theorem QueryImpl.IsDeterministic.simulateQ {α} (h : impl.IsDeterministic)
    (oa : OracleComp spec α) : ∀ st, (support ((simulateQ impl oa).run st)).Subsingleton
    -- induction on `oa` via simulateQ_pure/_bind/_spec_query + support_pure/_bind (cf. simulateQ_reachable)

theorem QueryImpl.IsDeterministic.addLift
    (hImpl : impl.IsDeterministic) (hC : ∀ q, (support (C q)).Subsingleton) :
    (impl.addLift C).IsDeterministic

/-- `.replay`'s challenge oracle is pure-valued, discharging the `hC` hypothesis of `addLift`. -/
theorem replayChallenge_replay_subsingleton (parent r replacement) :
    ∀ q, (support (replayChallenge parent r replacement .replay q)).Subsingleton

/-- **Determinism of a full-replay fork.** Under a deterministic ambient impl, the `.replay` fork's
  result has subsingleton support — a deterministic function of `replacement`. -/
theorem replayForkImpl_replay_deterministic (hImpl : impl.IsDeterministic) :
    (support ((replayForkImpl impl verifier stmtIn witIn prover
      parent r replacement .replay).run s)).Subsingleton
    -- = (hImpl.addLift replayChallenge_replay_subsingleton).simulateQ, then match/return preserve it
```

**Subsingleton, not singleton.** This is all heavy-lines needs: it couples the *realized* run's
acceptance to the deterministic predicate `acc(v) := "the (unique) outcome accepts"`, since under
subsingleton support the realized outcome **is** that unique element. Do **not** claim general
non-emptiness — VCVio has no `support`-nonemptiness lemma for `OracleComp`, and
`LawfulSeededReplay.det` only guarantees subsingleton. If a true singleton is ever needed, add a
`neverFails`-style totality law (`EvalDist/Defs/NeverFails.lean`); the seeded route does not.
`LawfulSeededReplay.det` is exactly `(s.pin t).IsDeterministic`, so under a seeded tape the fork
inherits determinism with no extra work.

---

## 3. Component B — the `SeededReplay` oSpec tape (interface)

Full spec in [cwss-seeded-replay-plan.md](cwss-seeded-replay-plan.md) §2.3; reproduced here as the
*interface* Component A depends on. It is `oSpec`-generic (no CWSS), so it lives in
`Rewinding/SeededReplay.lean`.

- **Data** `QueryImpl.SeededReplay impl init`: `Tape`, `genTape : ProbComp Tape`,
  `pinInit : Tape → ProbComp σ`, `pin : Tape → QueryImpl oSpec (StateT σ ProbComp)`.
- **Laws** `QueryImpl.LawfulSeededReplay s : Prop`:
  - `det t` : `(s.pin t).IsDeterministic`  *(§2.4 predicate — shared, not redefined)*
  - `stateless t` : the answer is a function of `(t, q)` only.
  - `faithful` : `genTape`-then-`pin` reproduces the live `evalDist`.
  - derived `consistent t : (s.pin t).ReplayConsistent` (from `det ∧ stateless`).
  - derived `transport` : lifts `faithful` to the whole experiment via `simulateQ_addLift_left/_getChallenge`.
- Constructors: `ofEmpty`/`ofDeterministic` (build first; `faithful := rfl`), `ofUniformSeed`
  (`faithful` from VCVio's `probOutput_generateSeed_bind_map_simulateQ`), future truth-table RO.

Component A consumes `det` (→ §2.4 determinism) and `consistent` (→ `(G3)` prefix_eq). Everything else
in A is tape-agnostic and instantiated at `s.pin t`.

---

## 4. How CWSS ⇒ KS consumes the method (thin client)

```lean
-- query datatype + oracle spec stay CWSS-side
structure CWSSStructure.ForkQueryVal (D) where
  parent : FullTranscript pSpec
  round  : pSpec.ChallengeIdx
  coord  : Fin (D.coordIndex round)
  value  : D.alphabet round

@[reducible] def CWSSStructure.forkOracleVal (D) (StmtOut) : OracleSpec D.ForkQueryVal :=
  fun _ => Option (SiblingRun pSpec StmtOut)

-- thin wrapper: compute the replacement by coordinate override, full replay
def CWSSStructure.cwssForkSeededImpl (D) [insts] (impl) (verifier) :
    StmtIn → WitIn → Prover … → QueryImpl (D.forkOracleVal StmtOut) (StateT σ ProbComp) :=
  fun stmtIn witIn prover q =>
    if q.value = D.decompose q.round (q.parent.challenges q.round) q.coord then return none
    else
      replayForkImpl impl verifier stmtIn witIn prover q.parent q.round
        ((D.decompose q.round).symm
          (Function.update (D.decompose q.round (q.parent.challenges q.round)) q.coord q.value))
        .replay
```

CWSS corollaries derived from §2.3:
- `cwssForkImpl_coordEq` from `(G1)`: substitute the `decompose`-update replacement, push through
  `Function.update_self`/`update_of_ne`. All `decompose` reasoning is confined here.
- distinctness (`IsSpecialSoundFamily`): distinct `value` ⇒ distinct fork-round coordinate, from `(G1)`
  + injectivity of `decompose`.

The collector (`collectSiblingsExhaustive`), `avoid`/without-replacement logic, heavy-lines, and the
reverse-induction additive bound stay in the CWSS implication file. The fork is value-indexed and
deterministic, so `avoid` is a collector bookkeeping concern, not an oracle concern.

---

## 5. Sufficiency for the additive `ε − κ` bound

The additive bound (FMN24 Lemma 2.31 / §8 abstract-sampling-game, `κ = Σ_m ℓ_m(k_m−1)/|S_m|`) needs,
at each round `m`, that the **accepting count over the round-`m` coordinate alphabet is a deterministic
function** once the deeper challenges and the ambient randomness are fixed; heavy-lines then gives the
per-round loss `ℓ_m(k_m−1)/|S_m|`, telescoping to `ε − κ`. The method supplies exactly this:

1. **`.replay` fixes the challenge suffix.** Forking round `m` to `replacement` replays rounds `< m`
   and `> m` from the parent; only round `m` changes (G1, G2). The parent's deeper challenges `c_{>m}`
   are held fixed across the coordinate sweep, while messages downstream recompute deterministically.
2. **`SeededReplay.pin t` fixes the ambient randomness** (`det` makes every `oSpec` answer a function
   of `(t, q)`).
3. **Together ⇒ determinism in the edit** (§2.4 `replayForkImpl_replay_deterministic`): given
   `(parent, t)`, the sibling run — hence its acceptance, hence by leaves-up induction its
   subtree-extractability — is a deterministic function of `replacement`.
4. **Heavy-lines applies.** For fixed `(c_{>m}, t)`, `acc_p^{c_{>m},t}(v) :=` "round-`(m+1)` subtree at
   `p++v` extractable" is a deterministic predicate of the coordinate value `v` (client maps `v` to
   `replacement = (decompose r).symm (update … v)`, transports the uniform measure via Bridge 1). The
   measured center is scored by the *same* predicate via `(G7)`. `prob_lines_light_le` bounds the
   light-line probability by `ℓ_m(k_m−1)/|S_m|`; averaging over `c_{>m}` and `t ← genTape` and
   telescoping (`T_m ≥ T_{m+1} − ℓ_m(k_m−1)/|S_m|`) yields `T_1 ≥ T_{μ+1} − κ = ε − κ`, with base
   `T_{μ+1} = ε` from `LawfulSeededReplay.faithful`.

**The tree is genuine.** Siblings share the round-`<m` prefix (G3) and differ from the center in
exactly one round-`m` coordinate (G1); deeper structure is built by re-forking each sibling (G4 makes
siblings realized). CWSS constrains only the *challenge*-tree edges; divergent prover messages
downstream are allowed.

**Necessity of `.replay`.** With `.resample`, step 1 fails (deeper challenges go live), `acc(v)` is a
random variable, and one gets only the multiplicative (Bellare–Neven) bound. The additive route
*requires* `.replay` + a fixed tape — both provided here. The remaining work (heavy-lines, collector,
reverse induction) is client-side probability/combinatorics, not forking.

---

## 6. File & module organization

### 6.1 `Rewinding` is a top-level `Security/` subpackage

The rewinding-extraction infrastructure (the abstract KS notions, the run-coupling layer, the general
fork, the seeded tape) is broad enough to be a **peer of** `KnowledgeSoundness`/`SpecialSoundness`,
not nested under one of them. It lives directly under `Security/`, using the **umbrella-file + folder**
convention the rest of `Security/` uses. The former leaf `KnowledgeSoundness/Rewinding.lean` becomes
`Rewinding/Basic.lean`.

```
Security/Rewinding.lean              (umbrella: imports Basic, Coupling, ReplayFork, SeededReplay)
Security/Rewinding/Basic.lean        (the former KnowledgeSoundness/Rewinding.lean — content unchanged)
Security/Rewinding/Coupling.lean     (§1 + §2.4)
Security/Rewinding/ReplayFork.lean   (§2)
Security/Rewinding/SeededReplay.lean (§3)
Security/KnowledgeSoundness.lean     (re-exports `Security.Rewinding` for convenience — module name
                                      `…Security.Rewinding`; dependents import the granular module)
```

### 6.2 Per-file contents

**`Rewinding/Basic.lean`** (= today's `Rewinding.lean`, unchanged): `Extractor.Rewinding`,
`QueryImpl.Reachable`, `QueryImpl.ReplayConsistent`, `Verifier.DeterminateAcceptance`,
`knowledgeSoundnessRewinding`, `knowledgeSoundnessRewindingWithError`. Imports `Security.Basic`
(which imports `OracleReduction.Execution`, so `Prover`/`Reduction` reach `Coupling` transitively).

**`Rewinding/Coupling.lean`** (relocated from `ForkOracle.lean`, de-`private`'d):
`FullTranscript.pinnedChallengeImpl`, `Prover.Realizes`; the §1 coupling lemmas; plus §2.4
`QueryImpl.IsDeterministic` + `.simulateQ`/`.addLift` closure. Imports `Rewinding/Basic`. Named
`Coupling` (not `Execution`) to avoid clashing with the core `OracleReduction/Execution.lean` and
because the lemmas are run-/replay-*coupling*. `simulateQ_addLift_left`/`_getChallenge` become public.

**`Rewinding/ReplayFork.lean`**: `ProtocolSpec.SiblingRun`, `ReplaySuffix`, `replayChallenge`,
`replayForkImpl`, `replayChallenge_replay_subsingleton`, `(G1)`–`(G7)`,
`replayForkImpl_replay_deterministic`. Imports `Rewinding/Coupling`.

**`Rewinding/SeededReplay.lean`**: `QueryImpl.SeededReplay`, `QueryImpl.LawfulSeededReplay`, derived
`consistent`/`transport`, constructors `ofEmpty`/`ofDeterministic`/`ofUniformSeed`. Imports
`Rewinding/Coupling`. Independent of `ReplayFork`.

**`CoordinateWiseSpecialSoundness/ForkOracle.lean`** (thinned): `ForkQueryVal`, `forkOracleVal`,
`cwssForkSeededImpl`, and the CWSS corollaries `cwssForkImpl_coordEq` + sibling-value distinctness. The
execution layer, `SiblingRun`, `Realizes`, `pinnedChallengeImpl` all leave this file; re-point its
import to `…Rewinding.ReplayFork`. The deprecated sampling `cwssForkImpl` is dropped — its only callers
are inside `DEPRECATED` blocks (CWSSRewinding 376–846 & 861+, SpecialSoundnessRewinding 107–136), so
this is build-safe.

### 6.3 Out of scope (CWSS-implication concerns, separate files)

- **`CoordinateWiseSpecialSoundness/HeavyLines.lean`** (NEW): protocol-free `prob_lines_light_le` + the
  `prob_lines_light_le_challenge` transport (via Bridge 1). Imports `CoordinateOracle` + Mathlib.
- **`Implications/CoordinateWiseSpecialSoundnessRewinding.lean`** (existing): the exhaustive collector,
  reverse-induction additive bound, and target theorem. Its live reusable assembly
  (`RunForest`/`runs`/`toTree`/`WellFormed`/`toTree_isStructured`/`mem_toTree_fullTranscripts`/
  `gatherFin`, lines 102–374) depends on `SiblingRun` and keeps compiling via
  `CWSSRewinding → ForkOracle → ReplayFork`.

### 6.4 Dependency DAG (acyclic)

```
Security.Basic
  └─ Rewinding/Basic
       └─ Rewinding/Coupling ───┬─ Rewinding/ReplayFork ─┐
                                └─ Rewinding/SeededReplay │
CWSS/Basic ───────────────────────────────────────────────┼─ CWSS/ForkOracle ─┐
CWSS/CoordinateOracle ── CWSS/HeavyLines ──────────────────┘                   │
                              Rewinding/SeededReplay ───────────────────────────┼─ Implications/CWSSRewinding
```
`CWSS/Basic` and `CWSS/CoordinateOracle` stay independent of `Rewinding`; `Rewinding/*` never imports
CWSS (it mentions `cwssForkImpl` only in prose docstrings).

### 6.5 Migration checklist & build order

1. `git mv` `KnowledgeSoundness/Rewinding.lean` → `Security/Rewinding/Basic.lean` (and any prior
   `Rewinding/` folder up to `Security/Rewinding/`); add the new umbrella `Security/Rewinding.lean`
   `Rewinding.lean`. `git add` paths; validate (still green — no logic moved).
2. `Rewinding/Coupling.lean`: cut the `ExecutionSemantics` section + `SiblingRun`/`Realizes`/
   `pinnedChallengeImpl` from `ForkOracle.lean`, drop `private`, publicize `simulateQ_addLift_*`; add
   §2.4 `IsDeterministic` + closure; re-point `ForkOracle.lean`'s imports. Validate.
3. `Rewinding/ReplayFork.lean`: `ReplaySuffix`/`replayChallenge`/`replayForkImpl`/`(G1)`–`(G7)`/
   `replay_deterministic` (move `SiblingRun` here). Validate.
4. `Rewinding/SeededReplay.lean` (parallel with 3): data + laws + `ofEmpty`/`ofDeterministic`.
5. Thin `ForkOracle.lean` to the CWSS wrapper + `coordEq` corollary. Validate.
6. (Client, separate PRs) `HeavyLines.lean`, then the collector + additive bound in
   `Implications/CWSSRewinding.lean`.

`ArkLib.lean` is generated — do not hand-edit; `git add` new files before validation so it regenerates.
Each step ends green.

### 6.6 Ranked risks

1. **`IsDeterministic.simulateQ`/`.addLift` (step 2).** New induction on `oa`; gates the additive route.
   Low–medium — same shape as the existing `simulateQ_reachable`. De-risk on a tiny `oSpec`.
2. **`SeededReplay.transport` (step 4).** The substantive obligation; all ingredients present
   (§6.7). Medium.
3. **Generalizing `(G1)`–`(G7)` (step 3).** Mechanical: swap the challenge oracle; `(G7)` is
   `runToRound_couple` at `bound = n`. Low.
4. **Relocation (steps 1–2).** Rename + `private`→public + import re-pointing. Low; touches the most
   files, so do it first and keep it logic-free.

### 6.7 Lemma reference (located in the working tree)

Per obligation, the primitives to build on. VCVio has **no** determinism predicate (we define
`IsDeterministic`) and **no** general `support`-nonemptiness (subsingleton suffices, §2.4).

- **§2.4 `IsDeterministic` closure** — VCVio `simulateQ_pure`/`_bind`/`_spec_query`/`_map`,
  `OracleComp.inductionOn`, `support_pure`/`_bind`/`_map`, `QueryImpl.addLift`/`add_apply_inl,inr`/
  `liftTarget_apply,_self`, `simulateQ_add_liftComp_left/right`; Mathlib `Set.Subsingleton`,
  `subsingleton_iff_singleton`.
- **§3 `transport`/`faithful`** — ArkLib `simulateQ_addLift_left`/`_getChallenge` (publicized); VCVio
  `seededOracle`, `generateSeed`, `QuerySeed`, `IsUniformSpec`, `probOutput_generateSeed_bind_map_simulateQ`,
  `evalDist_bind`/`_pure`, `probOutput_bind_eq_tsum`.
- **§2.3 `(G1)`–`(G7)`** — the relocated coupling lemmas; `runToRound_couple` (with `bound = n` for G7).
- **Heavy-lines (client)** — Mathlib `card_eq_sum_card_fiberwise`, `Fin.insertNthEquiv`/`removeNth`,
  `Function.update_self`/`update_of_ne`, `card_filter_le`, `tsub_le_iff_right`,
  `ENNReal.div_le_iff`/`le_div_iff_mul_le`, `PMF.uniformOfFintype` +
  `toOuterMeasure_uniformOfFintype_apply` (= count / card); VCVio `probEvent_exists_finset_le_sum`.

---

## 7. Settled decisions

- **Replacement is a value, not `(coord, value)`** — keeps `decompose` out of the kernel; `CoordEq` is
  a client corollary of (G1).
- **Fork is value-indexed and deterministic** — `avoid`/sampling is a collector concern.
- **`mode` controls only the suffix** — `.replay` (additive) and `.resample` (multiplicative) share
  (G1)–(G7); only §2.4/§5 branch on it.
- **Determinism via a reusable `IsDeterministic` predicate** — shared by §2.4 and
  `LawfulSeededReplay.det`; subsingleton support, not singleton.
- **Query datatype stays client-side** — the reusable surface is `replayForkImpl` + (G1)–(G7) +
  `replay_deterministic`, not the fork-oracle spec.
