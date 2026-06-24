# Core Rebuild: Porting Progress

Tracking the replacement of ArkLib's core IOR layer with one built on
`Interaction.Spec` (W-type game trees) + `RoleDecoration`.
Branch: `quang/core-rebuild`, based on `quang/bump-comppoly`.

Reference branch: `quang/iop-refactor` (old Refactor/ approach, archived).

## Current snapshot

The interaction oracle layer is the active design, but there are now
three oracle strata in the tree:

1. `ArkLib/OracleReduction/` is the legacy flat `ProtocolSpec n` stack. It is
   still imported by many older proof systems, but should not be extended except
   to keep old consumers compiling during migration.
2. `Interaction.Spec` + `OracleDecoration` is the transitional W-type oracle
   surface. It is quarantined under `Interaction/Oracle/Legacy/`.
3. `Interaction.Oracle.Spec` is the forward path. It distinguishes `.public`
   nodes from `.oracle` nodes and indexes verifier-visible behavior by
   `PublicTranscript`, avoiding the cast pressure of the decoration-only layer.

The current migration rule is: use `Interaction.Oracle.Spec` for new
oracle work, keep `OracleDecoration` only as quarantined legacy code, and treat
`OracleReduction/` as legacy.

## Porting strategy

Do not cut over old canonical specs until the `Interaction.Oracle.Spec` layer has been exercised
on multiple concrete protocols. The current strategy is **vertical slices with
core extraction**:

1. Keep old `Spec/` and `OracleReduction/` entrypoints stable while porting.
2. Build `Interaction.Oracle.Spec` protocol slices beside them under
   `ProofSystem/*/Interaction/`.
   Leaf protocols should use `Interaction.Oracle.Spec` directly and should not
   add new protocol-facing abstractions to `OracleReduction/` or
   `Interaction/Oracle/Legacy/`.
3. Extract common infrastructure only after at least two leaf ports need the
   same pattern. FRI is path/trace-heavy; Sumcheck is challenge/claim-state
   heavy. Both are needed before promoting helpers into `Interaction/Oracle/`.
4. Once several leaves share the same interaction-oracle core cleanly, port the generic
   execution/security/BCS layers.
5. Only then decide how old canonical entrypoints are retired, re-exported, or
   rewritten.

In short:

```text
old canonical specs stay put
        ↓
oracle-spec leaf slices beside them
        ↓
common interaction-oracle infrastructure extracted from repeated needs
        ↓
interaction-oracle execution / security / BCS story
        ↓
canonical cutover
```

As of the current branch, the interaction oracle design has:

- `Interaction/Oracle` is split into `Core.lean`, `Composition.lean`,
  `Spec.lean`, `Execution.lean`, `Security.lean`, `BCS.lean`, and
  `Chain.lean`, with the old `OracleDecoration` surface moved under
  `Interaction/Oracle/Legacy/`.
- The downstream `OracleDecoration` examples are quarantined under
  `ProofSystem/*/Interaction/Legacy/` while they remain useful as references.
  Sumcheck's old interaction sketches have been removed from the active import
  graph now that `Sumcheck/Interaction/{Oracle,SingleRound,General}.lean` are
  the default interaction-oracle surface.
- `InteractiveOracleVerifier` no longer bakes in `OptionT`; plain verifier
  output is separate from output-oracle access semantics.
- `OracleReduction` and `OracleReduction.Continuation` now use
  transcript-dependent output oracle families, on par with `OracleVerifier`.
- `OracleReduction.run` / `execute` are derived defs rather than stored fields.
- Reification for the transitional `OracleDecoration` surface is optional and
  now lives in `Interaction/Oracle/Legacy/Reification.lean`.
- The `Oracle.Spec` layer is implemented, but still has proof and BCS
  construction gaps listed below.
- Historically verified builds included:
  - `lake build ArkLib.Interaction.Oracle.Core ArkLib.Interaction.Oracle.Execution`
  - `lake build ArkLib.Interaction.Oracle.Legacy.Reification`
  - `lake build ArkLib.Interaction.Oracle.Legacy.Security`
  - `lake build ArkLib.ProofSystem.Sumcheck.Interaction.Oracle`

## Architecture

```
Interaction/             ← generic, standalone (future VCVio)
  Basic.lean               Spec.{u} (W-type), Transcript, Strategy, Decoration,
                           Decoration.map, Decoration.Refine, BundledMonad,
                           MonadDecoration,                            append/replicate/Chain (continuation-style),
                           stateChain (state-indexed), liftAppend,
                           stateChainLiftJoin, stateChainFamily, role-free
                           composition — universe-polymorphic throughout
  TwoParty.lean            Role, RoleDecoration (= Decoration on Spec),
                           Strategy.withRoles, Counterpart (with Output param),
                           runWithRoles (returns both outputs),
                           SenderDecoration (= Refine over RoleDecoration),
                           per-node monad variants, role-aware
                           append/replicate/stateChain combinators
  Multiparty/              Core local views and projected endpoints,
                           `Profile` per-party view assignments,
                           `Broadcast` owner/observer interaction,
                           `Directed` sender/receiver/hidden interaction,
                           definitional examples including quotient observation
  Reduction.lean           Prover (monadic setup, plain WitnessIn),
                           Verifier (= Counterpart with transcript-indexed leaf
                           output), transcript-indexed StatementOut/WitnessOut,
                           Reduction, Reduction.Continuation, Proof, execute,
                           Verifier.run, comp, stateChainComp,
                           stateChainCompUniform, ofChain (stateless
                           chain-based reduction)
  Security.lean            randomChallenger, completeness /
                           perfectCompleteness / soundness /
                           knowledgeSoundness (HasEvalSPMF),
                           completeness/soundness composition for `comp`,
                           `Extractor.Straightline`, ClaimTree,
                           KnowledgeClaimTree, rbrSoundness /
                           rbrKnowledgeSoundness (currently via random
                           challenger + transcript predicates)
  Oracle/
    Spec.lean              Oracle protocol spine: `.public`,
                           `.oracle`, `.done`, `PublicTranscript`,
                           `QueryHandle`, `toOracleSpec`,
                           `toMonadDecoration`
    Core.lean              Oracle reduction core:
                           shared oracle statement bundles plus
                           `Oracle.Prover`, `Oracle.Verifier`,
                           `Oracle.Reduction` over `Oracle.Spec`
    Execution.lean         concrete execution for `Oracle.Spec`
    Composition.lean       `Oracle.Spec` composition
    Chain.lean             N-ary `Oracle.Spec` chain composition
    Security.lean          `Oracle.Spec` completeness / soundness /
                           knowledge-soundness definitions
    BCS.lean               `Oracle.Spec` BCS transform scaffolding
    Legacy/
      Core.lean            quarantined `OracleDecoration`, `QueryHandle`,
                           `OracleCounterpart`, `Interaction.OracleVerifier`,
                           `OracleDecoration.OracleReduction`
      Execution.lean       quarantined execution for `OracleDecoration`
      Continuation.lean    quarantined continuation/composition layer for
                           `OracleDecoration`
      StateChain.lean      quarantined state-chain composition layer
      Security.lean        quarantined completeness / soundness /
                           knowledge-soundness for `OracleDecoration`
      Reification.lean     quarantined concrete reification layer
      Bridge.lean          quarantined spec/decorator conversion from
                           `Interaction.Spec` + `OracleDecoration` to
                           `Oracle.Spec`

OracleReduction/         ← legacy ArkLib-specific flat core
  OracleInterface.lean     Stable shared query/response abstraction; reused
                           by the interaction oracle layer
  ProtocolSpec/            old fixed-round protocol spine
  Basic.lean               old Prover/Verifier/OracleReduction API
  Execution.lean           old execution semantics
  Security/                old completeness, soundness, KS, RBR stack
  Composition/             old append/chain composition stack

ProofSystem/             ← concrete protocols on top of the above
  Sumcheck/Interaction/    `Defs.lean` / `CompPoly.lean` are still usable
                           shared interaction setup; `Oracle.lean`
                           contains the default one-round oracle surface;
                           `SingleRound.lean` and `General.lean` contain the
                           default single-round and n-round reductions;
                           old `OracleDecoration` protocol files have been
                           removed from the active import graph
  Fri/Interaction/         `Core.lean`, `FoldRound.lean`, `FinalFold.lean`,
                           `FoldPhase.lean`, `QueryRound.lean`, and
                           `General.lean` contain the `Oracle.Spec`
                           FRI phase surfaces and full composition
  (TODO) Oracle.Spec ports for Binius, commitment/BCS slices, ...
```

No `ProtocolSpec` or `Direction` wrapper — `Spec` + `RoleDecoration` replaces
`ProtocolSpec n` entirely. No separate `TwoParty` or `Multiparty` inductive —
roles are a decoration on `Spec`.

For oracle-spec work, `Oracle.Spec` further refines this rule: `.public` and
`.oracle` nodes replace the older convention of using ordinary sender nodes plus
an `OracleDecoration`.

## Completed

- [x] **Phase 1: Interaction foundation** — `Spec`, `Transcript`, `Strategy`,
  `Decoration`, `append`, `comp` in `Basic.lean`, universe-polymorphic
- [x] **Phase 2: Two-party and reduction** — `Role`, `RoleDecoration`,
  `Strategy.withRoles`, `Counterpart`, `runWithRoles` in `TwoParty.lean`;
  `Prover`, `Verifier`, `Reduction`, `execute` in `Reduction.lean`
- [x] **Phase 2b: Kill TwoParty / Multiparty inductives** — removed both
  separate inductives; roles are now a `Decoration (fun _ => Role)` on `Spec`;
  N-party is `Spec` + `PartyDecoration` + `Decoration.map`; all `rfl` examples
  pass through the projection
- [x] **Phase 2c: Monad decoration generalization** — `BundledMonad` standalone
  at root; `Counterpart.withMonads` fully monadic (uses node monad at all roles);
  `runWithRolesAndMonads` takes two separate monad decorations (strategy vs
  counterpart); `Decoration.map` added for natural transformations between
  decorations
- [x] **Phase 2d: Universe polymorphism** — `Spec.{u}`, `BundledMonad.{u,v}`,
  `Decoration.{u,v}`, `Strategy.{u}`, all combinators universe-polymorphic;
  `TwoParty.lean` / `Reduction.lean` work at `u = 0`
- [x] **Phase 2e: N-ary composition** — `replicate`, `Chain` (continuation-
  style), `stateChain` (state-indexed), `iterate`, `stateChainComp`,
  `Transcript.stateChainJoin` / `stateChainUnjoin`, and `stateChainFamily`
  for `Spec`, `Decoration`, `Strategy`, `Transcript`; round-trip lemmas
  (`split_append`, `append_split`, `stateChainSplit_stateChainAppend`,
  `stateChainUnjoin_join`, `stateChainJoin_unjoin`); role-aware wrappers for
  `RoleDecoration`, `Counterpart`, `Strategy.withRoles`
- [x] **Phase 2f: Decoration.Refine** — displayed decoration combinator
  (cf. displayed algebras, ornaments). `Refine F spec d` carries `F X l` at
  each node with label `l : L X` from decoration `d`. Composition:
  `Refine.append`, `.replicate`, `.stateChain`, `.map`. `SenderDecoration` in
  `TwoParty.lean` as a specialization to `RoleDecoration`.
- [x] **Phase 3: OracleDecoration** — `OracleDecoration` assigns
  `OracleInterface` instances at sender nodes (data, not typeclass).
  `QueryHandle` indexes oracle queries parameterized by a transcript (path-
  dependent oracle access — fundamental to W-type interactions where move types
  depend on prior moves). `toOracleSpec` and `answerQuery` defined by recursion.
- [x] **Phase 3b: Oracle verifier redesign** —
  `OracleCounterpart` models the round-by-round challenger with growing oracle
  access (`accSpec` starts at `[]ₒ`, grows by `oi.toOC.spec` at sender nodes).
  `InteractiveOracleVerifier` is the unified recursive type with plain leaf
  verifier output (no baked-in `OptionT`). `OracleVerifier` bundles `iov` +
  transcript-dependent `simulate`; reification moved out to the optional
  `Oracle/Legacy/Reification` layer. `OracleProver` and `OracleReduction` are
  defined.

- [x] **Phase 3c: Oracle reduction cutover** —
  `OracleReduction` and `OracleReduction.Continuation` now use
  transcript-dependent output oracle families, matching the dependency level of
  `OracleVerifier`. `run` / `execute` are derived defs. Binary composition,
  continuation retargeting, simulator composition, and state-chain verifier
  composition all build on the new interface.

- [x] **Phase 3d: Oracle module cleanup** —
  the old monolithic `Interaction/Oracle.lean` has been split into focused
  submodules. The split now includes both the transitional `OracleDecoration`
  surface and the `Oracle.Spec` surface. Some proof obligations have
  since reappeared as the oracle layer grew; see the active gaps above rather
  than treating this checkpoint as the current proof status.

- [x] **Phase 4: Security definitions** — `randomChallenger` (generic sampler
  to `Counterpart ProbComp`), `Reduction.completeness` / `perfectCompleteness`,
  `soundness`, `knowledgeSoundness`, `ClaimTree` / `KnowledgeClaimTree`
  (inductive on `Spec` + `RoleDecoration`), `good`/`Terminal`/`follow`/
  `terminalGood`/`maxPathError`/`IsSound`, `bound_terminalProb`
  (`sorry` proof), `rbrSoundness` / `rbrKnowledgeSoundness`, and the
  current bridge theorems (`sorry` where noted).
- [x] **Phase 4b: Counterpart output + simplified Reduction/Security** —
  `Counterpart` takes explicit `Output : Transcript spec → Type u` parameter
  (`Output ⟨⟩` at `.done`; old no-output = `fun _ => PUnit`).
  `runWithRoles` returns both prover and counterpart outputs.
  `Counterpart.iterate`/`stateChainComp` thread state `β` (mirrors strategy pattern).
  `OracleCounterpart` takes `Output : OracleSpec → Type` at `.done`;
  `InteractiveOracleVerifier` is now an abbrev to `OracleCounterpart`.
  Plain `Reduction` uses monadic prover setup, plain `WitnessIn`, and
  transcript-indexed `StatementOut` / `WitnessOut` as parallel families
  (no `WitnessOut` dependency on `StatementOut`).
  `Verifier` is an `abbrev` for `Counterpart` with caller-chosen leaf output;
  acceptance semantics live in `StatementOut` / `Accepts`.
  Security uses generic `[HasEvalSPMF m]` instead of `ProbComp`.
- [x] **Phase 4c: Role-aware sequential composition** —
  `Strategy.compWithRoles`, `Counterpart.append`, `Reduction.comp`, and the
  chain builders `Reduction.stateChainComp` / `Reduction.stateChainCompUniform`
  are implemented on top of `Spec.append` / `Spec.stateChain`.
  `Reduction.ofChain` provides stateless reduction composition over `Spec.Chain`.
- [x] **Phase 4d: Security composition + extractor cleanup** —
  `Reduction.comp` now factors through transcript-indexed
  `Reduction.Continuation`, with `reduction1` / `reduction2` naming throughout.
  `Reduction.completeness_comp`, `Reduction.perfectCompleteness_comp`, and
  `Reduction.soundness_comp` are proved against that interface.
  Security relations now take statement output before witness output, and
  `knowledgeSoundness` uses a dedicated `Extractor.Straightline` instead of an
  ad-hoc function type. `knowledgeSoundness_implies_soundness` is available
  when accepted terminal statements admit a canonical transcript-indexed
  `WitnessOut`.

## Oracle.Spec layer (forward path, cast-free)

The `Oracle.Spec` inductive provides a structural alternative to
`OracleDecoration` on `Interaction.Spec`. It distinguishes `.public` nodes
(value visible to both parties) from `.oracle` nodes (value accessed only
through queries), yielding cast-free `PublicTranscript` indexing.

This is the preferred API for new oracle protocols and transformations. The
older `OracleDecoration` surface remains useful as a quarantined reference for
already-ported interaction-oracle code, but it should not be the target for new
protocol migrations.

### Files

| File | Status | Content |
|------|--------|---------|
| `Oracle/Spec.lean` | Complete | `Oracle.Spec`, `RoleDeco`, `OracleDeco`, `PublicTranscript`, `toOracleSpec`, `toMonadDecoration`, `append`, `split` |
| `Oracle/Core.lean` | Mostly complete | shared oracle statement bundles, `Oracle.Prover`, `Oracle.Verifier` (with `toFun` starting at `[]ₒ`), `Oracle.Reduction` |
| `Oracle/Execution.lean` | Implemented, proof gaps | `Spec.runWithOracleCounterpart`, `Reduction.executeConcrete`, `Verifier.run` for `Oracle.Spec` layer; active map-output proof gaps |
| `Oracle/Composition.lean` | Complete, no sorry | `Reduction.comp`, `Counterpart.liftAcc`, `Verifier.retargetMonads` |
| `Oracle/Security.lean` | 1 sorry | `OutputRealizes`, `completeness`/`soundness`/`knowledgeSoundness`, `knowledgeSoundness_implies_soundness` (sorry) |
| `Oracle/BCS.lean` | Complete, no sorry | `CommitDeco`, `bcsSpec`, prover wrapping, `PublicQueryVerifier`, Phase 1/2 helpers, `answerCommittedQueries` |
| `Oracle/Chain.lean` | Implemented | N-ary `Oracle.Spec` chain composition and `Reduction.ofChain` |
| `Oracle/Legacy/*.lean` | Quarantined | transitional `OracleDecoration` implementation and bridge files slated for deletion after migration |

### Key design decisions

- `Oracle.Verifier.toFun` starts with `accSpec = []ₒ` (hardcoded). Composition
  uses `Counterpart.liftAcc` to bridge the empty accumulated spec to the
  dynamically growing one.
- Security definitions use `OutputRealizes` to bridge behavioral simulation and
  concrete oracle data. Completeness checks `OutputRealizes` as a conjunct.
  Knowledge soundness requires the adversarial prover to output concrete
  `oStmtOut`; the extractor sees it.
- `knowledgeSoundness_implies_soundness` requires `hLangOut` to include
  `OutputRealizes` (acceptance implies realizable output oracle behavior).

## In progress

- [ ] **Execution bridge lemmas for oracle composition** — close the
  active proof gap in `Oracle/Execution.lean` around output mapping. The
  old append-transcript simulation bridge is now quarantined in
  `Oracle/Legacy/Continuation.lean`.
- [ ] **Composition security for Oracle.Spec** — `Reduction.completeness_comp`
  statement for the new `Oracle.Spec` layer. The old `Interaction/Security.lean`
  has the analog; the new version needs `PublicTranscript` indexing and
  `OutputRealizes` handling.
- [ ] **BCS Oracle.Verifier construction** — combine `PublicQueryVerifier`
  Phase 1 (challenger) and Phase 2 (query/decide) into a proper
  `Oracle.Verifier` on `bcsSpec`. Current direction: model Phase 2 as an
  appended opening protocol, rather than trying to recover committed-message
  queries from `.public` commitment nodes.
- [ ] **Phase 2 opening protocol** — define `openingSpec`, `openingRoles`,
  Phase 2 prover/verifier for BCS. `Interaction/BCS/Verifier.lean` currently
  has the opening stubs. Depends on `CommitmentScheme.Basic.Opening`.

## Immediate deferred todos

- [ ] Treat `Oracle.Spec` as the forward path for new oracle work. Avoid
  adding new protocol-facing abstractions to legacy `OracleReduction/`, and keep
  `OracleDecoration` quarantined under `Oracle/Legacy/` as an interop layer.
- [ ] Prove `knowledgeSoundness_implies_soundness` in `Oracle/Security.lean`.
  `Spec.runWithOracleCounterpart_mapOutputWithRoles` is proved in
  `Execution.lean`. The remaining difficulty: the KS prover must produce
  oracle data satisfying `OutputRealizes`, but the prover cannot observe the
  verifier's leaf output during the interaction. See the docstring in
  `Security.lean` for details. A prior attempt using explicit
  `acceptOStmt`/`acceptWitness` parameters was circular (see docstring).
- [ ] State `Reduction.completeness_comp` for `Oracle.Spec` composition
  (very verbose due to oracle statement handling).
- [x] Make `Sumcheck/Interaction/Oracle.lean` the one-round `Oracle.Spec`
  surface. This establishes the first migration pattern: the round polynomial is
  an `.oracle` node,
  the verifier challenge is `.public`, and the public transcript contains only
  verifier-visible data.
- [x] Make `Sumcheck/Interaction/SingleRound.lean` the default single-round
  prover/reduction layer.
- [x] Make `Sumcheck/Interaction/General.lean` the default n-round reduction.
  This uses the oracle chain layer and a typed private residual witness that
  shrinks from `n` variables to `0` variables.
- [x] Remove the old Sumcheck `Interaction/Legacy` files from the active import
  graph.
- [x] Port and delete the old FRI `Interaction/Legacy` sketches.
  `Fri/Interaction/Core.lean`, `Fri/Interaction/FoldRound.lean`,
  `Fri/Interaction/FinalFold.lean`, `Fri/Interaction/FoldPhase.lean`,
  `Fri/Interaction/QueryRound.lean`, and `Fri/Interaction/General.lean` now
  cover the non-final fold phase, terminal fold, query round, and full
  composition. The old `Fri/Spec/General.lean` entrypoint is intentionally not
  cut over yet.
- [ ] Validate the boundary layer on concrete examples once operational
  pullbacks compile: Sumcheck single-round reuse, FRIBinius witness
  reinterpretation, and BatchedFRI batching boundary.
- [ ] Revisit generic verifier monads for relations (`MonadQuery`-style),
  deferred during current cutover.

## Planned
- [ ] **Leaf hardening** — keep FRI and Sumcheck interaction surfaces beside
  their old canonical specs where those canonical specs still exist, add
  honest-completeness sanity lemmas, and use them to identify reusable
  composition/query-routing helpers.
- [ ] **Protocol migration** — Binius, Whir, Stir, Components,
  CommitmentScheme, and BCS/commitment slices. Port leaves beside old
  entrypoints first; extract core abstractions only after repeated need.
- [ ] **Fiat-Shamir** — abstract FS transform on Spec + RoleDecoration
- [ ] **DuplexSponge FS** — concrete instantiation (deferred)
- [ ] **BCS transformation** — IOR + commitment → IR (in progress via
  `Oracle/BCS.lean`)

## Open questions / issues

- **OracleInterface integration** (RESOLVED): Oracle access is modeled via
  `OracleDecoration` — a per-sender-node attachment of `OracleInterface`
  instances as data (not typeclass). The oracle spec for querying messages is
  path-dependent (parameterized by the transcript), reflecting the W-type
  structure where move types depend on prior moves. This differs fundamentally
  from the old flat `ProtocolSpec n` approach.

- **Two interaction oracle surfaces** (OPEN): `OracleDecoration` over
  ordinary `Interaction.Spec` and `Oracle.Spec` currently coexist. The
  former is now quarantined under `Oracle/Legacy/` for existing
  interaction-oracle code; the latter is the forward path because
  `.public`/`.oracle` nodes make verifier-visible transcripts and oracle
  outputs definitionally cleaner. `Oracle/Legacy/Bridge.lean` converts specs
  and decorations, but verifier/reduction conversion is deferred because output
  types must be reindexed.

- **Execution of OracleReduction** (PARTIALLY RESOLVED): `OracleReduction.run`
  and `OracleReduction.execute` are reintroduced and build on
  `runWithOracleCounterpart`. The remaining execution-side gap is composition:
  the oracle analog of `Reduction.execute_comp` is still deferred.

- **Growing oracle access**: Both `OracleCounterpart` and
  `InteractiveOracleVerifier` use an `accSpec` parameter that grows at each
  sender node. This faithfully models verifier gaining oracle access round by
  round, supporting non-public-coin protocols. The accumulation is:
  `accSpec₀ = []ₒ`, then `accSpecᵢ₊₁ = accSpecᵢ + oiᵢ.toOC.spec`.
  The `OracleVerifier.iov` field starts with `accSpec = []ₒ`.

- **`simulate` is transcript-dependent; `reify` is optional**: Unlike the flat
  `ProtocolSpec n` model where message types are static, in the W-type model
  the oracle spec depends on the transcript (path through the tree).
  `simulate` is therefore transcript-dependent. Concrete reification is no
  longer part of the core oracle API; the transitional implementation lives in
  `Oracle/Legacy/Reification.lean`.

- **Witness typing** (RESOLVED): `WitnessIn` is now a plain type, not
  dependent on the input statement. `WitnessOut` remains parallel to
  `StatementOut` (both indexed by `(s, tr)`), so prover input/output are plain
  products and statement/witness compatibility is expressed in security
  relations rather than in the types.

- **Sequential security composition** (RESOLVED): `Reduction.comp` now consumes
  the second stage as a transcript-indexed `Reduction.Continuation`, so the
  completeness / perfect-completeness / soundness composition theorems can
  quantify directly over first-phase transcripts without encoding the second
  reduction awkwardly inside the theorem statement.

- **Knowledge soundness implies soundness** (OPEN): the natural proof via
  `mapOutputWithRoles` + `probEvent_mono` requires the KS prover to produce
  oracle data satisfying `OutputRealizes`, but the prover cannot observe the
  verifier's leaf output during the interaction. Prior attempts using explicit
  `acceptOStmt`/`acceptWitness` parameters were circular (they assume the
  caller can produce concrete oracle realizations, which is exactly the
  "knowledge" KS should extract). See docstring in `Oracle/Security.lean`.

- **Verifier-indexed RBR semantics**: `ClaimTree` / `rbrSoundness` currently
  talk about transcript predicates and `randomChallenger`, not the full
  statement-indexed `Verifier` object. This is the main remaining design gap in
  `Security.lean`.

- **Generic verifier monads** (DEFERRED): a later cleanup may let verifier code
  be written in any query-capable monad that lowers coherently to `OracleComp`,
  but the semantic core is intentionally still phrased in `OracleComp` during
  the current cutover.

- **Where Interaction goes long-term**: planned to move to VCVio once stable.
  Keep the generic interaction layer import-free from ArkLib. The oracle layer
  still bridges to ArkLib's shared `OracleInterface` abstraction until that
  abstraction is upstreamed or replaced.

## Related work

Our framework independently converges with several lines of work:

- **Escardo–Oliva (2023)** "Higher-order Games with Dependent Types" (TCS 974):
  type trees `𝑻` (= `Spec`), paths (= `Transcript`), `structure S`
  (= `Decoration S`), strategies, `Overline` (= `Decoration.map`).
  Multiple independent decorations; our `Refine` generalizes to dependent ones.
- **Hancock–Setzer (2000)**: structural recursion on interaction interface.
- **Interaction Trees** (Xia et al., POPL 2020): coinductive free monad analog.
- **Displayed algebras / Ornaments** (McBride 2010): `Decoration.Refine`.
- **Session types**: `Spec + RoleDecoration` as dependent session types.

## Old core (to be replaced)

| Area | Files | Status |
|------|-------|--------|
| `OracleReduction/ProtocolSpec/` | 3 files | Replaced by `Interaction/Basic/` modules |
| `OracleReduction/Basic.lean` | 1 file | Replaced by `Interaction/Reduction.lean` |
| `OracleReduction/` (rest) | ~32 files | Legacy; many TODO/sorry sites remain |
| `ProofSystem/` | many files | Mixed: older protocols still import legacy `OracleReduction`; Sumcheck/FRI `OracleDecoration` interaction work is quarantined under `Interaction/Legacy/` |
| `CommitmentScheme/` | several files | Still partly tied to legacy oracle interfaces |
| `OracleReduction/OracleInterface.lean` | 1 file | Stable, to be reused |

Breakage is expected and intentional. We fix downstream incrementally.
