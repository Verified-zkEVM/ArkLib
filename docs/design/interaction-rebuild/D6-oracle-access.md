# D6. Oracle families along a completed path, the oracle map, and routing

**Status:** Proposed: awaiting maintainer approval.
**Implemented by:** ArkLib PR A (commit 3, oracle family, append law and oracle map; commit 4,
routing in composed decisions) and ArkLib PR D (virtual outputs and routing support beyond A's
core, logged execution).

## Decision

A passive verifier (record D4) queries only after the interaction, when every oracle message is
present. Oracle access is therefore static: three pieces of data over a *completed* path, and
nothing that grows during a run.

**1. Oracles along a completed path.** For an oracle signature, the oracle messages along a run
form a family indexed by the shape path:

```lean
-- intended, not existing
def oracleIdx (s : FreeM OraclePoly PUnit) : Path s → Type          -- oracle nodes on the path
def oracles   (s) (p : Path s) : OracleSpec (oracleIdx s p)          -- their interfaces
def payloadImpl (s) (tr : PathAlong oracleSig s) :
    QueryImpl (oracles s (projectPathAlong oracleSig s tr)) Id       -- answers from `tr`'s payloads

theorem oracles_append (p₁ : Path s₁) (p₂ : Path (s₂ p₁)) :
    oracles (s₁.append s₂) (Path.append p₁ p₂) ≃ₒ oracles s₁ p₁ + oracles (s₂ p₁) p₂
theorem payloadImpl_append : payloadImpl (append tr₁ tr₂) ≅ payloadImpl tr₁ + payloadImpl tr₂
```

The index set depends on the path, because public messages select the suffix, but only through
the shape path `p`, which the verifier sees (record D3). The decision is typed
`StmtIn → (p : Path s) → View s p → OptionT (OracleComp (oSpec + [OStmtIn]ₒ + oracles s p))
(StmtOut p)`; in a run `p` is `projectPathAlong oracleSig s tr`, so `payloadImpl s tr` answers its
queries from the same run without a cast (record D4). Round-by-round state functions and extractors read
prefix payloads as transcript data, not through queries (record D7).

**2. The output interface is one oracle map.** The output oracle statements of a reduction are
given by a single structure from the inputs to the outputs:

```lean
-- intended, not existing
structure OracleMap (In : ιᵢ → Type) [∀ i, OracleInterface (In i)]
    (Out : ιₒ → Type) [∀ j, OracleInterface (Out j)] where
  f    : (∀ i, In i) → (∀ j, Out j)                         -- concrete output data
  impl : QueryImpl [Out]ₒ (OracleComp [In]ₒ)                -- query-by-query simulation
  law  : ∀ x q, simulateQ (answers x) (impl q) = pure (answer (f x) q)

-- the output interface of an oracle reduction on tree `s`
outputMap : StmtIn → (p : Path s) → View s p → OracleMap (OStmtIn + oracles s p) (OStmtOut p)
```

The output map may read the input statement and the verifier view (challenges and public
messages). The output statement type `StmtOut p` and the output family `OStmtOut p` are indexed
by the shape path `p`, so a public message may change both (see the open points below). `impl`
queries only the input oracle statements and the oracle messages on `p`, never the ambient oracles
`oSpec`.

- An *embedding* (every output is an input oracle or an oracle message, renamed) is a smart
  constructor that ignores the statement and the view: `impl` asks one renamed query and `f`
  reindexes.
- Oracle maps compose: `(g ∘ h).f = g.f ∘ h.f` and `(g ∘ h).impl = QueryImpl.compose g.impl
  h.impl`, with the law following from the two laws.

**3. Routing.** In a composed decision (record D5) the suffix's queries to its input oracles go
through the prefix's output map, and its queries to its own oracle messages map into the larger
family given by `oracles_append`. Both are `QueryImpl.compose` with the prefix map's `impl` and
a reindexing. The routing law states that the composed decision equals the prefix decision
followed by the suffix decision on the routed oracles, and that routing through `impl` agrees with
answering from `f` applied to the materialized prefix data.

**Accepted restriction.** A suffix's *shape* depends only on the public path and the input
statement, never on a value the prefix verifier obtains by an oracle query. No ArkLib protocol
needs more.

## Why

The current interaction layer gives the verifier access that grows during the run. Its local
syntax `localSyntax` (`ArkLib/Interaction/Oracle/Execution.lean:94`) types every node's
computation against accumulated access, and an oracle node extends it with
`Access.extend data.2.2 data.2.1` (line 105), defined with `extendImpl` in
`Oracle/Access.lean:44,49`. This machinery, with its decorations, world segments and phased
execution, exists only because that verifier queries mid-run. A passive verifier needs none of it.

The legacy layer has the three static pieces but in a two-case form. `OracleVerifier.outputOracle`
is `OracleOutputEmbedding … ⊕ OracleOutputSimulation …` (`OracleReduction/Basic.lean:342–344`),
and every consumer case-splits: `materializeOutputOracle` (line 360) and `simulateOutputQuery`
(line 390). The embedding is a special case of the simulation, `OracleOutputSimulation`
(line 271), whose fields `materializeOutput`, `simulateOutputQuery` and `simulateOutputQuery_eq`
correspond to `f`, `impl` and `law` above.

Two differences from the legacy simulation are deliberate.

- *The map reads the statement and the view.* Legacy `materializeOutput` and
  `simulateOutputQuery` both take `pSpec.Challenges`. Folded oracles need this: a folded output
  answers at a point `x` by querying a message oracle and combining the answers with a challenge
  `α`, so neither its data nor its simulation is a function of the oracles alone. Public messages
  and the input statement are already values the verifier holds, so reading them grants nothing
  new.
- *`impl` never queries `oSpec`.* Legacy `simulateOutputQuery` is typed in
  `OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ))`, but its law equates the simulation with
  `pure` of the materialized answer, so a lawful simulation never uses `oSpec`. Excluding it from
  the type states this and removes the ambient oracles from every composition of maps. Composition routes by hand: `firstQueryImpl`, `secondQueryImpl` and
`appendOutputSimulation` (`Composition/Sequential/Append/Basic.lean:491, 537, 601`), used by
`OracleVerifier.append` (line 619).

## Alternatives considered

- **The legacy sum `Embedding ⊕ Simulation`.** Two cases for one concept; every consumer and every
  composition lemma splits on it.
- **An output map that sees only the oracles** (no statement, no view). Cannot express folded
  oracles, which need the challenges.
- **`impl` with access to `oSpec`**, as legacy types it. The law already forbids lawful use of
  `oSpec`; keeping it in the type complicates composition for no expressible map.
- **Behavior only, without `f`** (the current interaction layer's `VirtualOracle`,
  `Oracle/Virtual.lean:66`, which has only `query : QueryImpl Out.spec (OracleComp srcSpec)`, and
  `SourceCtx`, `Oracle/Source.lean:39`). Output relations then become extensional statements about
  handlers, the next honest prover has no concrete data to work on, and the legacy
  materialization (record D8) must be reconstructed. The redundancy of `f` beside `impl` is the
  price of keeping concrete data, and the law ties them.
- **Per-node access** (`Access`, `extendImpl`, access decorations, world segments, phased
  execution). Unneeded once verifiers are passive.

## Consequences

- The legacy embedding (PR B) maps both `outputOracle` cases into one oracle map: the embedding
  case through the smart constructor, the simulation case field by field, reading the challenges
  from the view. Every legacy virtual output in the tree already queries only input and message
  oracles: Sumcheck (`ProofSystem/Sumcheck/Spec/SingleRound.lean:806`), BatchedFri
  (`ProofSystem/BatchedFri/Spec/SingleRound.lean:203`), BinaryBasefold
  (`ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:220`) and ToyProblem
  (`ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:278`). For the generic embedding B narrows the
  type of `simulateOutputQuery` by induction on the computation: a reachable `oSpec` query
  contradicts the agreement law, because the simulated computation is `pure`. Typing the
  unreachable branch needs an answer value, so the lemma assumes inhabited `oSpec` ranges.
  VCVio uses `[∀ t, Inhabited (spec.Range t)]` as a hypothesis and provides it for sums
  (`VCVio/OracleComp/OracleSpec.lean:145`, read at VCVio's reviewed head, not ArkLib's pin);
  whether VCVio already provides the narrowing lemma itself is unverified.
- Under this choice `f` supplies the legacy materialization directly (record D8).
- Per-node access has no replacement. PR D restates each test of mid-run access growth for passive
  verifiers (for example, "a decision cannot name an oracle outside its path" becomes a typing
  fact) or records it as retired with its mechanism, in D's migration list.
- The current layer's `appendExported` (`Oracle/SourceRouting.lean:441`) is reference material for
  routing; tree-independent mathematics is reused only through neutral owners.

**Acceptance tests (in A).** Routing through an embedding and through a virtual output both agree
with materialized data; the decision reaches oracle messages only by queries, answered from the
same run; `oracles_append` on a composed oracle protocol.

**Dependencies.** The composition law needs a VCVio lemma relating `simulateQ` and
`QueryImpl.compose`. Its availability at the pinned VCVio revision is unverified.

## Open points

- **Open: where `OracleInterface` instances live** (record D1), which fixes how `oracles` reads
  interfaces from positions or from `Γ`.
- **Path-indexed outputs, not open.** The output statement type and the output oracle family are
  indexed by the shape path: `StmtOut : Path s → Type u`, `J : Path s → Type uJ`,
  `B : (p : Path s) → J p → Type u` and `outputs : (p : Path s) → OracleFamily (J p) (B p)`
  (`OracleVerifier` in `OracleVerifier.lean`; the plain `Verifier` in `Reduction.lean` likewise).
  The decision returns `StmtOut p` and the output map targets `outputs p`, so a public message may
  change both, as in the frozen layer's `SourceRoutingDependentExample`. The shape path is public
  and fixed before the decision, so no cast is needed in a run. In an append the composite's
  output at a path of `s₁.append s₂` is the suffix's output at the split path (`splitFamily`,
  `OracleVerifier.splitOutputs` in `Composition.lean`); PolyFun's `Path.LiftAppend` is the same
  family by `liftAppend_split`. Security definitions index output languages and relations by the
  path through `PathProblem`. A verifier with one output type and family uses the constant
  families `fun _ => T` and `fun _ => OStmtOut`; the legacy embedding does so. The test
  `ArkLibTest/Interaction/Core/Oracle/DependentRouting.lean` ports the frozen example, with the
  Boolean sent by the prover because a passive verifier sends no messages.
