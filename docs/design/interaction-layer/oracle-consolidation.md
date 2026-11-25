# Oracle-access type consolidation

**Status:** Proposed. Design D is the recommended option, and the migration order in
[section 5](#5-migration-plan) was settled on 2026-11-25. Implementation has not started.

ArkLib's interaction layer should consolidate onto two oracle-access concepts: a flattened typeclass
`OracleInterface` and a four-field structure `OracleBundle`, deleting `OracleFamily` and its ten
bridge combinators. Both definitions move into `ArkLib/Relation/` at `Type` / `Type 1` with zero
universe parameters, and `OracleVerifier` becomes symmetric with `OracleBundle` inputs and
path-indexed `OracleBundle` outputs. The companion prototype
[`prototypes/OracleConsolidation.lean`](prototypes/OracleConsolidation.lean) checks the core
definitions, their equivalences with the current types, the transparency and erasure constraints in
Part 3, and a multi-stage routing example, without `sorry`. Its Design D definitions need no
universe pins; the equivalences with the current, still polymorphic types pin those types at `0`.

The prototype does not yet cover `SentOracles.queryNode` (the map from a query to the node that sent
it) on the binary-sum layout of PR 4; PR 4 starts by prototyping it.
All usage counts in this document were measured on commit `06caa6290d` (branch
`docs/interaction-oracle-consolidation-design`, after universe migration step 2) by scanning
stripped Lean code across `ArkLib/` and `ArkLibTest/`. This document is a design record only;
implementing the consolidation and running universe migration steps 3 through 6 remain out of scope.

## 1. Inventory of current oracle-access types and operations

The interaction layer currently maintains three types for data that answers queries
(`OracleInterface`, `OracleFamily`, and `OracleBundle`), an upstream wrapper (`OracleContext`) that
only one file uses, a protocol position carrier (`OraclePos`), a morphism type (`OracleMap`), and a
pure-lens pair (`OracleBundle.Lens` and `OracleBundle.Equiv`). Measuring code references across
`ArkLib/` and `ArkLibTest/` shows heavy use of `OracleInterface` across both layers, broad spread of
`OracleFamily` and `OracleBundle` in `Interaction/` and `Sumcheck/`, and near-zero production
adoption of `OracleContext`, `OracleBundle.tensor`, `OracleBundle.ofSpec`, `OracleBundle.Lens`, and
`OracleBundle.Equiv`.

### Core types

| Type | Kind and definition site | Files (ArkLib / Test) | Code hits | Current purpose |
|---|---|---:|---:|---|
| `OracleContext` (VCVio) | Structure, `.lake/packages/VCVio/VCVio/OracleComp/OracleContext.lean:25` | 1 / 0 | 5 | Bundles `OracleSpec ι` with `QueryImpl spec m`. VCVio itself has 0 callers outside `OracleContext.lean`. In ArkLib only `ArkLib/Relation/OracleInterface.lean:58,61,125` uses it. Five other files matching `OracleContext` (`ArkLib/OracleReduction/LiftContext/Lens.lean`, `LiftContext/OracleReduction.lean`, `ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean`, `Sumcheck/Impl/OracleProver.lean`, `Sumcheck/Spec/SingleRound.lean`) refer to an unrelated legacy namespace `OracleContext.Lens`. |
| `OracleInterface` | Class, `ArkLib/Relation/OracleInterface.lean:56` | 128 / 49 | 1,105 | Typeclass attaching `Query : Type v` and `toOC : OracleContext Query (ReaderM Message)` to a data carrier `Message : Type u`. Shared by both the interaction layer and the legacy `OracleReduction/` layer. Defines 121 `instance` declarations across 53 files (45 `ArkLib/`, 8 `ArkLibTest/`). |
| `OracleFamily` | Structure, `ArkLib/Relation/Basic.lean:25` | 36 / 25 | 307 | One-field wrapper holding `interface : ∀ i, OracleInterface (Realization i)` as explicit data over parameters `(Index : Type u)` and `(Realization : Index → Type v)`. Used for `OracleVerifier.outputs`, `oracleMessageFamily`, `sentOracleMessageFamily`, `StageChain` boundaries, and Sumcheck polynomial inputs. |
| `OracleBundle` | Structure, `ArkLib/Interaction/OracleVerifier.lean:106` | 22 / 15 | 289 | Four-field structure `{ Index, spec, Data, answer : Data → QueryImpl spec Id }` packaging a query specification with backing data. Used for `OracleVerifier.inputs`, `pathBundle`, `availableBundle`, `OracleMap` endpoints, and `BundleOps.lean`. |
| `OracleMap` | Structure, `ArkLib/Interaction/OracleVerifier.lean:143` | 22 / 27 | 303 | Morphism between two `OracleBundle`s pairing `f : In.Data → Out.Data`, `impl : QueryImpl Out.spec (OracleComp In.spec)`, and agreement `law`. Used for `OracleVerifier.outputMap`, path routing, stage composition, and derived oracles. |
| `OraclePos` | Inductive, `ArkLib/Interaction/Signature.lean:46` | 11 / 4 | 57 | Protocol tree positions `message X`, `challenge C`, and `oracle X interface` (`Signature.lean:49`). Carries `OracleInterface X` directly on the position. |

**Compatibility note on legacy `OracleInterfaces`.** The class `ProtocolSpec.OracleInterfaces`
(`ArkLib/OracleReduction/ProtocolSpec/Basic.lean:657`) appears in only 2 files and 7 hits
(`ArkLib/OracleReduction/ProtocolSpec/Basic.lean` and `ArkLib/OracleReduction/VectorIOR.lean:79`).
It belongs to the legacy `OracleReduction/` layer and retires with that layer. Flattening
`OracleInterface` does not break `OracleInterfaces` because `OracleInterfaces` stores `Option
(OracleInterface (pSpec.Message i))` without accessing `toOC`.

### Operations on `OracleInterface`

| Operation | Definition site | Files (ArkLib / Test) | Code hits | Purpose and notes |
|---|---|---:|---:|---|
| `toOC` (all code uses) | `ArkLib/Relation/OracleInterface.lean:58` | 23 / 13 | 128 | 109 construction hits across 35 files (`toOC := ...`, `toOC.spec := ...`, `toOC.impl := ...`) and 19 projection hits across 5 files (`OracleInterface.lean`, `StageChain.lean`, `Salt.lean`, `RandomQuery.lean`, `AccessTyping.lean`). Zero files construct `OracleInterface` with positional `⟨...⟩` syntax. |
| `OracleInterface.Response` | `ArkLib/Relation/OracleInterface.lean:68` | 4 / 1 | 33 | Unfolds to `O.toOC.spec q`. Mainly used in `KZG/Binding.lean` (22) and `KZG/FunctionBinding/Basic.lean` (6). |
| `OracleInterface.spec` | `ArkLib/Relation/OracleInterface.lean:72` | 0 / 0 | 0 | Zero external callers. `RandomQuery.lean:225,235` accesses `O.toOC.spec` directly instead. |
| `OracleInterface.answer` | `ArkLib/Relation/OracleInterface.lean:77` | 5 / 2 | 11 | Explicit qualified calls (`(O.toOC.impl q).run m`), plus unqualified dot-notation calls across `Relation/`, `OracleReduction/`, and `ProofSystem/`. |
| `OracleInterface.instDefault` | `ArkLib/Relation/OracleInterface.lean:94` | 8 / 28 | 86 | Trivial `Unit` query returning the message. Intentionally unregistered as a global instance. |
| `toOracleSpec` / `[v]ₒ` (excluding `[]ₒ`) | `ArkLib/Relation/OracleInterface.lean:106` | 73 / 17 | 768 | Semireducible conversion of `v : ι → Type` into `OracleSpec ((i : ι) × (O i).Query)`. Explicit form `[v]ₒ' O` accounts for 21 hits in 13 files. Distinct from VCVio's empty spec `[]ₒ` (93 files, 724 hits). |
| `OracleInterface.toOracleImpl` | `ArkLib/Relation/OracleInterface.lean:114` | 1 / 0 | 1 | Dead code. Zero callers outside its own definition; `simOracle0` (`199`) duplicates it. |
| `instProd` / `instTensorProd` / `instProdForall` / `instTensorForall` | `ArkLib/Relation/OracleInterface.lean:143-196` | 1 / 0 | 3 | Product and dependent-function instances. `instTensorForall` (`176-180`) is a copy-paste duplicate of `instProdForall` (`192-196`): both use `(i : ι) × (O i).Query` rather than a tensor product. |
| `simOracle` / `simOracle0` / `simOracle2` | `ArkLib/Relation/OracleInterface.lean:199-231` | 43 / 10 | 290 | Legacy and `Interaction/Legacy/` simulation handlers for `[T]ₒ`. |
| `agreementQueries` / `distanceLE` | `ArkLib/Relation/OracleInterface.lean:248,267` | 2 / 0 | 12 | Oracle distance predicate. Used only in `OracleInterface.lean` and `ArkLib/ProofSystem/Component/RandomQuery.lean`. |

### Operations on `OracleFamily`

| Operation | Definition site | Files (ArkLib / Test) | Code hits | Purpose and notes |
|---|---|---:|---:|---|
| `OracleFamily.Behavior` | `ArkLib/Relation/Basic.lean:43` | 3 / 2 | 7 | `QueryImpl O.spec Id`. Used in `Sumcheck/BehaviorComposition.lean`, `Sumcheck/Impl/Projection.lean`, `Sumcheck/Interval.lean` (test), and `AnswerOnlyRelations.lean`. |
| `behaviorOfRealizations` | `ArkLib/Relation/Basic.lean:46` | 9 / 11 | 90 | Evaluates `∀ i, O.Realization i` into `QueryImpl O.spec Id`. |
| `OracleFamily.reindex` | `ArkLib/Relation/Basic.lean:54` | 1 / 4 | 38 | Pulls back slots along `f : J → I`. Used in `OracleVerifier.lean:240` (`OracleMap.embedding`) and 4 interaction tests (`BundleFamilies`, `DerivedOracles`, `OracleMaps`, `UniverseCanary`). Other `.reindex` hits in `Data/`, `Binius/`, and `RingSwitching/` are `Basis.reindex` or `Matrix.reindex`. |
| `sumFamily` | `ArkLib/Interaction/OracleVerifier.lean:48` | 5 / 4 | 63 | Disjoint union of two `OracleFamily`s over `I ⊕ J`. |
| `singletonFamily` | `ArkLib/Interaction/OracleVerifier.lean:55` | 4 / 4 | 23 | Wraps one `OracleInterface X` into `OracleFamily PUnit (fun _ => X)`. |
| `sumData` / `sumData_eta` | `ArkLib/Interaction/OracleVerifier.lean:86,92` | 2 / 4 | 27 | Pairs realizations into `∀ k, Sum.elim A B k` and proves extensional round-trip. |
| `OracleMessageIndex` / `OracleMessage` | `ArkLib/Interaction/OracleVerifier.lean:31,39` | 8 / 6 | 38 | Slot index and message types along a completed path. |
| `oracleMessageFamily` | `ArkLib/Interaction/OracleVerifier.lean:60` | 13 / 16 | 130 | Family of oracle messages on a completed path, built recursively with `sumFamily` and `singletonFamily`. |
| `oracleMessageSpec` / `oracleMessageImpl` / `oracleMessages` | `ArkLib/Interaction/OracleVerifier.lean:69,81,72` | 8 / 2 (spec), 5 / 4 (impl), 25 / 21 (msgs) | 32 / 22 / 162 | Specification, pure handler, and extracted realizations of a completed path's oracle messages. |
| `oracleMessageFamily_append` / `split` | `ArkLib/Interaction/OracleVerifier.lean:327,346` | 3 / 1 | 25 | Routes oracle messages across `s₁.append s₂` through `sumFamily` and `familySumAssoc`. |
| `sentOracleMessageFamily` | `ArkLib/Interaction/Oracle/SentOracles.lean:71` | 1 / 0 | 25 | Partial-transcript counterpart to `oracleMessageFamily`, used only inside `SentOracles.lean`. |
| `liftQueries` / `lowerQueries` / `liftInputs` / `liftOutputs` / `lowerOutputs` | `ArkLib/Interaction/StageChain.lean:81-183` | 1 / 1 | 30 | Query-universe adapters. Scheduled for deletion in universe migration step 4 (`docs/design/interaction-rebuild/D2-ownership-and-universes.md:153-154`). |

### Operations on `OracleBundle` and `OracleMap`

| Operation | Definition site | Files (ArkLib / Test) | Code hits | Purpose and notes |
|---|---|---:|---:|---|
| `OracleBundle.ofFamily` (+ `CoeOut`) | `ArkLib/Interaction/OracleVerifier.lean:119,129` | 8 / 5 | 63 | Explicit conversion from `OracleFamily` to `OracleBundle` (plus implicit coercions via `CoeOut`). |
| `OracleBundle.sum` | `ArkLib/Interaction/OracleVerifier.lean:135` | 3 / 9 | 45 | Disjoint sum of two `OracleBundle`s with pair `Data := R.Data × R'.Data`. Used in `pathBundle` (52 files, 260 hits) and `availableBundle` (`SentOracles.lean:113`, 6 hits). |
| `OracleBundle.ofSpec` | `ArkLib/Interaction/Oracle/BundleOps.lean:30` | 1 / 1 | 3 | Behavior-only bundle (`Data := QueryImpl spec Id`, `answer := id`). Used only in `BundleOps.lean` and `ArkLibTest/Interaction/Oracle/DerivedOracles.lean:30`. (`ofSpec` hits in `Sumcheck/Computable.lean` and `DomainEquivalence.lean` refer to `RoundStatement.ofSpec`.) |
| `OracleMap.ofImpl` | `ArkLib/Interaction/Oracle/BundleOps.lean:38` | 1 / 1 | 2 | Builds an `OracleMap` into `OracleBundle.ofSpec spec`. Used only in `BundleOps.lean` and `DerivedOracles.lean:29`. |
| `OracleBundle.tensor` | `ArkLib/Interaction/Oracle/BundleOps.lean:46` | 1 / 1 | 9 | Product of queries and answers via `PFunctor.tensor`. Used only in `BundleOps.lean` and `ArkLibTest/Interaction/Oracle/OracleMaps.lean`. |
| `OracleBundle.liftResponse` | `ArkLib/Interaction/Oracle/BundleOps.lean:60` | 1 / 1 | 13 | Response-universe adapter. Scheduled for deletion in universe migration step 4. |
| `OracleBundle.Lens` / `Equiv` | `ArkLib/Interaction/Oracle/BundleOps.lean:73,141` | 1 / 1 | 24 / 11 | Single-query polynomial lens paired with `pullData`. Only production instance is `OracleBundle.Equiv.liftResponse` (`BundleOps.lean:168`); only test user is `OracleMaps.lean`. |
| `OracleMap.id` / `comp` / `fst` / `snd` / `par` / `sumAssoc` / `sumAssocSymm` | `ArkLib/Interaction/OracleVerifier.lean:158-231` | 14 / 17 | 84 | Core bundle-level `OracleMap` combinators (`fst` carries `@[macro_inline]`). |
| `OracleMap.withAmbient` | `ArkLib/Interaction/Composition.lean:492` | 3 / 5 | 18 | Lifts an `OracleMap` past `ambient` queries. Used in `Composition.lean`, `StageChain.lean`, `Oracle/Cost.lean`, and 5 interaction tests. |
| `OracleMap.embedding` | `ArkLib/Interaction/OracleVerifier.lean:239` | 5 / 13 | 43 | Slot-renaming map `In → In.reindex rename` on `OracleFamily`. |
| `ofSumFamily` / `toSumFamily` / `familySumAssoc` / `familySumAssocSymm` / `OracleMap.sum` | `ArkLib/Interaction/OracleVerifier.lean:246-320` | 2 / 1 | 26+ | Representation bridges converting between `sumFamily a b` and `OracleBundle.sum a b`. Used almost exclusively inside `OracleVerifier.lean`, `Composition.lean`, `SentOracles.lean`, and `BundleFamilies.lean`. |
| `pathLift` | `ArkLib/Interaction/OracleVerifier.lean:519` | 7 / 7 | 40 | `@[macro_inline]` query lift from `oracleMessageSpec` into `ambient + (pathBundle inputs s p).spec`. Currently takes `inputs : OracleFamily` even though `pathBundle` takes `OracleBundle`. |
| `splitOracleMessages` / `splitPathBundle` / `prefixRoute` / `suffixRoute` | `ArkLib/Interaction/Composition.lean:474-571` | 9 / 16 | 110 | Path splitting and routing combinators for sequential verifier composition. |
| `comapInputs` / `mapOutputs` | `ArkLib/Interaction/StageChain.lean:124,132` | 1 / 0 | 10 | Pre- and post-composition of `OracleVerifier` with `OracleMap`s, currently constrained to `OracleFamily` endpoints. |

### Users by directory

The inventory shows a sharp split between the two layers of ArkLib:

- **`ArkLib/Relation/` (2 files):** `OracleInterface.lean` defines `OracleInterface` and 14 core
  instances; `Basic.lean` defines `OracleFamily`, `ClaimFamily`, `Problem`, and `Relation`.
- **`ArkLib/Interaction/` core (4 files):** `Signature.lean` and `Protocol.lean` mention
  `OracleInterface` on `OraclePos.oracle`; `OracleVerifier.lean`, `Composition.lean`, and
  `StageChain.lean` carry 107 hits of `OracleFamily`, 85 of `OracleBundle`, and 94 of `OracleMap`.
- **`ArkLib/Interaction/Oracle/` (8 files):** `BundleOps.lean` and `Cost.lean` use `OracleBundle`
  only; `LoggedExecution.lean`, `QueriesByMove.lean`, `QueriesByMoveLaws.lean`,
  `Reassociation.lean`, `Routing.lean`, and `SentOracles.lean` mix `OracleBundle` inputs with
  `OracleFamily` outputs and `oracleMessageFamily`.
- **`ArkLib/Interaction/Security/` (10 files):** `Agreement.lean`, `Completeness.lean`,
  `CompositionSoundness.lean`, `Implications.lean`, `Knowledge.lean`, `KnowledgeComposition.lean`,
  `RoundByRound.lean`, `Soundness.lean`, `StateRestoration.lean`, and `StateRestorationBudget.lean`
  carry `OracleFamily` solely because `OracleVerifier.outputs` requires `OracleFamily`.
- **`ArkLib/Interaction/Legacy/` (6 files):** Bridges legacy `[OStmtIn]ₒ` and `[pSpec.Message]ₒ`
  families into `OracleVerifier`.
- **`ArkLib/ProofSystem/` (71 files for `OracleInterface`; 13 files for `OracleFamily`; 2 files for
  `OracleBundle`):** Every `OracleFamily` and `OracleBundle` user in `ProofSystem/` lives under
  `ArkLib/ProofSystem/Sumcheck/`. Both `Sumcheck/Types.lean:30-36` and
  `Sumcheck/Spec/PolynomialInterface.lean:31-32` wrap a single multivariate polynomial in a dummy
  `Unit → Type` function solely to build an `OracleFamily`. All other proof systems (`Fri`,
  `BatchedFri`, `Binius`, `Plonk`, `Spartan`, `RingSwitching`, `Component`, `ToyProblem`) still sit
  on legacy `OracleReduction/` and use `OracleInterface` only.
- **`ArkLib/Commitments/` (10 files):** `Functional/Basic.lean`, `Hachi/Commitment.lean`, and 8
  `KZG/` files use `OracleInterface` only (9 of them construct `OracleInterface` via `toOC`).
- **`ArkLib/OracleReduction/` (34 files):** Legacy layer; uses `OracleInterface` and `[v]ₒ` only (2
  files mention `toOC`).
- **`ArkLibTest/` (25 files for `OracleFamily`; 15 for `OracleBundle`; 49 for `OracleInterface`):**
  Interaction tests exercise every operation in `OracleVerifier.lean` and `BundleOps.lean`. Notably,
  `ArkLibTest/Interaction/Oracle/ProtocolTree/AccessTyping.lean:197-198,208-209` already builds an
  `OracleBundle` manually from a single `OracleInterface` via `⟨interface.Query,
  interface.toOC.spec, Messages, fun m q => (interface.toOC.impl q).run m⟩`.

## 2. Exact relationships between concepts

After universe migration step 5 places all data types in `Type` and all descriptions in `Type 1`,
only two genuinely distinct concepts remain. A typeclass `OracleInterface X` indexes a single
carrier `X : Type`, and a bundled description `OracleBundle : Type 1` packages `Data : Type` with
its interface. `OracleFamily` adds no expressiveness beyond an indexed function `I → OracleBundle`
(or `(i : I) → OracleInterface (A i)`). Likewise, `OracleContext` adds no expressiveness beyond
`(Query : Type) × ...` and introduces a `ReaderM` mismatch on heterogeneous sums.

Every claim in the tables below is checked in
[`prototypes/OracleConsolidation.lean`](prototypes/OracleConsolidation.lean). References cite the
flattened `Consolidated.OracleInterface` (`OracleConsolidation.lean:49`) and four-field
`Consolidated.OracleBundle` (`OracleConsolidation.lean:162`).

### Equivalences holding by `rfl` in both directions

| Relationship | Lean statement | Status | Prototype citation |
|---|---|---|---|
| Flattened interface vs VCVio `OracleContext` | `Consolidated.OracleInterface X ≃ (Query : Type) × OracleContext.{0, 0, 0} Query (ReaderM X)` | `rfl` both ways | `OracleConsolidation.lean:736` |
| Four-field `OracleBundle` vs Sigma of `OracleInterface` | `Consolidated.OracleBundle ≃ (Data : Type) × Consolidated.OracleInterface Data` | `rfl` both ways | `OracleConsolidation.lean:746` |
| Current `OracleInterface.{0, 0} X` vs flattened | `_root_.OracleInterface.{0, 0} X ≃ Consolidated.OracleInterface X` | `rfl` both ways | `OracleConsolidation.lean:755` |
| Current `OracleBundle.{0, 0, 0}` vs consolidated | `Interaction.OracleBundle.{0, 0, 0} ≃ Consolidated.OracleBundle` | `rfl` both ways | `OracleConsolidation.lean:764` |
| Current `OracleFamily.{0, 0, 0} I A` vs Pi of interfaces | `OracleFamily.{0, 0, 0} I A ≃ ((i : I) → Consolidated.OracleInterface (A i))` | `rfl` both ways | `OracleConsolidation.lean:773` |
| Total space of `OracleFamily` vs indexed bundles | `((I : Type) × (A : I → Type) × OracleFamily.{0, 0, 0} I A) ≃ ((I : Type) × (I → Consolidated.OracleBundle))` | `rfl` both ways | `OracleConsolidation.lean:783` |

Both round-trips hold by `rfl` because `ReaderT`, `Id`, `QueryImpl`, and structure eta all reduce
definitionally when the argument order matches.

### Combinator equalities holding by `rfl` in Design D

```lean
-- Sum answers reduce to VCVio's `QueryImpl.add` by `rfl`:
(R.sum S).answer x = R.answer x.1 + S.answer x.2

-- Product interface bundles identically to `OracleBundle.sum`:
OracleBundle.of (α × β) instProd = (OracleBundle.of α Oα).sum (OracleBundle.of β Oβ)

-- Indexed bundle matches `instProdForall` and semireducible `toOracleSpec`:
OracleBundle.ofIndexed A O = OracleBundle.of (∀ i, A i) (instProdForall A)
(OracleBundle.ofIndexed A O).spec = toOracleSpec A

-- Behavior-only bundle has identity answering:
(OracleBundle.ofSpec spec).answer = id

-- Projection lens embeds to `OracleMap.fst.impl` definitionally (`FreeM.map id` reduces):
(OracleBundle.Lens.fstLens R S).toOracleMap.impl = (OracleMap.fst R S).impl
```

Each equation is checked by `rfl` at `OracleConsolidation.lean:796-819`.

### Relationships that need a proof or fail

| Statement or operation | Result | Reason and prototype citation |
|---|---|---|
| `C₁.add C₂` for `C₁ : OracleContext Q₁ (ReaderM D₁)` and `C₂ : OracleContext Q₂ (ReaderM D₂)` | **Fails to typecheck** | `OracleContext.add` (`.lake/packages/VCVio/VCVio/OracleComp/OracleContext.lean:54`) fixes one monad `m` for both summands and cannot unify `ReaderM D₁` with `ReaderM D₂` (`OracleConsolidation.lean:839`). |
| `(fun q => (C₁.impl.addReaderT C₂.impl q).run x) = (fun q => (C₁.impl q).run x.1) + (fun q => (C₂.impl q).run x.2)` | **Fails `rfl`; needs proof** | `QueryImpl.addReaderT` pattern-matches `q` inside `ReaderT` rather than outside; proving equality requires `funext q; cases q <;> rfl` (`OracleConsolidation.lean:856-872`). |
| `B.spec` on `abbrev SigmaBundle := (Data : Type) × OracleInterface Data` | **Fails to typecheck** | Lean resolves dot notation on `Sigma`, not on the abbreviation; `Sigma.spec` does not exist (`OracleConsolidation.lean:876-885`). |
| `((indexed F).sum (indexed G)).Data = (indexed (Sum.elim F G)).Data` | **Fails `rfl`; needs `Equiv`** | Left side is `(∀ i, (F i).Data) × (∀ j, (G j).Data)`; right side is `∀ k, (Sum.elim F G k).Data`. Bridged only up to `OracleBundle.indexedSumEquiv` (`OracleConsolidation.lean:424,899`) and `sumData_eta` (`ArkLib/Interaction/OracleVerifier.lean:92`). |
| `OracleBundle.ofFamily : OracleFamily I A → OracleBundle` | **Not an equivalence** | Forgets the slot decomposition `I`; its image always has `Data = ∀ i, A i` and `Query = (i : I) × Q i`, missing `OracleBundle.ofSpec`, `OracleBundle.sum`, `OracleBundle.tensor`, and unindexed single oracles (`OracleConsolidation.lean:207-238`). |
| `OracleBundle.Lens.toOracleMap : Lens R S → OracleMap S R` | **Contravariant injection, not an equivalence** | Every pure single-query lens embeds contravariantly into `OracleMap` via VCVio's `QueryImpl.comapLens`, but `OracleMap` also expresses 0-query constants and multi-query adaptive simulations such as `doubleQueryMap` (`OracleConsolidation.lean:398,906`). |
| `instance : BadInterface (Polynomial R)` with `answer : Message → QueryImpl spec Id` | **Fails typeclass synthesis** | `Id` is semireducible in Lean 4, exposing `Semiring (Id ((ofFn fun x => R).Range point))` when elaborating `p.eval point` (`OracleConsolidation.lean:929-948`). |
| `rw` on `simulateQ` over 2-field `structure NestedBundle where Data : Type; interface : OracleInterface Data` | **Fails `.implicit` transparency check** | Unfolding `In.spec` exposes primitive projection `In.interface.2 : OracleSpec In.interface.1` while `@simulateQ`'s implicit index holds the semireducible class projection `OracleInterface.Query In.Data` (`OracleConsolidation.lean:952-1019`). |

## 3. Design options

Four designs span the trade-off space. Design A keeps all three types and adds coercions. Design B
replaces ArkLib's wrappers with VCVio's `OracleContext` and Sigma types. Design C deletes
`OracleFamily` while leaving `OracleInterface` unchanged. Design D deletes `OracleFamily` and
flattens `OracleInterface` onto a direct pure handler alongside four-field `OracleBundle`.

### Design A: Keep current types and add equivalences (baseline)

Design A retains `OracleInterface` (with `toOC : OracleContext Query (ReaderM Message)`),
`OracleFamily`, and `OracleBundle`, changing nothing except post-step-5 universes (`Type` / `Type
1`) and adding helper constructors `OracleBundle.ofInterface` and `OracleBundle.Lens.toOracleMap`.

```lean
-- Design A: current structures specialized to Type / Type 1
class OracleInterface (Message : Type) : Type 1 where
  Query : Type
  toOC : OracleContext.{0, 0, 0} Query (ReaderM Message)

structure OracleFamily (Index : Type) (Realization : Index → Type) : Type 1 where
  interface : ∀ i, OracleInterface (Realization i)

structure OracleBundle : Type 1 where
  Index : Type
  spec : OracleSpec Index
  Data : Type
  answer : Data → QueryImpl spec Id

@[reducible] def OracleBundle.ofInterface (X : Type) (I : OracleInterface X) : OracleBundle :=
  ⟨I.Query, I.toOC.spec, X, I.answer⟩
```

**Operations and users.** Every existing operation and caller stays intact. `OracleVerifier` keeps
its asymmetric signature (`inputs : OracleBundle`, `outputs : Path s → OracleFamily (J p) (B p)`).
`OracleVerifier.lean`, `Composition.lean`, `Routing.lean`, and `SentOracles.lean` retain
`sumFamily`, `singletonFamily`, `sumData`, `sumData_eta`, `ofSumFamily`, `toSumFamily`,
`familySumAssoc`, `familySumAssocSymm`, and `OracleMap.sum`. Sumcheck retains `PolynomialData : Unit
→ Type` and `polynomialFamily : OracleFamily Unit ...`.

**Costs and risks.**
- **Migration cost:** Near zero (one small PR adding two helpers).
- **Ongoing maintenance cost:** High. Every protocol verifier carries two extra implicit parameters
  `{J}` and `{B}` on outputs. Every path-splitting proof must route through `ofSumFamily` /
  `toSumFamily` and `sumData_eta`. Every single-oracle protocol must either invent a dummy `Unit`
  index or lose compatibility with `OracleVerifier.outputs`. Behavior-only bundles
  (`OracleBundle.ofSpec`) remain unwritable as verifier outputs, blocking derived outputs from
  entering `StageChain` or `OracleVerifier.append`.
- **Technical risk:** Low short-term risk, high long-term API drag as new protocols (`FRI`,
  `Binius`, `Plonk`, `Spartan`) port from `OracleReduction/` to `Interaction/`.

### Design B: Use VCVio `OracleContext` and Sigma types directly

Design B removes `OracleBundle` as a structure and removes `OracleInterface`'s wrapper by expressing
bundled oracles directly as VCVio's `OracleContext` in a Sigma type, keeping `OracleInterface` (if
at all) only as an abbreviation or thin class over `OracleContext`.

```lean
-- Design B: OracleContext + Sigma type
abbrev OracleBundle : Type 1 :=
  (Data : Type) × (Query : Type) × OracleContext.{0, 0, 0} Query (ReaderM Data)

def OracleBundle.sum (R S : OracleBundle) : OracleBundle :=
  ⟨R.1 × S.1, R.2.1 ⊕ S.2.1,
    ⟨R.2.2.spec + S.2.2.spec, QueryImpl.addReaderT R.2.2.impl S.2.2.impl⟩⟩
```

**Operations and users.** Every `B.Data`, `B.spec`, `B.answer`, `R.sum S`, and `R.tensor S` call
breaks dot notation (`OracleConsolidation.lean:885`) and becomes prefix calls or `.1` / `.2.1` /
`.2.2` projections. Every `simulateQ (B.answer x)` call must unpack `ReaderM` via `fun q =>
(B.2.2.impl q).run x`. `OracleContext.add` cannot implement `OracleBundle.sum` because `ReaderM
R.Data` and `ReaderM S.Data` are distinct monads (`OracleConsolidation.lean:839`). Using
`QueryImpl.addReaderT` breaks definitional equality `(R.sum S).answer x = R.answer x.1 + S.answer
x.2` (`OracleConsolidation.lean:856`). Every `OracleMap.fst` / `snd` / `par` / `sumAssoc` law loses
`rfl` and requires `funext` and `cases`.

**Costs and risks.**
- **Migration cost:** Very high. Touches every file in `Interaction/`, `ProofSystem/`,
  `Commitments/`, and `ArkLibTest/`.
- **Ergonomic and proof risk:** Severe. Loses dot notation on bundles, loses `rfl` on sum handlers,
  and forces every pure deterministic oracle in ArkLib to carry a `ReaderM` monad wrapper that
  VCVio's own `OracleContext.add` cannot compose across heterogeneous data types.
- **Verdict:** Rejected. `OracleContext` answers a different problem (fixed monad `m`, varying
  specs); ArkLib's bundles vary `Data` alongside `spec`.

### Design C: Two concepts, keeping `OracleInterface.toOC`

Design C deletes `OracleFamily` and its ten bridge combinators, replacing `OracleVerifier.outputs`
with `Path s → OracleBundle`, replacing `oracleMessageFamily` and `sentOracleMessageFamily` with
`oracleMessageBundle` and `sentOracleMessageBundle`, and representing slot-indexed collections as `F
: I → OracleBundle` combined via `OracleBundle.indexed`. It leaves `OracleInterface` untouched
(still wrapping `toOC : OracleContext Query (ReaderM Message)`).

```lean
-- Design C: OracleInterface unchanged (at Type), OracleBundle keeps 4 fields, OracleFamily deleted
class OracleInterface (Message : Type) : Type 1 where
  Query : Type
  toOC : OracleContext.{0, 0, 0} Query (ReaderM Message)

structure OracleBundle : Type 1 where
  Query : Type
  spec : OracleSpec Query
  Data : Type
  answer : Data → QueryImpl spec Id

@[reducible] def OracleBundle.of (Data : Type) (I : OracleInterface Data) : OracleBundle where
  Query := I.Query
  spec := I.toOC.spec
  Data := Data
  answer := I.answer

@[reducible] def OracleBundle.indexed {I : Type} (F : I → OracleBundle) : OracleBundle where
  Query := (i : I) × (F i).Query
  spec := fun q => (F q.1).spec q.2
  Data := ∀ i, (F i).Data
  answer data q := (F q.1).answer (data q.1) q.2
```

**Operations and users.**
- `OracleVerifier` becomes symmetric (`inputs : OracleBundle`, `outputs : Path s → OracleBundle`),
  deleting `{J}`, `{B}`, and `OracleBundle.ofFamily`.
- `oracleMessageBundle` and `sentOracleMessageBundle` build directly with `OracleBundle.empty` and
  `OracleBundle.sum`, deleting `sumFamily`, `singletonFamily`, `sumData`, `sumData_eta`,
  `ofSumFamily`, `toSumFamily`, `familySumAssoc`, `familySumAssocSymm`, and `OracleMap.sum`.
- `OracleMap.embedding` becomes `OracleMap.reindex (F : I → OracleBundle) (rename : J → I)`.
- `Sumcheck` replaces `PolynomialData` and `polynomialFamily` with `OracleBundle.ofInst (R⦃≤ deg⦄[X
  Fin n])`.
- All 35 files constructing `OracleInterface` via `toOC` (`Commitments/`, legacy `OracleReduction/`,
  `ProofSystem/`, tests) need zero edits.

**Costs and risks.**
- **Migration cost:** Medium. Touches the interaction layer (`Interaction/`, `Sumcheck/`,
  `ArkLibTest/Interaction/`), zero edits to `Commitments/` or legacy `OracleReduction/`.
- **Residual debt:** Keeps the `OracleContext` / `ReaderM` indirection that zero other VCVio or
  ArkLib modules use. Every new `OracleInterface` instance still writes `toOC.spec := ...` and
  `toOC.impl q := do return (← read) ...`. Because `OracleInterface.instProd` still depends on
  `QueryImpl.addReaderT`, the equality `OracleBundle.of (α × β) instProd = (OracleBundle.of α
  Oα).sum (OracleBundle.of β Oβ)` fails `rfl`. `RandomQuery.lean:225` and
  `OracleInterface.lean:85,249,268` still leak `O.toOC.spec` into public signatures.

### Design D: Two concepts, flattened `OracleInterface` and four-field `OracleBundle` (Recommended)

Design D makes the same `OracleFamily` deletion and `OracleBundle` unification as Design C, and also
flattens `OracleInterface` by replacing `toOC : OracleContext Query (ReaderM Message)` with `spec :
OracleSpec Query` and `answer : Message → (q : Query) → spec q`. Both `OracleInterface` and
`OracleBundle` (plus `OracleMap`) live in `ArkLib/Relation/`.

```lean
-- Design D: ArkLib/Relation/OracleInterface.lean (post-step-5)
@[ext]
class OracleInterface (Message : Type) : Type 1 where
  Query : Type
  spec : OracleSpec Query
  answer : Message → (q : Query) → spec q

-- ArkLib/Relation/OracleBundle.lean (post-step-5)
structure OracleBundle : Type 1 where
  Query : Type
  spec : OracleSpec Query
  Data : Type
  answer : Data → QueryImpl spec Id
```

Two Lean 4 implementation details discovered during prototyping shape Design D's exact field types:

1. **`OracleInterface.answer` uses `Message → (q : Query) → spec q`, not `Message → QueryImpl spec
   Id`.** Because `Id` is semireducible in Lean 4, typing the class field as `QueryImpl spec Id`
   puts `Id` in the expected return type of instance bodies and causes `Polynomial.eval` to fail
   `Semiring (Id ...)` synthesis (`OracleConsolidation.lean:929-948`). Using `(q : Query) → spec q`
   keeps `Polynomial.eval` elaborating cleanly while still unifying with `QueryImpl spec Id` by
   `rfl` (`OracleConsolidation.lean:62,189`).
2. **`OracleBundle` keeps four flat fields rather than nesting `interface : OracleInterface Data`.**
   A two-field structure `{ Data : Type; interface : OracleInterface Data }` is `rfl`-equivalent to
   the four-field structure, but defining `B.Query := B.interface.Query` and `B.spec :=
   B.interface.spec` routes `B.spec` through the semireducible class projection
   `OracleInterface.Query`. When `simp` unfolds `B.spec` to the primitive projection `In.interface.2
   : OracleSpec In.interface.1`, subsequent `rw` steps fail Lean 4's `.implicit` transparency check
   against `OracleSpec (OracleInterface.Query In.Data)` (`OracleConsolidation.lean:952-1019`).
   Keeping four direct structure fields eliminates that mismatch completely while preserving a
   two-way `rfl` equivalence with `(Data : Type) × OracleInterface Data`
   (`OracleConsolidation.lean:746`).

**Operations and users.**
- Every `OracleInterface` instance simplifies from `toOC.spec := ...; toOC.impl q := do return (←
  read) ...` to `spec := ...; answer m q := ...`.
- `OracleInterface.instProd` uses `QueryImpl.add` directly (`Oα.answerImpl x.1 + Oβ.answerImpl
  x.2`), deleting its dependence on `QueryImpl.addReaderT` and making `OracleBundle.of (α × β)
  instProd = (OracleBundle.of α Oα).sum (OracleBundle.of β Oβ)` hold by `rfl`
  (`OracleConsolidation.lean:799`).
- `OracleInterface.spec` becomes the structure projection itself, cleaning up
  `RandomQuery.lean:225,235` and `OracleInterface.lean:85,249,268`.
- `OracleBundle` and `OracleMap` move to `ArkLib/Relation/OracleBundle.lean` (tree-independent,
  alongside `OracleInterface` and `Relation`), letting `Sumcheck/Spec/PolynomialInterface.lean`
  define `polynomialBundle` without importing `Interaction/OracleVerifier.lean`.
- `OracleVerifier`, `Composition`, `StageChain`, `Oracle/Routing`, `Oracle/Reassociation`,
  `Oracle/SentOracles`, `Oracle/LoggedExecution`, `Oracle/QueriesByMove*`, `Security/*`, and
  `Sumcheck` gain the same simplifications as Design C: symmetric `OracleBundle` inputs and outputs,
  no `{J}` / `{B}`, no `ofFamily` / `ofSumFamily` / `toSumFamily` / `sumData` / `sumData_eta` /
  `familySumAssoc`, and first-class derived `OracleBundle.ofSpec` outputs
  (`OracleConsolidation.lean:1134-1206`).
- `SentOracles.lean` replaces `sentOracleMessageFamily` with `sentOracleMessageBundle` built from
  `OracleBundle.empty` and `OracleBundle.sum`, eliminating `erw [OracleMap.sum_impl_inr]`
  (`SentOracles.lean:258`) in favor of `rfl` on `OracleMap.par`. `SentOracleMessageIndex` and
  `SentOracleMessageIndex.node` can either remain as lightweight node-tracking indices or map
  `(sentOracleMessageBundle h).Query → Node s` directly.

**Costs and risks.**
- **Migration cost:** Medium-high. Adds one extra PR (35 files touching `toOC`) on top of Design C's
  interaction-layer migration.
- **Risks:** Flattening `OracleInterface` touches 2 legacy `OracleReduction/` files
  (`ProtocolSpec/Basic.lean`, `Salt.lean`), 9 `Commitments/` files, and 10 `ProofSystem/` files.
  Each edit is mechanical (replacing `toOC.spec` / `toOC.impl` with `spec` / `answer`, zero semantic
  change), and running PR 1 in isolation isolates any legacy regression from the `OracleFamily`
  removal.

### Comparison of the four designs

| Criterion | Design A (Baseline) | Design B (`OracleContext` + Σ) | Design C (2 concepts, keep `toOC`) | Design D (2 concepts, flattened) |
|---|---|---|---|---|
| Number of oracle-access concepts | 3 (+ `OracleContext`) | 1 (`OracleContext` + Σ) | 2 (+ `OracleContext`) | **2 (no `OracleContext`)** |
| Deletes `OracleFamily` and 10 bridges | No | Yes | Yes | **Yes** |
| Symmetric `OracleVerifier` inputs/outputs | No | Yes | Yes | **Yes** |
| Derived `ofSpec` valid as verifier output | No | Yes | Yes | **Yes** |
| Dot notation on `OracleBundle` | Yes | **No (fails)** | Yes | **Yes** |
| `(R.sum S).answer x = R.answer x.1 + S.answer x.2` by `rfl` | Yes | **No (fails)** | Yes | **Yes** |
| `of (α × β) instProd = (of α).sum (of β)` by `rfl` | No (`addReaderT`) | No | No (`addReaderT`) | **Yes** |
| Clean `answer m q` without `ReaderM`/`toOC` | No | No | No | **Yes** |
| Files touched outside `Interaction/` + `Sumcheck/` | 0 | All (~180) | 0 | 21 (`Relation` 1, legacy 2, `Commitments` 9, other `ProofSystem` 9) |

## 4. Recommendation

Adopt **Design D**, between universe migration steps 4 and 5 (section 5). Design D reduces the
interaction layer to the two concepts the codebase needs (`OracleInterface` for typeclass-indexed
carriers and `OracleBundle` for first-class explicit oracle specifications with backing data). It
deletes `OracleFamily`, eliminates all ten family-to-bundle bridges, removes the unused
`OracleContext` / `ReaderM` indirection, and satisfies the elaboration, transparency, and
executability constraints checked in
[`prototypes/OracleConsolidation.lean`](prototypes/OracleConsolidation.lean).

### Reasons for Design D

1. **Two concepts match the two distinct jobs.** Typeclass-driven code (`OracleReduction/`,
   `Commitments/`, `[v]ₒ`, `OracleBundle.ofInst`) needs `class OracleInterface (Message : Type) :
   Type 1` keyed on `Message`. Data-driven protocol boundaries (`OracleVerifier`, `StageChain`,
   `OracleMap`, `pathBundle`, `ofSpec`, `tensor`, `sum`) need a bundled value `OracleBundle : Type
   1` that does not rely on typeclass uniqueness (remembering that KZG and Spartan already define 14
   `local instance` overrides and `ArkLibTest/Interaction/` passes 15+ explicit `def` interfaces).
   `OracleFamily` occupies an awkward middle ground: it duplicates `I → OracleBundle`, cannot
   express `ofSpec`, `tensor`, or unindexed single oracles, and forces ten conversion bridges
   between `sumFamily` and `OracleBundle.sum`.
2. **Symmetric `OracleVerifier` unlocks derived outputs and simplifies composition.** Typing
   `outputs : Path s → OracleBundle` removes `{J}` and `{B}` from `OracleVerifier`, `Composition`,
   `StageChain`, `LoggedExecution`, `QueriesByMove*`, `Reassociation`, `Routing`, and all 10
   `Security/` files. It eliminates `OracleBundle.ofFamily` coercions at every stage seam and lets
   behavior-only outputs (`OracleBundle.ofSpec`) compose across stages
   (`OracleConsolidation.lean:1134-1206`).
3. **Flattening `OracleInterface` finishes the cleanup at low marginal cost.** Only 35 files across
   the entire repository mention `toOC` after step 4 removes `StageChain.lean`'s `liftQueries`, and
   zero files use positional `OracleInterface.mk`. Removing `toOC` closes both long-standing TODOs
   in `ArkLib/Relation/OracleInterface.lean:48-54` (dependent responses already exist via
   `OracleSpec`, and `OracleContext` proved unsuitable for heterogeneous pure data), drops
   `QueryImpl.addReaderT` from `OracleInterface.lean`, and lets `OracleInterface` and `OracleBundle`
   share the exact same pure `(Query, spec, answer)` shape.
4. **Moving `OracleBundle` and `OracleMap` to `ArkLib/Relation/` fixes the layer inversion.**
   Neither `OracleBundle` nor `OracleMap` depends on protocol trees, views, or execution. Placing
   them in `ArkLib/Relation/OracleBundle.lean` lets specification modules like
   `Sumcheck/Spec/PolynomialInterface.lean` export an `OracleBundle` directly without importing
   `Interaction/OracleVerifier.lean`.

### What Design D gives up

- **Upfront edit surface across legacy and commitment files.** Compared to Design C, flattening
  `OracleInterface` adds 21 non-interaction files (`OracleInterface.lean`, 2 legacy
  `OracleReduction/` files, 9 `Commitments/` files, and 9 non-Sumcheck `ProofSystem/` files) plus 13
  test files. Each edit is a mechanical 2-line replacement of `toOC.spec` / `toOC.impl` with `spec`
  / `answer`.
- **Implicit `OracleFamily` coercion and named slot indexing on `OracleMessage`.** Clients that
  inspect slot-indexed families write `F : I → OracleBundle` with `OracleBundle.indexed F` and
  `OracleMap.reindex F rename` instead of a dedicated `OracleFamily` type. Similarly,
  `oracleMessageBundle` produces nested binary sum queries (`Q₁ ⊕ (Q₂ ⊕ Empty)`) and tuple data (`X₁
  × (X₂ × Unit)`) rather than `(i : PUnit ⊕ ...) × Q i`. This removes `PUnit` noise from every
  oracle-message query and replaces 25-line `sumData_eta` proofs with one-line `Prod.ext` proofs
  (`OracleConsolidation.lean:554-582`), at the cost of updating concrete query patterns in
  `Sumcheck/Execution.lean`, `Legacy/OracleReduction.lean`, and interaction tests.
- **No global `OracleInterface B.Data` instance.** Users passing a bundle's data into a
  typeclass-driven legacy helper must supply `B.toInterface` explicitly. Registering `instance (B :
  OracleBundle) : OracleInterface B.Data` would trigger VCVio#772-style runaway synthesis matching
  `?B.Data` on every `OracleInterface _` goal
  (`.lake/packages/VCVio/VCVio/OracleComp/OracleSpec.lean:71-82`).

### History of the definitions

The current three types are the residue of four reworks, each of which added a layer around the
previous representation without removing it.

| When | Change | Reason |
|---|---|---|
| Dec 2024 to Feb 2026 | `class OracleInterface X` with `Query`, `Response` and `answer : X → Query → Response` | The original form, with one response type for all queries |
| Feb 2026 (#303, with VCVio #90) | `toOC : OracleContext Query (ReaderM X)` | VCVio made oracle specifications dependent, so the response type depends on the query. The rework adopted that through VCVio's new `OracleContext`, which pairs a specification with an implementation in a monad `m` |
| Aug to Sep 2026 (#811, #869) | `OracleFamily`, an indexed family of interfaces passed as data | The interaction layer needed explicit interfaces, not instances, for verifier outputs |
| Nov 2026 (#1475, #1476) | `OracleBundle` with `answer : Data → QueryImpl spec Id` | Partly to avoid `ReaderM`, which tied the data and response universes together ([implementation note 18](../interaction-rebuild/IMPLEMENTATION-NOTES.md#18-run-outputs-are-tied-to-the-monad-universe)) |

The gain of the February rework was dependent responses. The `OracleContext` packaging came with
it, and the interaction layer later built a parallel type partly to avoid that packaging.

**Why `OracleContext` was the wrong common structure.** `OracleContext ι m` abstracts over the
monad and fixes it across everything it combines: `OracleContext.add` adds two contexts only when
they share `m`. That fits its purpose, a set of ambient oracles implemented in one monad. Oracle
data is the opposite case. The monad never varies, because every answer is a pure read of the
data, so `ReaderM X` is the reader over `Id` in every use. The data type varies in every
combination, because one summand reads a polynomial and the other a codeword. Encoding the data
in the monad puts the varying part where the abstraction holds things fixed, so summing two oracles
over different data does not typecheck with `OracleContext.add`, and the workaround through
`QueryImpl.addReaderT` loses `rfl` (section 2).

The structure the three types share is an observation of a type through a family of queries:

```lean
spec   : OracleSpec Query                -- the response type of each query
answer : X → (q : Query) → spec q        -- what a value of X answers
```

An interface is this structure found by instance search, a bundle is this structure packaged with
its data type, and a family is this structure indexed by slots. Design D states it once, and the
prototype proves the packagings equivalent by `rfl` (section 2).

**Where proof engineering decides.** Two choices in Design D depart from the cleanest statement:
the bundle keeps four flat fields instead of `{Data; interface}`, and the interface's `answer`
avoids `QueryImpl spec Id` (section 3, Part 3 of the prototype). Both choose a representation and
leave the concept unchanged. The rule is to state the concept once as a theorem (the `rfl`
equivalences) and let elaboration and proof evidence choose the fields.

**A test for future reworks.** Abstract over what varies across the uses, and check that the
operations used most compute by `rfl` in the abstraction. `OracleContext` failed both tests for
oracle data. An `m` parameter on `answer` becomes worth its cost if ArkLib needs oracle data whose
answers are effectful, such as stateful or randomized oracles stored as data. Ambient random
oracles do not count: they live in the verifier's `ambient` specification and go through
`simulateQ`.

### Effectful answers

Design D keeps the answer of an interface pure. Effects belong in the handler a verifier runs its
queries against and in oracle maps, not in the interface. This was considered for compiling oracle
reductions into arguments (BCS and hash-based polynomial commitments), where answers come from
Merkle openings checked through a random oracle.

**Where the effect goes.** A passive verifier's decision is an `OracleComp` over the path's
oracles, and the ideal run answers it with pure reads of the data. After BCS, the verifier holds
only the roots and a final prover message with the openings, and it runs the same decision against
a checking handler:

```lean
-- sketch: looks up the answer in the openings and checks its path against the root
def merkleHandler (root : Digest) (openings : Openings) :
    QueryImpl (vectorSpec n α) (OptionT (OracleComp ro)) := fun i => do
  let (v, path) ← OptionT.mk (pure (openings.lookup i))
  guard (← Merkle.verify root i v path)
  pure v

compiledDecide := simulateQ (QueryImpl.id ambient + merkleHandler roots openings) (decide …)
```

The arkworks BCS crate has the same structure: its verifier's query phase is written once against
a round-oracle trait, with one implementation that records queries and one that answers from the
proof. The other two parts of BCS already have homes:

- Each oracle slot needs a commitment for its interface. `Commitment.Scheme`
  (`ArkLib/Commitments/Functional/Basic.lean`) commits to `Data` with an `OracleInterface Data`
  and opens a claim `answer d q = y` by an interactive proof. A Merkle tree is the instance for the
  point-query vector interface with a one-message opening, and VCVio proves Merkle extractability
  in the random-oracle model (`VCVio/CryptoFoundations/MerkleTree/`).
- The protocol is rewritten: each `oracle X I` node becomes a message carrying the root, and one
  final prover message carries the openings for the queries the decision makes on that path. The
  passive-verifier premise P1 is the shape Chiesa and Yogev's construction assumes (public coin,
  queries after the interaction). The legacy stub `ArkLib/OracleReduction/BCS/Basic.lean` and
  [design 04](../04-oracle-elimination-compiler.md) describe the same pipeline.

**Polynomial and vector oracles.** A codeword entry is an evaluation of the polynomial, so a
vector oracle is simulated exactly from a polynomial oracle by an `OracleMap`, whose `impl` is
already monadic in the source oracle. The reverse is not a map: a cheating prover's vector can be
far from every codeword, so an evaluation claim needs a proximity proof (FRI, STIR, WHIR) with a
soundness error. That is an oracle reduction appended to the protocol. A hash-based polynomial
commitment is therefore an encoding map, a proximity reduction, and BCS on the vector oracle.

**Why the interface stays pure.**

1. Soundness of an oracle reduction assumes that a repeated query gets the same answer. Under raw
   `OracleComp` semantics, a random-oracle query answers each call independently, and only a
   shared cache restores agreement (VCVio's test `VCVioTest/MerkleTreeExtractability.lean`,
   `repeatedQuery`). `OracleMap.law`, agreement, `distanceLE` and the knowledge-state functions
   all read answers as a function of the data and would need restating relative to a cache.
2. After compilation a possibly cheating prover supplies the answers. A monadic answer can
   describe an honest opening but not an adversary. The security content (binding, straight-line
   extraction from the query trace, state-restoration soundness in
   `ArkLib/Interaction/Security/StateRestoration.lean`) is a theorem relating the compiled run to
   the ideal run, not a field type.
3. By the test above, the handler varies across uses (ideal read, recording, checked opening) and
   the data's semantics does not. `decide` is already generic in its handler through `simulateQ`,
   so no interface change is needed, and the existing instances keep their pure answers.

An interface with a monadic answer is the same as a pure bundle followed by an effectful map out of
it (`OracleMap.withAmbient` adds the random oracle), so keeping interfaces pure loses nothing.

### Answer to record D1 open point and alignment with record D6

**Record D1 open point (`docs/design/interaction-rebuild/D1-signatures-and-shape.md:110-113`).**
Keep the oracle interface on `OraclePos.oracle (X : Type) (interface : OracleInterface X)` and leave
non-ownership metadata `Γ` empty for ArkLib signatures. Moving interfaces into `Γ` would reintroduce
the exact side-tree synchronization burden that record D2 eliminated when it removed
`RoleDecoration` (`docs/design/interaction-rebuild/D2-ownership-and-universes.md:67-77`): every
protocol append and path operation would have to thread and split a second tree-shaped decoration
alongside `s`. The only technical motive for separating `interface` from `OraclePos` under the old
universe ledger was avoiding an extra query universe parameter `q` on `OraclePos : Type (max (u + 1)
(q + 1))`. After universe migration step 5, `X : Type` and `OracleInterface X : Type 1` both yield
`OraclePos : Type 1` with zero universe parameters (`OracleConsolidation.lean:467`), removing that
motive entirely. Whether `OraclePos.oracle` keeps two arguments `(X : Type) (interface :
OracleInterface X)` or takes one `(B : OracleBundle)` is an independent ergonomic choice recorded in
Section 6; either keeps `Γ` empty.

**Record D6 alignment (`docs/design/interaction-rebuild/D6-oracle-access.md`).** Design D preserves
every semantic property of D6. Passive verifiers still query only after the run, oracle messages on
a completed path still depend only on the public shape path `p`, `OracleMap` keeps `(f, impl, law)`
without ambient queries, and sequential composition routes suffix queries through `prefixRoute` and
`suffixRoute`. Replacing `oracleMessageFamily` and `OracleVerifier.outputs` with `OracleBundle`
removes the legacy family representation leak from D6's core equations
(`OracleConsolidation.lean:503-726`).

### Instance search, reducibility, transparency, and compiler erasure

Design D preserves every elaboration and code-generation invariant required by ArkLib and verifies
each in Part 3 of [`prototypes/OracleConsolidation.lean`](prototypes/OracleConsolidation.lean):

1. **`OracleSpec` remains `@[implicit_reducible]`**
   (`.lake/packages/VCVio/VCVio/OracleComp/OracleSpec.lean:44`), and `OracleBundle.Query`, `spec`,
   `Data`, `answer` are direct structure fields on a four-field structure, avoiding the `.implicit`
   transparency mismatch exhibited by a two-field nested bundle
   (`OracleConsolidation.lean:952-1019`).
2. **`OracleInterface.answer` avoids `Id` in its field type**, preventing `Semiring (Id ...)`
   synthesis failure in polynomial instances (`OracleConsolidation.lean:929-948`).
3. **`OracleInterface.toOracleSpec` (`[v]ₒ`) stays semireducible**, preserving `[v]ₒ` as a stable
   head for `HasQuery` / `MonadLiftT` matching and keeping `simulateQ_simOracle2_liftM_query_snd`
   provable by `rfl` (`OracleConsolidation.lean:1035`) and `OracleReduction/Basic.lean:515`'s `erw`
   pattern working identically.
4. **Class projections (`OracleInterface.Query`) remain non-reducible in `synthInstance`** on both
   current and consolidated `OracleInterface` (`OracleConsolidation.lean:1027`).
   `OracleInterface.lean:311-313`'s explicit `Fintype` instance on `Query (R⦃≤ d⦄[X σ])` therefore
   stays needed and intact. Concrete flat bundles such as `OracleBundle.ofSpec (ZMod 7 →ₒ ZMod 7)`
   synthesize `Fintype` and `DecidableEq` directly (`OracleConsolidation.lean:1029-1030`).
5. **Core bundle combinators stay `@[reducible]`** (`of`, `ofInst`, `empty`, `sum`, `tensor`,
   `ofSpec`, `indexed`, `ofIndexed`) and `oracleMessageBundle` stays `@[implicit_reducible]`,
   matching today's unfolding discipline for `QueryImpl.add`, `simulateQ`, and `pathBundle`.
6. **Compiler erasure via `@[macro_inline]` stays intact.** `OracleMap.fst`
   (`OracleConsolidation.lean:274`) and `pathLift` (`OracleConsolidation.lean:609`) remain
   `@[macro_inline]`. Defining `computableMvPolyVerifier` against the `noncomputable` bundle
   `mathMvPolyBundle` compiles without `noncomputable` (`OracleConsolidation.lean:1049-1071`),
   matching `Sumcheck/Execution.lean:402-417`.

### Boundary with upstream VCVio

- **Keep in VCVio:** `OracleSpec`, `PFunctor` bridges (`toPFunctor`, `ofPFunctor`), `QueryImpl`,
  `QueryImpl.add`, `QueryImpl.compose`, `QueryImpl.comapLens`, and `OracleComp.mapLens`.
- **Propose upstream to VCVio:**
  1. A `Type`-monomorphic alias for `[]ₒ` (`emptySpec.{0, 0}`), already noted in
     `docs/design/interaction-rebuild/D2-ownership-and-universes.md:168`.
  2. Documenting or deprecating `OracleContext`
     (`.lake/packages/VCVio/VCVio/OracleComp/OracleContext.lean:25`). VCVio has zero callers of
     `OracleContext` itself, and once ArkLib PR 1 lands, ArkLib will have zero callers as well. If
     VCVio keeps `OracleContext` for fixed-monad ambient contexts, its docstring should clarify that
     heterogeneous pure data-backed oracles should not use `OracleContext Query (ReaderM Data)`.
- **Keep in ArkLib:** `OracleInterface`, `OracleBundle`, `OracleMap`, and protocol-path bundle
  operations. These encode ArkLib's representability split between concrete backing data `Data` and
  pure behavior `QueryImpl spec Id`, which is specific to interactive oracle reductions and witness
  relations.
- **What ArkLib does until upstream VCVio PRs land:** Define the `Type` alias for `[]ₒ` locally in
  `ArkLib/Relation/` (already planned for universe migration step 5) and drop the
  `VCVio.OracleComp.OracleContext` and `VCVio.OracleComp.SimSemantics.ReaderT.Basic` imports from
  `ArkLib/Relation/OracleInterface.lean` in PR 1. Design D has zero blocking upstream VCVio
  dependencies.

### Cost-benefit verdict

Consolidation under Design D is worth its cost. The interaction layer is still young: only one proof
system (`Sumcheck`) has been ported to `Interaction/`, while `FRI`, `BatchedFri`, `Binius`, `Plonk`,
`Spartan`, and `RingSwitching` have not yet been ported. Deleting `OracleFamily` and flattening
`OracleInterface` around universe migration step 5 touches about 65 files once, in five PRs, and
prevents every upcoming proof-system port from authoring dummy `Unit → Type` families, `toOC`
boilerplate, and asymmetric `OracleVerifier` signatures.

## 5. Migration plan

This order was settled on 2026-11-25. Universe step 4 runs first, narrowed to bundle universes and
the adapters. Consolidation PRs 2 to 5 follow and delete `OracleFamily`. Universe step 5 then fixes
the vocabulary universes and includes PR 1, which flattens `OracleInterface`. Step 6 runs last
([record D2](../interaction-rebuild/D2-ownership-and-universes.md#migration)).

### Placement relative to universe migration steps 4, 5, and 6

- **Step 4, narrowed:** remove the index, data and query universes of `OracleBundle` and delete the
  universe adapters (`liftQueries`, `lowerQueries`, `liftResponse`, `liftInputs`, `liftOutputs`,
  `lowerOutputs`). `OracleFamily` stays pinned at `0`, as most of its uses already are after step 3.
  Fixing its universes would be wasted, because PR 5 deletes it.
- **PRs 2 to 5, between steps 4 and 5:** after step 4, `OracleBundle` has no universe parameters, so
  the new combinators need only one pin, `OracleInterface.{0, 0}` in `OracleBundle.of`. Until PR 1
  lands, `OracleBundle.of` reads the current interface through `I.toOC.spec` and `fun m q =>
  (I.toOC.impl q).run m`.
- **Step 5 with PR 1 folded in:** step 5 and PR 1 both rewrite the definition of `OracleInterface`
  and visit the same 35 files, so one PR edits them once. By then `OracleFamily` is gone, so step 5
  does not touch it.
- **Step 6 last:** it replaces `UniverseCanary.lean`, drops the remaining test pins and updates the
  port tables once, for the final API.

### Compiling PR sequence

Each PR below compiles on its own with `./scripts/validate.sh`. The PRs keep their numbers; they
land in the order 2, 3, 4, 5, then 1 as part of step 5.

1. **PR 1: Flatten `OracleInterface` and remove `OracleContext` / `ReaderM` indirection.**
   - **Changes:** Replace `toOC : OracleContext Query (ReaderM Message)` in
     `ArkLib/Relation/OracleInterface.lean` with `spec : OracleSpec Query` and `answer : Message →
     (q : Query) → spec q`. Drop imports of `VCVio.OracleComp.OracleContext` and
     `SimSemantics.ReaderT.Basic`. Update `instProd` to use `QueryImpl.add`, remove dead
     `OracleInterface.toOracleImpl` and `OracleInterface.spec` (now a struct field), and fix or
     remove the duplicate `instTensorForall` (`OracleInterface.lean:176-180`). Mechanically update
     all remaining `toOC` sites.
   - **Files touched (35 files total after step 4 removes `StageChain.lean`'s `liftQueries`):**
     - `ArkLib/Relation/OracleInterface.lean`
     - `ArkLib/OracleReduction/ProtocolSpec/Basic.lean`, `ArkLib/OracleReduction/Salt.lean`
     - `ArkLib/Commitments/Functional/Hachi/Commitment.lean`, `ArkLib/Commitments/Functional/KZG/`
       (8 files: `Basic.lean`, `Binding.lean`, `Correctness.lean`, `FunctionBinding/Basic.lean`,
       `DegreeConflict.lean`, `EvaluationBindingConflict.lean`, `Support.lean`, `TauInQueries.lean`)
     - `ArkLib/ProofSystem/` (10 files: `Binius/BinaryBasefold/Spec.lean`,
       `Component/GeneratorBatch.lean`, `Component/QuotientZeroTest.lean`,
       `Component/RandomQuery.lean`, `Fri/Spec/SingleRound.lean`, `Spartan/Terminal.lean`,
       `Spartan/WitnessAttachment.lean`, `Sumcheck/Behavior.lean`, `Sumcheck/Computable.lean`,
       `Sumcheck/MessageTree.lean`)
     - `ArkLibTest/Interaction/` (13 test files constructing test `OracleInterface`s)
   - **Why it compiles standalone:** `OracleInterface.Query`, `Response`, `answer`, `toOracleSpec`,
     `OracleFamily`, and `OracleBundle` keep identical external signatures.

2. **PR 2: Relocate `OracleBundle` and `OracleMap` to `ArkLib/Relation/OracleBundle.lean` and add
   consolidated constructors.**
   - **Changes:** Move `OracleBundle`, `OracleBundle.sum`, `OracleBundle.ofSpec`,
     `OracleBundle.tensor`, `OracleBundle.Lens`, `OracleBundle.Equiv`, and `OracleMap` (bundle-level
     operations) to `ArkLib/Relation/OracleBundle.lean` (renaming `OracleBundle.Index` to `Query` if
     approved, or keeping `Index`). Add `OracleBundle.Behavior`, `toInterface`, `of`, `ofInst`,
     `empty`, `indexed`, `ofIndexed`, `OracleMap.emptyLeft`, `OracleMap.reindex`,
     `OracleBundle.Lens.toOracleMap`, and `OracleBundle.indexedSumEquiv`. Keep `OracleFamily`,
     `OracleBundle.ofFamily`, and `CoeOut` intact as temporary bridges. Update
     `ArkLib/Interaction/OracleVerifier.lean` and `ArkLib/Interaction/Oracle/BundleOps.lean` to
     import `ArkLib.Relation.OracleBundle` (retiring `BundleOps.lean` or keeping it as a thin
     re-export until PR 5).
   - **Files touched (~8 files):** `ArkLib/Relation/OracleBundle.lean` (new),
     `ArkLib/Relation/Basic.lean`, `ArkLib/Interaction/OracleVerifier.lean`,
     `ArkLib/Interaction/Oracle/BundleOps.lean`, `ArkLib/Interaction/Oracle/SentOracles.lean`, plus
     3 test files if `Index` is renamed to `Query` (`BundleFamilies.lean`, `OracleMaps.lean`,
     `RoutedAccess.lean`).
   - **Why it compiles standalone:** Additive relocation; every existing `OracleFamily`,
     `OracleBundle`, and `OracleVerifier` caller continues to compile unchanged.

3. **PR 3: Make `OracleVerifier`, `StageChain`, `Security/`, and `Sumcheck` symmetric in
   `OracleBundle`.**
   - **Changes:** Change `OracleVerifier.outputs` (`OracleVerifier.lean:503`) from `(p : Path s) →
     OracleFamily (J p) (B p)` to `Path s → OracleBundle`, dropping `{J}` and `{B}`. Update
     `OracleVerifier.Output` to `T p × (outputs p).Data`, update `pathLift`
     (`OracleVerifier.lean:520`) to take `inputs : OracleBundle` (keeping `@[macro_inline]`), and
     update `Composition.lean` (`splitOutputs`, `OutputCompatibility`, `append`), `StageChain.lean`
     (`comapInputs`, `mapOutputs`, `StageChain`), `Oracle/Routing.lean`,
     `Oracle/Reassociation.lean`, `Oracle/LoggedExecution.lean`, `Oracle/QueriesByMove.lean`,
     `Oracle/QueriesByMoveLaws.lean`, all 10 `Interaction/Security/` files,
     `Interaction/Legacy/OracleReduction.lean` / `OracleExecution.lean` / `OracleKnowledge.lean`,
     `Sumcheck/`, and tests. Existing `OracleFamily` callers temporarily pass `(outputs p :
     OracleBundle)` via the still-present `CoeOut`.
   - **Files touched (~52 files):** 3 core `Interaction/` files (`OracleVerifier`, `Composition`,
     `StageChain`), 5 `Interaction/Oracle/` files, 10 `Interaction/Security/` files, 3
     `Interaction/Legacy/` files, 11 `Sumcheck/` files, and ~20 `ArkLibTest/` files.
   - **Why it compiles standalone:** `OracleFamily`, `OracleBundle.ofFamily`, and
     `oracleMessageFamily` remain in place during this PR, isolating the `OracleVerifier` signature
     change from path-message representation changes.

4. **PR 4: Replace `oracleMessageFamily` and `sentOracleMessageFamily` with `oracleMessageBundle`
   and `sentOracleMessageBundle`, and delete family-sum bridges.**
   - **First:** prototype `SentOracles.queryNode` on the binary-sum layout and check the
     `PartialTranscripts`, `RoutedAccess` and `LoggedExecution` tests against it. The prototype file
     does not cover it yet.
   - **Changes:** Replace `oracleMessageFamily`, `oracleMessages`, `oracleMessageImpl`,
     `oracleMessageFamily_append`, `oracleMessageFamily_split`, and `splitOracleMessages` with the
     direct `OracleBundle.empty` / `OracleBundle.sum` versions (`OracleConsolidation.lean:503-601`).
     Update `SentOracles.lean` to use `sentOracleMessageBundle` and `OracleMap.par`. Simplify
     `splitPathBundle` (`Composition.lean:547`) by dropping `ofSumFamily`. Update
     `Oracle/Routing.lean`, `Oracle/Reassociation.lean`, `Interaction/Legacy/OracleReduction.lean` &
     `OracleExecution.lean`, `Sumcheck/` (`Composition`, `Execution`, `Tree`, `Indexed`,
     `Interpreted`, `InterpretedPath`, `LegacyEquivalence`, `SingleRound`, `Fold`), and interaction
     tests. Delete `sumFamily`, `singletonFamily`, `sumData`, `sumData_eta`, `ofSumFamily`,
     `toSumFamily`, `familySumAssoc`, `familySumAssocSymm`, and `OracleMap.sum`.
   - **Files touched (~35 files):** `OracleVerifier.lean`, `Composition.lean`, `StageChain.lean`,
     `Oracle/Routing.lean`, `Oracle/Reassociation.lean`, `Oracle/SentOracles.lean`,
     `Interaction/Legacy/OracleReduction.lean`, `OracleExecution.lean`, `OracleAppend.lean`, 9
     `Sumcheck/` files, and ~17 `ArkLibTest/` files.
   - **Why it compiles standalone:** PR 3 already converts every `OracleVerifier` boundary to
     `OracleBundle`. Switching `pathBundle` to `inputs.sum (oracleMessageBundle s p)` updates only
     path-message indexing and deletes the now-unused sum-family bridges.

5. **PR 5: Delete `OracleFamily`, `OracleBundle.ofFamily`, and `OracleMap.embedding`.**
   - **Changes:** Replace remaining direct `OracleFamily` definitions (`Sumcheck/Types.lean:35`,
     `Sumcheck/Spec/PolynomialInterface.lean:31`, `Sumcheck/Computable.lean`,
     `Sumcheck/Behavior.lean`, `Sumcheck/Projection.lean`, `Sumcheck/Impl/Projection.lean`,
     `Interaction/Legacy/OracleReduction.lean`'s `family`, and remaining tests such as
     `BundleFamilies.lean`, `AnswerOnlyRelations.lean`, `DependentRouting.lean`,
     `DerivedOracles.lean`, `OracleMaps.lean`) with `OracleBundle.of` / `ofInst` / `indexed` /
     `ofIndexed`, `OracleBundle.Behavior`, and `OracleMap.reindex`. Delete `OracleFamily` from
     `ArkLib/Relation/Basic.lean`, delete `OracleBundle.ofFamily` and its `CoeOut` instance, and
     delete `OracleMap.embedding`.
   - **Files touched (~25 files):** `ArkLib/Relation/Basic.lean`,
     `ArkLib/Relation/OracleBundle.lean`, `Interaction/Legacy/OracleReduction.lean`, 6 `Sumcheck/`
     files, and ~16 `ArkLibTest/` files.
   - **Why it compiles standalone:** Zero remaining callers reference `OracleFamily` or
     `OracleBundle.ofFamily`. Universe migration step 6 then runs cleanly on the consolidated API.

## 6. Open questions for the maintainer

1. **Arguments of `OraclePos.oracle`.** Once `OracleBundle` moves to
   `ArkLib/Relation/OracleBundle.lean` (PR 2), `OraclePos.oracle` can either keep two arguments
   `oracle (X : Type) (interface : OracleInterface X)` (matching `message (X : Type)` and `challenge
   (C : Type)`, with zero edits to 15 files matching on `OraclePos`) or take one argument `oracle (B
   : OracleBundle)` (eliminating `OracleBundle.of X I` inside `oracleMessageBundle`). Design D
   defaults to keeping `(X : Type) (interface : OracleInterface X)` unless the maintainer prefers
   `oracle (B : OracleBundle)`.
2. **Fate of `OracleBundle.Lens` and `OracleBundle.Equiv`.** After universe migration step 4 deletes
   `OracleBundle.liftResponse`, `OracleBundle.Lens` and `OracleBundle.Equiv` in
   `ArkLib/Interaction/Oracle/BundleOps.lean` have zero production callers (only
   `ArkLibTest/Interaction/Oracle/OracleMaps.lean` tests them). One-way routing is covered by
   `OracleMap` and VCVio's `QueryImpl.comapLens`, while `OracleBundle.Equiv` remains useful for
   symmetric structural isomorphisms like `indexedSumEquiv`. Decide whether to keep `Lens` and
   `Equiv` in `ArkLib/Relation/OracleBundle.lean` or retire them after step 4.
3. **Merging PR 1 into universe migration step 5.** Resolved on 2026-11-25: PR 1 is part of step 5
   (section 5).
4. **Renaming `OracleBundle.Index` to `OracleBundle.Query`.** Calling the field `Query` aligns
   `OracleBundle.Query` with `OracleInterface.Query` and removes the historical collision with
   `OracleFamily.Index` (slot index vs query index), touching 6 files (`OracleVerifier.lean`,
   `BundleOps.lean`, `SentOracles.lean`, `BundleFamilies.lean`, `OracleMaps.lean`,
   `RoutedAccess.lean`). Decide whether to rename or keep `Index`.
5. **Cleanup of `OracleInterface.instTensorForall`.** `ArkLib/Relation/OracleInterface.lean:176-180`
   duplicates `instProdForall` (`192-196`) verbatim and has zero callers. Decide whether to delete
   `instTensorForall` in PR 1 or repair it to use `(i : ι) → (O i).Query` and `∀ i, (O i).Response
   (q i)`.
6. **Upstream VCVio proposals.** Decide whether to open upstream VCVio PRs for (a) a `Type`-level
   `[]ₒ` alias and (b) deprecating or clarifying the docstring of `OracleContext` once ArkLib PR 1
   removes its last caller.
