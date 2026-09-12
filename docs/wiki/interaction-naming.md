# Typed interaction names

The typed interaction API names describe the mathematical data and its interpretation. The source
layer lives in [`Source.lean`](../../ArkLib/Interaction/Oracle/Source.lean); named contexts and their
models live in [`Resource.lean`](../../ArkLib/Interaction/Oracle/Resource.lean).

## Sources and their morphisms

`SourceCtx Query Env` is a reader-valued `OracleContext`. It specifies a response type for each
query and interprets each environment as a deterministic handler. Fixing an environment forgets
its representation and exposes its answers. Different environments may yield the same handler.

A `SourceHom S T` sends queries forward, pulls responses back through a polynomial lens, and pulls
environments back through `pullEnv : T.Env → S.Env` (schematically; the carriers are parameters).
Its commuting equation says that routing a query gives the same answer as interpreting it in the
pulled environment. `SourceEquiv` additionally provides inverse morphisms, including inverse
environment maps; equality of observable answers alone does not establish it.

| Operation | Queries | Responses | Environments |
| --- | --- | --- | --- |
| `S.sum T` | Either an `S` query or a `T` query | Response of the selected source | A pair |
| `S.tensor T` | A pair of queries | A pair of responses | A pair |
| `SourceCtx.sigma S` | An index and a query of that component | Response of that component | A dependent family |

`sum` is signature addition. `tensor` uses `PFunctor.tensor`: the polynomial tensor, whose response
directions form a product. It differs from the categorical product of polynomials, whose response
directions form a sum. `sigma` is indexed signature addition. These operations describe query
interfaces, without imposing disjointness of oracle names or a scheduling interpretation.

`SourceHom.sigmaMap` maps indexed sources componentwise; `sigmaInj` includes one component.
`SourceHom.congrFamily` retains its name because it transports within a family along an equality
of indices. For morphisms, `g.comp f` means first `f`, then `g`.

## Names, models, and views

`OracleModel` interprets a family indexed by stable names. It assigns source interpretations,
admissible `Realization` types, owner and origin metadata, and a language of `PropertySymbol`s.
`satisfies` interprets each property symbol as a predicate on realizations. `promised` selects the
symbols whose predicates hold for every admissible realization, as certified by
`satisfies_promises`. A `Guarantee` is a selected symbol together with evidence that it is promised.
These are ideal promises; cryptographic enforcement remains a separate compilation obligation.

`NamedContext` represents a subcontext through `name : Index ↪ Id`. It names distinct entries;
it neither stores their realizations nor allocates them. A `NamedContext.Inclusion S T` preserves
each name. Injectivity of the naming maps makes such an inclusion unique when it exists, even
though the two contexts may use different index types.

`NamedContext.View S` is an arbitrary indexed family of references into `S`, given by `toIndex`.
A view may omit entries or reference an entry repeatedly. Its interpreted source uses the original
context's realization family, so aliases observe the same realization. `share` combines views of
one context. `disjointUnion` combines contexts, or views over contexts, only with evidence that the
underlying names do not overlap. `disjointUnionSourceEquiv` relates this construction to `sum` of
the interpreted sources.

## Virtual interfaces and substitution

`OracleFamily` is an indexed family of realization types with explicit `interface` data. Its
`behaviorOfRealizations` interprets those values as answers; its `asBehaviorSource` instead admits
all deterministic handlers, including ones no realization represents. Neither injectivity nor
surjectivity of the interpretation is assumed. Reindexing a family copies interface types and
allows independently supplied values at repeated indices. It does not create a shared-realization
view.

`VirtualOracle srcSpec Out` supplies a program over `srcSpec` for every output query. Its `eval`
returns output behavior, without constructing output realizations. `substSource` replaces each
source query with a program over another signature. `mapSource` specializes this to a coherent
`SourceHom`; `sumWeaken` includes the source signature in a larger sum. `a.subst b` substitutes
`a`'s programs into the downstream oracle `b`; `substWithSuffix` also retains a separate suffix
signature for downstream queries. These operations use VCVio's existing interpreter.

`SemEquiv` compares answers under every deterministic source handler. It does not assert equal
query traces, equal cost, or equivalence under stateful handlers. In particular, an unused repeated
query can change a trace without changing deterministic answers. This semantic relation is the
one used for the exported identity and associativity laws.

## Claims and relations

`ClaimWith` pairs a public statement with an explicit representation of its oracle component.
`OpenClaim` carries query programs awaiting a handler; `ClosedClaim` carries observable behavior;
`ConcreteClaim` carries realizations interpreted by the declared interfaces. Closing an open claim
uses `closeWith`; interpreting a concrete claim uses `toClosed`. Neither operation checks relation
membership or proves that its inputs came from a protocol execution.

`ConcreteClaim.closesTo` says exactly that `toClosed` equals the specified closed claim. Hidden
representation tags and different programs can disappear under interpretation. In particular,
concrete realizations need not be honest, and an open claim need not be accepted.

`ClaimFamily` is a dependent family of claim types over a public context. `closedOracle` specializes
it to closed oracle claims. `Problem` adds claim-dependent witnesses, admissibility, and a relation
that entails admissibility. `language` existentially quantifies the witness. `Relation` removes the
admissibility restriction; it does not assert that every claim has a witness.

## Execution data and closing

`CoreRun` stores a concrete path, initial behavior, private output, and the terminal open claim.
`executeCore` packages these from the existing executor. The public carrier also admits algebraic
normal forms; an executor equation, interpreted support, or a runtime generation witness supplies
provenance when a theorem needs it. Constructor visibility is an API discipline, not that witness.

`TerminalClaim` is the optional-claim convention at a completed branch: `some` carries a claim and
`none` denotes verifier rejection. It does not represent failure of the ambient computation to
return. `CoreRun.closed` interprets only with its stored input behavior and path messages, accepting
no separate handler. `closed_eq_concrete_iff` characterizes agreement with a concrete claim by
statement and observable-answer equality, without asserting honesty or relation membership.

`TypeTree.sourceAfter` is one source context for the final accumulated access signature. Its
environment contains the initial handler and the messages along that branch. It does not choose
messages for unvisited branches or assert that arbitrary structural paths are inhabited.

## Sumcheck oracle roles

The single-round verifier checks the sent polynomial and evaluates it for the next target. Its
`outputOracle` instead retains the input oracle. This distinction allows a dishonest message to
pass the local sum check while the closed output relation fails; it is essential for soundness.
`degreeModel` interprets the degree guarantee already carried by the refined message type, and
`honestClaim` gives the corresponding concrete claim. `projectionOracle` answers univariate round
queries by the existing multivariate projection program.

`honestRun` is an algebraic normal form; `executeCore_honest` proves the actual executor returns it
under the input sum premise. Sampled perfect completeness additionally requires a lossless
challenge program. These completeness theorems do not establish adversarial soundness.

`legacy_input_iff` and `legacy_output_iff` give both directions of relation correspondence for
arbitrary concrete claims. `legacy_honest_verifier_correspondence` is narrower: it compares honest
executions. The legacy verifier reads the input polynomial for its next target, while the typed
verifier reads the sent polynomial. Their arbitrary-message executions are not identified.

## Other interaction names

`RoleDecoration.toExplicitRoles` fills the implicit sender role at oracle nodes while retaining
the oracle tree. `toTypeTreeRoles` also projects to the ordinary type tree. The distinction is
between explicit role information and a change of tree representation.

`Verifier.liftAccessImpl` lifts pure access answers into the verifier's computation monad and
combines them with ambient queries. The plain reduction API uses `Tree` for its type-tree
parameter and `r₁.then r₂` for sequential composition. `Reduction.execute_then` describes execution
in that order. Node contexts such as `RoleContext` retain their names: these are indexed
assignments over nodes, following PolyFun's context convention.

## Migrating callers

Update source operations before replacing other identifiers. The old `tensor` and new `tensor`
have different query types, so a compatibility alias cannot preserve both meanings. Replace old
`tensor` uses by `sum` first, then old `parallel` uses by `tensor`. Keep upstream `PFunctor.tensor`
unchanged. For named contexts and their views, replace old `tensor` uses by `disjointUnion`.

| Previous API | Current API |
| --- | --- |
| `SourceCtx.tensor`, `tensor_handler_inl/inr` | `SourceCtx.sum`, `sum_handler_inl/inr` |
| `SourceCtx.parallel`, `parallel_handler` | `SourceCtx.tensor`, `tensor_handler` |
| `SourceCtx.family`, `family_handler` | `SourceCtx.sigma`, `sigma_handler` |
| `SourceHom.familyMap`, `inFamily` | `SourceHom.sigmaMap`, `sigmaInj` |
| `SourceHom.onEnv` | `SourceHom.pullEnv` |
| `ResourceCatalog` | `OracleModel` |
| Catalog `Object`, `Descriptor` parameters | Model `Realization`, `PropertySymbol` parameters |
| Catalog `meaning`, `required`, `valid` | Model `satisfies`, `promised`, `satisfies_promises` |
| `ResourceCatalog.realizes` | `OracleModel.satisfies_guarantee` |
| `ResourceSchema` | `NamedContext` |
| `SchemaHom` | `NamedContext.Inclusion` |
| `ResourceView` | `NamedContext.View` |
| Context `Slot`, view `Handle` | `Index` |
| Context/view `key`, inclusion `key_eq` | `name`, `name_eq` |
| View `resolve` | `toIndex` |
| Context/view `tensor` | `disjointUnion` |
| `tensorSourceEquiv` | `disjointUnionSourceEquiv` |
| `RoleDecoration.toRuntimeRoles` | `RoleDecoration.toExplicitRoles` |
| `Verifier.readImpl` | `Verifier.liftAccessImpl` |
| `Interaction.Reduction.comp`, `execute_comp` | `Interaction.Reduction.then`, `execute_then` |
| `OracleFamily.ι`, `Obj`, `oracle` | `Index`, `Realization`, `interface` |
| `OracleFamily.answerData`, `asSource` | `behaviorOfRealizations`, `asBehaviorSource` |
| `VirtualOracle.mapSource` (program argument) | `VirtualOracle.substSource` |
| `VirtualOracle.rebase` (`SourceHom` argument) | `VirtualOracle.mapSource` |
| `VirtualOracle.tensorWeaken`, `substWith` | `sumWeaken`, `substWithSuffix` |
| `OracleClaim`, `DataClaim` | `OpenClaim`, `ConcreteClaim` |
| `TypeTree.sourcesAfter`, `sourcesAfter_handler` | `sourceAfter`, `sourceAfter_handler` |
| `CoreRun.closed_eq_data_iff` | `CoreRun.closed_eq_concrete_iff` |
| Single-round `degreeCatalog`, `honestData` | `degreeModel`, `honestClaim` |
| Single-round `outputView`, `projectionView` | `outputOracle`, `projectionOracle` |
| `executeSampled_measure_complete` | `executeSampled_measureCompleteness` |
| `legacy_verifier_correspondence` | `legacy_honest_verifier_correspondence` |
| `ProverOutputRealizes`, `proverOutputRealizes_iff` | `ConcreteClaim.closesTo`, `closesTo_iff` |
| `ClaimSchema`, `ClaimSchema.oracle` | `ClaimFamily`, `ClaimFamily.closedOracle` |
| Claim `rebase`, `closeWith_rebase` | `mapSource`, `closeWith_mapSource` |
| Claim `substWith`, `closeWith_substWith` | `substWithSuffix`, `closeWith_substWithSuffix` |

For virtual oracles, rename old `mapSource` uses to `substSource` before renaming `rebase` to
`mapSource`. Apply the same substitutions to associated theorem names and explicit `Tree` named arguments
(previously `Context`) in the plain reduction API. The legacy `Reduction` API outside
`Interaction` is unchanged. File and import paths remain unchanged.

After migration, run `lake build` and `lake test`. The
[source examples](../../ArkLibTest/Interaction/Oracle/SourceExample.lean) distinguish query sums
from paired queries; the [context examples](../../ArkLibTest/Interaction/Oracle/ResourceExample.lean)
exercise disjointness, aliasing, dependent interpretation, and promise preservation.
